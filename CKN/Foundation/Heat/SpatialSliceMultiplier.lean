-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The spatial Fourier multiplier acting slice by slice

Proposition `prop:heat-morrey-hoelder` of `paper/ckn.tex` builds
the potential `eq:heat-potential`

`h = W₊ * (F + ∑ₖ ςₖ(D) Gₖ)`,

in which the multipliers `ςₖ(D)` act **in the space variable only** while the
convolution with `W₊` is taken over `ℝ³ × ℝ`.  This file writes `ς(D)` by the
paper's own formula, in the paper's normalization

`ĝ(ξ) = ∫ g(y) e^{-i y·ξ} dy`,  `ς(D)g(x) = (2π)^{-3} ∫ e^{i x·ξ} ς(ξ) ĝ(ξ) dξ`,

and its slice-wise extension to a space-time function: at the point `(x,t)` the
operator sees only the time-`t` slice `y ↦ u(y,t)`.

The reason the definition is written out rather than taken from the ambient
library: the symbols of `ext:heat-kernel` are homogeneous of degree one and
therefore **not** smooth at the origin, so they are outside the temperate-growth
class that the library's Fourier-multiplier construction needs, and the ambient
spatial type `Fin 3 → ℝ` carries the supremum norm rather than an inner product,
which is what the library's Fourier transform is stated for.  Both formulas
below are elementary absolutely convergent integrals and need neither.

The main result is the identification

`ς(D) W(·,t) = spatialMultiplierHeatKernel ς (·) t`   for **every** `t`,

so the kernel of `CKN/Foundation/Euclidean/SpatialMultiplierKernel.lean`, which
is written as a bare inverse Fourier integral with a causal cut at `t ≤ 0`, is
literally the multiplier applied to the heat kernel — on the causal side as well,
where both sides vanish.  Its proof contains the spatial Gaussian transform
`Ŵ(·,t)(ξ) = e^{-t|ξ|²}` in the ambient type, which is proved here from the
one-dimensional Gaussian Fourier integral and the product structure of Lebesgue
measure on `Fin 3 → ℝ`.
-/

open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Euclidean CKN.Foundation.Parabolic

/-! ### The paper's spatial transform and multiplier -/

/-- The spatial Fourier transform in the normalization of
`ext:heat-kernel`: `ĝ(ξ) = ∫ g(y) e^{-i y·ξ} dy`. -/
def spatialFourierIntegral (g : Vec3 → ℂ) (ξ : Vec3) : ℂ :=
  ∫ y : Vec3, g y * Complex.exp (-(Complex.I * ((∑ j : Fin 3, y j * ξ j : ℝ) : ℂ)))

/-- The frequency integrand of `ς(D)g` at the spatial point `x`: the inverse
phase `e^{i x·ξ}`, the symbol `ς(ξ)` and the transform `ĝ(ξ)`. -/
def spatialMultiplierIntegrand (σ g : Vec3 → ℂ) (x ξ : Vec3) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) * σ ξ *
    spatialFourierIntegral g ξ

/-- The spatial Fourier multiplier `ς(D)` of `prop:heat-morrey-hoelder` applied to
a function of the space variable:
`ς(D)g(x) = (2π)^{-3} ∫ e^{i x·ξ} ς(ξ) ĝ(ξ) dξ`. -/
def spatialMultiplierApply (σ g : Vec3 → ℂ) (x : Vec3) : ℂ :=
  (2 * Real.pi : ℂ) ^ (-3 : ℤ) * ∫ ξ : Vec3, spatialMultiplierIntegrand σ g x ξ

/-- `ς(D)` acting in the space variable only, at each fixed time: the value at the
space-time point `z` is `ς(D)` applied to the time-`z.2` slice of `u`, evaluated at
`z.1`.  This is the sense in which `eq:heat-potential` applies its multipliers. -/
def sliceMultiplierApply (σ : Vec3 → ℂ) (u : Vec3 × ℝ → ℂ) (z : Vec3 × ℝ) : ℂ :=
  spatialMultiplierApply σ (fun y => u (y, z.2)) z.1

/-! ### Values at the degenerate data -/

@[simp]
theorem spatialFourierIntegral_zero (ξ : Vec3) :
    spatialFourierIntegral (fun _ => 0) ξ = 0 := by
  simp [spatialFourierIntegral]

@[simp]
theorem spatialMultiplierApply_zero_fun (σ : Vec3 → ℂ) (x : Vec3) :
    spatialMultiplierApply σ (fun _ => 0) x = 0 := by
  simp [spatialMultiplierApply, spatialMultiplierIntegrand]

@[simp]
theorem spatialMultiplierApply_zero_symbol (g : Vec3 → ℂ) (x : Vec3) :
    spatialMultiplierApply (fun _ => 0) g x = 0 := by
  simp [spatialMultiplierApply, spatialMultiplierIntegrand]

/-- At the zero frequency the transform is the total mass of `g`.  The phase has
dropped out, so this value is the same for either sign convention and by itself
fixes neither.  What fixes the normalization `(2π)^{-3}` of `spatialMultiplierApply`
is the constant symbol `fun _ => 1`, for which the operator has to be — and is — the
identity on a heat-kernel slice; and what fixes the relative sign of the forward and
inverse phases is the translation split `e^{i(x-y)·ξ} = e^{i x·ξ} e^{-i y·ξ}` used in
`spatialMultiplierApply_spatialHeatConv`, together with agreement with
`spatialMultiplierHeatIntegrand`. -/
theorem spatialFourierIntegral_at_zero (g : Vec3 → ℂ) :
    spatialFourierIntegral g 0 = ∫ y : Vec3, g y := by
  simp [spatialFourierIntegral]

/-! ### The spatial Gaussian transform in the ambient type -/

/-- One coordinate factor of the Gaussian carrying the forward phase. -/
private def gaussianPhaseFactor (t c u : ℝ) : ℂ :=
  (((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * (u : ℂ) ^ 2) *
    Complex.exp (-(Complex.I * ((u * c : ℝ) : ℂ)))

private theorem gaussianPhaseFactor_integral {t : ℝ} (ht : 0 < t) (c : ℝ) :
    ∫ u : ℝ, gaussianPhaseFactor t c u = Complex.exp (-((t * c ^ 2 : ℝ) : ℂ)) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hbre : (0 : ℝ) < (((1 / (4 * t) : ℝ) : ℂ)).re := by
    simpa using hb
  have hrw : ∀ u : ℝ, gaussianPhaseFactor t c u =
      (((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (-(c : ℂ)) * (u : ℂ)) *
          Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * (u : ℂ) ^ 2)) := by
    intro u
    unfold gaussianPhaseFactor
    have hphase : Complex.exp (-(Complex.I * ((u * c : ℝ) : ℂ))) =
        Complex.exp (Complex.I * (-(c : ℂ)) * (u : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [hphase]
    ring
  simp_rw [hrw]
  rw [integral_const_mul, fourierIntegral_gaussian hbre (-(c : ℂ))]
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hdiv : ((Real.pi : ℂ) / ((1 / (4 * t) : ℝ) : ℂ)) = ((4 * Real.pi * t : ℝ) : ℂ) := by
    have h4t : ((1 / (4 * t) : ℝ) : ℂ) ≠ 0 := by
      simpa using (ne_of_gt hb)
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := by
      simpa using (ne_of_gt ht)
    push_cast
    field_simp
  rw [hdiv]
  have hhalf : ((4 * Real.pi * t : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (((4 * Real.pi * t) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hpos.le]
    norm_num
  rw [hhalf]
  have hcancel : (((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      (((4 * Real.pi * t) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hpos]
    norm_num
  have hexp : (-(-(c : ℂ)) ^ 2 / (4 * ((1 / (4 * t) : ℝ) : ℂ))) =
      -((t * c ^ 2 : ℝ) : ℂ) := by
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := by
      simpa using (ne_of_gt ht)
    push_cast
    field_simp
  rw [hexp, ← mul_assoc, hcancel, one_mul]

private theorem heatKernel_phase_eq_prod {t : ℝ} (ht : 0 < t) (ξ y : Vec3) :
    (heatKernel y t : ℂ) *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, y j * ξ j : ℝ) : ℂ))) =
      ∏ j : Fin 3, gaussianPhaseFactor t (ξ j) (y j) := by
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  unfold gaussianPhaseFactor
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum,
    ← Complex.exp_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcube : (((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) ^ 3 =
      (((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow,
      ← Real.rpow_natCast ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2)) 3,
      ← Real.rpow_mul hpos.le]
    norm_num
  have hgauss : Complex.exp (∑ j : Fin 3, -((1 / (4 * t) : ℝ) : ℂ) * (y j : ℂ) ^ 2) =
      ((Real.exp ((-∑ i, y i ^ 2) / (4 * t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := by
      simpa using (ne_of_gt ht)
    field_simp
  have hphase : Complex.exp (∑ j : Fin 3, -(Complex.I * ((y j * ξ j : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * ((∑ j : Fin 3, y j * ξ j : ℝ) : ℂ))) := by
    congr 1
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hcube, hgauss, hphase, heatKernel_eq_formula_sum ht]
  push_cast
  ring

/-- The spatial Fourier transform of the heat kernel at a positive time is the
Gaussian `e^{-t|ξ|²}`; this is the normalization stated in
`CKN/Foundation/Euclidean/SpatialMultiplierKernel.lean`. -/
theorem spatialFourierIntegral_heatKernel {t : ℝ} (ht : 0 < t) (ξ : Vec3) :
    spatialFourierIntegral (fun y => (heatKernel y t : ℂ)) ξ =
      Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) := by
  have hvol : (volume : Measure Vec3) =
      Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) := volume_pi
  have hstep : spatialFourierIntegral (fun y => (heatKernel y t : ℂ)) ξ =
      ∫ y : Vec3, ∏ j : Fin 3, gaussianPhaseFactor t (ξ j) (y j) :=
    integral_congr_ae
      (Filter.Eventually.of_forall fun y => heatKernel_phase_eq_prod ht ξ y)
  rw [hstep, hvol, integral_fin_nat_prod_eq_prod
    (fun j : Fin 3 => fun u : ℝ => gaussianPhaseFactor t (ξ j) u)]
  simp_rw [gaussianPhaseFactor_integral ht]
  rw [← Complex.exp_sum]
  congr 1
  rw [vec3EuclideanNorm_sq]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- At zero frequency the Gaussian transform is the total mass `1`: the transform is
not the zero function, and the normalization above is pinned. -/
theorem spatialFourierIntegral_heatKernel_at_zero {t : ℝ} (ht : 0 < t) :
    spatialFourierIntegral (fun y => (heatKernel y t : ℂ)) 0 = 1 := by
  rw [spatialFourierIntegral_heatKernel ht, vec3EuclideanNorm_zero]
  norm_num

/-! ### The multiplier applied to the heat kernel -/

/-- On the causal side the heat kernel slice is the zero function. -/
theorem heatKernel_slice_eq_zero {t : ℝ} (ht : t ≤ 0) :
    (fun y : Vec3 => (heatKernel y t : ℂ)) = fun _ => 0 := by
  funext y
  rw [heatKernel_eq_zero_of_nonpos ht]
  norm_num

/-- The defining frequency integral of the multiplier kernel at a positive time. -/
private theorem spatialMultiplierHeatKernel_of_pos (σ : Vec3 → ℂ) (x : Vec3) {t : ℝ}
    (ht : 0 < t) :
    spatialMultiplierHeatKernel σ x t =
      (2 * Real.pi : ℂ) ^ (-3 : ℤ) * ∫ ξ : Vec3, spatialMultiplierHeatIntegrand σ x t ξ := by
  simp [spatialMultiplierHeatKernel, ht]

/-- The identification of the kernel of `ext:heat-kernel`: the inverse Fourier
integral `spatialMultiplierHeatKernel ς` is exactly `ς(D)` applied to the heat
kernel slice, at **every** time, the causal branch `t ≤ 0` included, where both
sides vanish. -/
theorem spatialMultiplierApply_heatKernel (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) :
    spatialMultiplierApply σ (fun y => (heatKernel y t : ℂ)) x =
      spatialMultiplierHeatKernel σ x t := by
  by_cases ht : 0 < t
  · have hint : ∀ ξ : Vec3,
        spatialMultiplierIntegrand σ (fun y => (heatKernel y t : ℂ)) x ξ =
          spatialMultiplierHeatIntegrand σ x t ξ := by
      intro ξ
      rw [spatialMultiplierIntegrand, spatialFourierIntegral_heatKernel ht,
        spatialMultiplierHeatIntegrand]
    rw [spatialMultiplierApply, spatialMultiplierHeatKernel_of_pos σ x ht]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hint)
  · rw [heatKernel_slice_eq_zero (le_of_not_gt ht), spatialMultiplierApply_zero_fun,
      spatialMultiplierHeatKernel_of_nonpos σ x (le_of_not_gt ht)]

/-- The causal kernel `W₊` gives the same identification, with the same value on the
causal side. -/
theorem spatialMultiplierApply_heatKernelPlus (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) :
    spatialMultiplierApply σ
        (fun y : Vec3 => (heatKernelPlus ((y, t) : ParabolicPoint) : ℂ)) x =
      spatialMultiplierHeatKernel σ x t := by
  have hslice : (fun y : Vec3 => (heatKernelPlus ((y, t) : ParabolicPoint) : ℂ)) =
      fun y : Vec3 => (heatKernel y t : ℂ) := by
    funext y
    exact congrArg Complex.ofReal (heatKernelPlus_eq_heatKernel ((y, t) : ParabolicPoint))
  rw [hslice, spatialMultiplierApply_heatKernel]

/-- The slice-wise form: applying `ς(D)` in space at each fixed time to the causal
heat kernel reproduces `spatialMultiplierHeatKernel` at every space-time point. -/
theorem sliceMultiplierApply_heatKernelPlus (σ : Vec3 → ℂ) (z : Vec3 × ℝ) :
    sliceMultiplierApply σ
        (fun w : Vec3 × ℝ => (heatKernelPlus ((w.1, w.2) : ParabolicPoint) : ℂ)) z =
      spatialMultiplierHeatKernel σ z.1 z.2 :=
  spatialMultiplierApply_heatKernelPlus σ z.1 z.2

end CKN.Foundation.Heat
