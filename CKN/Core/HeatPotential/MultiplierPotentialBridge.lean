-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.SliceMultiplierConvolution

/-!
# The general-symbol heat potential and what it is a potential of

Display `eq:heat-potential` of `paper/ckn.tex` (line 2887) defines

`h = W₊ * (F + ∑ₖ ςₖ(D) Gₖ)`,

the convolution taken over `ℝ³ × ℝ` and the multipliers acting in the space variable
only.  The kernel-side object that the estimates of `prop:heat-morrey-hoelder` are
actually written for is the sum of convolutions against `W₊` and against the kernels
`ςₖ(D)W₊`; the two are identified in the proof by the sentence at line 2921.

This file records both objects and proves the identification, so that a consumer of the
kernel formula is entitled to call it the potential of `F + ∑ₖ ςₖ(D)Gₖ` rather than of
an unrelated family of kernels.  The multiplier sits under the time integral, applied to
each causal heat slice, which is the only placement at which it is an absolutely
convergent frequency integral; see the module docstring of
`CKN/Foundation/Heat/SliceMultiplierConvolution.lean`.

The space-time variable is the product `Vec3 × ℝ`, as it is for the distribution carrier
`heatKernelPlusDistribution`, and not the parabolic metric type; the two carry the same
measure and the same topology.
-/

open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic

/-- The causal heat potential `W₊ * F` of a scalar source, written as a convolution
against the kernel `W₊` of `ext:heat-kernel`. -/
def causalHeatPotential (F : Vec3 × ℝ → ℂ) (w : Vec3 × ℝ) : ℂ :=
  ∫ v : Vec3 × ℝ, (heatKernelPlus ((w.1 - v.1, w.2 - v.2) : ParabolicPoint) : ℂ) * F v

/-- The kernel-side representative of `eq:heat-potential`: the causal heat potential of
the scalar source plus, for each symbol, the convolution of that source with the kernel
`ςₖ(D)W₊`. -/
def causalMultiplierPotential {K : ℕ} (σ : Fin K → Vec3 → ℂ)
    (F : Vec3 × ℝ → ℂ) (G : Fin K → Vec3 × ℝ → ℂ) (w : Vec3 × ℝ) : ℂ :=
  causalHeatPotential F w +
    ∑ k, ∫ v : Vec3 × ℝ,
      spatialMultiplierHeatKernel (σ k) (w.1 - v.1) (w.2 - v.2) * G k v

/-- The causal heat potential is the time integral of the heat-smoothed slices of its
source: `W₊ * F (x,t) = ∫ (W(·,t-s) * F(·,s))(x) ds`.  No causal case split is needed:
`W₊` and `W` agree at every time, both vanishing for nonpositive times. -/
theorem causalHeatPotential_eq_integral_slice {F : Vec3 × ℝ → ℂ} (w : Vec3 × ℝ)
    (hint : Integrable (fun v : Vec3 × ℝ =>
      (heatKernelPlus ((w.1 - v.1, w.2 - v.2) : ParabolicPoint) : ℂ) * F v) volume) :
    causalHeatPotential F w =
      ∫ s : ℝ, spatialHeatConv (w.2 - s) (fun y : Vec3 => F (y, s)) w.1 := by
  simp only [causalHeatPotential]
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [spatialHeatConv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact congrArg (fun r : ℝ => (r : ℂ) * F (y, s))
    (heatKernelPlus_eq_heatKernel ((w.1 - y, w.2 - s) : ParabolicPoint))

/-- **`eq:heat-potential`, identified.**  The kernel-side potential is the potential of
`F + ∑ₖ ςₖ(D)Gₖ`: each multiplier slot is the time integral of `ςₖ(D)` applied in space
to the causal heat slice of `Gₖ`.

The integrability hypotheses are the ones the paper discharges from the local
integrability of `W₊` and of `ςₖ(D)W₊` — the first and fourth clauses of
`eq:heat-kernel-bounds` — together with the bounded support of the sources; they are the
side conditions of the two Fubini steps and carry no part of the conclusion. -/
theorem causalMultiplierPotential_eq_slice_form {K : ℕ} {σ : Fin K → Vec3 → ℂ}
    (hcont : ∀ k, ContinuousOn (σ k) ({0}ᶜ : Set Vec3))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k))
    {F : Vec3 × ℝ → ℂ} {G : Fin K → Vec3 × ℝ → ℂ}
    (hGslice : ∀ k, ∀ᵐ s : ℝ, Integrable (fun y : Vec3 => G k (y, s)) volume)
    (w : Vec3 × ℝ)
    (hF : Integrable (fun v : Vec3 × ℝ =>
      (heatKernelPlus ((w.1 - v.1, w.2 - v.2) : ParabolicPoint) : ℂ) * F v) volume)
    (hG : ∀ k, Integrable (fun v : Vec3 × ℝ =>
      spatialMultiplierHeatKernel (σ k) (w.1 - v.1) (w.2 - v.2) * G k v) volume) :
    causalMultiplierPotential σ F G w =
      (∫ s : ℝ, spatialHeatConv (w.2 - s) (fun y : Vec3 => F (y, s)) w.1) +
        ∑ k, ∫ s : ℝ, spatialMultiplierApply (σ k)
          (spatialHeatConv (w.2 - s) (fun y : Vec3 => G k (y, s))) w.1 := by
  rw [causalMultiplierPotential, causalHeatPotential_eq_integral_slice w hF]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  exact integral_multiplierHeatKernel_eq_integral_sliceMultiplier (hcont k) (hhom k)
    (hGslice k) w (hG k)

/-- The multiplier slot of the potential vanishes on the zero source, so the
identification above is not vacuous through a degenerate right-hand side. -/
@[simp]
theorem causalMultiplierPotential_zero_sources {K : ℕ} (σ : Fin K → Vec3 → ℂ)
    (w : Vec3 × ℝ) :
    causalMultiplierPotential σ (fun _ => 0) (fun _ _ => 0) w = 0 := by
  simp [causalMultiplierPotential, causalHeatPotential]

end CKN.Core.HeatPotential
