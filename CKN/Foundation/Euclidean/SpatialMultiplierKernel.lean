-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.DegreeOneSymbol
import CKN.Foundation.Heat.Basic

/-!
# The spatial Fourier multiplier applied to the heat kernel

External Input `ext:heat-kernel` of `paper/ckn.tex` records the size, gradient
and time-derivative bounds of `ς(D)W₊`, where `W₊(t,x) = 1_{t>0}(4πt)^{-3/2}
e^{-|x|²/(4t)}` and `ς(D)` is the spatial Fourier multiplier of a symbol `ς`
smooth away from the origin and homogeneous of degree one; the display
`eq:heat-kernel-bounds` in the proof of Proposition `prop:heat-morrey-hoelder`
is the same list.

At each positive time the spatial Fourier transform of `W₊(·,t)` is
`e^{-t|ξ|²}` in the paper's normalization `ĝ(ξ) = ∫ g(y) e^{-i y·ξ} dy`, so
`ς(D)W₊(·,t)` is the inverse transform `(2π)^{-3} ∫ e^{i x·ξ} ς(ξ) e^{-t|ξ|²} dξ`.
This file records that kernel, its causal vanishing for nonpositive times, and
the fact that the defining frequency integral converges absolutely for every
symbol of the class.  The three pointwise estimates themselves are the content
of the external input and are not proved here.
-/

open scoped BigOperators
open Set MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat

/-- The integrand of the frequency integral for `ς(D)W₊` at the space-time
point `(x,t)`: the phase `e^{i x·ξ}`, the symbol `ς(ξ)`, and the Gaussian
`e^{-t|ξ|²}` that is the spatial Fourier transform of `W₊(·,t)`. -/
def spatialMultiplierHeatIntegrand (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) (ξ : Vec3) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) * σ ξ *
    Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))

/-- The kernel `ς(D)W₊` of External Input `ext:heat-kernel`, written as the
inverse spatial Fourier integral at positive times and extended by zero to
nonpositive times, as `W₊` itself is.  The value on the time-zero hyperplane is
the causal one; a spatial multiplier is nonlocal, so no pointwise derivative
claim is made across that hyperplane. -/
def spatialMultiplierHeatKernel (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) : ℂ :=
  if 0 < t then
    (2 * Real.pi : ℂ) ^ (-3 : ℤ) * ∫ ξ : Vec3, spatialMultiplierHeatIntegrand σ x t ξ
  else 0

/-- Scalar majorant: `√s e^{-a s} ≤ (1 + 2/a) e^{-(a/2) s}` for `s ≥ 0`, `a > 0`. -/
private theorem sqrt_mul_exp_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    Real.sqrt s * Real.exp (-(a * s)) ≤
      (1 + 2 / a) * Real.exp (-(a / 2 * s)) := by
  set E := Real.exp (-(a / 2 * s)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hEle : E ≤ 1 := by
    rw [hE]
    exact Real.exp_le_one_iff.2 (by nlinarith only [ha, hs])
  have hsqrt : Real.sqrt s ≤ 1 + s := by
    have hle : s ≤ (1 + s) ^ 2 := by nlinarith only [hs, sq_nonneg s]
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by linarith only [hs])] at h
  have hlin : s * E ≤ 2 / a := by
    have hx : a / 2 * s ≤ Real.exp (a / 2 * s) := by
      have h := Real.add_one_le_exp (a / 2 * s)
      linarith only [h]
    have hFpos : 0 < Real.exp (a / 2 * s) := Real.exp_pos _
    have hinv : E = (Real.exp (a / 2 * s))⁻¹ := by
      rw [hE, Real.exp_neg]
    rw [hinv, mul_inv_le_iff₀ hFpos]
    have h2a : (0 : ℝ) < 2 / a := by positivity
    have hmul := mul_le_mul_of_nonneg_left hx h2a.le
    have heq : 2 / a * (a / 2 * s) = s := by field_simp
    linarith only [hmul, heq]
  have hinner : Real.sqrt s * E ≤ 1 + 2 / a := by
    have h1 : Real.sqrt s * E ≤ (1 + s) * E := by
      apply mul_le_mul_of_nonneg_right hsqrt hEpos.le
    have h2 : (1 + s) * E = E + s * E := by ring
    linarith only [h1, h2, hEle, hlin]
  have hsplit : Real.exp (-(a * s)) = E * E := by
    rw [hE, ← Real.exp_add]
    ring_nf
  calc Real.sqrt s * Real.exp (-(a * s))
      = (Real.sqrt s * E) * E := by rw [hsplit]; ring
    _ ≤ (1 + 2 / a) * E := by
        exact mul_le_mul_of_nonneg_right hinner hEpos.le

private theorem integrable_gaussian_half {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Vec3 => Real.exp (-(t / 2 * vec3EuclideanNorm ξ ^ 2))) volume := by
  have ht' : (0 : ℝ) < 1 / (2 * t) := by positivity
  have hHK := heatKernel_integrable (t := 1 / (2 * t)) ht'
  have hc : ((4 * Real.pi * (1 / (2 * t))) ^ (-(3 : ℝ) / 2)) ≠ 0 := by
    have : (0 : ℝ) < 4 * Real.pi * (1 / (2 * t)) := by positivity
    positivity
  have hform : (fun ξ : Vec3 => Real.exp (-(t / 2 * vec3EuclideanNorm ξ ^ 2))) =
      fun ξ : Vec3 => ((4 * Real.pi * (1 / (2 * t))) ^ (-(3 : ℝ) / 2))⁻¹ *
        heatKernel ξ (1 / (2 * t)) := by
    funext ξ
    rw [heatKernel_eq_formula_sum ht', ← mul_assoc, inv_mul_cancel₀ hc, one_mul,
      vec3EuclideanNorm_sq]
    congr 1
    field_simp
    ring
  rw [hform]
  exact hHK.const_mul _

/-- The frequency integral defining `ς(D)W₊` at positive time converges
absolutely for every symbol of the class of External Input `ext:heat-kernel`:
the Gaussian `e^{-t|ξ|²}` beats the linear growth of the symbol. -/
theorem integrable_spatialMultiplierHeatIntegrand {σ : Vec3 → ℂ}
    (hcont : ContinuousOn σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) (x : Vec3) {t : ℝ} (ht : 0 < t) :
    Integrable (spatialMultiplierHeatIntegrand σ x t) volume := by
  obtain ⟨C, hC0, hCb⟩ := norm_le_of_isDegreeOneHomogeneous hcont hhom
  have hσmeas : AEStronglyMeasurable σ volume := by
    have h := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : Vec3)).compl
    rwa [restrict_compl_singleton (0 : Vec3)] at h
  have hphase : Continuous fun ξ : Vec3 =>
      Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) := by
    apply Complex.continuous_exp.comp
    apply continuous_const.mul
    exact Complex.continuous_ofReal.comp
      (continuous_finsetSum _ fun j _ => (continuous_apply j).const_mul _)
  have hgauss : Continuous fun ξ : Vec3 =>
      Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) := by
    apply Complex.continuous_exp.comp
    exact (Complex.continuous_ofReal.comp
      ((continuous_vec3EuclideanNorm.pow 2).const_mul t)).neg
  have hmeas : AEStronglyMeasurable (spatialMultiplierHeatIntegrand σ x t) volume :=
    (hphase.aestronglyMeasurable.mul hσmeas).mul hgauss.aestronglyMeasurable
  refine Integrable.mono'
    (g := fun ξ : Vec3 => C * (1 + 2 / t) *
      Real.exp (-(t / 2 * vec3EuclideanNorm ξ ^ 2)))
    ((integrable_gaussian_half ht).const_mul _) hmeas ?_
  filter_upwards with ξ
  have hnormphase : ‖Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hre : (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)).re =
      -(t * vec3EuclideanNorm ξ ^ 2) := by
    simp only [Complex.neg_re, Complex.ofReal_re]
  have hnormgauss : ‖Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ =
      Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
    rw [Complex.norm_exp, hre]
  have hs : (0 : ℝ) ≤ vec3EuclideanNorm ξ ^ 2 := sq_nonneg _
  have hsqrt : Real.sqrt (vec3EuclideanNorm ξ ^ 2) = vec3EuclideanNorm ξ :=
    Real.sqrt_sq (vec3EuclideanNorm_nonneg ξ)
  have hmaj := sqrt_mul_exp_le (a := t) (s := vec3EuclideanNorm ξ ^ 2) ht hs
  rw [hsqrt] at hmaj
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) :=
    (Real.exp_pos _).le
  calc ‖spatialMultiplierHeatIntegrand σ x t ξ‖
      = ‖σ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
        unfold spatialMultiplierHeatIntegrand
        rw [norm_mul, norm_mul, hnormphase, hnormgauss, one_mul]
    _ ≤ (C * vec3EuclideanNorm ξ) * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
        gcongr
        exact hCb ξ
    _ = C * (vec3EuclideanNorm ξ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) := by ring
    _ ≤ C * ((1 + 2 / t) * Real.exp (-(t / 2 * vec3EuclideanNorm ξ ^ 2))) := by
        gcongr
    _ = C * (1 + 2 / t) * Real.exp (-(t / 2 * vec3EuclideanNorm ξ ^ 2)) := by ring

/-- The multiplier kernel inherits the causality of `W₊`: it vanishes at every
nonpositive time. -/
theorem spatialMultiplierHeatKernel_of_nonpos (σ : Vec3 → ℂ) (x : Vec3) {t : ℝ}
    (ht : t ≤ 0) : spatialMultiplierHeatKernel σ x t = 0 := by
  simp [spatialMultiplierHeatKernel, not_lt.mpr ht]

end CKN.Foundation.Euclidean
