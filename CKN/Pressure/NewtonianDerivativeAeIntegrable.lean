-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.HlsRieszPotentialFinite
import CKN.Pressure.KernelMeasurability
import CKN.Pressure.PkBoundsP7

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean

set_option autoImplicit false

namespace CKN

/-! ## Absolute convergence of the derivative-Newtonian convolution for
`L^{5/2}` functions, almost everywhere

The four theorems below state that for an `L^{5/2}` function `g`, the signed
derivative-Newtonian convolution
`∫ ∂ᵢN(x - y) g(y) dy` is absolutely convergent for almost every `x`. -/

/-- The enorm of the `i`-th spatial derivative of the Newtonian kernel at `x - y`
is bounded by a constant times the Riesz kernel. -/
theorem spatialDeriv_newtonianKernel_enorm_le_rieszKernelOne {i : Fin 3} {x y : Vec3}
    (hxy : x ≠ y) :
    ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hb := CKN.Foundation.Heat.newtonianKernel_spatialDeriv_size_bound hz i
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
  have hpi : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  calc
    ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)‖ₑ =
        ENNReal.ofReal |CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
          (x - y)| := by
      simpa only [Real.norm_eq_abs] using
        (ofReal_norm
          (CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y))).symm
    _ ≤ ENNReal.ofReal ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ 2)⁻¹) :=
      ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal ((4 * Real.pi)⁻¹) *
        (ENNReal.ofReal ‖x - y‖) ^ (-2 : ℝ) := by
      rw [ENNReal.ofReal_mul hpi]
      rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < 4 * Real.pi)]
      rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < ‖x - y‖ ^ 2)]
      have hpow : ENNReal.ofReal (‖x - y‖ ^ 2) =
          (ENNReal.ofReal ‖x - y‖) ^ (2 : ℕ) :=
        ENNReal.ofReal_pow hnorm.le 2
      have hinv := congrArg Inv.inv hpow
      rw [hinv, ← ENNReal.rpow_natCast, ENNReal.rpow_neg]
      norm_num
    _ = ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y := by
      rw [rieszKernelOne, dist_eq_norm]

/-- The `∫⁻` of the enorm of the integrand is bounded by a constant times the Riesz
potential. -/
theorem lintegral_enorm_spatialDeriv_newtonianKernel_mul_le (i : Fin 3) (g : Vec3 → ℝ)
    (x : Vec3) :
    ∫⁻ y, ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y) * g y‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszPotentialOne g x := by
  have hkernel : ∀ᵐ y ∂volume,
      ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)‖ₑ ≤
        ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y := by
    filter_upwards [Measure.ae_ne volume x] with y hy
    exact spatialDeriv_newtonianKernel_enorm_le_rieszKernelOne hy.symm
  calc
    ∫⁻ y, ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
        (x - y) * g y‖ₑ ≤
        ∫⁻ y, (ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y) *
          ENNReal.ofReal |g y| := by
      apply lintegral_mono_ae
      filter_upwards [hkernel] with y hy
      calc
        ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
            (x - y) * g y‖ₑ =
            ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
              (x - y)‖ₑ * ENNReal.ofReal |g y| := by
          have hg : ENNReal.ofReal |g y| = ‖g y‖ₑ := by
            simpa only [Real.norm_eq_abs] using ofReal_norm (g y)
          rw [hg, ← enorm_mul]
        _ ≤ (ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszKernelOne x y) *
            ENNReal.ofReal |g y| :=
          mul_le_mul_of_nonneg_right hy (by positivity)
    _ = ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszPotentialOne g x := by
      rw [rieszPotentialOne]
      rw [← lintegral_const_mul' (ENNReal.ofReal ((4 * Real.pi)⁻¹))
        _ ENNReal.ofReal_ne_top]
      ac_rfl

/-- For a fixed `x` where the Riesz potential is finite, the derivative-Newtonian
convolution with `g` is integrable. -/
theorem integrable_spatialDeriv_newtonianKernel_mul_of_rieszPotentialOne_ne_top
    {g : Vec3 → ℝ} (hg : AEStronglyMeasurable g volume) (i : Fin 3) {x : Vec3}
    (hx : rieszPotentialOne g x ≠ ∞) :
    Integrable (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y) * g y)
      volume := by
  have hmeas : AEStronglyMeasurable
      (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y) * g y)
      volume :=
    ((measurable_spatialDeriv_newtonianKernel i).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hg
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    ∫⁻ y, ‖CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y) * g y‖ₑ ≤
      ENNReal.ofReal ((4 * Real.pi)⁻¹) * rieszPotentialOne g x :=
      lintegral_enorm_spatialDeriv_newtonianKernel_mul_le i g x
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hx)

/-- For an `L^{5/2}` function `g`, the derivative-Newtonian convolution is integrable
for almost every `x`. -/
theorem ae_integrable_spatialDeriv_newtonianKernel_mul {g : Vec3 → ℝ} (hg : Measurable g)
    (hfinite : (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) < ∞) (i : Fin 3) :
    ∀ᵐ x ∂volume, Integrable
      (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y) * g y) volume := by
  filter_upwards [ae_rieszPotentialOne_lt_top hg hfinite] with x hx
  exact integrable_spatialDeriv_newtonianKernel_mul_of_rieszPotentialOne_ne_top
    hg.aestronglyMeasurable i hx.ne

end CKN
