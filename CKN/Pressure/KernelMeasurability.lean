-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.NewtonianRepresentation
import CKN.Pressure.LeibnizLaplacian

open MeasureTheory
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN

/-- If `k` is measurable, `g` is integrable, and `|k(x - y)| ≤ A` whenever `g y ≠ 0`,
then the product `k(x - ·) * g` is integrable. -/
theorem integrable_kernel_mul_of_abs_le_on_support
    {k g : Vec3 → ℝ} {x : Vec3} {A : ℝ}
    (hk : Measurable k) (hg : Integrable g volume)
    (hpoint : ∀ y, g y ≠ 0 → |k (x - y)| ≤ A) :
    Integrable (fun y => k (x - y) * g y) volume := by
  have hmeas : AEStronglyMeasurable (fun y => k (x - y) * g y) volume := by
    exact (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  refine (hg.norm.const_mul A).mono' hmeas ?_
  filter_upwards [] with y
  by_cases hgy : g y = 0
  · simp [hgy]
  · simpa only [Real.norm_eq_abs, abs_mul, mul_comm] using
      (mul_le_mul_of_nonneg_right (hpoint y hgy) (abs_nonneg (g y)))

/-- The Newtonian kernel `z ↦ 1 / (4π |z|₂)` is measurable. -/
theorem measurable_newtonianKernel : Measurable (newtonianKernel : Vec3 → ℝ) := by
  have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  unfold newtonianKernel
  exact measurable_const.div (measurable_const.mul hnorm)

/-- The negated Newtonian kernel is measurable. -/
theorem measurable_neg_newtonianKernel :
    Measurable (fun z : Vec3 => -newtonianKernel z) :=
  measurable_newtonianKernel.neg

/-- Each first-order spatial derivative of the Newtonian kernel is measurable. -/
theorem measurable_spatialDeriv_newtonianKernel (i : Fin 3) :
    Measurable (fun z : Vec3 => CKN.spatialDeriv newtonianKernel i z) := by
  unfold CKN.spatialDeriv
  exact measurable_fderiv_apply_const ℝ newtonianKernel (CKN.basisVec i)

/-- Each second-order spatial derivative of the Newtonian kernel is measurable. -/
theorem measurable_spatialDeriv_spatialDeriv_newtonianKernel (i j : Fin 3) :
    Measurable (fun z : Vec3 => CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j z) := by
  unfold CKN.spatialDeriv
  exact measurable_fderiv_apply_const ℝ (CKN.spatialDeriv newtonianKernel i)
    (CKN.basisVec j)

end CKN
