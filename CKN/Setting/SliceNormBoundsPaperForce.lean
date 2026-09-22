-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SpatialSliceNormIdentifyForce
import CKN.Setting.SliceTimeNormForce

open MeasureTheory Set
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace CKN

/-- Paper equation `eq:slice-norm-bounds`, force line: the `L^q(J_ρ)` time norm of the
`L^q(B_ρ)` force slice norm equals `ρ^(5/q - 3) * lambda q f z ρ`, i.e. the factor
`ρ^(5/q - 3)` times the scale quantity `lambda`. -/
theorem forceSpatialSliceNorm_timeNorm_eq_lambda
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, forceSpatialSliceNorm f z.1 ρ q s ^ q) ^ (1 / q : ℝ) =
      ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ) := by
  let B : Set Vec3 := vec3Ball z.1 ρ
  let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  have hqpos : 0 < q := lt_trans (by norm_num : (0 : ℝ) < 5 / 2) hsol.2.2.2.1
  have h_ae_eq : (fun s => forceSpatialSliceNorm f z.1 ρ q s ^ q) =ᵐ[volume.restrict T]
      (fun s => ‖(∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)‖ₑ ^ q) := by
    filter_upwards [forceSpatialSliceNorm_eq_ofReal_ae hsol z hρ hsub] with s hs
    rw [hs]
    have h_nonneg_int : 0 ≤ ∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q :=
      integral_nonneg fun y => Real.rpow_nonneg (vec3EuclideanNorm_nonneg _) _
    have h_nonneg_G : 0 ≤ (∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ) :=
      Real.rpow_nonneg h_nonneg_int _
    have h_pow_eq : ((∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)) ^ q =
        ∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q := by
      calc
        ((∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)) ^ q
            = (∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ ((1 / q : ℝ) * q) := by
          rw [Real.rpow_mul h_nonneg_int]
        _ = (∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 : ℝ) := by
          field_simp [hqpos.ne']
        _ = ∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q := by rw [Real.rpow_one]
    calc
      ENNReal.ofReal ((∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)) ^ q
          = ENNReal.ofReal (((∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)) ^ q) := by
        rw [ENNReal.ofReal_rpow_of_nonneg h_nonneg_G hqpos.le]
      _ = ENNReal.ofReal (∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) := by rw [h_pow_eq]
      _ = ‖(∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)‖ₑ ^ q := by
        rw [Real.enorm_eq_ofReal h_nonneg_G, ENNReal.ofReal_rpow_of_nonneg h_nonneg_G hqpos.le,
          h_pow_eq]
  have h_lintegral_eq : (∫⁻ s in T, forceSpatialSliceNorm f z.1 ρ q s ^ q) =
      (∫⁻ s in T, ‖(∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)‖ₑ ^ q) := by
    rw [lintegral_congr_ae h_ae_eq]
  rw [h_lintegral_eq]
  rw [← eLpNorm'_eq_lintegral_enorm]
  exact forceSliceTimeNorm_eq_lambda hsol z hρ hsub

end CKN
