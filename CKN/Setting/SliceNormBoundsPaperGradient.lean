-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SpatialSliceNormIdentifyGradient
import CKN.Setting.SliceTimeNormGradient

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- Paper equation `eq:slice-norm-bounds`, gradient line: the `L²(J_ρ)` time norm of the
`L²(B_ρ)` gradient slice norm equals `ρ^(1/2) β(ρ)`. -/
theorem gradientSpatialSliceNorm_timeNorm_eq_beta
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, gradientSpatialSliceNorm Du z.1 ρ s ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt ρ * beta u Du z ρ) := by
  set G := fun s : ℝ =>
    (∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s)) ^ (1 / 2 : ℝ) with hG
  have hG_nonneg : ∀ s, 0 ≤ G s := by
    intro s
    dsimp [G]
    refine Real.rpow_nonneg ?_ (1 / 2 : ℝ)
    refine setIntegral_nonneg (vec3Ball_measurable z.1 ρ) (fun y _ => ?_)
    unfold spatialGradientSq
    refine Finset.sum_nonneg (fun i _ => ?_)
    refine Finset.sum_nonneg (fun j _ => ?_)
    positivity
  have h_ae_eq_sq : ∀ᵐ s ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)),
      gradientSpatialSliceNorm Du z.1 ρ s ^ (2 : ℝ) = (ENNReal.ofReal (G s)) ^ (2 : ℝ) := by
    filter_upwards [gradientSpatialSliceNorm_eq_ofReal_ae hsol z hρ hsub] with s hs
    rw [hs, hG]
  have h_enorm : ∀ s, ‖G s‖ₑ = ENNReal.ofReal (G s) := by
    intro s
    rw [Real.enorm_eq_ofReal (hG_nonneg s)]
  have h_left_eq : (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2,
      gradientSpatialSliceNorm Du z.1 ρ s ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      eLpNorm' G (2 : ℝ) (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
    rw [lintegral_congr_ae h_ae_eq_sq]
    rw [eLpNorm'_eq_lintegral_enorm]
    simp_rw [h_enorm]
  rw [h_left_eq]
  exact gradientSliceTimeNorm_eq_beta hsol z hρ hsub

end CKN
