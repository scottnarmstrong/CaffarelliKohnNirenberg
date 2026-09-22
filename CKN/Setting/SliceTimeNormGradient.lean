-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.PkBoundsUnconditionalCore
import CKN.Setting.SliceNormBounds

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false

namespace CKN

/-- Paper equation `eq:slice-norm-bounds`, gradient time-norm display: the
`L²(J_ρ)` time norm of the `L²(B_ρ)` gradient slice norm equals `ρ^(1/2) β(ρ)`. -/
theorem gradientSliceTimeNorm_eq_beta
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    eLpNorm' (fun s : ℝ =>
        (∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s)) ^ (1 / 2 : ℝ))
      (2 : ℝ) (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
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
  have h_enorm : ∀ s, ‖G s‖ₑ = ENNReal.ofReal (G s) := by
    intro s
    rw [Real.enorm_eq_ofReal (hG_nonneg s)]
  rw [eLpNorm'_eq_lintegral_enorm]
  simp_rw [h_enorm]
  have h_meas : AEMeasurable (fun w : ParabolicPoint =>
      ENNReal.ofReal (spatialGradientSq u Du w))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    have h_int : Integrable (fun w : ParabolicPoint =>
        spatialGradientSq u Du w)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
      pressure_gradient_integrable hsol hρ hsub
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      h_int.aestronglyMeasurable.aemeasurable
  rw [show (fun s : ℝ => ENNReal.ofReal (G s) ^ (2 : ℝ)) =
      fun s => ENNReal.ofReal (G s ^ (2 : ℝ)) by
    ext s
    rw [ENNReal.ofReal_rpow_of_nonneg (hG_nonneg s) (by norm_num : 0 ≤ (2 : ℝ))]]
  have h_sq : ∀ s, G s ^ (2 : ℝ) = ∫ y in vec3Ball z.1 ρ,
      spatialGradientSq u Du (y, s) := by
    intro s
    dsimp [G]
    have h_int_nonneg : 0 ≤ ∫ y in vec3Ball z.1 ρ,
        spatialGradientSq u Du (y, s) :=
      setIntegral_nonneg (vec3Ball_measurable z.1 ρ) (fun y _ => by
        unfold spatialGradientSq
        refine Finset.sum_nonneg (fun i _ => ?_)
        refine Finset.sum_nonneg (fun j _ => ?_)
        positivity)
    calc
      ((∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
          = (∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s))
            ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by
        rw [Real.rpow_mul h_int_nonneg (1 / 2 : ℝ) (2 : ℝ)]
      _ = (∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s)) ^ (1 : ℝ) := by
        have h_exp : (1 / 2 : ℝ) * (2 : ℝ) = (1 : ℝ) := by norm_num
        rw [h_exp]
      _ = ∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s) := by
        rw [Real.rpow_one]
  simp_rw [h_sq]
  -- Now we have ∫⁻ s in Ioc ..., ENNReal.ofReal (∫ y ..., spatialGradientSq ...)
  -- First, convert the Bochner integral to lintegral for a.e. s
  have h_int_slice : ∀ᵐ s ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)),
      Integrable (fun y : Vec3 => spatialGradientSq u Du (y, s))
        (volume.restrict (vec3Ball z.1 ρ)) := by
    have h_int_cyl : Integrable (fun w : ParabolicPoint => spatialGradientSq u Du w)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
      pressure_gradient_integrable hsol hρ hsub
    have h_int_prod : Integrable (fun w : ParabolicPoint => spatialGradientSq u Du w)
        (((volume : Measure Vec3).restrict (vec3Ball z.1 ρ)).prod
          (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))) := by
      have h_vol : (volume : Measure ParabolicPoint).restrict (parabolicCylinder z.1 z.2 ρ) =
          ((volume : Measure Vec3).restrict (vec3Ball z.1 ρ)).prod
            (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
        rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
        exact (Measure.prod_restrict (vec3Ball z.1 ρ) (Ioc (z.2 - ρ ^ 2) z.2)
          (μ := volume) (ν := volume)).symm
      rw [← h_vol]
      exact h_int_cyl
    exact h_int_prod.prod_left_ae
  have h_slice_nonneg : ∀ᵐ s ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)),
      0 ≤ᵐ[volume.restrict (vec3Ball z.1 ρ)] fun y => spatialGradientSq u Du (y, s) := by
    filter_upwards [h_int_slice] with s hs
    refine ae_of_all _ (fun y => ?_)
    unfold spatialGradientSq
    positivity
  have h_ofReal_eq : ∀ᵐ s ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)),
      ENNReal.ofReal (∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s)) =
      ∫⁻ y in vec3Ball z.1 ρ, ENNReal.ofReal (spatialGradientSq u Du (y, s)) := by
    filter_upwards [h_int_slice, h_slice_nonneg] with s hs hsn
    rw [ofReal_integral_eq_lintegral_ofReal hs hsn]
  rw [lintegral_congr_ae h_ofReal_eq]
  -- Now we have ∫⁻ s in Ioc ..., ∫⁻ y in vec3Ball ..., ENNReal.ofReal (spatialGradientSq ...)
  -- Apply lintegral_parabolicCylinder to swap
  have h_meas : AEMeasurable (fun w : ParabolicPoint =>
      ENNReal.ofReal (spatialGradientSq u Du w))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    have h_int : Integrable (fun w : ParabolicPoint =>
        spatialGradientSq u Du w)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
      pressure_gradient_integrable hsol hρ hsub
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      h_int.aestronglyMeasurable.aemeasurable
  rw [← lintegral_parabolicCylinder h_meas]
  rw [sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq hsol z hρ hsub]
  have h_rho_nonneg : 0 ≤ ρ := hρ.le
  have h_beta_nonneg : 0 ≤ beta u Du z ρ := by
    unfold beta
    refine Real.rpow_nonneg ?_ (1 / 2 : ℝ)
    refine mul_nonneg (inv_nonneg.mpr h_rho_nonneg) ?_
    exact ENNReal.toReal_nonneg
  have h_beta_sq_nonneg : 0 ≤ beta u Du z ρ ^ 2 := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg h_rho_nonneg h_beta_sq_nonneg)
    (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  calc
    ENNReal.ofReal ((ρ * beta u Du z ρ ^ 2) ^ (1 / 2 : ℝ))
        = ENNReal.ofReal (ρ ^ (1 / 2 : ℝ) * (beta u Du z ρ ^ 2) ^ (1 / 2 : ℝ)) := by
      rw [Real.mul_rpow h_rho_nonneg (by positivity : 0 ≤ beta u Du z ρ ^ 2)]
    _ = ENNReal.ofReal (Real.sqrt ρ * (beta u Du z ρ ^ 2) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
    _ = ENNReal.ofReal (Real.sqrt ρ * beta u Du z ρ) := by
      rw [show (beta u Du z ρ ^ 2) ^ (1 / 2 : ℝ) = beta u Du z ρ from
        calc
          (beta u Du z ρ ^ 2) ^ (1 / 2 : ℝ) = ((beta u Du z ρ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
            norm_num
          _ = (beta u Du z ρ) ^ ((2 : ℝ) * (1 / 2 : ℝ)) := by
            rw [Real.rpow_mul h_beta_nonneg (2 : ℝ) (1 / 2 : ℝ)]
          _ = (beta u Du z ρ) ^ (1 : ℝ) := by
            have h_exp : (2 : ℝ) * (1 / 2 : ℝ) = (1 : ℝ) := by norm_num
            rw [h_exp]
          _ = beta u Du z ρ := by rw [Real.rpow_one]
      ]

end CKN
