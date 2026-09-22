-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SpatialSliceNorms
import CKN.Setting.SliceNormBounds
import CKN.Pressure.PkBoundsUnconditionalCore
import CKN.Foundation.Parabolic.Integration.Average

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace CKN

/-!
# Identification of the pressure spatial slice norm with the explicit real integral

Paper equation `eq:slice-norms`: identify the pressure spatial slice norm
of `CKN/Setting/SpatialSliceNorms.lean` with the explicit real integral used by the
scale quantity `delta`.
-/

/-- Paper equation `eq:slice-norms`, pressure line: the pressure `L^{3/2}` spatial slice
norm on `vec3Ball x ρ` at time `s` equals the `ENNReal.ofReal` of the `L^{3/2}`-norm
power `(2/3)` of the slice `|p(·,s)|`. -/
theorem pressureSpatialSliceNorm_eq_ofReal_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureSpatialSliceNorm p z.1 ρ s =
        ENNReal.ofReal ((∫ y in vec3Ball z.1 ρ, |p (y, s)| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) := by
  -- The cylinder lintegral is finite
  have hfin_cyl_ennreal : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) < ⊤ :=
    sws_pressure_integral_lt_top hsol hρ hsub
  -- Convert to lintegral of ENNReal.ofReal (|p| ^ (3/2))
  have hfin_cyl_ofReal : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) < ⊤ := by
    have h_eq : (fun w => ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) =
        (fun w => ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) := by
      ext w
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (p w)) (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    simpa [h_eq] using hfin_cyl_ennreal
  -- Get a local box whose spaceTimeSet contains the cylinder
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hp_meas : AEStronglyMeasurable p
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.1.mono_measure (Measure.restrict_mono hcyl le_rfl)
  -- The function |p| ^ (3/2) is AEStronglyMeasurable on the cylinder
  have h_abs_meas_cyl : AEStronglyMeasurable (fun w => |p w|)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    continuous_abs.comp_aestronglyMeasurable hp_meas
  have h_pow_meas_cyl : AEStronglyMeasurable (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp_aestronglyMeasurable
      h_abs_meas_cyl
  -- Nonnegativity on the cylinder
  have h_nonneg_cyl : 0 ≤ᵐ[volume.restrict (parabolicCylinder z.1 z.2 ρ)]
      fun w => |p w| ^ (3 / 2 : ℝ) :=
    Eventually.of_forall (fun w => Real.rpow_nonneg (abs_nonneg _) _)
  -- Hence |p| ^ (3/2) is IntegrableOn the cylinder
  have h_int_cyl : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ))
      (parabolicCylinder z.1 z.2 ρ) volume :=
    (lintegral_ofReal_ne_top_iff_integrable h_pow_meas_cyl h_nonneg_cyl).mp
      (ne_of_lt hfin_cyl_ofReal)
  -- Convert to Integrable on the restricted product measure
  have h_int_cyl_prod : Integrable (fun w => |p w| ^ (3 / 2 : ℝ))
      ((volume.restrict (vec3Ball z.1 ρ)).prod (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))) := by
    rw [Measure.prod_restrict]
    change Integrable (fun w : ParabolicPoint => |p w| ^ (3 / 2 : ℝ))
      ((volume : Measure ParabolicPoint).restrict
        (vec3Ball z.1 ρ ×ˢ Ioc (z.2 - ρ ^ 2) z.2))
    simpa [parabolicCylinder, IntegrableOn] using h_int_cyl
  -- For a.e. s, the slice y ↦ |p (y, s)| ^ (3/2) is integrable on the spatial ball
  have h_slice_int_ae : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      Integrable (fun y => |p (y, s)| ^ (3 / 2 : ℝ)) (volume.restrict (vec3Ball z.1 ρ)) :=
    h_int_cyl_prod.prod_left_ae
  -- For a.e. s, the slice y ↦ p (y, s) is AEStronglyMeasurable on the spatial ball
  have hp_meas_prod : AEStronglyMeasurable p
      ((volume.restrict (vec3Ball z.1 ρ)).prod (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))) := by
    rw [Measure.prod_restrict]
    change AEStronglyMeasurable (fun w : ParabolicPoint => p w)
      ((volume : Measure ParabolicPoint).restrict
        (vec3Ball z.1 ρ ×ˢ Ioc (z.2 - ρ ^ 2) z.2))
    simpa [parabolicCylinder] using hp_meas
  have hp_meas_slice_ae : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      AEStronglyMeasurable (fun y => p (y, s)) (volume.restrict (vec3Ball z.1 ρ)) :=
    hp_meas_prod.prodMk_right
  -- The exponent
  let e : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)
  have he_ne_zero : e ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 3 / 2))
  have he_ne_top : e ≠ ∞ := ENNReal.ofReal_ne_top
  have he_toReal : e.toReal = (3 / 2 : ℝ) :=
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hone_div_toReal : (1 : ℝ) / e.toReal = (2 / 3 : ℝ) := by
    rw [he_toReal]
    norm_num
  have h_cont_rpow_23 : Continuous (fun x : ℝ => x ^ (2/3 : ℝ)) :=
    Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)
  -- Process each s
  filter_upwards [h_slice_int_ae, hp_meas_slice_ae] with s hs hs_meas
  -- hs : Integrable (fun y => |p (y, s)| ^ (3/2 : ℝ)) (volume.restrict (vec3Ball z.1 ρ))
  -- hs_meas : AEStronglyMeasurable (fun y => p (y, s)) (volume.restrict (vec3Ball z.1 ρ))
  have h_slice_nonneg : 0 ≤ ∫ y in vec3Ball z.1 ρ, |p (y, s)| ^ (3 / 2 : ℝ) :=
    integral_nonneg_of_ae (Eventually.of_forall (fun y =>
      Real.rpow_nonneg (abs_nonneg _) _))
  -- AEStronglyMeasurable of |p(·, s)| ^ (3/2) from integrability
  have h_pow_meas : AEStronglyMeasurable (fun y => |p (y, s)| ^ (3 / 2 : ℝ))
      (volume.restrict (vec3Ball z.1 ρ)) :=
    hs.aestronglyMeasurable
  -- AEStronglyMeasurable of |p(·, s)| via composition with x ↦ x^(2/3)
  have h_abs_meas : AEStronglyMeasurable (fun y => |p (y, s)|)
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have h_comp : (fun y => (|p (y, s)| ^ (3/2 : ℝ)) ^ (2/3 : ℝ)) =
        (fun y => |p (y, s)|) := by
      ext y
      rw [← Real.rpow_mul (abs_nonneg (p (y, s))),
        show ((3/2 : ℝ) * (2/3 : ℝ)) = (1 : ℝ) by norm_num, Real.rpow_one]
    rw [← h_comp]
    exact h_cont_rpow_23.comp_aestronglyMeasurable h_pow_meas
  have h_nonneg_ae : 0 ≤ᵐ[volume.restrict (vec3Ball z.1 ρ)]
      fun y => |p (y, s)| ^ (3 / 2 : ℝ) :=
    Eventually.of_forall (fun y => Real.rpow_nonneg (abs_nonneg _) _)
  calc
    pressureSpatialSliceNorm p z.1 ρ s
        = eLpNorm (fun y => p (y, s)) e (volume.restrict (vec3Ball z.1 ρ)) := rfl
    _ = eLpNorm (fun y => |p (y, s)|) e (volume.restrict (vec3Ball z.1 ρ)) := by
      refine eLpNorm_congr_enorm_ae hs_meas h_abs_meas
        (Eventually.of_forall (fun y => ?_))
      simp [Real.enorm_eq_ofReal_abs]
    _ = (∫⁻ y in vec3Ball z.1 ρ, ‖|p (y, s)|‖ₑ ^ e.toReal) ^ (1 / e.toReal) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal he_ne_zero he_ne_top h_abs_meas]
    _ = (∫⁻ y in vec3Ball z.1 ρ, ENNReal.ofReal (|p (y, s)| ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := by
      simp [Real.enorm_eq_ofReal_abs, he_toReal,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    _ = (ENNReal.ofReal (∫ y in vec3Ball z.1 ρ, |p (y, s)| ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hs h_nonneg_ae]
    _ = ENNReal.ofReal ((∫ y in vec3Ball z.1 ρ, |p (y, s)| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg h_slice_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]

end CKN
