-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.PkBoundsUnconditionalCore
import CKN.Setting.SliceNormBounds

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false

namespace CKN

/-!
# Time slice norm of the pressure

This module formalizes the third display of paper equation `eq:slice-norm-bounds`:
the $L^{3/2}(J_\rho)$ time norm of the $L^{3/2}(B_\rho)$ pressure slice norm equals
$\rho^{4/3}\delta(\rho)^2$.
-/

/-- Paper equation `eq:slice-norm-bounds`, pressure line: the $L^{3/2}(J_\rho)$ time norm
of the $L^{3/2}(B_\rho)$ pressure slice norm equals $\\rho^{4/3}\\delta(\\rho)^2$. -/
theorem pressureSliceTimeNorm_eq_delta_sq
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    eLpNorm' (fun s : ℝ =>
        (∫ y in vec3Ball z.1 ρ, |p (y, s)| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ))
      (3 / 2 : ℝ) (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
    ENNReal.ofReal (ρ ^ (4 / 3 : ℝ) * delta p z ρ ^ 2) := by
  let Bρ : Set Vec3 := vec3Ball z.1 ρ
  let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  let F : Vec3 × ℝ → ℝ := fun w => |p w|
  let G : ℝ → ℝ := fun s =>
    (∫ x in Bρ, (F (x, s)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hBmeas : MeasurableSet Bρ := vec3Ball_measurable z.1 ρ
  have hTmeas : MeasurableSet Tρ := measurableSet_Ioc
  have hpglobal : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.1
  have hpprod : AEStronglyMeasurable p
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hpglobal
  have hpBT : AEStronglyMeasurable p
      ((volume.restrict Bρ).prod (volume.restrict Tρ)) :=
    hpprod.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball)
      (Measure.restrict_mono_set volume htime))
  have hpPowGlobal : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hdata.2.2.2.2.2.2.1
  have hpPowBT : Integrable (fun w : Vec3 × ℝ =>
      |p w| ^ (3 / 2 : ℝ))
      ((volume.restrict Bρ).prod (volume.restrict Tρ)) := by
    have h := hpPowGlobal.integrable_norm_rpow (by norm_num) (by norm_num)
    change Integrable (fun w : Vec3 × ℝ =>
      ‖p w‖ ^ (ENNReal.ofReal (3 / 2 : ℝ)).toReal)
      ((volume.restrict Ω').prod (volume.restrict J)) at h
    have h' : Integrable (fun w : Vec3 × ℝ =>
        |p w| ^ (3 / 2 : ℝ))
        ((volume.restrict Ω').prod (volume.restrict J)) := by
      simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
        Real.norm_eq_abs] using h
    exact h'.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball)
      (Measure.restrict_mono_set volume htime))
  have hFglobal : AEStronglyMeasurable
      (fun w : ParabolicPoint => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
    have hpabs := continuous_abs.comp_aestronglyMeasurable hpglobal
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp_aestronglyMeasurable
      hpabs
  have hFglobalT : AEStronglyMeasurable
      (fun w : ParabolicPoint => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' Tρ)) := by
    apply hFglobal.mono_measure
    apply Measure.restrict_mono_set volume
    intro w hw
    exact ⟨hw.1, htime hw.2⟩
  have hGae : AEMeasurable (fun s : ℝ =>
      ∫ x in Bρ, (F (x, s)) ^ (3 / 2 : ℝ))
      (volume.restrict Tρ) :=
    pressure_slice_integral_aemeasurable hBmeas hTmeas hball hFglobalT
  have hGmeas : AEStronglyMeasurable G (volume.restrict Tρ) := by
    have hc : Continuous (fun x : ℝ => x ^ (2 / 3 : ℝ)) :=
      Real.continuous_rpow_const (by norm_num)
    exact (hc.measurable.comp_aemeasurable hGae).aestronglyMeasurable
  have hGnonneg : 0 ≤ᵐ[volume.restrict Tρ] G :=
    Filter.Eventually.of_forall (fun s => Real.rpow_nonneg
      (integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => by
        dsimp [F]
        positivity)) _)
  have hFpCyl : Integrable (fun w : ParabolicPoint =>
      |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
    change Integrable (fun w : Vec3 × ℝ => |p w| ^ (3 / 2 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Bρ ×ˢ Tρ))
    rw [← Measure.prod_restrict]
    exact hpPowBT
  have hlinCyl : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) =
      ENNReal.ofReal (ρ ^ 2 * delta p z ρ ^ 3) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hFpCyl]
    · rw [sws_integral_abs_pow_eq_delta_cube hsol z hρ hsub]
    · exact Filter.Eventually.of_forall (fun w => Real.rpow_nonneg
        (abs_nonneg _) _)
  have hswap := pressure_prod_lintegral_swap (B := Bρ) (T := Tρ)
    (F := fun w => |p w| ^ (3 / 2 : ℝ)) hpPowBT.aemeasurable
  have hlinBT : (∫⁻ w in Bρ ×ˢ Tρ,
      ENNReal.ofReal ((F w) ^ (3 / 2 : ℝ))) =
      ENNReal.ofReal (ρ ^ 2 * delta p z ρ ^ 3) := by
    change (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) = _
    exact hlinCyl
  have hGpow : ∀ᵐ s ∂volume.restrict Tρ,
      ‖G s‖ₑ ^ (3 / 2 : ℝ) =
      ∫⁻ x in Bρ, ENNReal.ofReal ((F (x, s)) ^ (3 / 2 : ℝ)) := by
    have hs := hpPowBT.prod_left_ae
    filter_upwards [hs] with s hs
    have hI : 0 ≤ ∫ x in Bρ, (F (x, s)) ^ (3 / 2 : ℝ) :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => by
        dsimp [F]
        positivity)
    have hconv := ofReal_integral_eq_lintegral_ofReal hs
      (Filter.Eventually.of_forall fun x => by
        dsimp [F]
        positivity)
    rw [show G s = (∫ x in Bρ, (F (x, s)) ^ (3 / 2 : ℝ)) ^
        (2 / 3 : ℝ) by rfl]
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hI _),
      ← ENNReal.ofReal_rpow_of_nonneg hI (by norm_num),
      ← ENNReal.rpow_mul]
    norm_num
    exact hconv
  have hdelta_nonneg : 0 ≤ delta p z ρ := by
    unfold delta
    refine Real.rpow_nonneg ?_ (1 / 3 : ℝ)
    refine mul_nonneg (Real.rpow_nonneg hρ.le _) ?_
    exact ENNReal.toReal_nonneg
  calc
    eLpNorm' G (3 / 2 : ℝ) (volume.restrict Tρ)
        = (∫⁻ s in Tρ, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
      rw [eLpNorm'_eq_lintegral_enorm]
      norm_num
    _ = (∫⁻ s in Tρ, ∫⁻ x in Bρ,
        ENNReal.ofReal ((F (x, s)) ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := by
      congr 1
      apply lintegral_congr_ae
      exact hGpow
    _ = (∫⁻ w in Bρ ×ˢ Tρ,
        ENNReal.ofReal ((F w) ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := by
      rw [← hswap]
    _ = ENNReal.ofReal (ρ ^ 2 * delta p z ρ ^ 3) ^ (2 / 3 : ℝ) := by
      rw [hlinBT]
    _ = ENNReal.ofReal ((ρ ^ 2 * delta p z ρ ^ 3) ^ (2 / 3 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (sq_nonneg _) (pow_nonneg hdelta_nonneg _))
        (by norm_num)]
    _ = ENNReal.ofReal (ρ ^ (4 / 3 : ℝ) * delta p z ρ ^ 2) := by
      congr 1
      calc
        (ρ ^ 2 * delta p z ρ ^ 3) ^ (2 / 3 : ℝ)
            = (ρ ^ 2) ^ (2 / 3 : ℝ) * (delta p z ρ ^ 3) ^ (2 / 3 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
        _ = (ρ ^ (2 : ℝ)) ^ (2 / 3 : ℝ) * (delta p z ρ ^ (3 : ℝ)) ^ (2 / 3 : ℝ) := by
          norm_num
        _ = ρ ^ ((2 : ℝ) * (2 / 3 : ℝ)) * delta p z ρ ^ ((3 : ℝ) * (2 / 3 : ℝ)) := by
          rw [← Real.rpow_mul hρ.le (2 : ℝ) (2 / 3 : ℝ),
            ← Real.rpow_mul hdelta_nonneg (3 : ℝ) (2 / 3 : ℝ)]
        _ = ρ ^ (4 / 3 : ℝ) * delta p z ρ ^ 2 := by norm_num

end CKN
