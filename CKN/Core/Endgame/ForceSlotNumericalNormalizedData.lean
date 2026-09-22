-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumericalNormalization
import CKN.Core.Endgame.ForceSlotNumericalEnergy
import CKN.Core.Endgame.Localization
import CKN.Setting.ScalingInvariance
import CKN.Setting.PoincareSobolevL1SliceBasic
import CKN.Foundation.Parabolic.BallDisplays

/-!
# Normalized energy from the original solution norms

The normalization radius and its energy bound depend only on the fixed
radii and the three prescribed norm bounds.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The normalized energy bound, including the volume loss from lowering
velocity integrability from ten thirds to three. -/
def forceSlotEnergy (q r₂ r₃ U P F : ℝ) : ℝ≥0∞ :=
  forceSlotNormalizedEnergyBound (32 * endgameLocalRadius r₂ r₃) q
    (ENNReal.ofReal U * ENNReal.ofReal (8 * Real.pi / 3 * r₂ ^ 5) ^ (1 / 30 : ℝ))
    (ENNReal.ofReal P) (ENNReal.ofReal F)

/-- The energy expression is finite before any solution is chosen. -/
theorem forceSlotEnergy_lt_top (q r₂ r₃ U P F : ℝ) (hq : 0 ≤ q) :
    forceSlotEnergy q r₂ r₃ U P F < ⊤ := by
  apply forceSlotNormalizedEnergyBound_lt_top _ _ hq
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
    ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The original scalar norm bounds control the entire normalized energy. -/
theorem force_slot_rescaled_energy_le
    {q r₂ r₃ U P F : ℝ} (hq : 5 / 2 < q) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    {Ω : Set Vec3} {I : Set ℝ} {u f : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) {z₀ z : ParabolicPoint}
    (hdom : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hz : z ∈ Metric.closedBall z₀ r₃)
    (hU : eLpNorm (fun w => vec3EuclideanNorm (u w)) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal U)
    (hP : eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal P)
    (hF : eLpNorm (fun w => vec3EuclideanNorm (f w)) (ENNReal.ofReal q)
      (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal F) :
    let μ := 32 * endgameLocalRadius r₂ r₃
    let b : ParabolicPoint := (z.1, z.2 + 16 * endgameLocalRadius r₂ r₃ ^ 2)
    (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ b u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |rescalePressure μ b p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ b f w)) ^ q) ≤
      ENNReal.ofReal (forceSlotEnergy q r₂ r₃ U P F).toReal := by
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  have hμ : 0 < 32 * endgameLocalRadius r₂ r₃ := by positivity
  have hbox := localBox_of_parabolic_ball hr₂ hdom
  have hdata := hsol.2.2.2.2.2.1 _ _ hbox
  have heq : Metric.ball z₀ r₂ = spaceTimeSet (vec3Ball z₀.1 r₂)
      (Ioo (z₀.2 - r₂ ^ 2) (z₀.2 + r₂ ^ 2)) := by
    rw [metricBall_eq_parabolicBall]
    rfl
  have hu : AEStronglyMeasurable (fun w => vec3EuclideanNorm (u w))
      (volume.restrict (Metric.ball z₀ r₂)) := by
    rw [heq]
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hdata.1
  have hp : AEStronglyMeasurable p (volume.restrict (Metric.ball z₀ r₂)) := by
    rw [heq]
    exact hdata.2.2.1
  have hf : AEStronglyMeasurable (fun w => vec3EuclideanNorm (f w))
      (volume.restrict (Metric.ball z₀ r₂)) := by
    rw [heq]
    apply continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
    exact hdata.2.2.2.1
  have hU3 := force_slot_velocity_cube_norm_le (ENNReal.ofReal U) hu hU
  rw [volume_metricBall z₀ hr₂.le] at hU3
  have hQB := (force_slot_normalized_unit_subset_step2 hrr hz).trans
    (Metric.ball_subset_ball (by linarith only [hr₂] : r₂ / 4 ≤ r₂))
  have hQ : parabolicCylinder
      (scalingParabolic (32 * endgameLocalRadius r₂ r₃)
        (z.1, z.2 + 16 * endgameLocalRadius r₂ r₃ ^ 2) ((0, 0) : ParabolicPoint)).1
      (scalingParabolic (32 * endgameLocalRadius r₂ r₃)
        (z.1, z.2 + 16 * endgameLocalRadius r₂ r₃ ^ 2) ((0, 0) : ParabolicPoint)).2
      ((32 * endgameLocalRadius r₂ r₃) * 1) ⊆ Metric.ball z₀ r₂ := by
    rw [← force_slot_cylinder_image hμ
      ((z.1, z.2 + 16 * endgameLocalRadius r₂ r₃ ^ 2) : ParabolicPoint)
      ((0, 0) : ParabolicPoint) 1]
    exact (image_mono subset_closure).trans hQB
  have hE := force_slot_normalized_energy_le _ q _ _ _ hμ
    (by linarith only [hq]) _ hQ hu hp hf hU3 hP hF
  rw [ENNReal.ofReal_toReal (forceSlotEnergy_lt_top q r₂ r₃ U P F
    (by linarith only [hq])).ne]
  simpa only [rescaleVelocity, rescalePressure, rescaleForce, vec3EuclideanNorm_smul,
    abs_mul, abs_of_pos hμ, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
    abs_of_pos (pow_pos hμ 3), forceSlotEnergy, scalingParabolic] using hE

end CKN.Core.Endgame
