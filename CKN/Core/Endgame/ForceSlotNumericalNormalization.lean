-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumericalScaling
import CKN.Core.Endgame.ForceSlotNumericalData

/-!
# Full source carriers inside normalized past cylinders

A forward shift of the terminal time allows a past-cylinder estimate to
cover the entire symmetric source ball. The normalization uses the fixed
endgame radius, so neither the dilation nor the carrier losses depend on
the solution.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- A normalized closed unit cylinder lies in a slightly larger metric ball
about its image centre. -/
theorem force_slot_scaled_unit_closure_subset (a : ℝ) (ha : 0 < a)
    (z : ParabolicPoint) :
    scalingParabolic a z '' closure (parabolicCylinder (0 : Vec3) 0 1) ⊆
      Metric.ball z (2 * a) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)] at hw
  change vec3EuclideanNorm (w.1 - 0) ≤ 1 ∧ w.2 ∈ Icc (0 - 1 ^ 2) 0 at hw
  simp only [sub_zero, one_pow, zero_sub] at hw
  rw [metricBall_eq_parabolicBall]
  change vec3EuclideanNorm ((z.1 + a • w.1) - z.1) < 2 * a ∧
    z.2 - (2 * a) ^ 2 < z.2 + a ^ 2 * w.2 ∧
    z.2 + a ^ 2 * w.2 < z.2 + (2 * a) ^ 2
  rw [add_sub_cancel_left, vec3EuclideanNorm_smul, abs_of_pos ha]
  have hspace := mul_le_mul_of_nonneg_left hw.1 ha.le
  have hlo := mul_le_mul_of_nonneg_left hw.2.1 (sq_nonneg a)
  have hhi := mul_le_mul_of_nonneg_left hw.2.2 (sq_nonneg a)
  exact ⟨by linarith only [hspace, ha],
    by nlinarith only [hlo, sq_pos_of_pos ha],
    by nlinarith only [hhi, sq_pos_of_pos ha]⟩

/-- The final pressure cylinder after normalization contains the full
symmetric source ball, including times after its centre. -/
theorem force_slot_source_subset_normalized_pressure (a : ℝ) (ha : 0 < a)
    (z : ParabolicPoint) :
    Metric.ball z (2 * a) ⊆
      scalingParabolic (32 * a) (z.1, z.2 + 16 * a ^ 2) ''
        parabolicCylinder (0 : Vec3) 0 (19 / 32) := by
  rw [force_slot_cylinder_image (by positivity : 0 < 32 * a)
    ((z.1, z.2 + 16 * a ^ 2) : ParabolicPoint) ((0, 0) : ParabolicPoint)]
  have hmap : scalingParabolic (32 * a) (z.1, z.2 + 16 * a ^ 2)
      ((0, 0) : ParabolicPoint) = ((z.1, z.2 + 16 * a ^ 2) : ParabolicPoint) := by
    simp only [scalingParabolic, parabolicTranslate, parabolicScale, smul_zero, mul_zero, add_zero]
    rfl
  rw [hmap]
  intro w hw
  rw [metricBall_eq_parabolicBall] at hw
  change vec3EuclideanNorm (w.1 - z.1) < 2 * a ∧
    z.2 - (2 * a) ^ 2 < w.2 ∧ w.2 < z.2 + (2 * a) ^ 2 at hw
  change vec3EuclideanNorm (w.1 - z.1) < 32 * a * (19 / 32) ∧
    z.2 + 16 * a ^ 2 - (32 * a * (19 / 32)) ^ 2 < w.2 ∧
    w.2 ≤ z.2 + 16 * a ^ 2
  exact ⟨by linarith only [hw.1, ha],
    by nlinarith only [hw.2.1, sq_pos_of_pos ha],
    by nlinarith only [hw.2.2, sq_pos_of_pos ha]⟩

/-- The final pressure cylinder after normalization contains the full
symmetric source ball, including times after its centre. -/
theorem force_slot_collar_subset_normalized_pressure (a : ℝ) (ha : 0 < a)
    (z : ParabolicPoint) :
    Metric.ball z (4 * a) ⊆
      scalingParabolic (32 * a) (z.1, z.2 + 16 * a ^ 2) ''
        parabolicCylinder (0 : Vec3) 0 (19 / 32) := by
  rw [force_slot_cylinder_image (by positivity : 0 < 32 * a)
    ((z.1, z.2 + 16 * a ^ 2) : ParabolicPoint) ((0, 0) : ParabolicPoint)]
  have hmap : scalingParabolic (32 * a) (z.1, z.2 + 16 * a ^ 2)
      ((0, 0) : ParabolicPoint) = ((z.1, z.2 + 16 * a ^ 2) : ParabolicPoint) := by
    simp only [scalingParabolic, parabolicTranslate, parabolicScale, smul_zero, mul_zero, add_zero]
    rfl
  rw [hmap]
  intro w hw
  rw [metricBall_eq_parabolicBall] at hw
  change vec3EuclideanNorm (w.1 - z.1) < 4 * a ∧
    z.2 - (4 * a) ^ 2 < w.2 ∧ w.2 < z.2 + (4 * a) ^ 2 at hw
  change vec3EuclideanNorm (w.1 - z.1) < 32 * a * (19 / 32) ∧
    z.2 + 16 * a ^ 2 - (32 * a * (19 / 32)) ^ 2 < w.2 ∧
    w.2 ≤ z.2 + 16 * a ^ 2
  exact ⟨by linarith only [hw.1, ha],
    by nlinarith only [hw.2.1, sq_pos_of_pos ha],
    by nlinarith only [hw.2.2, sq_pos_of_pos ha]⟩

/-- The normalized unit cylinder stays inside the carrier on which Step 2
supplies its uniform numerical bounds. -/
theorem force_slot_normalized_unit_subset_step2 {r₂ r₃ : ℝ}
    (hrr : r₃ < r₂ / 4) {z₀ z : ParabolicPoint}
    (hz : z ∈ Metric.closedBall z₀ r₃) :
    scalingParabolic (32 * endgameLocalRadius r₂ r₃)
      (z.1, z.2 + 16 * endgameLocalRadius r₂ r₃ ^ 2) ''
        closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ Metric.ball z₀ (r₂ / 4) := by
  let a := endgameLocalRadius r₂ r₃
  have ha : 0 < a := by dsimp [a, endgameLocalRadius]; linarith only [hrr]
  have hshift : ((z.1, z.2 + 16 * a ^ 2) : ParabolicPoint) ∈ Metric.closedBall z (4 * a) := by
    have hd := step2_shifted_center_dist (w := z) (r := 4 * a) (by positivity)
    change @dist ParabolicPoint _ ((z.1, z.2 + 16 * a ^ 2) : ParabolicPoint) z ≤ 4 * a
    convert hd.le using 1
    congr 2
    ring
  apply (force_slot_scaled_unit_closure_subset (32 * a) (by positivity) _).trans
  apply Set.Subset.trans (parabolic_ball_subset_ball_of_center_mem_closedBall hshift
    (show 4 * a + 2 * (32 * a) ≤ 68 * a by ring_nf; rfl))
  apply parabolic_ball_subset_ball_of_center_mem_closedBall hz
  dsimp [a, endgameLocalRadius]
  linarith only [hrr]

/-- The numerical Step 2 bound transports to each normalized interior
cylinder with its field amplitude retained. -/
theorem force_slot_normalized_morrey_le
    (P τ c R : ℝ) (K : ℝ≥0∞) (hP : 0 < P) (hPτ : P ≤ τ)
    (hR : 0 ≤ R) (hR1 : R ≤ 1)
    {r₂ r₃ : ℝ} (hrr : r₃ < r₂ / 4) {z₀ z : ParabolicPoint}
    (hz : z ∈ Metric.closedBall z₀ r₃) (f : ParabolicPoint → ℝ)
    (hN : morreyBallNorm P τ ((Metric.ball z₀ (r₂ / 4)).indicator f) ≤ K) :
    morreyNorm P τ ((parabolicCylinder (0 : Vec3) 0 R).indicator
      (fun w => c * f (scalingParabolic (32 * endgameLocalRadius r₂ r₃)
        (z.1, z.2 + 16 * endgameLocalRadius r₂ r₃ ^ 2) w))) ≤
      ENNReal.ofReal |c| *
        (ENNReal.ofReal (32 * endgameLocalRadius r₂ r₃) ^ (-5 / τ : ℝ) * K) := by
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  apply force_slot_subcarrier_scaling_le _ c P τ K (by positivity) hP
  · apply Set.Subset.trans (image_mono ?_) (force_slot_normalized_unit_subset_step2 hrr hz)
    exact (parabolicCylinder_mono hR hR1).trans subset_closure
  · exact (morreyNorm_le_morreyBallNorm hP.le hPτ _).trans hN

/-- A normalized pressure-cylinder bound controls a field on the entire
endgame source ball after removing its rescaling amplitude. -/
theorem force_slot_source_morrey_of_normalized
    (P τ c : ℝ) (K : ℝ≥0∞) (hP : 0 < P) (hc : c ≠ 0)
    (a : ℝ) (ha : 0 < a) (z : ParabolicPoint) (f : ParabolicPoint → ℝ)
    (hN : morreyNorm P τ ((parabolicCylinder (0 : Vec3) 0 (19 / 32)).indicator
      (fun w => c * f (scalingParabolic (32 * a) (z.1, z.2 + 16 * a ^ 2) w))) ≤ K) :
    morreyNorm P τ ((Metric.ball z (2 * a)).indicator f) ≤
      ENNReal.ofReal (32 * a) ^ (5 / τ : ℝ) * (ENNReal.ofReal |c⁻¹| * K) := by
  apply force_slot_subcarrier_unscaling_le _ c P τ K (by positivity) hc hP _ _ _ f ?_ hN
  intro w hw
  obtain ⟨v, hv, heq⟩ := force_slot_source_subset_normalized_pressure a ha z hw
  have hvw : v = w := force_slot_scaling_injective (by positivity) _ heq
  simpa only [hvw] using hv

end CKN.Core.Endgame
