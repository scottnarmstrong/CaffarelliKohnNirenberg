-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.UniformCutoffFamily

/-!
# Uniform bounds for all localization coefficients

The explicit parabolic cutoff controls its value, time derivative, first
spatial derivatives, and spatial Laplacian with a single radius-dependent
constant. This is the common coefficient bound needed by both source slots.
-/

open Set Metric
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- One bound for the value and all derivatives used in the heat equation. -/
def forceSlotCutoffConstant (a : ℝ) : ℝ :=
  1 + uniformCutoffConstant / a + 3 * (uniformCutoffConstant / a ^ 2)

/-- The common coefficient bound is positive at every positive radius. -/
theorem forceSlotCutoffConstant_pos {a : ℝ} (ha : 0 < a) :
    0 < forceSlotCutoffConstant a := by
  have hC := uniformCutoffConstant_pos
  unfold forceSlotCutoffConstant
  positivity

/-- The explicit smooth cutoff has a common bound for its four coefficients. -/
theorem endgameCutoff_coefficients_le (z : ParabolicPoint) {a : ℝ} (ha : 0 < a) :
    ∀ w : Vec3 × ℝ, |endgameCutoff z ha w| ≤ forceSlotCutoffConstant a ∧
      |timePartial (endgameCutoff z ha) w| ≤ forceSlotCutoffConstant a ∧
      (∀ j, |spatialPartial (endgameCutoff z ha) j w| ≤ forceSlotCutoffConstant a) ∧
      |spatialLaplacian (fun x => endgameCutoff z ha (x, w.2)) w.1| ≤
        forceSlotCutoffConstant a := by
  intro w
  have hC := uniformCutoffConstant_nonneg
  have hfirst : 0 ≤ uniformCutoffConstant / a := div_nonneg hC ha.le
  have hsecond : 0 ≤ uniformCutoffConstant / a ^ 2 := div_nonneg hC (sq_nonneg a)
  have hone : 1 ≤ forceSlotCutoffConstant a := by
    unfold forceSlotCutoffConstant
    linarith only [hfirst, hsecond]
  have hx : uniformCutoffConstant / a ≤ forceSlotCutoffConstant a := by
    unfold forceSlotCutoffConstant
    linarith only [hsecond]
  have ht : uniformCutoffConstant / a ^ 2 ≤ forceSlotCutoffConstant a := by
    unfold forceSlotCutoffConstant
    linarith only [hfirst, hsecond]
  have hΔ : 3 * (uniformCutoffConstant / a ^ 2) ≤ forceSlotCutoffConstant a := by
    unfold forceSlotCutoffConstant
    linarith only [hfirst]
  refine ⟨?_, (endgameCutoff_abs_timePartial_le z ha w).trans ht,
    fun j => (endgameCutoff_abs_spatialPartial_le z ha j w).trans hx, ?_⟩
  · have hv : |endgameCutoff z ha w| ≤ 1 := by
      change |endgameSpaceCutoff z ha w.1 * endgameTimeCutoff z a w.2| ≤ 1
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul
        (endgameSpaceCutoff_abs_le_one z ha w.1)
        (endgameTimeCutoff_abs_le_one z a w.2) (abs_nonneg _) zero_le_one
    exact hv.trans hone
  · change |∑ j : Fin 3, spatialSecondPartial (endgameCutoff z ha) j j w| ≤ _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun j _ => endgameCutoff_abs_spatialSecondPartial_le z ha j j w)).trans
    simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hΔ

/-- The explicit cutoff fits in the product box of radius three times the
localization radius; this box remains compactly inside the original domain. -/
theorem force_slot_cutoff_local_box {r₂ r₃ : ℝ} (hr₃ : 0 < r₃)
    (hrr : r₃ < r₂ / 4) {Ω : Set Vec3} {I : Set ℝ} {z₀ z : ParabolicPoint}
    (hdom : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hz : z ∈ Metric.closedBall z₀ r₃) (ha : 0 < endgameLocalRadius r₂ r₃) :
    localBox Ω I (vec3Ball z.1 (3 * endgameLocalRadius r₂ r₃))
      (Ioo (z.2 - (3 * endgameLocalRadius r₂ r₃) ^ 2)
        (z.2 + (3 * endgameLocalRadius r₂ r₃) ^ 2)) ∧
    tsupport (endgameCutoff z ha) ⊆ vec3Ball z.1 (3 * endgameLocalRadius r₂ r₃) ×ˢ
      Ioo (z.2 - (3 * endgameLocalRadius r₂ r₃) ^ 2)
        (z.2 + (3 * endgameLocalRadius r₂ r₃) ^ 2) := by
  constructor
  · apply localBox_of_parabolic_ball (by positivity)
    apply Set.Subset.trans ?_ hdom
    apply parabolic_ball_subset_ball_of_center_mem_closedBall hz
    unfold endgameLocalRadius
    linarith only [hr₃, hrr]
  · intro w hw
    have hball := Metric.ball_subset_ball (by linarith only [ha] :
      2 * endgameLocalRadius r₂ r₃ ≤ 3 * endgameLocalRadius r₂ r₃)
      (endgameCutoff_tsupport_subset z ha hw)
    rw [metricBall_eq_parabolicBall] at hball
    exact hball

/-- The endgame cutoff family satisfies the common coefficient bound before
any domain, centre, or solution is selected. -/
theorem exists_force_slot_cutoff_family (r₂ r₃ : ℝ) (hr₃ : 0 < r₃)
    (hrr : r₃ < r₂ / 4) :
    let C₁₀ := forceSlotCutoffConstant (endgameLocalRadius r₂ r₃)
    0 ≤ C₁₀ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (z₀ z : ParabolicPoint),
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
        z ∈ Metric.closedBall z₀ r₃ →
        ∃ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
          localBox Ω I Ω' J ∧
          spaceTimeSet Ω' J ⊆ Metric.ball z (4 * endgameLocalRadius r₂ r₃) ∧
          tsupport φ ⊆ Ω' ×ˢ J ∧
          (∀ w ∈ Metric.ball z (endgameLocalRadius r₂ r₃), φ w = 1) ∧
          tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
            Metric.ball z (2 * endgameLocalRadius r₂ r₃) ∧
          (∀ w : Vec3 × ℝ, |φ w| ≤ C₁₀ ∧ |timePartial φ w| ≤ C₁₀ ∧
            (∀ j, |spatialPartial φ j w| ≤ C₁₀) ∧
            |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C₁₀) := by
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  refine ⟨(forceSlotCutoffConstant_pos ha).le, ?_⟩
  intro Ω I z₀ z hdom hz
  have hsub : Metric.ball z (2 * endgameLocalRadius r₂ r₃) ⊆
      Metric.ball z₀ (r₂ / 4) := by
    refine parabolic_ball_subset_ball_of_center_mem_closedBall hz ?_
    unfold endgameLocalRadius
    linarith only [hrr]
  have hts : tsupport (endgameCutoff z ha) ⊆
      parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (r₂ / 4) :=
    (endgameCutoff_tsupport_subset z ha).trans (preimage_mono hsub)
  obtain ⟨hbox, hφbox⟩ := force_slot_cutoff_local_box hr₃ hrr hdom hz ha
  refine ⟨endgameCutoff z ha, vec3Ball z.1 (3 * endgameLocalRadius r₂ r₃),
    Ioo (z.2 - (3 * endgameLocalRadius r₂ r₃) ^ 2)
      (z.2 + (3 * endgameLocalRadius r₂ r₃) ^ 2), ⟨endgameCutoff_smooth z ha,
      endgameCutoff_hasCompactSupport z ha, ?_⟩,
    hbox, ?_, hφbox,
    fun _ hw => endgameCutoff_eq_one ha hw,
    endgameCutoff_tsupport_subset z ha, endgameCutoff_coefficients_le z ha⟩
  · intro w hw
    exact hdom (Metric.ball_subset_ball (by linarith only [hr₂]) (hts hw))
  · intro w hw
    apply Metric.ball_subset_ball (by linarith only [ha] :
      3 * endgameLocalRadius r₂ r₃ ≤ 4 * endgameLocalRadius r₂ r₃)
    rw [metricBall_eq_parabolicBall]
    exact hw

end CKN.Core.Endgame
