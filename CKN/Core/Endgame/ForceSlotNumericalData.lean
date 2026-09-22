-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step2.MorreyFormUniform
import CKN.Core.Endgame.QuantitativeEndgame
import CKN.Foundation.Parabolic.Morrey.Cylinders

/-!
# Step 2 data on the endgame source carrier

The initial velocity and gradient bounds are chosen before the solution.
Restriction to each local source ball preserves those bounds, and comparison
with cylinder Morrey norms introduces no additional constant.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- Every doubled endgame source ball is contained in the Step 2 carrier. -/
theorem force_slot_carrier_subset {r₂ r₃ : ℝ}
    (hrr : r₃ < r₂ / 4) {z₀ z : ParabolicPoint}
    (hz : z ∈ Metric.closedBall z₀ r₃) :
    Metric.ball z (2 * endgameLocalRadius r₂ r₃) ⊆ Metric.ball z₀ (r₂ / 4) := by
  refine parabolic_ball_subset_ball_of_center_mem_closedBall hz ?_
  unfold endgameLocalRadius
  linarith only [hrr]

/-- Uniform Step 2 bounds control the indicated local velocity and gradient
in cylinder Morrey norms at every endgame centre. -/
theorem exists_force_slot_step2_bounds (M r₂ r₃ : ℝ)
    (hM : 1 ≤ M) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4) :
    ∃ KU KD : ℝ≥0∞, KU < ⊤ ∧ KD < ⊤ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ z₀ : ParabolicPoint,
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
        (∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
          max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
            M * r ^ (2 / 5 : ℝ)) →
        ∀ z ∈ Metric.closedBall z₀ r₃,
          (∀ i, morreyNorm 3 (25 / 3)
            ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
              (fun w => u w i)) ≤ KU) ∧
          (∀ i j, morreyNorm 2 (25 / 8)
            ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
              (fun w => Du w i j)) ≤ KD) := by
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  obtain ⟨KU, KD, KP, hKU, hKD, _hKP, hstep⟩ :=
    step2_morrey_form_uniform M r₂ hM hr₂
  refine ⟨KU, KD, hKU, hKD, ?_⟩
  intro Ω I q u Du p f hsol z₀ hdom hdec z hz
  obtain ⟨hU, hD, _hP⟩ := hstep hsol z₀ hdom hdec
  have hsub := force_slot_carrier_subset hrr hz
  constructor
  · intro i
    apply (morreyNorm_le_morreyBallNorm (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (3 : ℝ) ≤ 25 / 3) _).trans
    apply le_trans (morreyBallNorm_mono (by norm_num) ?_) (hU i)
    intro w
    by_cases hw : w ∈ Metric.ball z (2 * endgameLocalRadius r₂ r₃)
    · rw [indicator_of_mem hw, indicator_of_mem (hsub hw)]
    · rw [indicator_of_notMem hw, abs_zero]
      exact abs_nonneg _
  · intro i j
    apply (morreyNorm_le_morreyBallNorm (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) ≤ 25 / 8) _).trans
    apply le_trans (morreyBallNorm_mono (by norm_num) ?_) (hD i j)
    intro w
    by_cases hw : w ∈ Metric.ball z (2 * endgameLocalRadius r₂ r₃)
    · rw [indicator_of_mem hw, indicator_of_mem (hsub hw)]
    · rw [indicator_of_notMem hw, abs_zero]
      exact abs_nonneg _

/-- The original vector force norm controls the scalar indicated norm used
by the termwise force estimate on every smaller measurable carrier. -/
theorem force_slot_force_component_norm_le (q : ℝ) (Fnorm : ℝ≥0∞) (hq : 0 < q)
    {Q B : Set ParabolicPoint} (hQ : MeasurableSet Q) (hQB : Q ⊆ B)
    {f : ParabolicPoint → Vec3} (i : Fin 3)
    (hf : AEMeasurable (fun w => f w i) (volume.restrict Q))
    (hF : eLpNorm (fun w => vec3EuclideanNorm (f w)) (ENNReal.ofReal q)
      (volume.restrict B) ≤ Fnorm) :
    eLpNorm' (Q.indicator (fun w => f w i)) q volume ≤ Fnorm := by
  have hi : AEMeasurable (Q.indicator (fun w => f w i)) volume :=
    (aemeasurable_indicator_iff hQ).mpr hf
  have hN : eLpNorm (Q.indicator (fun w => f w i)) (ENNReal.ofReal q) volume ≤ Fnorm := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hQ]
    apply (eLpNorm_mono_real hf.aestronglyMeasurable (fun w => ?_)).trans
    · exact (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hQB)).trans hF
    · change |f w i| ≤ vec3EuclideanNorm (f w)
      exact Real.abs_le_sqrt (Finset.single_le_sum
        (fun j _ => sq_nonneg (f w j)) (Finset.mem_univ i))
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hq).ne'
    ENNReal.ofReal_ne_top hi.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le] at hN
  exact hN

end CKN.Core.Endgame
