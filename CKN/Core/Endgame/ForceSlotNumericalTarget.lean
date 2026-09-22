-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumerical

/-!
# The endgame force bound from Step 2 and a selected pressure gradient

Step 2 chooses the initial velocity and gradient constants before the
solution. An improved velocity bound and a selected weak pressure gradient
then supply the full localized force estimate with an explicit constant.
The local integrability and weak-gradient identity are retained on exactly
the supplied cutoff box.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The five-term numerical constant at the endgame source radius. -/
def endgameForceSlotBound (q C r₂ r₃ : ℝ) (KU KU25 KD KP Fnorm : ℝ≥0∞) : ℝ≥0∞ :=
  forceSlotNumericalBound q C (4 * endgameLocalRadius r₂ r₃) KU KU25 KD KP Fnorm

/-- Step 2 and the selected gradient give the numerical force-source
conclusion on every endgame cutoff carrier. The improved velocity and
pressure-gradient bounds are stated explicitly as the remaining analytic
inputs, with their constants fixed before all fields. -/
theorem endgame_force_slot_of_step2_and_selected_gradient
    (q M r₂ r₃ C F : ℝ) (hq : 5 / 2 < q) (hM : 1 ≤ M)
    (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4) (hC : 0 ≤ C) :
    ∃ KU KD : ℝ≥0∞, KU < ⊤ ∧ KD < ⊤ ∧
      ∀ KU25 KP : ℝ≥0∞, KU25 < ⊤ → KP < ⊤ →
      endgameForceSlotBound q C r₂ r₃ KU KU25 KD KP (ENNReal.ofReal F) < ⊤ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
        (z₀ : ParabolicPoint),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
        (∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
          max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
            M * r ^ (2 / 5 : ℝ)) →
        eLpNorm (fun w => vec3EuclideanNorm (f w)) (ENNReal.ofReal q)
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal F →
        ∀ z ∈ Metric.closedBall z₀ r₃,
        ∀ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
          localBox Ω I Ω' J → tsupport φ ⊆ Ω' ×ˢ J →
          tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
            Metric.ball z (2 * endgameLocalRadius r₂ r₃) →
          (∀ w : Vec3 × ℝ, |φ w| ≤ C ∧ |timePartial φ w| ≤ C ∧
            (∀ j, |spatialPartial φ j w| ≤ C) ∧
            |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C) →
        ∀ Dp : ParabolicPoint → Vec3,
          (∀ i, Integrable (fun w => Dp w i)
            (volume.restrict (spaceTimeSet Ω' J))) →
          (∀ i (ψ : Vec3 × ℝ → ℝ),
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ Ω' ×ˢ J →
            (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
              -(∫ w : ParabolicPoint, Dp w i * ψ w)) →
          (∀ i, morreyNorm 3 25
            ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
              (fun w => u w i)) ≤ KU25) →
          (∀ i, morreyNorm (6 / 5) (min q (25 / 9))
            ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
              (fun w => Dp w i)) ≤ KP) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, Integrable (fun w => Dp w i)
            (volume.restrict (spaceTimeSet Ω' J))) ∧
          (∀ i (ψ : Vec3 × ℝ → ℝ),
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ Ω' ×ˢ J →
            (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
              -(∫ w : ParabolicPoint, Dp w i * ψ w)) ∧
          (∀ i, AEMeasurable (fun w => localizedGradientSourceG φ u Du f Dp w i) volume) ∧
          (∀ j i, AEMeasurable (fun w => localizedGradientSourceH φ u j w i) volume) ∧
          (∀ i, HasCompactSupport (fun w => localizedGradientSourceG φ u Du f Dp w i)) ∧
          (∀ j i, HasCompactSupport (fun w => localizedGradientSourceH φ u j w i)) ∧
          (∀ i, morreyNorm (6 / 5) (min q (25 / 9))
            (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤
              endgameForceSlotBound q C r₂ r₃ KU KU25 KD KP (ENNReal.ofReal F)) := by
  obtain ⟨KU, KD, hKU, hKD, hstep⟩ := exists_force_slot_step2_bounds M r₂ r₃ hM hr₃ hrr
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  refine ⟨KU, KD, hKU, hKD, ?_⟩
  intro KU25 KP hKU25 hKP
  refine ⟨forceSlotNumericalBound_lt_top q C _ hq (by positivity)
    hKU hKU25 hKD hKP ENNReal.ofReal_lt_top, ?_⟩
  intro Ω I u Du p f z₀ hsol hdom hdec hF z hz φ Ω' J hφ hbox hφbox hsupp hcoeff
    Dp hDp hweak hU25 hP
  obtain ⟨hU, hD⟩ := hstep hsol z₀ hdom hdec z hz
  have hsub : Metric.ball z (2 * endgameLocalRadius r₂ r₃) ⊆ Metric.ball z₀ r₂ :=
    (force_slot_carrier_subset hrr hz).trans
      (Metric.ball_subset_ball (by linarith only [hr₂]))
  have hcarrier : Metric.ball z (2 * (2 * endgameLocalRadius r₂ r₃)) ⊆ spaceTimeSet Ω I := by
    apply Set.Subset.trans ?_ hdom
    refine parabolic_ball_subset_ball_of_center_mem_closedBall hz ?_
    unfold endgameLocalRadius
    linarith only [hr₃, hrr]
  have hFlocal := (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)).trans hF
  have hN := force_slot_numerical_bound_of_selected_gradient q C _ KU KU25 KD KP
    (ENNReal.ofReal F) hq (by positivity) hC hsol hφ hbox hφbox hcoeff z hcarrier hsupp
    hU hU25 hD hP hDp hFlocal
  obtain ⟨hGae, hHae, hGc, hHc⟩ := force_slot_sources_measurable_compact hsol hφ hbox hφbox hDp
  refine ⟨Dp, hDp, hweak, hGae, hHae, hGc, hHc, ?_⟩
  intro i
  simpa only [endgameForceSlotBound,
    show 2 * (2 * endgameLocalRadius r₂ r₃) = 4 * endgameLocalRadius r₂ r₃ by ring] using hN i

end CKN.Core.Endgame
