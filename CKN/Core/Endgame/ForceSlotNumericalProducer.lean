-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumericalSelected
import CKN.Core.Endgame.ForceSlotNumericalTarget
import CKN.Core.Endgame.ForceSlotNumericalCutoff

/-!
# The numerical force-source producer

The selected pressure gradient is required on its localization collar.
The five explicit source estimates give the numerical force bound with
all constants fixed before the solution.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The quantitative pressure estimate and heat representation supply the
exact numerical force-source producer on its fixed pressure collar. -/
theorem exists_force_slot_numerical_producer
    (hGA : oneSidedPressureGradientQuantitative)
    (q M r₂ r₃ U P F C₁₀ C_CZ : ℝ)
    (hq : 5 / 2 < q) (hM : 1 ≤ M) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hC : 0 ≤ C₁₀) (hCZ : 0 ≤ C_CZ)
    (hL : ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {φ : Vec3 × ℝ → ℝ}, φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
        ∀ {Ω' : Set Vec3} {J : Set ℝ}, localBox Ω I Ω' J →
        tsupport φ ⊆ Ω' ×ˢ J →
        ∀ {Dp : ParabolicPoint → Vec3},
        (∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet Ω' J))) →
        (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ Ω' ×ˢ J →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
        localizedVelocity φ u =ᵐ[volume]
          (fun z i => heatPotential
            (fun w => localizedGradientSourceG φ u Du f Dp w i)
            (fun j w => localizedGradientSourceH φ u j w i) z)) :
    ∃ KU KD KU25 KP : ℝ≥0∞, KU < ⊤ ∧ KD < ⊤ ∧ KU25 < ⊤ ∧ KP < ⊤ ∧
    let KF₀ := endgameForceSlotBound q C₁₀ r₂ r₃ KU KU25 KD KP (ENNReal.ofReal F)
    KF₀ < ⊤ ∧
    (∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
        (z₀ : ParabolicPoint),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
        (∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
          max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
            M * r ^ (2 / 5 : ℝ)) →
        eLpNorm (fun z => vec3EuclideanNorm (u z)) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal U →
        eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal P →
        eLpNorm (fun z => vec3EuclideanNorm (f z)) (ENNReal.ofReal q)
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal F →
        ∀ z ∈ Metric.closedBall z₀ r₃,
        ∀ (φ : Vec3 × ℝ → ℝ),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
          tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
            Metric.ball z (2 * endgameLocalRadius r₂ r₃) →
          (∀ w : Vec3 × ℝ, |φ w| ≤ C₁₀ ∧
            |timePartial φ w| ≤ C₁₀ ∧
            (∀ j, |spatialPartial φ j w| ≤ C₁₀) ∧
            |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C₁₀) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, Integrable (fun w => Dp w i)
            (volume.restrict (Metric.ball z (4 * endgameLocalRadius r₂ r₃)))) ∧
          (∀ i (ψ : Vec3 × ℝ → ℝ),
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹'
              Metric.ball z (4 * endgameLocalRadius r₂ r₃) →
            (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
              -(∫ w : ParabolicPoint, Dp w i * ψ w)) ∧
          (∀ i, AEMeasurable
            (fun w => localizedGradientSourceG φ u Du f Dp w i) volume) ∧
          (∀ j i, AEMeasurable
            (fun w => localizedGradientSourceH φ u j w i) volume) ∧
          (∀ i, HasCompactSupport
            (fun w => localizedGradientSourceG φ u Du f Dp w i)) ∧
          (∀ j i, HasCompactSupport
            (fun w => localizedGradientSourceH φ u j w i)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
            (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤ KF₀)) := by
  obtain ⟨KU, KD, KU25, KP, hKU, hKD, hKU25, hKP, hselected⟩ :=
    exists_force_slot_uniform_selected_gradient hGA q M r₂ r₃ U P F C_CZ
      hq hM hr₃ hrr hCZ (fun _ _ _ _ _ _ _ hs _ _ _ hφ hb ht hi hw =>
        hL hs hφ hb ht hi hw)
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  let a := endgameLocalRadius r₂ r₃
  have ha : 0 < a := by dsimp [a, endgameLocalRadius]; linarith only [hrr]
  refine ⟨KU, KD, KU25, KP, hKU, hKD, hKU25, hKP,
    forceSlotNumericalBound_lt_top q C₁₀ _ hq (by positivity)
      hKU hKU25 hKD hKP ENNReal.ofReal_lt_top, ?_⟩
  intro Ω I u Du p f z₀ hsol hdom hdec hU hP hF z hz φ hφ hsupp hcoeff
  obtain ⟨hUi, hDi, hU25, Dp, hDp, hweak, hPN⟩ :=
    hselected Ω I u Du p f z₀ hsol hdom hdec hU hP hF z hz
  let B := vec3Ball z.1 (3 * a)
  let J := Ioo (z.2 - (3 * a) ^ 2) (z.2 + (3 * a) ^ 2)
  have hbox : localBox Ω I B J := (force_slot_cutoff_local_box hr₃ hrr hdom hz ha).1
  have hB : spaceTimeSet B J ⊆ Metric.ball z (4 * a) := by
    intro w hw
    apply Metric.ball_subset_ball (by linarith only [ha] : 3 * a ≤ 4 * a)
    rw [metricBall_eq_parabolicBall]
    exact hw
  have hφbox : tsupport φ ⊆ B ×ˢ J := by
    intro w hw
    have hm := Metric.ball_subset_ball (by linarith only [ha] : 2 * a ≤ 3 * a) (hsupp hw)
    rw [metricBall_eq_parabolicBall] at hm
    exact hm
  have hDpBox (i : Fin 3) := (hDp i).mono_measure (Measure.restrict_mono_set volume hB)
  have hcarrier : Metric.ball z (2 * (2 * a)) ⊆ spaceTimeSet Ω I := by
    apply Set.Subset.trans ?_ hdom
    apply parabolic_ball_subset_ball_of_center_mem_closedBall hz
    dsimp [a, endgameLocalRadius]
    linarith only [hr₃, hrr]
  have hsub : Metric.ball z (2 * a) ⊆ Metric.ball z₀ r₂ :=
    (force_slot_carrier_subset hrr hz).trans
      (Metric.ball_subset_ball (by linarith only [hr₂]))
  have hFlocal := (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)).trans hF
  have hN := force_slot_numerical_bound_of_selected_gradient q C₁₀ (2 * a)
    KU KU25 KD KP (ENNReal.ofReal F) hq (by positivity) hC hsol hφ hbox hφbox hcoeff
    z hcarrier hsupp hUi hU25 hDi hPN hDpBox hFlocal
  obtain ⟨hGae, hHae, hGc, hHc⟩ :=
    force_slot_sources_measurable_compact hsol hφ hbox hφbox hDpBox
  refine ⟨Dp, hDp, hweak, hGae, hHae, hGc, hHc, ?_⟩
  intro i
  simpa only [endgameForceSlotBound,
    show 2 * (2 * a) = 4 * endgameLocalRadius r₂ r₃ by dsimp [a]; ring] using hN i

end CKN.Core.Endgame
