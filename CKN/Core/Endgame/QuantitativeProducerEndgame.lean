-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.QuantitativeLocalizedEndgame

/-! # Uniform Hölder bounds from a numerical source producer

The Hölder constant is chosen before the solution, domain, and center. The
result remains conditional on uniform numerical estimates for the literal
localized sources; it does not establish those analytic estimates.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- A uniform numerical source producer gives a Hölder constant depending
only on the prescribed numerical parameters, before all solution data. -/
theorem endgame_holder_norm_of_uniform_source_producer
    (q M r₂ r₃ U P F : ℝ)
    (hq : 5 / 2 < q) (_ : 1 ≤ M)
    (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hU : 0 ≤ U) (_ : 0 ≤ P) (_ : 0 ≤ F)
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
            (fun j w => localizedGradientSourceH φ u j w i) z))
    (hsource : ∃ KF KG : ℝ≥0∞, KF < ∞ ∧ KG < ∞ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ)
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
        ∃ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ)
          (Dp : ParabolicPoint → Vec3),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
          localBox Ω I Ω' J ∧ tsupport φ ⊆ Ω' ×ˢ J ∧
          (∀ w ∈ Metric.ball z (endgameLocalRadius r₂ r₃), φ w = 1) ∧
          (∀ i, Integrable (fun w => Dp w i)
            (volume.restrict (spaceTimeSet Ω' J))) ∧
          (∀ i (ψ : Vec3 × ℝ → ℝ),
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ Ω' ×ˢ J →
            (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
              -(∫ w : ParabolicPoint, Dp w i * ψ w)) ∧
          (∀ i, AEMeasurable
            (fun w => localizedGradientSourceG φ u Du f Dp w i) volume) ∧
          (∀ j i, AEMeasurable (fun w => localizedGradientSourceH φ u j w i) volume) ∧
          (∀ i, HasCompactSupport (fun w => localizedGradientSourceG φ u Du f Dp w i)) ∧
          (∀ j i, HasCompactSupport (fun w => localizedGradientSourceH φ u j w i)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (stepTheta₀ (stepGamma₀ q))
            (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤ KF) ∧
          (∀ j i, morreyNorm (6 / 5 : ℝ) (stepTheta₁ (stepGamma₀ q))
            (fun w => localizedGradientSourceH φ u j w i) ≤ KG)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ)
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
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (Metric.closedBall z₀ r₃)] u ∧
          ParabolicHolderVecNormLE (Metric.closedBall z₀ r₃) w (stepGamma₀ q) C ∧
          ∀ z ∈ Metric.ball z₀ r₃, IsRegularPoint Ω I u z := by
  obtain ⟨KF, KG, hKF, hKG, hsource⟩ := hsource
  refine ⟨endgameHolderBound q r₂ r₃ U KF KG, ?_, ?_⟩
  · have ha : 0 ≤ endgameLocalRadius r₂ r₃ := by
      unfold endgameLocalRadius
      linarith only [hrr]
    have hLnonneg := endgameLocalHolderBound_nonneg q ha hU KF KG
    unfold endgameHolderBound
    exact add_nonneg hLnonneg (le_trans hLnonneg (le_max_left _ _))
  · intro Ω I u Du p f z₀ hsol hdom hdecay hUnorm hPnorm hFnorm
    exact endgame_holder_norm_of_localized_source_bounds q r₂ r₃ U KF KG
      hq hr₃ hrr hU hKF hKG hL hsol hdom hUnorm
      (hsource Ω I u Du p f z₀ hsol hdom hdecay hUnorm hPnorm hFnorm)

end CKN.Core.Endgame
