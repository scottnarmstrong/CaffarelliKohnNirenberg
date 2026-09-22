-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.QuantitativeEndgame
import CKN.Core.Endgame.Localization
import CKN.Core.Step4.SourceMorreyGradient
import CKN.Setting.PoincareSobolevL1SliceBasic

/-! # Quantitative bounds from literal localized sources

The numerical source bounds remain explicit hypotheses. This result converts
them, together with the localized heat identity, into a uniform full Hölder
norm. It does not establish the uniform source estimates themselves.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- Literal localized sources with common numerical bounds give an explicit
Hölder norm on the prescribed closed ball and interior regularity. -/
theorem endgame_holder_norm_of_localized_source_bounds
    (q r₂ r₃ U : ℝ) (KF KG : ℝ≥0∞)
    (hq : 5 / 2 < q) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hU : 0 ≤ U) (hKF : KF < ∞) (hKG : KG < ∞)
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
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint}
    (hdom : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hUnorm : eLpNorm (fun z => vec3EuclideanNorm (u z))
      (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict (Metric.ball z₀ r₂)) ≤
        ENNReal.ofReal U)
    (hsource : ∀ z ∈ Metric.closedBall z₀ r₃,
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
        (∀ i, AEMeasurable (fun w => localizedGradientSourceG φ u Du f Dp w i) volume) ∧
        (∀ j i, AEMeasurable (fun w => localizedGradientSourceH φ u j w i) volume) ∧
        (∀ i, HasCompactSupport (fun w => localizedGradientSourceG φ u Du f Dp w i)) ∧
        (∀ j i, HasCompactSupport (fun w => localizedGradientSourceH φ u j w i)) ∧
        (∀ i, morreyNorm (6 / 5 : ℝ) (stepTheta₀ (stepGamma₀ q))
          (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤ KF) ∧
        (∀ j i, morreyNorm (6 / 5 : ℝ) (stepTheta₁ (stepGamma₀ q))
          (fun w => localizedGradientSourceH φ u j w i) ≤ KG)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (Metric.closedBall z₀ r₃)] u ∧
      ParabolicHolderVecNormLE (Metric.closedBall z₀ r₃) w (stepGamma₀ q)
        (endgameHolderBound q r₂ r₃ U KF KG) ∧
      ∀ z ∈ Metric.ball z₀ r₃, IsRegularPoint Ω I u z := by
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  have hbox := localBox_of_parabolic_ball hr₂ hdom
  have hdata := hsol.2.2.2.2.2.1 _ _ hbox
  have hball : Metric.ball z₀ r₂ =
      spaceTimeSet (vec3Ball z₀.1 r₂) (Ioo (z₀.2 - r₂ ^ 2) (z₀.2 + r₂ ^ 2)) := by
    rw [metricBall_eq_parabolicBall z₀ r₂]
    rfl
  have hu : AEStronglyMeasurable (fun z => vec3EuclideanNorm (u z))
      (volume.restrict (Metric.ball z₀ r₂)) := by
    rw [hball]
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hdata.1
  apply endgame_holder_norm_of_local_source_bounds q r₂ r₃ U KF KG hq hr₃ hrr
    hU hKF hKG ((Metric.ball_subset_ball (by linarith only [hr₂])).trans hdom)
    hu hUnorm
  intro z hz
  obtain ⟨φ, Ω', J, Dp, hφ, hbox', hsupp, hone, hDp, hweak,
    hF, hG, hFc, hGc, hNF, hNG⟩ := hsource z hz
  refine ⟨localizedGradientSourceG φ u Du f Dp, localizedGradientSourceH φ u,
    hF, hG, hFc, hGc, hNF, hNG, ?_⟩
  have hrep := hL hsol hφ hbox' hsupp hDp hweak
  filter_upwards [ae_restrict_of_ae hrep,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with w hw hwm
  have hφw := hone w hwm
  simpa only [localizedVelocity, hφw, one_smul] using hw

end CKN.Core.Endgame
