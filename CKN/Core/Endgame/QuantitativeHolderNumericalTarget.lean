-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.QuantitativeHolderSourceTarget
import CKN.Core.Endgame.QuantitativeHolderDerivativeSource
import CKN.Core.Endgame.Localization
import CKN.Core.Step2.MorreyFormUniform

/-!
# The numerical source data of `thm:endgame` with the derivative slot proved

The quantitative consumer of `thm:endgame` needs numerical Morrey bounds for
both slots of the localized equation, fixed before the solution, the domain
and the center. The derivative slot is `-2 (∂_i φ) u`, so its bound follows
from two numbers that already precede the solution: a derivative bound for
the localization cutoffs, which depends on the radii alone, and the Step 2
velocity Morrey constant, which depends on `M` and `r₂` alone.

This module carries out that step. What remains assumed is the force slot,
namely the numerical Morrey bound for `g - φ ∇p` at the exponent
`min {q, 25/9}` of the proof of `thm:endgame`, together with the selected
pressure gradient it contains, and a family of localization cutoffs with a
common bound for the cutoff value, time derivative, spatial first derivatives,
and spatial Laplacian. The force estimate uses exactly these same coefficient
bounds. Neither assumption mentions Hölder continuity.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The numerical source data of `thm:endgame` at the exponents `θ₀`, `θ₁`
of `eq:q0q1`, from a cutoff family with a common derivative bound `C₁₀`, the
Step 2 velocity constant, and a numerical force-slot bound `KF₀`. The
derivative-slot constant is proved, not assumed: it is
`endgameDerivativeSourceFactor` times `endgameDerivativeSourceConstant C₁₀`
applied to the Step 2 velocity constant attached to `M` and `r₂`. -/
theorem endgame_source_target_of_force_producer
    (q M r₂ r₃ U P F C₁₀ : ℝ) (KF₀ : ℝ≥0∞)
    (hq : 5 / 2 < q) (hM : 1 ≤ M) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hC : 0 ≤ C₁₀) (hKF₀ : KF₀ < ∞)
    (hcut : ∀ (Ω : Set Vec3) (I : Set ℝ) (z₀ z : ParabolicPoint),
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
          (∀ w : Vec3 × ℝ, |φ w| ≤ C₁₀ ∧
            |timePartial φ w| ≤ C₁₀ ∧
            (∀ j, |spatialPartial φ j w| ≤ C₁₀) ∧
            |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C₁₀))
    (hforce : ∀ (Ω : Set Vec3) (I : Set ℝ)
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
            (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤ KF₀)) :
    ∃ KF KG : ℝ≥0∞, KF < ∞ ∧ KG < ∞ ∧
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
          (∀ j i, AEMeasurable
            (fun w => localizedGradientSourceH φ u j w i) volume) ∧
          (∀ i, HasCompactSupport
            (fun w => localizedGradientSourceG φ u Du f Dp w i)) ∧
          (∀ j i, HasCompactSupport
            (fun w => localizedGradientSourceH φ u j w i)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (stepTheta₀ (stepGamma₀ q))
            (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤ KF) ∧
          (∀ j i, morreyNorm (6 / 5 : ℝ) (stepTheta₁ (stepGamma₀ q))
            (fun w => localizedGradientSourceH φ u j w i) ≤ KG) := by
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  obtain ⟨Kᵤ, K_Du, Kₚ, hKᵤ, _hK_Du, _hKₚ, hstep2⟩ :=
    step2_morrey_form_uniform M r₂ hM hr₂
  refine ⟨KF₀, endgameDerivativeSourceFactor q r₂ r₃ *
    endgameDerivativeSourceConstant C₁₀ Kᵤ, hKF₀,
    ENNReal.mul_lt_top (endgameDerivativeSourceFactor_lt_top hrr)
      (endgameDerivativeSourceConstant_lt_top hKᵤ), ?_⟩
  intro Ω I u Du p f z₀ hsol hdom hdecay hUnorm hPnorm hFnorm z hz
  obtain ⟨φ, Ω', J, hφ, hbox, hboxcarrier, hφbox, hone, hφcarrier, hcoeff⟩ :=
    hcut Ω I z₀ z hdom hz
  obtain ⟨Dp, hDpIntCarrier, hDpweakCarrier, hGmeas, hHmeas, hGsupp, hHsupp, hGnorm⟩ :=
    hforce Ω I u Du p f z₀ hsol hdom hdecay hUnorm hPnorm hFnorm z hz
      φ hφ hφcarrier hcoeff
  have hDpInt (i : Fin 3) := (hDpIntCarrier i).mono_measure
    (Measure.restrict_mono_set volume hboxcarrier)
  have hDpweak (i : Fin 3) (ψ : Vec3 × ℝ → ℝ)
      (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
      (hs : tsupport ψ ⊆ Ω' ×ˢ J) :=
    hDpweakCarrier i ψ hψ (fun w hw => hboxcarrier (hs hw))
  -- the cutoff derivatives vanish outside the fixed local ball
  have hvanish : ∀ j, ∀ w ∉ Metric.ball z (2 * endgameLocalRadius r₂ r₃),
      spatialPartial φ j w = 0 := by
    intro j w hw
    have hnot : (w.1, w.2) ∉ tsupport φ := fun hm => hw (hφcarrier hm)
    have hd := spatialPartial_zero_of_not_mem_tsupport_public hφ.1 hnot j
    change spatialPartial φ j w = 0 at hd
    exact hd
  -- the local ball sits inside the Step 2 carrier
  have hsub : Metric.ball z (2 * endgameLocalRadius r₂ r₃) ⊆
      Metric.ball z₀ (r₂ / 4) := by
    refine parabolic_ball_subset_ball_of_center_mem_closedBall hz ?_
    unfold endgameLocalRadius
    linarith only [hr₃, hrr]
  have hsubfull : Metric.ball z (2 * endgameLocalRadius r₂ r₃) ⊆
      Metric.ball z₀ r₂ :=
    hsub.trans (Metric.ball_subset_ball (by linarith only [hr₂]))
  -- componentwise velocity measurability on the local ball
  have hboxfull := localBox_of_parabolic_ball hr₂ hdom
  have hdata := hsol.2.2.2.2.2.1 _ _ hboxfull
  have hballeq : Metric.ball z₀ r₂ =
      spaceTimeSet (vec3Ball z₀.1 r₂) (Ioo (z₀.2 - r₂ ^ 2) (z₀.2 + r₂ ^ 2)) := by
    rw [metricBall_eq_parabolicBall z₀ r₂]
    rfl
  have humeas : ∀ i, AEMeasurable (fun w => u w i)
      (volume.restrict (Metric.ball z (2 * endgameLocalRadius r₂ r₃))) := by
    intro i
    have hfull : AEMeasurable (fun w => u w i)
        (volume.restrict (Metric.ball z₀ r₂)) := by
      rw [hballeq]
      exact aemeasurable_pi_iff.mp hdata.1.aemeasurable i
    exact hfull.mono_measure (Measure.restrict_mono_set volume hsubfull)
  -- the Step 2 velocity bound restricted to the local ball
  obtain ⟨hu25, _hDu25, _hp25⟩ := hstep2 hsol z₀ hdom hdecay
  have hvel : ∀ i, morreyBallNorm 3 (25 / 3 : ℝ)
      ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
        (fun w => u w i)) ≤ Kᵤ := by
    intro i
    refine le_trans (morreyBallNorm_mono (by norm_num) ?_) (hu25 i)
    intro w
    by_cases hw : w ∈ Metric.ball z (2 * endgameLocalRadius r₂ r₃)
    · rw [indicator_of_mem hw, indicator_of_mem (hsub hw)]
    · rw [indicator_of_notMem hw, abs_zero]
      exact abs_nonneg _
  have hHnorm : ∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
      (fun w => localizedGradientSourceH φ u j w i) ≤
        endgameDerivativeSourceConstant C₁₀ Kᵤ := by
    intro j i
    exact morreyNorm_localizedGradientSourceH_le hC
      Metric.isOpen_ball.measurableSet (fun j w => (hcoeff (w.1, w.2)).2.2.1 j)
        hvanish humeas hvel j i
  have hHvanish : ∀ j i, ∀ w ∉ Metric.ball z (2 * endgameLocalRadius r₂ r₃),
      localizedGradientSourceH φ u j w i = 0 := by
    intro j i w hw
    simp only [localizedGradientSourceH, localizedEquationH, hvanish j w hw,
      mul_zero, zero_smul, Pi.zero_apply]
  obtain ⟨hFtheta, hGtheta⟩ := source_norm_bounds_at_holder_exponents_on_ball
    q (2 * endgameLocalRadius r₂ r₃) KF₀
    (endgameDerivativeSourceConstant C₁₀ Kᵤ) hq (by linarith only [ha])
    (z₀ := z) hGnorm hHnorm hHvanish
  refine ⟨φ, Ω', J, Dp, hφ, hbox, hφbox, hone, hDpInt, hDpweak, hGmeas, hHmeas,
    hGsupp, hHsupp, hFtheta, ?_⟩
  intro j i
  refine (hGtheta j i).trans (le_of_eq ?_)
  unfold endgameDerivativeSourceFactor
  norm_num only [show 2 * (2 * endgameLocalRadius r₂ r₃) =
    4 * endgameLocalRadius r₂ r₃ by ring]

/-- The quantitative endgame constant of `thm:endgame` with the derivative
slot proved: a cutoff family with a common derivative bound, the Step 2
constants, and a numerical force-slot bound give a Hölder constant fixed
before the solution, the domain and the center. -/
theorem endgame_holder_norm_of_force_producer
    (q M r₂ r₃ U P F C₁₀ : ℝ) (KF₀ : ℝ≥0∞)
    (hq : 5 / 2 < q) (hM : 1 ≤ M) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hU : 0 ≤ U) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (hC : 0 ≤ C₁₀) (hKF₀ : KF₀ < ∞)
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
    (hcut : ∀ (Ω : Set Vec3) (I : Set ℝ) (z₀ z : ParabolicPoint),
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
          (∀ w : Vec3 × ℝ, |φ w| ≤ C₁₀ ∧
            |timePartial φ w| ≤ C₁₀ ∧
            (∀ j, |spatialPartial φ j w| ≤ C₁₀) ∧
            |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C₁₀))
    (hforce : ∀ (Ω : Set Vec3) (I : Set ℝ)
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
            (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤ KF₀)) :
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
          ∀ z ∈ Metric.ball z₀ r₃, IsRegularPoint Ω I u z :=
  endgame_holder_norm_of_uniform_source_producer q M r₂ r₃ U P F hq hM hr₃ hrr
    hU hP hF hL
    (endgame_source_target_of_force_producer q M r₂ r₃ U P F C₁₀ KF₀
      hq hM hr₃ hrr hC hKF₀ hcut hforce)

end CKN.Core.Endgame
