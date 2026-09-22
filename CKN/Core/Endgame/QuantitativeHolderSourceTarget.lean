-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.QuantitativeProducerEndgame
import CKN.Core.Endgame.Localization
import CKN.Core.Endgame.CompactBall
import CKN.Core.Endgame.SourceExponents
import CKN.Setting.ScalingInvarianceTests

/-!
# Numerical source data at the Hölder exponents of `thm:endgame`

The quantitative form of `thm:endgame` asks for a Hölder constant fixed
before the solution, the domain and the center. Its consumer needs the
Morrey norms of the two literal localized sources at the exponents `θ₀` and
`θ₁` of `eq:q0q1`, bounded by numbers chosen in advance.

Two steps of that reduction are solution independent and are carried out
here. First, the localization cutoff of `lem:local-equation` is built at the
fixed scale attached to the pair of radii `r₂`, `r₃`: it equals one on the
ball of radius `(r₂/4 - r₃)/512` around any center of the inner ball and is
supported in twice that ball. Second, the source exponents of the proof of
`thm:endgame`, namely `min {q, 25/9}` for the force slot and `25/3` for the
derivative slot, are converted to `θ₀` and `θ₁`; on the bounded support of
the derivative slot this costs the explicit radius factor recorded below and
nothing else.

What is left assumed is exactly the analytic content of the quantitative
Steps 2--4: numerical Morrey bounds for the literal localized sources at the
paper's own exponents, with constants preceding all solution data. No Hölder
conclusion is assumed anywhere.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The radius parameter of the localization cutoff attached to the pair of
radii of `thm:endgame`: the cutoff equals one on the ball of radius
`endgameLocalRadius r₂ r₃` and is supported in twice that ball. -/
def endgameCutoffScale (r₂ r₃ : ℝ) : ℝ := 8 * endgameLocalRadius r₂ r₃

/-- The cutoff scale is positive on the admissible pairs of radii. -/
theorem endgameCutoffScale_pos {r₂ r₃ : ℝ} (hrr : r₃ < r₂ / 4) :
    0 < endgameCutoffScale r₂ r₃ := by
  unfold endgameCutoffScale endgameLocalRadius
  linarith only [hrr]

/-- The explicit factor paid when the derivative source exponent `25/3` of
the proof of `thm:endgame` is lowered to `θ₁` on a support of radius
`2 * endgameLocalRadius r₂ r₃`. -/
def endgameDerivativeSourceFactor (q r₂ r₃ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 * endgameLocalRadius r₂ r₃) ^
    (5 * (1 / stepTheta₁ (stepGamma₀ q) - 3 / 25))

/-- The exponent-conversion factor is finite. -/
theorem endgameDerivativeSourceFactor_lt_top {q r₂ r₃ : ℝ} (hrr : r₃ < r₂ / 4) :
    endgameDerivativeSourceFactor q r₂ r₃ < ∞ := by
  have ha : 0 < 4 * endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  unfold endgameDerivativeSourceFactor
  exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top)

/-- The localization cutoff of `lem:local-equation` at the fixed scale of
`thm:endgame`: around every center of the inner ball it equals one on the
ball of radius `endgameLocalRadius r₂ r₃` and is supported in twice that
ball, inside a local box of the solution domain. Only the radii enter. -/
theorem exists_endgame_localization_cutoff
    {Ω : Set Vec3} {I : Set ℝ} {z₀ z : ParabolicPoint} {r₂ r₃ : ℝ}
    (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hdom : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hz : z ∈ Metric.closedBall z₀ r₃) :
    ∃ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
      localBox Ω I Ω' J ∧
      tsupport φ ⊆ Ω' ×ˢ J ∧
      (∀ w ∈ Metric.ball z (endgameLocalRadius r₂ r₃), φ w = 1) ∧
      tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
        Metric.ball z (2 * endgameLocalRadius r₂ r₃) := by
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  have hscale : 0 < endgameCutoffScale r₂ r₃ := endgameCutoffScale_pos hrr
  have hsub : Metric.ball z (2 * endgameCutoffScale r₂ r₃) ⊆
      Metric.ball z₀ (2 * r₂) := by
    refine parabolic_ball_subset_ball_of_center_mem_closedBall hz ?_
    unfold endgameCutoffScale endgameLocalRadius
    linarith only [hr₃, hrr]
  obtain ⟨φ, hφ, _hrange, hone, hsupp, hbox, hφbox⟩ :=
    exists_localization_cutoff (z₀ := z) (r := endgameCutoffScale r₂ r₃)
      hscale (hsub.trans hdom)
  refine ⟨φ, vec3Ball z.1 (endgameCutoffScale r₂ r₃),
    Ioo (z.2 - endgameCutoffScale r₂ r₃ ^ 2)
      (z.2 + endgameCutoffScale r₂ r₃ ^ 2), hφ, hbox, hφbox, ?_, ?_⟩
  · intro w hw
    have hmem : w ∈ Metric.closedBall z (endgameCutoffScale r₂ r₃ / 8) := by
      refine Metric.ball_subset_closedBall ?_
      refine Metric.ball_subset_ball ?_ hw
      unfold endgameCutoffScale
      linarith only [ha]
    exact hone w hmem
  · refine hsupp.trans (preimage_mono (Metric.ball_subset_ball ?_))
    unfold endgameCutoffScale
    linarith only [ha]

/-- Numerical Morrey bounds for the literal localized sources at the paper's
own source exponents, with the two constants preceding all solution data,
give the numerical source data at the exponents `θ₀` and `θ₁` required by the
quantitative consumer of `thm:endgame`. The force slot keeps its constant;
the derivative slot pays exactly the explicit radius factor
`endgameDerivativeSourceFactor`, because its support is the fixed ball of
radius `2 * endgameLocalRadius r₂ r₃`. -/
theorem endgame_source_target_of_numerical_producer
    (q M r₂ r₃ U P F : ℝ) (KF₀ KG₀ : ℝ≥0∞)
    (hq : 5 / 2 < q) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hKF₀ : KF₀ < ∞) (hKG₀ : KG₀ < ∞)
    (hnum : ∀ (Ω : Set Vec3) (I : Set ℝ)
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
        ∀ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
          localBox Ω I Ω' J →
          tsupport φ ⊆ Ω' ×ˢ J →
          tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
            Metric.ball z (2 * endgameLocalRadius r₂ r₃) →
        ∃ Dp : ParabolicPoint → Vec3,
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
          (∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
            (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤ KF₀) ∧
          (∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
            (fun w => localizedGradientSourceH φ u j w i) ≤ KG₀)) :
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
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  refine ⟨KF₀, endgameDerivativeSourceFactor q r₂ r₃ * KG₀, hKF₀,
    ENNReal.mul_lt_top (endgameDerivativeSourceFactor_lt_top hrr) hKG₀, ?_⟩
  intro Ω I u Du p f z₀ hsol hdom hdecay hUnorm hPnorm hFnorm z hz
  obtain ⟨φ, Ω', J, hφ, hbox, hφbox, hone, hφcarrier⟩ :=
    exists_endgame_localization_cutoff hr₃ hrr hdom hz
  obtain ⟨Dp, hDpInt, hDpweak, hGmeas, hHmeas, hGsupp, hHsupp, hGnorm, hHnorm⟩ :=
    hnum Ω I u Du p f z₀ hsol hdom hdecay hUnorm hPnorm hFnorm z hz
      φ Ω' J hφ hbox hφbox hφcarrier
  have hHvanish : ∀ j i, ∀ w ∉ Metric.ball z (2 * endgameLocalRadius r₂ r₃),
      localizedGradientSourceH φ u j w i = 0 := by
    intro j i w hw
    have hnot : (w.1, w.2) ∉ tsupport φ := fun hm => hw (hφcarrier hm)
    have hd := spatialPartial_zero_of_not_mem_tsupport_public hφ.1 hnot j
    change spatialPartial φ j w = 0 at hd
    simp only [localizedGradientSourceH, localizedEquationH, hd, mul_zero,
      zero_smul, Pi.zero_apply]
  obtain ⟨hFtheta, hGtheta⟩ := source_norm_bounds_at_holder_exponents_on_ball
    q (2 * endgameLocalRadius r₂ r₃) KF₀ KG₀ hq (by linarith only [ha])
    (z₀ := z) hGnorm hHnorm hHvanish
  refine ⟨φ, Ω', J, Dp, hφ, hbox, hφbox, hone, hDpInt, hDpweak, hGmeas, hHmeas,
    hGsupp, hHsupp, hFtheta, ?_⟩
  intro j i
  refine (hGtheta j i).trans (le_of_eq ?_)
  unfold endgameDerivativeSourceFactor
  norm_num only [show 2 * (2 * endgameLocalRadius r₂ r₃) =
    4 * endgameLocalRadius r₂ r₃ by ring]

/-- The quantitative endgame constant from numerical source bounds at the
paper's own source exponents. Composing the exponent conversion above with
the quantitative consumer of `thm:endgame` gives a Hölder constant fixed
before the solution, the domain and the center, on the closed inner ball. -/
theorem endgame_holder_norm_of_numerical_producer
    (q M r₂ r₃ U P F : ℝ) (KF₀ KG₀ : ℝ≥0∞)
    (hq : 5 / 2 < q) (hM : 1 ≤ M) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hU : 0 ≤ U) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (hKF₀ : KF₀ < ∞) (hKG₀ : KG₀ < ∞)
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
    (hnum : ∀ (Ω : Set Vec3) (I : Set ℝ)
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
        ∀ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
          localBox Ω I Ω' J →
          tsupport φ ⊆ Ω' ×ˢ J →
          tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
            Metric.ball z (2 * endgameLocalRadius r₂ r₃) →
        ∃ Dp : ParabolicPoint → Vec3,
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
          (∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
            (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤ KF₀) ∧
          (∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
            (fun w => localizedGradientSourceH φ u j w i) ≤ KG₀)) :
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
    (endgame_source_target_of_numerical_producer q M r₂ r₃ U P F KF₀ KG₀
      hq hr₃ hrr hKF₀ hKG₀ hnum)

end CKN.Core.Endgame
