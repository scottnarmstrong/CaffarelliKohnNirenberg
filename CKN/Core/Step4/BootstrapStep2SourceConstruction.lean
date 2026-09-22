-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.BootstrapFaithfulProp
import CKN.Core.Step2.MorreyDecayFaithful
import CKN.Core.Step2.MorreyFormUniform

/-!
# Building the Step 2 Morrey data consumed by one bootstrap round

`Step2MorreySources` is the hypothesis of `bootstrap_round_of_step2`: the three
Morrey memberships of the Step 2 display, carried on the ball `Q₂` on which the
round is run.  This file produces that structure, so that the bootstrap round is
a statement about data that exists rather than a conditional nobody can trigger.

The construction has two layers.  The first is the Step 2 lemma in Morrey form:
on the neighbourhood supplied by the Morrey decay estimate, the localized
velocity, gradient and pressure lie in `M^{3,25/3}`, `M^{2,25/8}` and
`M^{3/2,25/8}`.  The second removes the decay estimate from the hypotheses by
producing it from the small-gradient criterion, leaving a threshold `ε₁` fixed
before any solution and the suitable weak solution itself.

The last three results run the bootstrap round on the constructed data at the
Step 2 velocity exponent `25/3`.  The round's output exponent is then exactly
`25`, and the conclusion is the Morrey membership `M^{3,25}` on every strictly
smaller ball; in particular on the quarter ball, which is the set on which the
one-round velocity improvement is stated.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Step4

/-- The Step 2 Morrey data on `Q₂ = 𝔅_{r₂/4}(z₀)`, packaged as the structure the
bootstrap round consumes.  The hypotheses are the neighbourhood radius, the decay
constant, the suitable weak solution, the inclusion of `𝔅_{2r₂}(z₀)` in the
space-time domain, and the Morrey decay estimate on `𝔅_{r₂}(z₀)`. -/
theorem step2MorreySources_of_morreyDecay
    {r₂ M : ℝ} (hr₂ : 0 < r₂) (hM : 1 ≤ M)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint}
    (hdom : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
        M * r ^ (2 / 5 : ℝ)) :
    Step2MorreySources
      (Q₂ := Metric.ball z₀ (r₂ / 4)) (u := u) (Du := Du) (p := p) := by
  obtain ⟨Kᵤ, K_Du, Kₚ, hKᵤ, hK_Du, hKₚ, hbounds⟩ :=
    CKN.step2_morrey_form_uniform M r₂ hM hr₂
  obtain ⟨huN, hDuN, hpN⟩ := hbounds hsol z₀ hdom hdecay
  obtain ⟨hu, hDu, hp⟩ :=
    CKN.step2_morrey_form_uniform_membership hKᵤ hK_Du hKₚ huN hDuN hpN
  exact ⟨hu, hDu, hp⟩

/-- The Step 2 Morrey data for every suitable weak solution with small gradient
limsup at the base point.  The threshold `ε₁` is fixed before the solution; the
neighbourhood radius `r₂` is produced with the data. -/
theorem step2MorreySources_of_sws :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (q : ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          ∃ r₂ : ℝ, 0 < r₂ ∧
            Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I ∧
            Step2MorreySources
              (Q₂ := Metric.ball z₀ (r₂ / 4)) (u := u) (Du := Du) (p := p) := by
  obtain ⟨C₂₇, hC₂₇, hdecay⟩ := CKN.morrey_decay_from_gradient
  refine ⟨CKN.iterationEpsilonStar C₂₇, CKN.iterationEpsilonStar_pos hC₂₇, ?_⟩
  intro Ω I q u Du p f hsol z₀ hz₀ hlim
  obtain ⟨r₂, M, hr₂, hM, hdom, hbound⟩ :=
    hdecay hsol hsol.2.2.2.1 hz₀ hlim
  exact ⟨r₂, hr₂, hdom,
    step2MorreySources_of_morreyDecay hr₂ hM hsol hdom hbound⟩

/-- One bootstrap round on the constructed Step 2 data, run at the Step 2
velocity exponent `25/3`.  The round's output exponent is `25`, so the velocity
gains the Morrey membership `M^{3,25}` on every ball strictly inside `Q₂`. -/
theorem bootstrapRoundGain_of_step2MorreySources
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (r₂ r₃ : ℝ)
    (hr₂ : 0 < r₂) (hr₃ : 0 < r₃) (hr₃₂ : r₃ < r₂ / 4)
    (hdom : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hStep2 : Step2MorreySources
      (Q₂ := Metric.ball z₀ (r₂ / 4)) (u := u) (Du := Du) (p := p)) :
    CKN.morreyVecMem 3 25 (Metric.ball z₀ r₃) u := by
  obtain ⟨varsigma, hvarsigma, hmem⟩ :=
    bootstrap_round_of_step2 hsol z₀ r₂ r₃ hr₂ hr₃ hr₃₂ hdom hsol.2.2.2.1
      hStep2 (25 / 3 : ℝ) (by norm_num) hStep2.velocity (by norm_num)
  have hrecip : 1 / varsigma = 1 / (25 : ℝ) := by
    rw [hvarsigma]; norm_num
  have hinv : varsigma⁻¹ = (25 : ℝ)⁻¹ := by
    simpa only [one_div] using hrecip
  have heq : varsigma = (25 : ℝ) := by
    simpa only [inv_inv] using congrArg (fun x : ℝ => x⁻¹) hinv
  rw [heq] at hmem
  exact hmem

/-- The quarter-ball form of the round's conclusion: the Morrey membership
`M^{3,25}` on `𝔅_{(r₂/4)/4}(z₀)`, the set carrying the one-round velocity
improvement when that improvement is run on `𝔅_{r₂/4}(z₀)`. -/
theorem bootstrapRoundGain_quarterBall_of_step2MorreySources
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (r₂ : ℝ) (hr₂ : 0 < r₂)
    (hdom : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hStep2 : Step2MorreySources
      (Q₂ := Metric.ball z₀ (r₂ / 4)) (u := u) (Du := Du) (p := p)) :
    CKN.morreyVecMem 3 25 (Metric.ball z₀ (r₂ / 4 / 4)) u :=
  bootstrapRoundGain_of_step2MorreySources hsol z₀ r₂ (r₂ / 4 / 4) hr₂
    (by positivity) (by linarith only [hr₂]) hdom hStep2

/-- The quarter-ball gain from the three Step 2 memberships in unpackaged form,
that is, in the shape in which the neighbourhood lemma of Step 2 delivers
them. -/
theorem bootstrapRoundGain_of_morreySources
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (r₂ : ℝ) (hr₂ : 0 < r₂)
    (hdom : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hu : CKN.morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ (r₂ / 4)) u)
    (hDu : ∀ i : Fin 3, CKN.morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ (r₂ / 4)) (fun z => Du z i))
    (hp : morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
      ((Metric.ball z₀ (r₂ / 4)).indicator p) < ⊤) :
    CKN.morreyVecMem 3 25 (Metric.ball z₀ (r₂ / 4 / 4)) u :=
  bootstrapRoundGain_quarterBall_of_step2MorreySources hsol z₀ r₂ hr₂ hdom
    ⟨hu, hDu, hp⟩

/-- The one-round velocity improvement interface, in the exact shape the
regularity assembly consumes it, discharged through `bootstrap_round_of_step2`.
Two inputs beyond that interface are written out: the Step 2 pressure bound on
the same ball, and the fourfold larger domain ball the round is proved on. -/
theorem routeAOneRoundInterface_of_bootstrapRound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (R : ℝ) (hR : 0 < R)
    (hdom : Metric.ball z₀ (8 * R) ⊆ spaceTimeSet Ω I)
    (hu : CKN.morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u)
    (hDu : ∀ i : Fin 3, CKN.morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ R) (fun z => Du z i))
    (hp : morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
      ((Metric.ball z₀ R).indicator p) < ⊤) :
    CKN.morreyVecMem 3 25 (Metric.ball z₀ (R / 4)) u := by
  have hquarter : 4 * R / 4 = R := by ring
  have hdouble : 2 * (4 * R) = 8 * R := by ring
  have hdom' : Metric.ball z₀ (2 * (4 * R)) ⊆ spaceTimeSet Ω I := by
    rw [hdouble]; exact hdom
  have hu' : CKN.morreyVecMem 3 (25 / 3 : ℝ)
      (Metric.ball z₀ (4 * R / 4)) u := by rw [hquarter]; exact hu
  have hDu' : ∀ i : Fin 3, CKN.morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ (4 * R / 4)) (fun z => Du z i) := by
    rw [hquarter]; exact hDu
  have hp' : morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
      ((Metric.ball z₀ (4 * R / 4)).indicator p) < ⊤ := by
    rw [hquarter]; exact hp
  exact bootstrapRoundGain_of_step2MorreySources hsol z₀ (4 * R) (R / 4)
    (by linarith only [hR]) (by linarith only [hR])
    (by rw [hquarter]; linarith only [hR]) hdom' ⟨hu', hDu', hp'⟩

/-- The one-round Morrey gain for every suitable weak solution with small
gradient limsup at the base point, obtained by running `bootstrap_round_of_step2`
on the Step 2 data constructed above.  The threshold `ε₁` is fixed before the
solution. -/
theorem bootstrapRoundGain_of_sws :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (q : ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          ∃ r₂ : ℝ, 0 < r₂ ∧
            Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I ∧
            ∀ r₃ : ℝ, 0 < r₃ → r₃ < r₂ / 4 →
              CKN.morreyVecMem 3 25 (Metric.ball z₀ r₃) u := by
  obtain ⟨ε₁, hε₁, hsources⟩ := step2MorreySources_of_sws
  refine ⟨ε₁, hε₁, ?_⟩
  intro Ω I q u Du p f hsol z₀ hz₀ hlim
  obtain ⟨r₂, hr₂, hdom, hStep2⟩ := hsources Ω I q u Du p f hsol z₀ hz₀ hlim
  refine ⟨r₂, hr₂, hdom, ?_⟩
  intro r₃ hr₃ hr₃₂
  exact bootstrapRoundGain_of_step2MorreySources hsol z₀ r₂ r₃ hr₂ hr₃ hr₃₂
    hdom hStep2

end CKN.Core.Step4
