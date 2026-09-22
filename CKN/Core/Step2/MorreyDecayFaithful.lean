-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step2.MorreyDecay
import CKN.Core.Step2.ThetaDecayAbsoluteConstant

open CKN.Foundation.Parabolic Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Small gradient limsup gives uniform neighbourhood Morrey decay, with the
threshold fixed by the absolute leading theta-decay constant. -/
theorem morrey_decay_from_gradient :
    ∃ C₂₇ : ℝ, 0 < C₂₇ ∧ ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      5 / 2 < q → ∀ {z₀ : ParabolicPoint}, z₀ ∈ spaceTimeSet Ω I →
      Filter.limsup (fun r : ℝ =>
          (ENNReal.ofReal r)⁻¹ *
            ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
              ENNReal.ofReal (spatialGradientSq u Du w))
        (𝓝[>] (0 : ℝ)) <
          ENNReal.ofReal ((iterationEpsilonStar C₂₇) ^ (2 : ℕ)) →
      ∃ r₂ M : ℝ, 0 < r₂ ∧ 1 ≤ M ∧
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I ∧
        (∀ z, z ∈ Metric.ball z₀ r₂ → ∀ r : ℝ, 0 < r → r < r₂ →
          max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
            M * r ^ (2 / 5 : ℝ)) := by
  obtain ⟨C₂₇, hC₂₇, hq⟩ := thetaDecay_T_of_sws_absolute
  refine ⟨C₂₇, hC₂₇, ?_⟩
  intro Ω I q u Du p f hsol hqRange z₀ hz₀ hβlim
  obtain ⟨C₂₈, hC₂₈, hdisplays⟩ := hq q
  have hThetaDecay :
      ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
            C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
              C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
                  theta (iterationKappa C₂₇) u Du p z ρ +
              C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    lambda q f z ρ ^ (1 / 2 : ℝ) +
              C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ ∧
        (theta (iterationKappa C₂₇) u Du p z ρ ≤ 1 →
          theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
            C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
              2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    theta (iterationKappa C₂₇) u Du p z ρ +
              C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    lambda q f z ρ ^ (1 / 2 : ℝ) +
              C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ) := by
    intro z ρ hρ hsub
    exact hdisplays Ω I u Du p f hsol hρ hsub
  exact morreyDecay_of_thetaDecay hsol hqRange hz₀ hC₂₇ hC₂₈
    hThetaDecay hβlim

end CKN
