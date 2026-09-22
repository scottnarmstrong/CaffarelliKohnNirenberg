-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step2.ThetaDecayAbsoluteConstant

open CKN.Foundation.Parabolic CKN.Core.Step3
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The first combined-decay display with an absolute leading constant and a
force-exponent-dependent second constant. -/
theorem theta_decay_discharge :
    ∃ C₂₇ : ℝ, 0 < C₂₇ ∧ ∀ q : ℝ, 5 / 2 < q →
      ∃ C₂₈ : ℝ, 0 < C₂₈ ∧
        ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
          (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
          (f : ParabolicPoint → Vec3), IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ (z : ParabolicPoint) (ρ : ℝ), 0 < ρ →
            closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
            let κ := iterationKappa C₂₇
            theta κ u Du p z (κ * ρ) ≤
              C₂₇ * κ ^ (2 / 3 : ℝ) * theta κ u Du p z ρ +
                C₂₇ * κ ^ (-5 : ℝ) *
                  (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
                    theta κ u Du p z ρ +
                C₂₈ * κ ^ (-1 / 2 : ℝ) * theta κ u Du p z ρ ^ (1 / 2 : ℝ) *
                  lambda q f z ρ ^ (1 / 2 : ℝ) +
                C₂₈ * κ ^ (-3 : ℝ) * lambda q f z ρ := by
  obtain ⟨C₂₇, hC₂₇, hq⟩ := thetaDecay_T_of_sws_absolute
  refine ⟨C₂₇, hC₂₇, ?_⟩
  intro q hqRange
  obtain ⟨C₂₈, hC₂₈, hdisplay⟩ := hq q
  refine ⟨C₂₈, hC₂₈, ?_⟩
  intro Ω I u Du p f hsol z ρ hρ hsub
  exact (hdisplay Ω I u Du p f hsol hρ hsub).1

end CKN
