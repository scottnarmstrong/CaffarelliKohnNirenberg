-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step2.ThetaDecayAbsoluteConstant

/-!
# The small-`θ` decay display

This file extracts the small-`θ` conclusion of the combined decay theorem at
the fixed iteration scale. -/

open CKN.Foundation.Parabolic Set

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The small-`θ` display with an absolute leading constant and a
force-exponent-dependent second constant. -/
theorem theta_small_paper :
    ∃ C₂₇ : ℝ, 0 < C₂₇ ∧ ∀ q : ℝ, ∃ C₂₈ : ℝ, 0 < C₂₈ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
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
  obtain ⟨C₂₇, hC₂₇, h⟩ := thetaDecay_T_of_sws_absolute
  refine ⟨C₂₇, hC₂₇, ?_⟩
  intro q
  obtain ⟨C₂₈, hC₂₈, hh⟩ := h q
  refine ⟨C₂₈, hC₂₈, ?_⟩
  intro Ω I u Du p f hsol z ρ hρ hsub
  exact (hh Ω I u Du p f hsol hρ hsub).2

end CKN
