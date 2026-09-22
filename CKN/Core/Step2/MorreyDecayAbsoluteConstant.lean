-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step2.MorreyDecay
import CKN.Core.Step2.ThetaDecayAbsoluteConstant

/-!
# Morrey decay on a neighbourhood, with an absolute leading constant

Paper label `prop:morrey-decay`, display `eq:morrey-decay`: for `q > 5/2` and a
suitable weak solution whose gradient limsup at `z₀` is below `ε_*`, the three
scaling quantities decay like `r^{2/5}` on a neighbourhood of `z₀`.

The constants `κ`, `η`, `ε_*` and `Λ₀` of `conv:kappa` are built from `C₂₇`
alone, and `C₂₇` is absolute: the paper fixes it before the integrability
exponent `q` of the force.  The established assembly `morreyDecay_of_thetaDecay`
takes the one-step decay display with its two constants as a hypothesis, and
`thetaDecay_T_of_sws_absolute` supplies that display with `C₂₇` quantified
before `q`.  Combining the two gives the display in the paper's order of
quantifiers.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- **Morrey decay on a neighbourhood (`prop:morrey-decay`, `eq:morrey-decay`)**
with the leading constant `C₂₇` absolute: it is fixed before the force
exponent `q`, so that the scale ratio `κ`, the threshold `η` and the smallness
threshold `ε_*` of `conv:kappa` are absolute as well. -/
theorem morreyDecay_of_sws_absolute :
    ∃ C₂₇ : ℝ, 0 < C₂₇ ∧ ∀ q : ℝ, 5 / 2 < q →
      ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
        {f : ParabolicPoint → Vec3} {z₀ : ParabolicPoint},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f → z₀ ∈ spaceTimeSet Ω I →
        Filter.limsup (fun r : ℝ => (ENNReal.ofReal r)⁻¹ *
            ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r, ENNReal.ofReal (spatialGradientSq u Du w))
          (𝓝[>] (0 : ℝ)) < ENNReal.ofReal ((iterationEpsilonStar C₂₇) ^ (2 : ℕ)) →
        ∃ r₂ M : ℝ, 0 < r₂ ∧ 1 ≤ M ∧ Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I ∧
          ∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
            max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ) := by
  obtain ⟨C₂₇, hC₂₇, hforce⟩ := thetaDecay_T_of_sws_absolute
  refine ⟨C₂₇, hC₂₇, ?_⟩
  intro q hq Ω I u Du p f z₀ hsol hz₀ hlim
  obtain ⟨C₂₈, hC₂₈, hdecay⟩ := hforce q
  exact morreyDecay_of_thetaDecay hsol hq hz₀ hC₂₇ hC₂₈
    (fun hρ hsub => hdecay Ω I u Du p f hsol hρ hsub) hlim

end CKN
