-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step2.ThetaDecayAbsoluteConstant
import CKN.Core.Step2.MorreyDecayAux

/-!
# The scale iteration with absolute `κ` and `η`

Paper label `prop:iteration` (display `eq:iteration-concl`): with `κ`, `η` and
`ε` the **absolute** parameters of `conv:kappa` and `Λ₀ = Λ₀(q)`, a suitable
weak solution whose combined quantity and force quantity are small at one
scale `r₅` satisfies `θ(z, κⁿ r₅) ≤ η κ^{nε}` for every `n`, and consequently

`max {α(z,r), β(z,r), δ(z,r)²} ≤ θ(z,r) ≤ M r^ε`, `M = κ^{-4/3-ε} η r₅^{-ε}`,

for every `0 < r ≤ r₅`.

`CKN.iteration_of_thetaDecay` carries the whole of `lem:theta-decay` as a
hypothesis.  The theorem below removes the dependence of `C₂₇` on the force
exponent: the decay input is discharged from the solution by
`CKN.thetaDecay_T_of_sws_absolute`, whose `C₂₇` is absolute, and the first
conclusion of `eq:iteration-concl` is supplied by
`CKN.MorreyDecayAux.max_components_le_theta`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step3

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Paper label `prop:iteration`, both conclusions, with `κ = iterationKappa C₂₇`
and `η = iterationEta C₂₇` built from an absolute `C₂₇` (so independent of the
force exponent `q`) and `Λ₀ = Λ₀(q)`. -/
theorem iteration_of_sws_absolute :
    ∃ C₂₇ : ℝ, 0 < C₂₇ ∧ ∀ q : ℝ, ∃ C₂₈ : ℝ, 0 < C₂₈ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
        {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {r₅ : ℝ}, 0 < r₅ →
          closure (parabolicCylinder z.1 z.2 r₅) ⊆ spaceTimeSet Ω I →
          theta (iterationKappa C₂₇) u Du p z r₅ ≤ iterationEta C₂₇ →
          lambda q f z r₅ ≤ iterationLambda₀ C₂₇ C₂₈ →
          (∀ n : ℕ, theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ ^ n * r₅) ≤
              iterationEta C₂₇ * iterationKappa C₂₇ ^ ((n : ℝ) * iterationEpsilon)) ∧
          ∀ r : ℝ, 0 < r → r ≤ r₅ →
            max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
                theta (iterationKappa C₂₇) u Du p z r ∧
              theta (iterationKappa C₂₇) u Du p z r ≤
                iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) * iterationEta C₂₇ *
                  r₅ ^ (-iterationEpsilon) * r ^ iterationEpsilon := by
  obtain ⟨C₂₇, hC₂₇, hq⟩ := thetaDecay_T_of_sws_absolute
  refine ⟨C₂₇, hC₂₇, fun q => ?_⟩
  obtain ⟨C₂₈, hC₂₈, hdecay⟩ := hq q
  refine ⟨C₂₈, hC₂₈, ?_⟩
  intro Ω I u Du p f hsol z r₅ hr₅ hz hθ₅ hLam₅
  have hit := iteration_of_thetaDecay hsol hC₂₇ hC₂₈ hr₅ hz hθ₅ hLam₅
    (fun {w} {ρ} hρ hw => hdecay Ω I u Du p f hsol hρ hw)
  refine ⟨hit.1, fun r hr hrr => ⟨?_, hit.2 r hr hrr⟩⟩
  exact MorreyDecayAux.max_components_le_theta (iterationKappa_pos hC₂₇)
    ((iterationKappa_le_half C₂₇).trans (by norm_num))
    (alpha_nonneg u z hr.le) (beta_nonneg u Du z hr.le)

end CKN
