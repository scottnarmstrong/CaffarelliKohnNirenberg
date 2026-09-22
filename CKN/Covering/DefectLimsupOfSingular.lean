-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Covering.TheoremCDefectFaithful
import CKN.Core.Endgame.TheoremBUnconditional

/-!
# The defect inequality at a singular point

Paper label `eq:defect` (Step 1 of the proof of `thm:C`): with
`ε₁ = ε₁(q)` the constant of `thm:B` and `ε_* = ε₁² > 0`, every singular point
`z` of a suitable weak solution satisfies

`limsup_{r → 0⁺} r⁻¹ ∬_{Cyl_r(z)} |∇u|² ≥ ε_*`.

This is `thm:B` read in contrapositive form: if the normalised gradient
`limsup` were below `ε_*`, the point would be regular.  The contrapositive
step is `CKN.defect_of_singular_point`; the criterion it takes as a hypothesis
is supplied here by the unconditional gradient criterion
`CKN.Core.Endgame.epsilonRegularityGradient_unconditional`, so the display
below depends on no analytic input beyond suitability.

The normalising factor is written `(ENNReal.ofReal r)⁻¹`, the form used by
`thm:B`; on the punctured neighbourhood `𝓝[>] 0` that is the paper's `1/r`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Paper label `eq:defect`: at every singular point of a suitable weak
solution the normalised gradient `limsup` is at least `ε_* = ε₁²`, with `ε₁`
the threshold of `thm:B`.  The threshold is fixed before the solution, the
point and the radius. -/
theorem defect_limsup_of_singular (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
        (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ z ∈ SingularSet Ω I u,
          ENNReal.ofReal (ε₁ ^ (2 : ℕ)) ≤
            Filter.limsup (fun r : ℝ =>
                (ENNReal.ofReal r)⁻¹ *
                  ∫⁻ w in parabolicCylinder z.1 z.2 r,
                    ENNReal.ofReal (spatialGradientSq u Du w))
              (𝓝[>] (0 : ℝ)) := by
  obtain ⟨ε₁, hε₁, hB⟩ := CKN.Core.Endgame.epsilonRegularityGradient_unconditional q hq
  refine ⟨ε₁, hε₁, fun Ω I u Du p f hsol z hz => ?_⟩
  exact (defect_of_singular_point hsol hε₁ (hB Ω I u Du p f hsol) hz).1

end CKN
