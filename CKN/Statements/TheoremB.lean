-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Main.TheoremB
import CKN.Main.TheoremBPaper
import CKN.Statements.SpaceTimeSet
import CKN.Statements.SuitableWeakSolutionIntegrable
import CKN.Statements.SuitableWeakSolution
import CKN.Statements.RegularPoint
import CKN.Statements.SpatialGradientSq

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Theorem B from paper label `thm:B`, with the gradient limsup taken in `ℝ≥0∞`. -/
theorem epsilonRegularityGradient (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        (hsol : IsSuitableWeakSolution Ω I q u Du p f) →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          IsRegularPoint Ω I u z₀ :=
by exact CKN.Main.epsilonRegularityGradientPaper q hq

end CKN
