-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Main.TheoremCProvider
import CKN.Main.TheoremB

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Main

/-- The parabolic singular set of a suitable weak solution has zero one dimensional Hausdorff measure. -/
theorem caffarelliKohnNirenberg (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 := by
  exact CKN.caffarelliKohnNirenberg_provider_of_epsilonRegularityGradient
    CKN.Main.epsilonRegularityGradient q hq

end CKN.Main
