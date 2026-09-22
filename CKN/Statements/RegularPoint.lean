-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.SpaceTimeSet
import CKN.Statements.ParabolicHolderVecOn
import CKN.Foundation.Parabolic.Basic

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The regular-point predicate from paper label `def:regular`, with the Hölder representative convention of docs/DESIGN_NOTES.md. -/
def IsRegularPoint (Ω : Set Vec3) (I : Set ℝ)
    (u : ParabolicPoint → Vec3) (z₀ : ParabolicPoint) : Prop :=
  z₀ ∈ spaceTimeSet Ω I ∧
    ∃ N : Set ParabolicPoint, IsOpen N ∧ z₀ ∈ N ∧
      N ⊆ spaceTimeSet Ω I ∧ ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict N] u ∧ ParabolicHolderVecOn N w γ

end CKN
