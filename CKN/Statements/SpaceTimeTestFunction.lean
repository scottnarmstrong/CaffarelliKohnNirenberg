-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.SpaceTimeSet
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The smooth compactly supported test-function class on `Ω × I` from paper label `def:sws`; its ordinary product space follows the test-function convention of docs/DESIGN_NOTES.md. -/
def spaceTimeTestFunction {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Ω : Set Vec3) (I : Set ℝ) : Set (Vec3 × ℝ → V) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ spaceTimeSet Ω I}

end CKN
