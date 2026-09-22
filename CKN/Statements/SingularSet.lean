-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.RegularPoint

open Set

set_option autoImplicit false

open CKN.Foundation.Parabolic

namespace CKN

/-- The singular set from paper label `def:regular`. -/
def SingularSet (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3) :
    Set ParabolicPoint :=
  {z | z ∈ spaceTimeSet Ω I ∧ ¬ IsRegularPoint Ω I u z}

end CKN
