-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

set_option autoImplicit false

open CKN.Foundation.Parabolic

namespace CKN

/-- The open space-time carrier `Ω × I` from paper label `def:sws`. -/
def spaceTimeSet (Ω : Set Vec3) (I : Set ℝ) : Set ParabolicPoint := Ω ×ˢ I

end CKN
