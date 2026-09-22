-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.LocalLp

open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- Componentwise local vector `Lp` membership used by paper label `def:sws`. -/
def localVecLp (E : Set ParabolicPoint) (p : ℝ)
    (g : ParabolicPoint → Vec3) : Prop :=
  ∀ i : Fin 3, localLp E p (fun z => g z i)

end CKN
