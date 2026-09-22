-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

open Set
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- Compactly interior spatial and time subdomains used by paper label `def:sws`. -/
def localBox (Ω : Set Vec3) (I : Set ℝ) (Ω' : Set Vec3) (J : Set ℝ) : Prop :=
  IsOpen Ω' ∧ IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω ∧
    OrdConnected J ∧ IsCompact (closure J) ∧ closure J ⊆ I

end CKN
