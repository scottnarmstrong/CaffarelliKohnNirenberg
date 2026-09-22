-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- The squared spatial-gradient density used by paper label `def:sws`. -/
def spatialGradientSq (_u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) : ℝ :=
  ∑ i, ∑ j, (Du z i j) ^ (2 : ℕ)

end CKN
