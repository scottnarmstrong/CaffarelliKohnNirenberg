-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.Alpha
import CKN.Statements.Beta
import CKN.Statements.Delta

set_option autoImplicit false

open CKN.Foundation.Parabolic

namespace CKN

/-- The iteration quantity θ from the manuscript, `eq:theta`. -/
noncomputable def theta (κ : ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  alpha u z r + beta u Du z r + κ ^ (-4 : ℝ) * (delta p z r) ^ (2 : ℕ)

end CKN
