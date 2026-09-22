-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.SpatialPartial

open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The iterated spatial derivative used in the local energy inequality. -/
def spatialSecondPartial (g : ParabolicPoint → ℝ) (i j : Fin 3)
    (z : ParabolicPoint) : ℝ :=
  spatialPartial (fun w => spatialPartial g i w) j z

end CKN
