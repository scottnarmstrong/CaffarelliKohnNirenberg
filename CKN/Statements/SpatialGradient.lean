-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.SpatialPartial

open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The classical coordinate gradient expression associated with `rem:gradient-datum`. -/
def spatialGradient (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (i : Fin 3) : Vec3 :=
  fun j => spatialPartial (fun w => u w i) j z

end CKN
