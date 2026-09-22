-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Examples.ShearCounterexample

/-! # A concrete exponent-two suitable shear witness. -/

set_option autoImplicit false
noncomputable section

open CKN.Foundation.Parabolic Set

namespace CKN

theorem IsSuitableWeakSolutionAtExponent_satisfiable :
    IsSuitableWeakSolutionAtExponent (vec3Ball 0 1) (Ioo (-1) 1) 2
      shearCounterexampleVelocity shearCounterexampleDu
      shearCounterexamplePressure shearCounterexampleForce :=
  shearCounterexample_suitableAtExponent

end CKN
