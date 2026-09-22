-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.LpExtension

open scoped ENNReal
set_option autoImplicit false

namespace CKN.Foundation.Euclidean

/-- Transporting an `LpExtensionInput` along an equality of its constant does not
change its operator. -/
theorem lpExtensionInput_mp_T {p : ℝ≥0∞} {C D : ℝ}
    (hCD : C = D) (h : LpExtensionInput p C)
    (e : LpExtensionInput p C = LpExtensionInput p D) :
    (e.mp h).T = h.T := by
  subst hCD
  rfl

end CKN.Foundation.Euclidean
