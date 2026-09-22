-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import Mathlib.Analysis.Normed.Group.Real

/-!
# Ambient coordinate carriers

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port keeps only the coordinate carrier needed by the
weak-derivative API and uses the `CKN` namespace.
-/

namespace CKN

/-- The native coordinate model of a finite-dimensional real vector space. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

end CKN
