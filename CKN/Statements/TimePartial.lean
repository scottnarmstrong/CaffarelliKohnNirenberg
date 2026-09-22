-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add

open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Factor-wise time derivative on the ordinary product space described in docs/DESIGN_NOTES.md. -/
def timePartial (g : ParabolicPoint → ℝ) (z : ParabolicPoint) : ℝ :=
  (fderiv ℝ (fun s : ℝ => g (z.1, s)) z.2) 1

end CKN
