-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import CKN.Foundation.Sobolev.Ambient.Basis

open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Factor-wise spatial derivative on the ordinary product space described in docs/DESIGN_NOTES.md. -/
def spatialPartial (g : ParabolicPoint → ℝ) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  (fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) (basisVec i)

end CKN
