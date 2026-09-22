-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.WeakDerivative
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Uniqueness of weak partial derivatives

Locally integrable weak partial derivatives of the same function on an open
set agree almost everywhere.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Locally integrable weak partial derivatives of the same function agree almost everywhere. -/
theorem hasWeakPartialDerivOn_unique_ae {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {f g h : Vec d → ℝ}
    (hgLoc : LocallyIntegrableOn g U volume) (hhLoc : LocallyIntegrableOn h U volume)
    (hg : HasWeakPartialDerivOn U i f g) (hh : HasWeakPartialDerivOn U i f h) :
    g =ᵐ[volume.restrict U] h :=
  HasWeakPartialDerivOn.ae_eq hU hgLoc hhLoc hg hh

end CKN
