-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Ambient.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Coordinate basis for native vectors

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port retains the coordinate basis and reconstruction facts
needed to state coordinate weak derivatives, under the `CKN` namespace.
-/

namespace CKN

/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

@[simp]
theorem basisVec_apply {d : ℕ} (i j : Fin d) :
    basisVec i j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [basisVec]
  · simp [basisVec, h]

/-- Coordinate reconstruction in the native basis. -/
theorem sum_smul_basisVec {d : ℕ} (x : Vec d) :
    ∑ i : Fin d, x i • basisVec i = x := by
  funext j
  simp [basisVec_apply]

end CKN
