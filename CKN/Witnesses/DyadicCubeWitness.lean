-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.CZDecomposition

open CKN.Foundation.Parabolic

/-!
# A concrete dyadic cube member

This file witnesses that `dyadicCubeMember` is inhabited by the origin in the
scale-zero cube with zero corner.
-/

set_option autoImplicit false

namespace CKN.Foundation.Euclidean

/-- The origin belongs to the scale-zero dyadic cube with zero corner. -/
theorem dyadicCubeMember_satisfiable :
    ∃ (D : Set DyadicIndex) (x : Vec3), dyadicCubeMember D x := by
  let Q : DyadicIndex := ⟨0, fun _ => 0⟩
  refine ⟨{Q}, 0, ⟨Q, by simp, ?_⟩⟩
  rw [dyadicCubeSet, mem_dyadicCube]
  intro i
  constructor <;> norm_num [Q, dyadicScale]

end CKN.Foundation.Euclidean
