-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- Vector-valued parabolic Hölder control from paper label `def:holder`. -/
def ParabolicHolderVecOn (U : Set ParabolicPoint) (g : ParabolicPoint → Vec3)
    (γ : ℝ) : Prop :=
  ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧
    (∀ z ∈ U, vec3EuclideanNorm (g z) ≤ B) ∧
    (∀ z ∈ U, ∀ w ∈ U,
      vec3EuclideanNorm (g z - g w) ≤ K * parabolicDist z w ^ γ)

end CKN
