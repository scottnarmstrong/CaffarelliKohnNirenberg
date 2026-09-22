-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- A bounded vector-valued parabolic Hölder norm built from paper label `def:holder`. -/
def ParabolicHolderVecNormLE (U : Set ParabolicPoint) (g : ParabolicPoint → Vec3)
    (γ C : ℝ) : Prop :=
  ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ B + K ≤ C ∧
    (∀ z ∈ U, vec3EuclideanNorm (g z) ≤ B) ∧
    (∀ z ∈ U, ∀ w ∈ U,
      vec3EuclideanNorm (g z - g w) ≤ K * parabolicDist z w ^ γ)

end CKN
