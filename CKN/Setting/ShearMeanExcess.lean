-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Integration.Average
import CKN.Foundation.Sobolev.Ambient.Basis

/-!
# The spatial-mean excess of a shear flow vanishes

Paper label `rem:two-means` ("Why the two means are different"): on the shear
family `u(y,s) = a(s) e₁` the velocity excess built with the *spatial* mean
`⨍_{B_r(x)} u(·,s)` vanishes identically, while `u` need not be better than
`C^{1/3}` in time.  This is the second half of the remark, and it is the reason
the velocity in `eq:excess` is compared with a space-time mean.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

set_option autoImplicit false

noncomputable section

namespace CKN

/-- **`rem:two-means`, the shear family.**  For `u(y,s) = a(s) e₁` the excess
computed with the spatial mean at each time vanishes identically: the
integrand is the cube of the norm of `a(s) e₁ − ⨍_{B_r(x)} a(s) e₁ = 0`. -/
theorem spatialMeanExcess_shear_eq_zero (a : ℝ → ℝ) (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) :
    ∫ w in parabolicCylinder z.1 z.2 r,
      vec3EuclideanNorm (a w.2 • basisVec (0 : Fin 3) -
        ⨍ _y in vec3Ball z.1 r, a w.2 • basisVec (0 : Fin 3)) ^ 3 = 0 := by
  have hpos : volume (vec3Ball z.1 r) ≠ 0 := (volume_vec3Ball_pos hr).ne'
  have htop : volume (vec3Ball z.1 r) ≠ ∞ := volume_vec3Ball_lt_top.ne
  have hmean : ∀ w : ParabolicPoint,
      (⨍ _y in vec3Ball z.1 r, a w.2 • basisVec (0 : Fin 3)) =
        a w.2 • basisVec (0 : Fin 3) := fun w => setAverage_const hpos htop _
  have hzero : ∀ w : ParabolicPoint,
      vec3EuclideanNorm (a w.2 • basisVec (0 : Fin 3) -
        ⨍ _y in vec3Ball z.1 r, a w.2 • basisVec (0 : Fin 3)) ^ 3 = 0 := by
    intro w
    rw [hmean w, sub_self, vec3EuclideanNorm_zero]
    norm_num
  simp only [hzero]
  exact integral_zero _ _

end CKN
