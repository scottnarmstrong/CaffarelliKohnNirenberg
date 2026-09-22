-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.CylinderCenteredGlobal
import CKN.Foundation.Heat.CylinderCenteredPartialLink
import CKN.Foundation.Parabolic.Vec3Norm

open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN.Foundation.Heat

/-! ## Positivity of the backward Gaussian test function

The centered backward Gaussian test function of `eq:psi-r` is strictly
positive at every parabolic point whose time coordinate lies below `t₀ + r²`.
-/

/-- The centered backward heat test function is strictly positive for every
parabolic point with time coordinate below `t₀ + r²`. -/
theorem centeredBackwardHeatTest_pos {x₀ : Vec3} {t₀ r : ℝ} (hr : 0 < r)
    {z : ParabolicPoint} (ht : z.2 < t₀ + r ^ 2) :
    0 < centeredBackwardHeatTest x₀ t₀ r z := by
  have hτ : 0 < r ^ 2 - (z.2 - t₀) := by
    linarith only [ht]
  unfold centeredBackwardHeatTest backwardHeatTestFunction
  exact mul_pos (pow_pos hr 2) (heatKernel_pos hτ)

end CKN.Foundation.Heat
