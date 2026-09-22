-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The velocity cubic quantity γ from the manuscript, `eq:alpha-beta`. -/
noncomputable def gamma (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  (r ^ (-2 : ℝ) * (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) ^ (1 / 3 : ℝ)

end CKN
