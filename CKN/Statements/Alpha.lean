-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Integration.Scaling

open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The velocity energy quantity α from the manuscript, `eq:alpha-beta`. -/
noncomputable def alpha (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  (r⁻¹ * (timeSliceEnergyEssSup z.1 z.2 r
      (fun w => vec3EuclideanNorm (u w))).toReal) ^ (1 / 2 : ℝ)

end CKN
