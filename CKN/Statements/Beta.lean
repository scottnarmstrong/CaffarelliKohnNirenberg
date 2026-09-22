-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.SpatialGradientSq
import CKN.Foundation.Parabolic.Basic

open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The gradient quantity β from the manuscript, `eq:alpha-beta`; `Du` is the explicit gradient datum. -/
noncomputable def beta (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  (r⁻¹ * (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (spatialGradientSq u Du w)).toReal) ^ (1 / 2 : ℝ)

end CKN
