-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The pressure quantity δ from the manuscript, `eq:alpha-beta`. -/
noncomputable def delta (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  (r ^ (-2 : ℝ) * (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^ (1 / 3 : ℝ)

end CKN
