-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.Decay
import CKN.Core.Step4.Bootstrap

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

theorem routeA_parameter_checks :
    2 * (25 / 11 : ℝ) < 5 ∧
    1 / (25 / 11 : ℝ) - 1 / 5 = 6 / 25 ∧
    (25 : ℝ)⁻¹ = (25 / 3 : ℝ)⁻¹ - (1 / 5 - (25 / 3 : ℝ)⁻¹) := by
  norm_num

end CKN.Core.Step4
