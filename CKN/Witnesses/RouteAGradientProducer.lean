-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.RouteAAssembly
import CKN.Core.Step4.BootstrapFaithfulPotential

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-- The uniform pressure-gradient route specializes to the first-round exponent. -/
theorem routeA_gradient_producer_satisfiable :
    routeA_gradient_producer := by
  intro q hq Ω I u Du p f hsol z₀ R hR hdom hu hDu
  obtain ⟨Dp, hAE, hweak, hN⟩ :=
    bootstrap_routeA_uniform q (25 / 3) hq (by norm_num) (by norm_num)
      hsol z₀ R hR hdom hu hDu
  refine ⟨Dp, hAE, hweak, ?_⟩
  simpa only [show ((1 / (25 / 3 : ℝ) + 8 / 25)⁻¹) = 25 / 11 by norm_num]
    using hN

end CKN.Core.Step4
