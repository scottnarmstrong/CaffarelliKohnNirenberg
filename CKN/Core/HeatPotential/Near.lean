-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.Exponents
import CKN.Core.HeatPotential.Morrey
import CKN.Foundation.Heat.IntegralBounds
import CKN.Foundation.Parabolic.Morrey.AdamsBridge

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

/-!
The source block used for the local part of a heat potential.  The radius is
written with the gauge `parabolicRho₂`, whose time component is symmetric;
this is the geometry needed for a genuine parabolic metric ball.
-/
def heatPotentialNearSet (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  {v | parabolicRho₂ z v < (64 : ℝ) * r}




end CKN.Core.HeatPotential
