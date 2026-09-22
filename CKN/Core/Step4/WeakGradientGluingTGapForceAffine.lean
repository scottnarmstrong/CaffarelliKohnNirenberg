-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.WeakGradientGluingTGapForceIncrement

/-! # An absolute affine threshold for the force-potential increment -/

open MeasureTheory Set
open scoped ENNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- An explicit absolute threshold for the force-potential increment. -/
def gapForceIncrementThreshold : ℝ := 5 * gapForceIncrementCoefficient

end CKN.Core.Step4
