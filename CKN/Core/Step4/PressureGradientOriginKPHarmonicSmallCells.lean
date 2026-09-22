-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Core.Step4.PressureGradientOriginKPHarmonicCells
import CKN.Core.Step4.PressureGradientGluedMarginGeometry
import CKN.Core.Step4.WeakGradientGluingTRieszSourceQuantitative
open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4
/-- The source collar is never smaller than one quarter, while its half-ball
contains the tested small cell. -/
def originHarmonicCellRadius (r : ℝ) : ℝ := max (1/4) (2*r)

end CKN.Core.Step4
