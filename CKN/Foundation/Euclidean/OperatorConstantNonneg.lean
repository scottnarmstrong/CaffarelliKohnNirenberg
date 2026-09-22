-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.CZUnconditional
import CKN.Pressure.OscillationLin34

open Real

set_option autoImplicit false

namespace CKN.Foundation.Euclidean

/-- The gradient operator constant is nonnegative. -/
theorem czGradientOperatorConstant_nonneg : 0 ≤ czGradientOperatorConstant := by
  unfold czGradientOperatorConstant czGradientComponentConstant
  positivity

/-- The P1 operator constant is nonnegative. -/
theorem czP1OperatorConstant_nonneg : 0 ≤ czP1OperatorConstant := by
  unfold czP1OperatorConstant czP1Constant
  positivity

end CKN.Foundation.Euclidean

namespace CKN

/-- The Lin 3.4 force constant is nonnegative given a nonnegative parameter. -/
theorem lin34ForceConstant_nonneg {C₁₃ : ℝ} (hC : 0 ≤ C₁₃) : 0 ≤ lin34ForceConstant C₁₃ := by
  unfold lin34ForceConstant
  positivity

end CKN
