-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.PkBoundsUnconditionalConstants
import CKN.Foundation.Harmonic.InteriorEstimatesBasic

open scoped ENNReal NNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN

/-! Unconditional nonnegativity of the pressure constants. -/

/-- The unconditional nonnegativity of `pressureP234Constant`. -/
theorem pressureP234Constant_nonneg' : 0 ≤ pressureP234Constant := by
  have hC₁ := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hC₂ := CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  unfold pressureP234Constant
  positivity

/-- The unconditional nonnegativity of `pressureP56Constant`. -/
theorem pressureP56Constant_nonneg' : 0 ≤ pressureP56Constant := by
  have hC₁ := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hC₂ := CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  unfold pressureP56Constant
  positivity

/-- The unconditional nonnegativity of `pressureP13Constant q` for any real `q`. -/
theorem pressureP13Constant_nonneg' (q : ℝ) : 0 ≤ pressureP13Constant q := by
  have hC₁ := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hC₂ := CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  unfold pressureP13Constant
  positivity

/-- The unconditional nonnegativity of `pressureP12Constant`. -/
theorem pressureP12Constant_nonneg : 0 ≤ pressureP12Constant := by
  have h := pressureP234Constant_nonneg'
  unfold pressureP12Constant
  exact h.trans (le_max_left (a := pressureP234Constant) (b := pressureP56Constant))

end CKN
