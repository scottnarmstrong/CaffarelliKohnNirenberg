-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Basic

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- Negation leaves the parabolic Morrey seminorm invariant. -/
theorem morreyNorm_neg (p q : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (fun z => -f z) = morreyNorm p q f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

/-- Absolute value leaves the parabolic Morrey seminorm invariant. -/
theorem morreyNorm_abs (p q : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (fun z => |f z|) = morreyNorm p q f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_abs]

end CKN.Foundation.Parabolic.Morrey
