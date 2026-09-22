-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- Local scalar `Lp` membership used by paper label `def:sws`. -/
def localLp (E : Set ParabolicPoint) (p : ℝ) (g : ParabolicPoint → ℝ) : Prop :=
  MeasureTheory.MemLp g (ENNReal.ofReal p) (volume.restrict E)

end CKN
