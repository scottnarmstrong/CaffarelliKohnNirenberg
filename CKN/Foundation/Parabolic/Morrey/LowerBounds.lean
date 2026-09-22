-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.MorreyVecMem

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- Every individual Morrey ball cell is dominated by the Morrey ball seminorm. -/
theorem morreyBallCell_le_morreyBallNorm (p q : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    morreyBallCell p q f z r ≤ morreyBallNorm p q f := by
  unfold morreyBallNorm
  exact le_iSup_of_le z (le_iSup_of_le ⟨r, hr⟩ le_rfl)

/-- If the Morrey ball seminorm is finite, every Morrey ball cell is finite. -/
theorem morreyBallCell_lt_top_of_morreyBallNorm_lt_top {p q : ℝ}
    {f : ParabolicPoint → ℝ} (h : morreyBallNorm p q f < ∞)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    morreyBallCell p q f z r < ∞ :=
  lt_of_le_of_lt (morreyBallCell_le_morreyBallNorm p q f z hr) h

end CKN.Foundation.Parabolic.Morrey
