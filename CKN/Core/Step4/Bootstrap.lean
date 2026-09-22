-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PointwisePotential
import CKN.Core.ExponentDisplays
import CKN.Core.Parameters
import CKN.Foundation.Parabolic.Morrey.AdamsM4
import CKN.Foundation.Parabolic.Morrey.Minkowski

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Step4

/-- The three source memberships in the paper's Step 2 Morrey display.
The finite ball norms are the bounded norms appearing there. -/
structure Step2MorreySources
    {Q₂ : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} : Prop where
  velocity : CKN.morreyVecMem 3 (25 / 3 : ℝ) Q₂ u
  gradient : ∀ i : Fin 3,
    CKN.morreyVecMem 2 (25 / 8 : ℝ) Q₂ (fun z => Du z i)
  pressure : morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
      (Q₂.indicator p) < ∞


theorem adamsExponentGain {β τ : ℝ} (hτ : 0 < τ) :
    1 / (τ / (1 - β * τ / 5)) = 1 / τ - β / 5 := by
  exact adams_exponent_identity hτ




theorem oneRound :
    1 / (25 : ℝ) + 1 / (25 / 3 : ℝ) = 4 / 25 ∧
    1 / (25 / 8 : ℝ) + 1 / (25 : ℝ) = 9 / 25 ∧
    1 / (25 / 8 : ℝ) + 1 / (25 / 3 : ℝ) > 2 / 5 := by
  norm_num

theorem oneRoundGain :
    1 / (25 : ℝ) = 1 / (25 / 3 : ℝ) -
      (1 / 5 - 1 / (25 / 3 : ℝ)) := by
  norm_num

end CKN.Core.Step4
