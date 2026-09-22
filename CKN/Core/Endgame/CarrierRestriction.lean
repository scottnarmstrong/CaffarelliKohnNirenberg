-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.OneSidedMeasurability
import CKN.Foundation.Parabolic.Morrey.Basic
import CKN.Statements.MorreyVecMem

/-! # Restriction of indicated Morrey data

Smaller carriers retain the same numerical Morrey bound. Joint measurability
on a spatial-time strip gives globally measurable past-cylinder indications.
-/

open Set MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- Restricting an indicated source cannot increase its Morrey norm. -/
theorem morreyNorm_indicator_mono_set {P τ : ℝ} (hP : 0 ≤ P)
    {S T : Set ParabolicPoint} (hST : S ⊆ T) (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (S.indicator f) ≤ morreyNorm P τ (T.indicator f) := by
  apply morreyNorm_mono hP
  intro z
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem (hST hz)]
  · rw [indicator_of_notMem hz, abs_zero]
    exact abs_nonneg _

/-- Componentwise ball-Morrey membership restricts to any smaller carrier. -/
theorem morreyVecMem_mono_carrier {P τ : ℝ} (hP : 0 ≤ P)
    {S T : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    (hST : S ⊆ T) (hu : morreyVecMem P τ T u) : morreyVecMem P τ S u := by
  intro i
  apply lt_of_le_of_lt _ (hu i)
  apply morreyBallNorm_mono hP
  intro z
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem (hST hz)]
  · rw [indicator_of_notMem hz, abs_zero]
    exact abs_nonneg _


end CKN.Core.Endgame
