-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.MorreyVecMem
import CKN.Foundation.Parabolic.Morrey.Neg

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Monotonicity of componentwise parabolic Morrey membership under subset restriction.
If `u` has finite Morrey norm on `S`, then it also has finite Morrey norm on any
subset `S' ⊆ S`. -/
theorem morreyVecMem_mono {P τ : ℝ} (hP : 0 ≤ P)
    {S S' : Set ParabolicPoint} (hS : S' ⊆ S)
    {u : ParabolicPoint → Vec3} (h : morreyVecMem P τ S u) :
    morreyVecMem P τ S' u := by
  intro i
  have h_bound : ∀ w, |S'.indicator (fun z => u z i) w| ≤ |S.indicator (fun z => u z i) w| := by
    intro w
    by_cases hw : w ∈ S'
    · have hwS : w ∈ S := hS hw
      simp [Set.indicator_of_mem hw, Set.indicator_of_mem hwS]
    · simp [Set.indicator_of_notMem hw, abs_nonneg]
  exact lt_of_le_of_lt (morreyBallNorm_mono hP h_bound) (h i)

end CKN
