-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.CZDecomposition
import CKN.Foundation.Sobolev.W1p.Basic
import CKN.Statements.LocalLp
import CKN.Setting.DivergenceFreeSlice

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN.Foundation.Euclidean

/-- The dyadic high-average predicate has a concrete constant-data instance. -/
theorem dyadicHigh_satisfiable :
    ∃ (F : Vec3 → ℝ) (height : ℝ) (Q : DyadicIndex),
      dyadicHigh F height Q := by
  refine ⟨fun _ => 0, -1, ⟨0, fun _ => 0⟩, ?_⟩
  norm_num [dyadicHigh, dyadicAbsAverage, dyadicAverage]

end CKN.Foundation.Euclidean

namespace CKN

/-- The weak divergence-free condition has the identically zero slice as a
concrete instance. -/
theorem SliceDivergenceFree_satisfiable :
    ∃ (Ω : Set Vec3) (u : ParabolicPoint → Vec3) (s : ℝ),
      SliceDivergenceFree Ω u s := by
  refine ⟨Set.univ, fun _ => 0, 0, ?_⟩
  intro ψ hψ hψc hψΩ
  simp

/-- Coordinatewise gradient membership is inhabited by the zero field. -/
theorem GradMemLpOn_satisfiable :
    ∃ (U : Set Vec3) (p : ℝ≥0∞) (Du : Vec3 → Vec3),
      GradMemLpOn U p Du := by
  refine ⟨Set.univ, 2, fun _ => 0, ?_⟩
  intro i
  exact MemLp.zero

/-- Local scalar Lebesgue membership is inhabited by zero data. -/
theorem localLp_satisfiable :
    ∃ (E : Set ParabolicPoint) (p : ℝ) (g : ParabolicPoint → ℝ),
      localLp E p g := by
  refine ⟨Set.univ, 2, fun _ => 0, ?_⟩
  exact MemLp.zero

end CKN
