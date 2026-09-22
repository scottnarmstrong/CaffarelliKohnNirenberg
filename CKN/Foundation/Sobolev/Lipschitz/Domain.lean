-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.H1.Basic
import CKN.Foundation.Parabolic.Basic
import CKN.Foundation.Parabolic.Vec3Norm

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

namespace CKN

set_option autoImplicit false

/-!
This file gives the bounded Lipschitz-domain carrier used by the faithful
Sobolev input.  The chart in the predicate is a general continuous linear
equivalence.  On bounded open subsets of Euclidean space this is equivalent
to using a rigid motion, by the uniform-cone characterization of Lipschitz
domains; the general form keeps the carrier stable under the natural linear
coordinates used below.
-/

noncomputable def coordinatePermutation (k : Fin 3) : Vec3 ≃ₗ[ℝ] Vec3 :=
  { toFun := fun v i => v ((Equiv.swap k 2) i)
    invFun := fun v i => v ((Equiv.swap k 2).symm i)
    left_inv := by
      intro v
      funext i
      simp
    right_inv := by
      intro v
      funext i
      simp
    map_add' := by
      intro v w
      funext i
      simp
    map_smul' := by
      intro a v
      funext i
      simp }

noncomputable def negateLast : Vec3 ≃ₗ[ℝ] Vec3 :=
  { toFun := fun v i => if i = 2 then -v i else v i
    invFun := fun v i => if i = 2 then -v i else v i
    left_inv := by
      intro v
      funext i
      by_cases hi : i = 2 <;> simp [hi]
    right_inv := by
      intro v
      funext i
      by_cases hi : i = 2 <;> simp [hi]
    map_add' := by
      intro v w
      funext i
      by_cases hi : i = 2
      · subst i
        simp
        ring
      · simp [hi]
    map_smul' := by
      intro a v
      funext i
      by_cases hi : i = 2 <;> simp [hi] }

noncomputable def coordinateChartLinear (k : Fin 3) (negate : Bool) : Vec3 ≃ₗ[ℝ] Vec3 :=
  if negate then
    (coordinatePermutation k).trans negateLast
  else coordinatePermutation k

private theorem coordinateChartLinear_norm_le (k : Fin 3) (negate : Bool) (v : Vec3) :
    ‖coordinateChartLinear k negate v‖ ≤ ‖v‖ := by
  classical
  by_cases hs : negate
  · simp only [coordinateChartLinear, hs, ↓reduceIte, LinearEquiv.trans_apply]
    simp only [coordinatePermutation, negateLast]
    change ‖fun i => if i = 2 then -(v ((Equiv.swap k 2) i))
      else v ((Equiv.swap k 2) i)‖ ≤ ‖v‖
    rw [Pi.norm_def]
    have hnn : Finset.univ.sup (fun i : Fin 3 =>
        ‖if i = 2 then -(v ((Equiv.swap k 2) i)) else v ((Equiv.swap k 2) i)‖₊) ≤
        (⟨‖v‖, norm_nonneg v⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i hi
      by_cases hi2 : i = 2
      · subst hi2
        simp only [ite_true, Equiv.swap_apply_right, nnnorm_neg]
        exact_mod_cast norm_le_pi_norm v k
      · simp [hi2]
        exact_mod_cast norm_le_pi_norm v ((Equiv.swap k 2) i)
    exact_mod_cast hnn
  · simp only [coordinateChartLinear, hs]
    simp only [coordinatePermutation]
    change ‖fun i => v ((Equiv.swap k 2) i)‖ ≤ ‖v‖
    rw [Pi.norm_def]
    have hnn : Finset.univ.sup (fun i : Fin 3 =>
        ‖v ((Equiv.swap k 2) i)‖₊) ≤ (⟨‖v‖, norm_nonneg v⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i hi
      exact_mod_cast norm_le_pi_norm v ((Equiv.swap k 2) i)
    exact_mod_cast hnn

private theorem coordinateChartLinear_symm_norm_le (k : Fin 3) (negate : Bool) (v : Vec3) :
    ‖(coordinateChartLinear k negate).symm v‖ ≤ ‖v‖ := by
  classical
  by_cases hs : negate
  · simp only [coordinateChartLinear, hs, ↓reduceIte, LinearEquiv.trans_symm]
    simp [coordinatePermutation, negateLast]
    change ‖fun i => if (Equiv.swap k 2) i = 2 then
      -(v ((Equiv.swap k 2) i)) else v ((Equiv.swap k 2) i)‖ ≤ ‖v‖
    rw [Pi.norm_def]
    have hnn : Finset.univ.sup (fun i : Fin 3 =>
        ‖if (Equiv.swap k 2) i = 2 then -(v ((Equiv.swap k 2) i))
          else v ((Equiv.swap k 2) i)‖₊) ≤
        (⟨‖v‖, norm_nonneg v⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i hi
      by_cases hi2 : (Equiv.swap k 2) i = 2
      · simp [hi2]
        exact_mod_cast norm_le_pi_norm v 2
      · simp [hi2]
        exact_mod_cast norm_le_pi_norm v ((Equiv.swap k 2) i)
    exact_mod_cast hnn
  · simp only [coordinateChartLinear, hs]
    simp only [coordinatePermutation]
    change ‖fun i => v ((Equiv.swap k 2).symm i)‖ ≤ ‖v‖
    rw [Pi.norm_def]
    have hnn : Finset.univ.sup (fun i : Fin 3 =>
        ‖v ((Equiv.swap k 2).symm i)‖₊) ≤
        (⟨‖v‖, norm_nonneg v⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i hi
      exact_mod_cast norm_le_pi_norm v ((Equiv.swap k 2).symm i)
    exact_mod_cast hnn

noncomputable def coordinateChart (k : Fin 3) (negate : Bool) : Vec3 ≃L[ℝ] Vec3 :=
  (coordinateChartLinear k negate).toContinuousLinearEquivOfBounds 1 1 (by
    intro v
    simpa using coordinateChartLinear_norm_le k negate v) (by
    intro v
    simpa using coordinateChartLinear_symm_norm_le k negate v)

@[simp] theorem coordinateChart_apply (k : Fin 3) (negate : Bool) (v : Vec3) :
    coordinateChart k negate v = coordinateChartLinear k negate v :=
  rfl

theorem coordinateChart_norm_le (k : Fin 3) (negate : Bool) (v : Vec3) :
    ‖coordinateChart k negate v‖ ≤ ‖v‖ := by
  exact coordinateChartLinear_norm_le k negate v

/-- Bounded Lipschitz domains in the chart form used by the paper.

The continuous linear equivalence is the flexible formulation of a local
rigid-motion graph chart; for bounded open Euclidean sets the two formulations
are equivalent by the uniform-cone characterization. -/
def IsBoundedLipschitzDomain (U : Set Vec3) : Prop :=
  IsOpen U ∧ Bornology.IsBounded U ∧
    ∀ x ∈ frontier U,
      ∃ e : Vec3 ≃L[ℝ] Vec3, ∃ r : ℝ, 0 < r ∧
        ∃ g : (Fin 2 → ℝ) → ℝ, ∃ L : ℝ≥0, LipschitzWith L g ∧ g 0 = 0 ∧
          ∀ y ∈ Metric.ball x r,
            (y ∈ U ↔ g (fun j : Fin 2 => e (y - x) j.castSucc) < e (y - x) 2)

end CKN
