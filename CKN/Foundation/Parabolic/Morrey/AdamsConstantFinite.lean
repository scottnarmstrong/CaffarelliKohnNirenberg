-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Adams
import CKN.Foundation.Parabolic.Morrey.Tail
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace CKN.Foundation.Parabolic.Morrey

/-- The geometric constant in the local Hedberg estimate is finite when β > 0. -/
theorem parabolicHedbergNearConstant_ne_top {β : ℝ} (hβ : 0 < β) :
    parabolicHedbergNearConstant β ≠ ∞ := by
  unfold parabolicHedbergNearConstant
  have hvol : volume (parabolicCylinder (0 : Vec3) 0 1) < ∞ :=
    Integration.volume_parabolicCylinder_lt_top
  have hp : ENNReal.ofReal ((2 : ℝ) ^ (5 : ℕ)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hp5 : ENNReal.ofReal ((2 : ℝ) ^ (5 : ℕ)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hpre : (ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) ≠ ∞ :=
    ENNReal.mul_ne_top hp (ENNReal.mul_ne_top hp5 hvol.ne)
  refine ENNReal.mul_ne_top hpre ?_
  · -- the tsum part is finite
    have hr_lt_one : ENNReal.ofReal ((2 : ℝ) ^ (-β)) < 1 := by
      refine (ENNReal.ofReal_lt_one.mpr ?_)
      have : (2 : ℝ) ^ (-β) < 1 := by
        refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) ?_
        linarith only [hβ]
      exact this
    have hsum : ∑' n : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) =
        (ENNReal.ofReal ((2 : ℝ) ^ (-β))) * ((1 - ENNReal.ofReal ((2 : ℝ) ^ (-β)))⁻¹) := by
      calc
        ∑' n : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)
            = ∑' n : ℕ, (ENNReal.ofReal ((2 : ℝ) ^ (-β))) ^ (n + 1) := by
          refine tsum_congr (fun n => ?_)
          have hpos : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
          calc
            ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)
                = ENNReal.ofReal (((2 : ℝ) ^ (-((n : ℝ) + 1))) ^ β) := by
              simp [Int.cast_negSucc]
            _ = ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) + 1) * β)) := by
              rw [Real.rpow_mul hpos]
            _ = ENNReal.ofReal ((2 : ℝ) ^ (-β * ((n : ℝ) + 1))) := by ring_nf
            _ = ENNReal.ofReal (((2 : ℝ) ^ (-β)) ^ ((n : ℝ) + 1)) := by
              rw [Real.rpow_mul hpos (-β) ((n : ℝ) + 1)]
            _ = ENNReal.ofReal (((2 : ℝ) ^ (-β)) ^ (n + 1 : ℕ)) := by
              rw [← Real.rpow_natCast ((2 : ℝ) ^ (-β)) (n + 1), Nat.cast_add, Nat.cast_one]
            _ = (ENNReal.ofReal ((2 : ℝ) ^ (-β))) ^ (n + 1) := by
              rw [ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _)]
        _ = (ENNReal.ofReal ((2 : ℝ) ^ (-β))) * ((1 - ENNReal.ofReal ((2 : ℝ) ^ (-β)))⁻¹) := by
          rw [ENNReal.tsum_geometric_add_one]
    have hsum_ne_top : ∑' n : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) ≠ ∞ := by
      rw [hsum]
      refine ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) ?_
      rw [ENNReal.inv_ne_top]
      exact (tsub_pos_of_lt hr_lt_one).ne'
    exact hsum_ne_top

/-- The dyadic constant used by the Morrey tail estimate is finite when β < 5 / q. -/
theorem parabolicTailKernelConstant_ne_top {β q : ℝ} (h : β < 5 / q) :
    parabolicTailKernelConstant β q ≠ ∞ := by
  unfold parabolicTailKernelConstant
  have ha : β - 5 / q < 0 := sub_neg.mpr h
  have hxpos : 0 < ENNReal.ofReal (2 : ℝ) := by
    refine ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hx0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := hxpos.ne'
  have hx_top : ENNReal.ofReal (2 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hx_one_lt : 1 < ENNReal.ofReal (2 : ℝ) := by
    rw [ENNReal.one_lt_ofReal]
    norm_num
  have hxa_lt_one : (ENNReal.ofReal (2 : ℝ)) ^ (β - 5 / q) < 1 :=
    ENNReal.rpow_lt_one_of_one_lt_of_neg hx_one_lt ha
  have hsum : ∑' n : ℕ, (ENNReal.ofReal (2 : ℝ)) ^
      ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q))) =
      ((1 - (ENNReal.ofReal (2 : ℝ)) ^ (β - 5 / q))⁻¹) *
      (ENNReal.ofReal (2 : ℝ)) ^ (2 * (5 * (1 - 1 / q))) := by
    calc
      ∑' n : ℕ, (ENNReal.ofReal (2 : ℝ)) ^
          ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q)))
          = ∑' n : ℕ,
              ((ENNReal.ofReal (2 : ℝ)) ^ ((n : ℝ) * (β - 5 / q))) *
              (ENNReal.ofReal (2 : ℝ)) ^ (2 * (5 * (1 - 1 / q))) := by
        refine tsum_congr (fun n => ?_)
        rw [ENNReal.rpow_add ((n : ℝ) * (β - 5 / q))
          (2 * (5 * (1 - 1 / q))) hx0 hx_top]
      _ = (∑' n : ℕ, (ENNReal.ofReal (2 : ℝ)) ^ ((n : ℝ) * (β - 5 / q))) *
          (ENNReal.ofReal (2 : ℝ)) ^ (2 * (5 * (1 - 1 / q))) := by
        rw [ENNReal.tsum_mul_right]
      _ = (∑' n : ℕ, ((ENNReal.ofReal (2 : ℝ)) ^ (β - 5 / q)) ^ (n : ℝ)) *
          (ENNReal.ofReal (2 : ℝ)) ^ (2 * (5 * (1 - 1 / q))) := by
        refine congrArg (· * _) (tsum_congr (fun n => ?_))
        rw [mul_comm (n : ℝ), ENNReal.rpow_mul (ENNReal.ofReal (2 : ℝ)) (β - 5 / q) (n : ℝ),
          ENNReal.rpow_natCast]
      _ = (∑' n : ℕ, ((ENNReal.ofReal (2 : ℝ)) ^ (β - 5 / q)) ^ n) *
          (ENNReal.ofReal (2 : ℝ)) ^ (2 * (5 * (1 - 1 / q))) := by
        refine congrArg (· * _) (tsum_congr (fun n => ?_))
        rw [ENNReal.rpow_natCast]
      _ = (1 - (ENNReal.ofReal (2 : ℝ)) ^ (β - 5 / q))⁻¹ *
          (ENNReal.ofReal (2 : ℝ)) ^ (2 * (5 * (1 - 1 / q))) := by
        rw [ENNReal.tsum_geometric]
  rw [hsum]
  refine ENNReal.mul_ne_top ?_ ?_
  · rw [ENNReal.inv_ne_top]
    exact (tsub_pos_of_lt hxa_lt_one).ne'
  · refine ENNReal.rpow_ne_top_of_ne_zero hx0 hx_top

/-- The sum of the local Hedberg constant and the tail kernel constant is finite when
β > 0, τ > 0, and β * τ < 5. -/
theorem parabolicHedbergNear_add_tail_ne_top {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ)
    (hβτ : β * τ < 5) :
    parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨parabolicHedbergNearConstant_ne_top hβ,
    parabolicTailKernelConstant_ne_top ((lt_div_iff₀ hτ).2 hβτ)⟩
