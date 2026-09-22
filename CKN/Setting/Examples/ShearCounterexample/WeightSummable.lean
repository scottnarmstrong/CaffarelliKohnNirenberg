-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Summability of the shear weights. -/
set_option autoImplicit false
noncomputable section

def shearWeight (n : ℕ) : ℝ := 1 / (n + 1 : ℝ) ^ (3 / 4 : ℝ)

theorem shearWeight_sq_summable : Summable (fun n : ℕ => shearWeight n ^ 2) := by
  have hp := (Real.summable_one_div_nat_add_rpow 1 (3 / 2 : ℝ)).2 (by norm_num)
  have heq : (fun n : ℕ => shearWeight n ^ 2) =
      fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ) := by
    funext n
    have hb : 0 ≤ (n : ℝ) + 1 := by positivity
    have hpow : ((n + 1 : ℝ) ^ (3 / 4 : ℝ)) ^ 2 =
        ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hb]
      congr 1
      norm_num
    rw [shearWeight, div_pow, one_pow, hpow, abs_of_nonneg hb]
  rw [heq]
  exact hp
