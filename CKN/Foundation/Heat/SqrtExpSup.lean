-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Bounds.Basic

set_option autoImplicit false

namespace CKN.Foundation.Heat

open Real

/-- The supremum of `√s * e^{-s}` over `s ≥ 0` is `(2e)^{-1/2}`. -/
theorem sqrt_mul_exp_neg_le (s : ℝ) :
    Real.sqrt s * Real.exp (-s) ≤ (Real.sqrt (2 * Real.exp 1))⁻¹ := by
  by_cases hs : s ≤ 0
  · -- s ≤ 0: left side is zero, right side is positive
    have hsqrt : Real.sqrt s = 0 := Real.sqrt_eq_zero_of_nonpos hs
    have hpos : 0 < (Real.sqrt (2 * Real.exp 1))⁻¹ := by
      have hpos' : 0 < Real.sqrt (2 * Real.exp 1) :=
        Real.sqrt_pos_of_pos (by positivity : 0 < 2 * Real.exp 1)
      positivity
    rw [hsqrt, zero_mul]
    exact hpos.le
  · -- 0 < s
    have hs_pos : 0 < s := lt_of_not_ge hs
    -- (1) key scalar inequality: s * exp(-(2*s)) ≤ (2 * exp 1)⁻¹
    have hkey : s * Real.exp (-(2 * s)) ≤ (2 * Real.exp 1)⁻¹ := by
      have hineq : 2 * s ≤ Real.exp (2 * s - 1) := by
        have := Real.add_one_le_exp (2 * s - 1)
        linarith only [this]
      have hexp_add : Real.exp (2 * s - 1) = Real.exp (2 * s) * Real.exp (-1) := by
        calc
          Real.exp (2 * s - 1) = Real.exp (2 * s + (-1)) := by ring_nf
          _ = Real.exp (2 * s) * Real.exp (-1) := Real.exp_add (2 * s) (-1)
      have hexp_neg_one : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
      have h_exp_one_pos : 0 < Real.exp 1 := Real.exp_pos _
      rw [hexp_add, hexp_neg_one] at hineq
      -- hineq: 2*s ≤ exp(2*s) * (exp 1)⁻¹
      have h_mul : 2 * s * Real.exp (-(2 * s)) * Real.exp 1 ≤ 1 := by
        calc
          2 * s * Real.exp (-(2 * s)) * Real.exp 1 ≤
              (Real.exp (2 * s) * (Real.exp 1)⁻¹) * Real.exp (-(2 * s)) * Real.exp 1 := by
            gcongr
          _ = Real.exp (2 * s) * Real.exp (-(2 * s)) := by
            field_simp [h_exp_one_pos.ne']
          _ = Real.exp (2 * s + (-(2 * s))) := by rw [Real.exp_add]
          _ = Real.exp 0 := by ring_nf
          _ = 1 := Real.exp_zero
      -- h_mul: 2*s * exp(-(2*s)) * exp(1) ≤ 1
      -- We want: s * exp(-(2*s)) ≤ (2 * exp(1))⁻¹
      -- Rewrite RHS as 1 / (2 * exp(1)) and use le_div_iff₀
      have hpos : 0 < 2 * Real.exp 1 := by positivity
      rw [← one_div]
      apply (le_div_iff₀ hpos).mpr
      calc
        s * Real.exp (-(2 * s)) * (2 * Real.exp 1) =
            2 * s * Real.exp (-(2 * s)) * Real.exp 1 := by ring_nf
        _ ≤ 1 := h_mul
    -- (2) identity: √s * exp(-s) = √(s * exp(-(2*s)))
    have h_exp_sq : (Real.exp (-s)) ^ 2 = Real.exp (-(2 * s)) := by
      calc
        (Real.exp (-s)) ^ 2 = Real.exp ((2 : ℕ) * (-s)) := by
          simpa using (Real.exp_nat_mul (-s) 2).symm
        _ = Real.exp (-(2 * s)) := by ring_nf
    have h_identity : Real.sqrt s * Real.exp (-s) = Real.sqrt (s * Real.exp (-(2 * s))) := by
      calc
        Real.sqrt s * Real.exp (-s) = Real.sqrt s * Real.sqrt ((Real.exp (-s)) ^ 2) := by
          rw [Real.sqrt_sq (Real.exp_pos _).le]
        _ = Real.sqrt (s * (Real.exp (-s)) ^ 2) := by
          rw [Real.sqrt_mul hs_pos.le]
        _ = Real.sqrt (s * Real.exp (-(2 * s))) := by rw [h_exp_sq]
    -- (3) combine
    calc
      Real.sqrt s * Real.exp (-s) = Real.sqrt (s * Real.exp (-(2 * s))) := h_identity
      _ ≤ Real.sqrt ((2 * Real.exp 1)⁻¹) := Real.sqrt_le_sqrt hkey
      _ = (Real.sqrt (2 * Real.exp 1))⁻¹ := by rw [Real.sqrt_inv]

end CKN.Foundation.Heat
