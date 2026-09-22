-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Hedberg
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The small exponent displays of the pressure and potential sections

This file records the elementary range statements and one algebraic identity
from `paper/ckn.tex`:

* `eq:kappa` — the ratio `r / ρ` of a small cylinder radius to the pressure
  cylinder radius lies in `(0, 1/2]` when `0 < r ≤ ρ/2`;
* `eq:hedberg-lambda` — under Hedberg's hypotheses `a > 0`, `τ > 0` and
  `a τ < 5` the exponent `ϰ = a τ / 5` (the Morrey exponent
  `hedbergMorreyExponent`) lies in `(0, 1)`, so that `λ = 1 - ϰ` is positive;
* `eq:adams-exponents` — the reciprocal identity
  `1 / (τ / λ) = 1 / τ - a / 5` with `λ = 1 - a τ / 5`.
-/

open scoped ENNReal NNReal Topology

open MeasureTheory Set Metric

open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false

noncomputable section

namespace CKN.Core

/-- Equation `eq:kappa`: for a pressure cylinder radius `ρ > 0` and a small
radius `0 < r ≤ ρ/2`, the ratio `r / ρ` lies in `(0, 1/2]`. -/
theorem kappa_mem_Ioc {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ / 2) (hρ : 0 < ρ) :
    0 < r / ρ ∧ r / ρ ≤ 1 / 2 := by
  constructor
  · exact div_pos hr hρ
  · calc
      r / ρ ≤ (ρ / 2) / ρ := div_le_div_of_nonneg_right hrρ hρ.le
      _ = 1 / 2 := by field_simp

/-- Equation `eq:hedberg-lambda`: under the Hedberg hypotheses on the exponent
`β = a` and the integrability exponent `q = τ` (both positive with
`β * q < 5`), the Morrey exponent `ϰ = β q / 5` lies in `(0, 1)`. -/
theorem hedbergMorreyExponent_mem_Ioo {β q : ℝ} (hβ : 0 < β) (hq : 0 < q)
    (hβq : β * q < 5) :
    0 < hedbergMorreyExponent β q ∧ hedbergMorreyExponent β q < 1 := by
  unfold hedbergMorreyExponent
  constructor
  · positivity
  · rw [div_lt_one (by norm_num : (0 : ℝ) < 5)]
    exact hβq


/-- Equation `eq:adams-exponents`: for `q > 0` and `λ = 1 - β q / 5 ≠ 0` the
reciprocal of `q / λ` is `1 / q - β / 5`. -/
theorem adams_exponent_identity {β q : ℝ} (hq : 0 < q) :
    1 / (q / (1 - β * q / 5)) = 1 / q - β / 5 := by
  rw [one_div_div]
  field_simp

end CKN.Core
