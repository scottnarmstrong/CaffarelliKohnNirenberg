-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Parameters

/-!
# The admissible range of the bootstrap exponent

Paper label `eq:bootstrap-cond`.  `prop:bootstrap` fixes `τ₀ = q` and then says
*"Let `τ > 5` be such that `1_{Q₂}u ∈ 𝓜^{3,τ}` and `1/τ₃ + 1/τ > 2/5`"*: the
display is a **hypothesis** on `τ`, not a conclusion, and it is not implied by
`τ > 5`.

Since `τ₃ = 25/8`, the condition `1/τ₃ + 1/τ > 2/5` reads `8/25 + 1/τ > 2/5`,
that is `1/τ > 2/25`, that is `τ < 25/2`.  So the displays `τ > 5` and
`eq:bootstrap-cond` together say exactly `5 < τ < 25/2`, and the condition fails
for every `τ ≥ 25/2`.  The instance actually used downstream, `τ = τ₂ = 25/3`, sits in that range;
the range is characterised by `bootstrap_condition_iff`, with the usable
direction supplied by `bootstrap_condition_of_mem_range`.

This file records the characterisation, so that a consumer of `prop:bootstrap`
can see which `τ` the proposition admits.
-/

open scoped Topology

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Paper label `eq:bootstrap-cond`: for a positive exponent `τ`, the bootstrap
condition `2/5 < 1/τ₃ + 1/τ` holds exactly when `τ < 25/2`. -/
theorem bootstrap_condition_iff (τ : ℝ) (hτ : 0 < τ) :
    2 / 5 < 1 / stepTau₃ + 1 / τ ↔ τ < 25 / 2 := by
  rw [stepTau₃]
  rw [show (1 : ℝ) / (25 / 8) = 8 / 25 by norm_num]
  constructor
  · intro h
    have h' : (2 : ℝ) / 25 < 1 / τ := by linarith only [h]
    rw [lt_div_iff₀ hτ] at h'
    linarith only [h']
  · intro h
    have h' : (2 : ℝ) / 25 * τ < 1 := by linarith only [h]
    rw [← lt_div_iff₀ hτ] at h'
    linarith only [h']

/-- Paper label `eq:bootstrap-cond`, the direction `prop:bootstrap` consumes:
every `τ` with `5 < τ < 25/2` satisfies the bootstrap condition. -/
theorem bootstrap_condition_of_mem_range {τ : ℝ} (h5 : 5 < τ) (hup : τ < 25 / 2) :
    2 / 5 < 1 / stepTau₃ + 1 / τ :=
  (bootstrap_condition_iff τ (by linarith only [h5])).mpr hup

/-- Paper label `eq:bootstrap-cond`: `τ > 5` alone does **not** imply the
bootstrap condition.  At `τ = 25/2` the two sides of the display are equal, so
the condition fails there, and a fortiori for every larger `τ`. -/
theorem not_bootstrap_condition_of_ge {τ : ℝ} (hup : 25 / 2 ≤ τ) :
    ¬ 2 / 5 < 1 / stepTau₃ + 1 / τ := by
  have hτ : (0 : ℝ) < τ := by linarith only [hup]
  intro h
  exact absurd ((bootstrap_condition_iff τ hτ).mp h) (not_lt.mpr hup)

end CKN
