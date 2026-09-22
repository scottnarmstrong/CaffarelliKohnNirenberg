-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.Exponents

/-! # Heat-potential exponents for an arbitrary Hölder exponent

The reciprocal formulas and strict ordering follow from the explicit
exponents `5 / (2 - γ)` and `5 / (1 - γ)` for every `0 < γ < 1`.
-/

set_option autoImplicit false
noncomputable section

namespace CKN.Core.HeatPotential

/-- The formulas and inequalities of `eq:q0q1` for every Hölder exponent
strictly between zero and one. -/
theorem heat_morrey_exponent_formulas {γ : ℝ} (hγpos : 0 < γ) (hγone : γ < 1) :
    let θ₀ : ℝ := 5 / (2 - γ)
    let θ₁ : ℝ := 5 / (1 - γ)
    1 / θ₀ = (2 - γ) / 5 ∧
    1 / θ₁ = (1 - γ) / 5 ∧
    5 / 2 < θ₀ ∧ 5 < θ₁ ∧ θ₀ < θ₁ := by
  dsimp only
  have hden₀ : 0 < 2 - γ := by linarith only [hγone]
  have hden₁ : 0 < 1 - γ := sub_pos.mpr hγone
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [one_div, inv_div]
  · simp only [one_div, inv_div]
  · apply (lt_div_iff₀ hden₀).mpr
    linarith only [hγpos]
  · apply (lt_div_iff₀ hden₁).mpr
    linarith only [hγpos]
  · apply (div_lt_div_iff₀ hden₀ hden₁).mpr
    linarith only

end CKN.Core.HeatPotential
