-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import CKN.Core.Iteration.ThetaDecayAlgebra

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The "Pressure part" of the proof of `lem:theta-decay` of `paper/ckn.tex`: from the
pressure decay bound
`δ(r) ≤ C₁₄ κ^{-1/2} √α √β + C₁₄ κ^{1/3} δ + C₁₅ κ^{1/2} √λ`
one obtains, after squaring with the elementary inequality `(x+y+z)² ≤ 3(x²+y²+z²)`
and multiplying by `κ⁻⁴`, the inequality

`κ⁻⁴ δ(r)² ≤ 3 C₁₄² κ⁻⁵ β θ + 3 C₁₄² κ^{2/3} θ + 3 C₁₅² κ⁻³ λ`,

where `θ = α + β + κ⁻⁴δ²` and `κ > 0`. -/
theorem thetaDecay_pressure_part {κ C₁₄ C₁₅ α β δ lam δr : ℝ} (hκ : 0 < κ) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hlam : 0 ≤ lam) (hδr : 0 ≤ δr)
    (hB : δr ≤ C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β
        + C₁₄ * κ ^ (1 / 3 : ℝ) * δ + C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) :
    κ ^ (-4 : ℝ) * δr ^ 2 ≤
      3 * C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * thetaValue κ α β δ
        + 3 * C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * thetaValue κ α β δ
        + 3 * C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam := by
  simp only [thetaValue]
  set T : ℝ := α + β + κ ^ (-4 : ℝ) * δ ^ 2 with hT
  have hκ4 : 0 ≤ κ ^ (-4 : ℝ) := Real.rpow_nonneg hκ.le _
  have hT_nonneg : 0 ≤ T := by
    rw [hT]
    nlinarith only [hα, hβ, mul_nonneg hκ4 (sq_nonneg δ)]
  have hαT : α ≤ T := by
    rw [hT]
    nlinarith only [hβ, mul_nonneg hκ4 (sq_nonneg δ)]
  have hκδ2T : κ ^ (-4 : ℝ) * δ ^ 2 ≤ T := by
    rw [hT]
    nlinarith only [hα, hβ]
  -- the three squares, each reduced with `← Real.rpow_add`
  have hhalf : (κ ^ (-1 / 2 : ℝ)) ^ 2 = κ ^ (-1 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hκ]
    norm_num
  have hthird : (κ ^ (1 / 3 : ℝ)) ^ 2 = κ ^ (2 / 3 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hκ]
    norm_num
  have hhalf' : (κ ^ (1 / 2 : ℝ)) ^ 2 = κ := by
    rw [pow_two, ← Real.rpow_add hκ]
    norm_num
  have hXsq : (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2
      = C₁₄ ^ 2 * κ ^ (-1 : ℝ) * α * β := by
    rw [mul_pow, mul_pow, mul_pow, hhalf, Real.sq_sqrt hα, Real.sq_sqrt hβ]
  have hYsq : (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2 = C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * δ ^ 2 := by
    rw [mul_pow, mul_pow, hthird]
  have hZsq : (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2 = C₁₅ ^ 2 * κ * lam := by
    rw [mul_pow, mul_pow, hhalf', Real.sq_sqrt hlam]
  have h45 : κ ^ (-4 : ℝ) * κ ^ (-1 : ℝ) = κ ^ (-5 : ℝ) := by
    rw [← Real.rpow_add hκ]
    norm_num
  have h43 : κ ^ (-4 : ℝ) * κ = κ ^ (-3 : ℝ) := by
    calc κ ^ (-4 : ℝ) * κ = κ ^ (-4 : ℝ) * κ ^ (1 : ℝ) := by rw [Real.rpow_one κ]
      _ = κ ^ ((-4 : ℝ) + 1) := (Real.rpow_add hκ _ _).symm
      _ = κ ^ (-3 : ℝ) := by norm_num
  have hX2 : κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2 ≤
      C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T := by
    rw [hXsq]
    calc κ ^ (-4 : ℝ) * (C₁₄ ^ 2 * κ ^ (-1 : ℝ) * α * β)
        = C₁₄ ^ 2 * (κ ^ (-4 : ℝ) * κ ^ (-1 : ℝ)) * (α * β) := by ring
      _ = C₁₄ ^ 2 * κ ^ (-5 : ℝ) * (α * β) := by rw [h45]
      _ ≤ C₁₄ ^ 2 * κ ^ (-5 : ℝ) * (T * β) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαT hβ)
            (mul_nonneg (sq_nonneg C₁₄) (Real.rpow_nonneg hκ.le _))
      _ = C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T := by ring
  have hY2 : κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2 ≤
      C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T := by
    rw [hYsq]
    calc κ ^ (-4 : ℝ) * (C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * δ ^ 2)
        = C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * (κ ^ (-4 : ℝ) * δ ^ 2) := by ring
      _ ≤ C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T :=
          mul_le_mul_of_nonneg_left hκδ2T
            (mul_nonneg (sq_nonneg C₁₄) (Real.rpow_nonneg hκ.le _))
  have hZ2 : κ ^ (-4 : ℝ) * (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2 ≤
      C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam := by
    rw [hZsq]
    have hcongr : κ ^ (-4 : ℝ) * (C₁₅ ^ 2 * κ * lam) = C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam := by
      rw [show κ ^ (-4 : ℝ) * (C₁₅ ^ 2 * κ * lam) = C₁₅ ^ 2 * (κ ^ (-4 : ℝ) * κ) * lam
            from by ring, h43]
    rw [hcongr]
  have hδr2 : δr ^ 2 ≤ 3 * ((C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2
      + (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2
      + (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2) := by
    have h1 : δr ^ 2 ≤ (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β
        + C₁₄ * κ ^ (1 / 3 : ℝ) * δ + C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2 :=
      pow_le_pow_left₀ hδr hB 2
    have h2 : (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β
        + C₁₄ * κ ^ (1 / 3 : ℝ) * δ + C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2
        ≤ 3 * ((C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2
          + (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2
          + (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2) := by
      nlinarith only [
        sq_nonneg (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β
          - C₁₄ * κ ^ (1 / 3 : ℝ) * δ),
        sq_nonneg (C₁₄ * κ ^ (1 / 3 : ℝ) * δ
          - C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam),
        sq_nonneg (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam
          - C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β)]
    linarith only [h1, h2]
  calc κ ^ (-4 : ℝ) * δr ^ 2
      ≤ κ ^ (-4 : ℝ) * (3 * ((C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2
          + (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2
          + (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2)) :=
        mul_le_mul_of_nonneg_left hδr2 (Real.rpow_nonneg hκ.le _)
    _ = 3 * (κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (-1 / 2 : ℝ) * Real.sqrt α * Real.sqrt β) ^ 2
          + κ ^ (-4 : ℝ) * (C₁₄ * κ ^ (1 / 3 : ℝ) * δ) ^ 2
          + κ ^ (-4 : ℝ) * (C₁₅ * κ ^ (1 / 2 : ℝ) * Real.sqrt lam) ^ 2) := by ring
    _ ≤ 3 * (C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T + C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T
          + C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
        exact add_le_add (add_le_add hX2 hY2) hZ2
    _ = 3 * C₁₄ ^ 2 * κ ^ (-5 : ℝ) * β * T + 3 * C₁₄ ^ 2 * κ ^ (2 / 3 : ℝ) * T
          + 3 * C₁₅ ^ 2 * κ ^ (-3 : ℝ) * lam := by ring

end CKN
