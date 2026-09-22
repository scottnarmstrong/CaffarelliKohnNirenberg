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

/-! ### Elementary real inequalities used in the energy estimate -/

/-- A product of two real powers of a positive base adds the exponents. -/
private lemma rpow_mul_of_add {κ : ℝ} (hκ : 0 < κ) {a b c : ℝ} (h : a + b = c) :
    κ ^ a * κ ^ b = κ ^ c := by
  rw [← Real.rpow_add hκ, h]

/-- `√(x+y) ≤ √x + √y` for `x, y ≥ 0`. -/
private lemma sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith only [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x,
      Real.sqrt_nonneg y, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  rwa [Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt x + Real.sqrt y)] at h

/-- `√T · √(√T) · √(√b) ≤ T` when `0 ≤ b ≤ T`; this is the bound
`b^{1/4}T^{1/4} ≤ T^{1/2}` used term by term in the paper's energy estimate. -/
private lemma sqrt_mul_sqrt_sqrt_le {T b : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T) :
    Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt b) ≤ T := by
  have hT : 0 ≤ T := le_trans hb hbT
  refine le_of_sq_le_sq ?_ hT
  have hsqrtTb : Real.sqrt (T * b) ≤ T := by
    refine le_of_sq_le_sq ?_ hT
    rw [Real.sq_sqrt (by positivity : 0 ≤ T * b)]
    nlinarith only [hbT, hT]
  calc (Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt b)) ^ 2
      = T * Real.sqrt T * Real.sqrt b := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hT, Real.sq_sqrt (Real.sqrt_nonneg T),
          Real.sq_sqrt (Real.sqrt_nonneg b)]
    _ = T * Real.sqrt (T * b) := by rw [Real.sqrt_mul hT]; ring
    _ ≤ T * T := mul_le_mul_of_nonneg_left hsqrtTb hT
    _ = T ^ 2 := by ring

/-- `√(√T) · √(√b) ≤ √T` when `b ≤ T`. -/
private lemma sqrt_sqrt_mul_sqrt_sqrt_le {T b : ℝ} (hbT : b ≤ T) :
    Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt b) ≤ Real.sqrt T := by
  calc Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt b)
      ≤ Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt T) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hbT))
          (Real.sqrt_nonneg _)
    _ = Real.sqrt T := by rw [Real.mul_self_sqrt (Real.sqrt_nonneg T)]

/-- The pressure bound `δ ≤ κ²√T` implied by `κ^{-4}δ² ≤ T`. -/
private lemma delta_le_kappa_sq_sqrt {κ δ T : ℝ} (hκ : 0 < κ)
    (h : κ ^ (-4 : ℝ) * δ ^ 2 ≤ T) : δ ≤ κ ^ (2 : ℝ) * Real.sqrt T := by
  have hκ4 : 0 < κ ^ (4 : ℝ) := Real.rpow_pos_of_pos hκ 4
  have hcancel : κ ^ (4 : ℝ) * κ ^ (-4 : ℝ) = 1 := by
    rw [rpow_mul_of_add hκ (by norm_num : (4 : ℝ) + -4 = 0), Real.rpow_zero]
  have hsq : δ ^ 2 ≤ κ ^ (4 : ℝ) * T := by
    have h' := mul_le_mul_of_nonneg_left h hκ4.le
    rwa [← mul_assoc, hcancel, one_mul] at h'
  have hT : 0 ≤ T := le_trans (by positivity : 0 ≤ κ ^ (-4 : ℝ) * δ ^ 2) h
  have hκsq : (κ ^ (2 : ℝ)) ^ 2 = κ ^ (4 : ℝ) := by
    rw [pow_two, rpow_mul_of_add hκ (by norm_num : (2 : ℝ) + 2 = 4)]
  have hrhs : (κ ^ (2 : ℝ) * Real.sqrt T) ^ 2 = κ ^ (4 : ℝ) * T := by
    rw [mul_pow, hκsq, Real.sq_sqrt hT]
  refine le_of_sq_le_sq ?_ (by positivity)
  rwa [hrhs]

/-! ### The energy part of the combination step -/

/-- **The energy part of `lem:theta-decay`.**  The "Energy part" display in the
proof of `lem:theta-decay` of `paper/ckn.tex`: the Caccioppoli inequality
`eq:caccioppoli` (constants `C₂₅`, `C₂₆`) together with the
Gagliardo–Nirenberg inequality `eq:gagliardo` (constant `C₉`) bound the
increments `αr + βr` at the smaller radius by the combined quantity
`θ = α + β + κ⁻⁴δ²`, keeping the sharp powers of the scale ratio `κ`:

  `α(r) + β(r) ≤ C₂₅(1 + 2C₉^{1/2})κθ + 2C₂₅C₉^{1/2}κ⁻¹β^{1/2}θ
                  + 2C₂₆C₉^{1/2}κ^{-1/2}θ^{1/2}λ^{1/2}`.

The hypotheses `hA` and `hC` are the paper's (A) and (C) at the radii `r = κρ`
(left-hand quantities `αr, βr`) and `ρ` (right-hand quantities `α, β, γ, δ,
λ`). -/
theorem thetaDecay_energy_part {κ C₉ C₂₅ C₂₆ α β γ δ lam αr βr : ℝ} (hκ : 0 < κ)
    (hC₉ : 0 ≤ C₉) (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : αr + βr ≤ C₂₅ * κ * α + C₂₅ * κ⁻¹ * Real.sqrt α * Real.sqrt β * Real.sqrt γ
        + C₂₅ * κ⁻¹ * δ * Real.sqrt γ + C₂₆ * κ ^ (-1 / 2 : ℝ) * Real.sqrt γ * Real.sqrt lam)
    (hC : γ ≤ C₉ * Real.sqrt α * Real.sqrt β + C₉ * α) :
    αr + βr ≤ C₂₅ * (1 + 2 * Real.sqrt C₉) * κ * thetaValue κ α β δ
      + 2 * C₂₅ * Real.sqrt C₉ * κ⁻¹ * Real.sqrt β * thetaValue κ α β δ
      + 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt (thetaValue κ α β δ)
          * Real.sqrt lam := by
  simp only [thetaValue]
  rw [show κ⁻¹ = κ ^ (-1 : ℝ) from (Real.rpow_neg_one κ).symm] at hA ⊢
  have hκδ2 : 0 ≤ κ ^ (-4 : ℝ) * δ ^ 2 := by positivity
  set T : ℝ := α + β + κ ^ (-4 : ℝ) * δ ^ 2 with hT
  have hT_nonneg : 0 ≤ T := by rw [hT]; linarith only [hα, hβ, hκδ2]
  have hαT : α ≤ T := by rw [hT]; linarith only [hβ, hκδ2]
  have hβT : β ≤ T := by rw [hT]; linarith only [hα, hκδ2]
  have hκδ2T : κ ^ (-4 : ℝ) * δ ^ 2 ≤ T := by rw [hT]; linarith only [hα, hβ]
  have hδT : δ ≤ κ ^ (2 : ℝ) * Real.sqrt T := delta_le_kappa_sq_sqrt hκ hκδ2T
  have hcore : Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) ≤ T :=
    sqrt_mul_sqrt_sqrt_le hβ hβT
  have hsqrtβsqrt : Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) ≤ Real.sqrt T :=
    sqrt_sqrt_mul_sqrt_sqrt_le hβT
  -- The square root of the Gagliardo–Nirenberg output.
  have hγsqrt : Real.sqrt γ ≤ Real.sqrt C₉ *
      (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) + Real.sqrt T) := by
    have hγ' : γ ≤ C₉ * (Real.sqrt T * Real.sqrt β + T) := by
      have h1 : C₉ * Real.sqrt α * Real.sqrt β ≤ C₉ * (Real.sqrt T * Real.sqrt β) := by
        have h : Real.sqrt α * Real.sqrt β ≤ Real.sqrt T * Real.sqrt β :=
          mul_le_mul (Real.sqrt_le_sqrt hαT) le_rfl (Real.sqrt_nonneg β)
            (Real.sqrt_nonneg T)
        calc C₉ * Real.sqrt α * Real.sqrt β = C₉ * (Real.sqrt α * Real.sqrt β) := by ring
          _ ≤ C₉ * (Real.sqrt T * Real.sqrt β) := mul_le_mul_of_nonneg_left h hC₉
      have h2 : C₉ * α ≤ C₉ * T := mul_le_mul_of_nonneg_left hαT hC₉
      calc γ ≤ C₉ * Real.sqrt α * Real.sqrt β + C₉ * α := hC
        _ ≤ C₉ * (Real.sqrt T * Real.sqrt β) + C₉ * T := add_le_add h1 h2
        _ = C₉ * (Real.sqrt T * Real.sqrt β + T) := by ring
    calc Real.sqrt γ ≤ Real.sqrt (C₉ * (Real.sqrt T * Real.sqrt β + T)) :=
          Real.sqrt_le_sqrt hγ'
      _ = Real.sqrt C₉ * Real.sqrt (Real.sqrt T * Real.sqrt β + T) := by
          rw [Real.sqrt_mul hC₉]
      _ ≤ Real.sqrt C₉ * (Real.sqrt (Real.sqrt T * Real.sqrt β) + Real.sqrt T) :=
          mul_le_mul_of_nonneg_left
            (sqrt_add_le' (mul_nonneg (Real.sqrt_nonneg T) (Real.sqrt_nonneg β))
              hT_nonneg)
            (Real.sqrt_nonneg C₉)
      _ = Real.sqrt C₉ *
            (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) + Real.sqrt T) := by
          rw [Real.sqrt_mul (Real.sqrt_nonneg T)]
  -- The four Caccioppoli terms, with the sharp powers of `κ`.
  have hT1 : C₂₅ * κ * α ≤ C₂₅ * κ * T :=
    mul_le_mul_of_nonneg_left hαT (mul_nonneg hC₂₅ hκ.le)
  have hT2 : C₂₅ * κ ^ (-1 : ℝ) * Real.sqrt α * Real.sqrt β * Real.sqrt γ ≤
      2 * C₂₅ * Real.sqrt C₉ * κ ^ (-1 : ℝ) * Real.sqrt β * T := by
    have hprod : Real.sqrt α * Real.sqrt β * Real.sqrt γ ≤
        2 * Real.sqrt C₉ * Real.sqrt β * T := by
      have h1 : Real.sqrt α * Real.sqrt β * Real.sqrt γ ≤ Real.sqrt C₉ *
          (Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) * Real.sqrt β
            + Real.sqrt T * Real.sqrt β * Real.sqrt T) := by
        calc Real.sqrt α * Real.sqrt β * Real.sqrt γ
            ≤ Real.sqrt T * Real.sqrt β *
                (Real.sqrt C₉ *
                  (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) + Real.sqrt T)) :=
              mul_le_mul
                (mul_le_mul (Real.sqrt_le_sqrt hαT) le_rfl (Real.sqrt_nonneg β)
                  (Real.sqrt_nonneg T))
                hγsqrt (Real.sqrt_nonneg γ)
                (mul_nonneg (Real.sqrt_nonneg T) (Real.sqrt_nonneg β))
          _ = Real.sqrt C₉ *
                (Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β)
                    * Real.sqrt β
                  + Real.sqrt T * Real.sqrt β * Real.sqrt T) := by ring
      have hb1 : Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β)
            * Real.sqrt β ≤ T * Real.sqrt β :=
        mul_le_mul_of_nonneg_right hcore (Real.sqrt_nonneg β)
      have hb2 : Real.sqrt T * Real.sqrt β * Real.sqrt T ≤ T * Real.sqrt β := by
        have heq : Real.sqrt T * Real.sqrt β * Real.sqrt T = T * Real.sqrt β := by
          rw [mul_assoc, mul_comm (Real.sqrt β) (Real.sqrt T), ← mul_assoc,
            Real.mul_self_sqrt hT_nonneg]
        exact le_of_eq heq
      have h2 : Real.sqrt C₉ *
            (Real.sqrt T * Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) * Real.sqrt β
              + Real.sqrt T * Real.sqrt β * Real.sqrt T) ≤
          Real.sqrt C₉ * (T * Real.sqrt β + T * Real.sqrt β) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (Real.sqrt_nonneg C₉)
      calc Real.sqrt α * Real.sqrt β * Real.sqrt γ ≤ _ := h1
        _ ≤ Real.sqrt C₉ * (T * Real.sqrt β + T * Real.sqrt β) := h2
        _ = 2 * Real.sqrt C₉ * Real.sqrt β * T := by ring
    calc C₂₅ * κ ^ (-1 : ℝ) * Real.sqrt α * Real.sqrt β * Real.sqrt γ
        = C₂₅ * κ ^ (-1 : ℝ) * (Real.sqrt α * Real.sqrt β * Real.sqrt γ) := by ring
      _ ≤ C₂₅ * κ ^ (-1 : ℝ) * (2 * Real.sqrt C₉ * Real.sqrt β * T) :=
          mul_le_mul_of_nonneg_left hprod
            (mul_nonneg hC₂₅ (Real.rpow_nonneg hκ.le _))
      _ = 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-1 : ℝ) * Real.sqrt β * T := by ring
  have hT3 : C₂₅ * κ ^ (-1 : ℝ) * δ * Real.sqrt γ ≤
      2 * C₂₅ * Real.sqrt C₉ * κ * T := by
    have hprod : δ * Real.sqrt γ ≤ 2 * Real.sqrt C₉ * κ ^ (2 : ℝ) * T := by
      have h1 : δ * Real.sqrt γ ≤ Real.sqrt C₉ * κ ^ (2 : ℝ) *
          (Real.sqrt T * (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β))
            + Real.sqrt T * Real.sqrt T) := by
        calc δ * Real.sqrt γ
            ≤ (κ ^ (2 : ℝ) * Real.sqrt T) *
                (Real.sqrt C₉ *
                  (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) + Real.sqrt T)) :=
              mul_le_mul hδT hγsqrt (Real.sqrt_nonneg γ)
                (mul_nonneg (Real.rpow_nonneg hκ.le _) (Real.sqrt_nonneg T))
          _ = Real.sqrt C₉ * κ ^ (2 : ℝ) *
                (Real.sqrt T * (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β))
                  + Real.sqrt T * Real.sqrt T) := by ring
      rw [Real.mul_self_sqrt hT_nonneg] at h1
      have hcore' : Real.sqrt T * (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β)) ≤ T := by
        rw [← mul_assoc]; exact hcore
      have h2 : Real.sqrt C₉ * κ ^ (2 : ℝ) *
            (Real.sqrt T * (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β)) + T) ≤
          Real.sqrt C₉ * κ ^ (2 : ℝ) * (T + T) :=
        mul_le_mul_of_nonneg_left (add_le_add hcore' le_rfl)
          (mul_nonneg (Real.sqrt_nonneg C₉) (Real.rpow_nonneg hκ.le _))
      calc δ * Real.sqrt γ ≤ _ := h1
        _ ≤ Real.sqrt C₉ * κ ^ (2 : ℝ) * (T + T) := h2
        _ = 2 * Real.sqrt C₉ * κ ^ (2 : ℝ) * T := by ring
    have hpow : κ ^ (-1 : ℝ) * κ ^ (2 : ℝ) = κ := by
      rw [rpow_mul_of_add hκ (by norm_num : (-1 : ℝ) + 2 = 1), Real.rpow_one]
    calc C₂₅ * κ ^ (-1 : ℝ) * δ * Real.sqrt γ
        = C₂₅ * κ ^ (-1 : ℝ) * (δ * Real.sqrt γ) := by ring
      _ ≤ C₂₅ * κ ^ (-1 : ℝ) * (2 * Real.sqrt C₉ * κ ^ (2 : ℝ) * T) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg hC₂₅ (Real.rpow_nonneg hκ.le _))
      _ = 2 * C₂₅ * Real.sqrt C₉ * (κ ^ (-1 : ℝ) * κ ^ (2 : ℝ)) * T := by ring
      _ = 2 * C₂₅ * Real.sqrt C₉ * κ * T := by rw [hpow]
  have hT4 : C₂₆ * κ ^ (-1 / 2 : ℝ) * Real.sqrt γ * Real.sqrt lam ≤
      2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam := by
    have hγle : Real.sqrt γ ≤ 2 * Real.sqrt C₉ * Real.sqrt T := by
      calc Real.sqrt γ ≤ Real.sqrt C₉ *
            (Real.sqrt (Real.sqrt T) * Real.sqrt (Real.sqrt β) + Real.sqrt T) := hγsqrt
        _ ≤ Real.sqrt C₉ * (Real.sqrt T + Real.sqrt T) :=
            mul_le_mul_of_nonneg_left (add_le_add hsqrtβsqrt le_rfl)
              (Real.sqrt_nonneg C₉)
        _ = 2 * Real.sqrt C₉ * Real.sqrt T := by ring
    calc C₂₆ * κ ^ (-1 / 2 : ℝ) * Real.sqrt γ * Real.sqrt lam
        = C₂₆ * κ ^ (-1 / 2 : ℝ) * (Real.sqrt γ * Real.sqrt lam) := by ring
      _ ≤ C₂₆ * κ ^ (-1 / 2 : ℝ) *
            (2 * Real.sqrt C₉ * Real.sqrt T * Real.sqrt lam) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hγle (Real.sqrt_nonneg lam))
            (mul_nonneg hC₂₆ (Real.rpow_nonneg hκ.le _))
      _ = 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam := by ring
  have hE : αr + βr ≤ C₂₅ * κ * T
      + 2 * C₂₅ * Real.sqrt C₉ * κ ^ (-1 : ℝ) * Real.sqrt β * T
      + 2 * C₂₅ * Real.sqrt C₉ * κ * T
      + 2 * C₂₆ * Real.sqrt C₉ * κ ^ (-1 / 2 : ℝ) * Real.sqrt T * Real.sqrt lam := by
    linarith only [hA, hT1, hT2, hT3, hT4]
  have hsum : C₂₅ * κ * T + 2 * C₂₅ * Real.sqrt C₉ * κ * T
      = C₂₅ * (1 + 2 * Real.sqrt C₉) * κ * T := by ring
  linarith only [hE, hsum]

end CKN
