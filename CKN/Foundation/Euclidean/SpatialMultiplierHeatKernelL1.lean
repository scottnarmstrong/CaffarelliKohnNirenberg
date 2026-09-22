-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelOscillatory
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Uniform integrability estimates for damped homogeneous symbols
-/

open scoped BigOperators
open MeasureTheory Set Module

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier

/-- The critical-order derivatives of a damped homogeneous symbol have a uniform L¹ bound. -/
theorem exists_uniform_integral_iteratedFDeriv_highDampedFrequency
    {τ : Vec3 → ℂ} (d : ℕ) (hd : d ≤ 3)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      Integrable (iteratedFDeriv ℝ (d + 4) (highDampedFrequencyFunction τ t)) ∧
      ∫ ξ : Vec3,
        ‖iteratedFDeriv ℝ (d + 4) (highDampedFrequencyFunction τ t) ξ‖ ≤ C := by
  let n := d + 4
  have hn : n ≤ 7 := by dsimp [n]; omega
  obtain ⟨Kc, hKc, hcompact⟩ :=
    exists_uniform_norm_iteratedFDeriv_highDampedFrequency_compact d n hn hτ hhom
  obtain ⟨Kt, hKt, htail⟩ :=
    exists_uniform_norm_iteratedFDeriv_highDampedFrequency_tail d hd hτ hhom
  let K : ℝ := max (25 * Kc) (25 * Kt)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hG : Integrable (fun ξ : Vec3 =>
      (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ))) volume := by
    have hdim : (finrank ℝ Vec3 : ℝ) < 4 := by
      rw [Module.finrank_fintype_fun_eq_card]
      norm_num [Vec3]
    have h := integrable_rpow_neg_one_add_norm_sq (E := Vec3) (μ := volume)
      (r := 4) hdim
    simpa only [show -(4 : ℝ) / 2 = -(2 : ℝ) by norm_num] using h
  have hGnonneg : ∀ ξ : Vec3, 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) := by
    intro ξ
    exact Real.rpow_nonneg (by positivity) _
  have hGform : ∀ ξ : Vec3,
      (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) = ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by
    intro ξ
    calc
      (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) =
          ((1 + ‖ξ‖ ^ 2) ^ (2 : ℝ))⁻¹ := by
        rw [Real.rpow_neg (by positivity)]
      _ = ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by rw [Real.rpow_ofNat]
  refine ⟨K * ∫ ξ : Vec3, (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) ∂volume, ?_, ?_⟩
  · have hIntG : 0 ≤ ∫ ξ : Vec3, (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) ∂volume :=
      integral_nonneg (fun ξ => hGnonneg ξ)
    exact mul_nonneg hK hIntG
  · intro t ht ht1
    constructor
    · exact integrable_iteratedFDeriv_highDampedFrequency d (d + 4) (by omega)
        hτ hhom t ht
    · have hmajor : Integrable (fun ξ : Vec3 =>
        K * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ))) volume := hG.const_mul K
      have hpoint : ∀ ξ : Vec3,
          ‖iteratedFDeriv ℝ (d + 4) (highDampedFrequencyFunction τ t) ξ‖ ≤
            K * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) := by
        intro ξ
        let r := vec3EuclideanNorm ξ
        have hr : 0 ≤ r := vec3EuclideanNorm_nonneg ξ
        have hnormle : ‖ξ‖ ≤ r := norm_le_vec3EuclideanNorm ξ
        have hGξ := hGform ξ
        by_cases hcompact' : r ≤ 2
        · have hbase : 1 + ‖ξ‖ ^ 2 ≤ 5 := by
            have hnormtwo : ‖ξ‖ ≤ 2 := le_trans hnormle hcompact'
            nlinarith only [hnormtwo, norm_nonneg ξ]
          have hden : (1 + ‖ξ‖ ^ 2) ^ 2 ≤ 25 := by
            have h := pow_le_pow_left₀ (by positivity) hbase 2
            norm_num at h ⊢
            exact h
          have hGlo : 1 / 25 ≤ (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) := by
            rw [hGξ]
            have hInv : (25 : ℝ)⁻¹ ≤ ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ :=
              (inv_le_inv₀ (by norm_num) (by positivity)).2 hden
            have hfrac : (1 : ℝ) / 25 = (25 : ℝ)⁻¹ := by norm_num
            rw [hfrac]
            exact hInv
          have honeG : 1 ≤ 25 * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) := by
            calc
              1 = 25 * (1 / 25) := by norm_num
              _ ≤ 25 * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hGlo (by norm_num)
          have hcomp := hcompact t ht ht1 ξ (by simpa [r] using hcompact')
          have hGpos := hGnonneg ξ
          calc
            ‖iteratedFDeriv ℝ (d + 4) (highDampedFrequencyFunction τ t) ξ‖ ≤ Kc := by
              simpa [n] using hcomp
            _ ≤ Kc * (25 * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ))) :=
              by simpa only [mul_one] using mul_le_mul_of_nonneg_left honeG hKc
            _ = 25 * Kc * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) := by ring
            _ ≤ K * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hGpos
        · have hlarge : 2 < r := lt_of_not_ge hcompact'
          have hrpos : 0 < r := by linarith only [hlarge]
          have hbase : 1 + ‖ξ‖ ^ 2 ≤ (5 / 4) * r ^ 2 := by
            calc
              1 + ‖ξ‖ ^ 2 ≤ 1 + r ^ 2 := by gcongr
              _ ≤ (5 / 4) * r ^ 2 := by nlinarith only [hlarge, sq_nonneg r]
          have hden : (1 + ‖ξ‖ ^ 2) ^ 2 ≤ 25 * r ^ 4 := by
            calc
              (1 + ‖ξ‖ ^ 2) ^ 2 ≤ ((5 / 4) * r ^ 2) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hbase 2
              _ = (25 / 16) * r ^ 4 := by ring
              _ ≤ 25 * r ^ 4 := by
                exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hr 4)
          have hGlo : (25 * r ^ 4)⁻¹ ≤
              (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) := by
            rw [hGξ]
            exact (inv_le_inv₀ (by positivity) (by positivity)).2 hden
          have hscale : (r ^ 4)⁻¹ ≤
              25 * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) := by
            calc
              (r ^ 4)⁻¹ = 25 * (25 * r ^ 4)⁻¹ := by field_simp
              _ ≤ 25 * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hGlo (by norm_num)
          have htail' := htail t ht ht1 ξ
            (by simpa [r] using show 1 / 2 ≤ r from by linarith only [hlarge])
          have hGpos := hGnonneg ξ
          calc
            ‖iteratedFDeriv ℝ (d + 4) (highDampedFrequencyFunction τ t) ξ‖ ≤
                Kt * (r ^ 4)⁻¹ := by simpa [r] using htail'
            _ ≤ Kt * (25 * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ))) :=
              mul_le_mul_of_nonneg_left hscale hKt
            _ = 25 * Kt * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) := by ring
            _ ≤ K * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hGpos
      have hnormInt :=
        (integrable_iteratedFDeriv_highDampedFrequency d (d + 4) (by omega)
          hτ hhom t ht).norm
      have hInt := integral_mono_ae hnormInt hmajor (ae_of_all volume hpoint)
      calc
        ∫ ξ : Vec3,
            ‖iteratedFDeriv ℝ (d + 4) (highDampedFrequencyFunction τ t) ξ‖ ∂volume ≤
          ∫ ξ : Vec3, K * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) ∂volume := hInt
        _ = K * ∫ ξ : Vec3, (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) ∂volume := by
          rw [integral_const_mul]

end CKN.Foundation.Euclidean
