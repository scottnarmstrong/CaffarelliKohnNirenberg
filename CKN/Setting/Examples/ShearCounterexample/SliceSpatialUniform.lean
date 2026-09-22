-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.SliceSpatialLp
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Uniform spatial slice estimates for the shear profile. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

private theorem shearScale_sum_range_le (N : ℕ) :
    ∑ n ∈ Finset.range N, shearScale n ≤ 4 / 3 := by
  calc
    ∑ n ∈ Finset.range N, shearScale n ≤ ∑' n : ℕ, (1 / 4 : ℝ) ^ n := by
      apply (summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum
      intro n hn
      positivity
    _ = (1 - (1 / 4 : ℝ))⁻¹ := tsum_geometric_of_lt_one (by norm_num) (by norm_num)
    _ = 4 / 3 := by norm_num [div_eq_mul_inv]

private theorem shearSliceFiniteTermSum_eLpNorm_uniform {N : ℕ} {t : ℝ} :
    eLpNorm (fun x : Vec 2 =>
      ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, t)) 2 volume ≤
      ENNReal.ofReal (16 / 3 * shearUnitBump_bound.choose) := by
  let C := Classical.choose shearUnitBump_bound
  have hC : 0 ≤ C := Classical.choose_spec shearUnitBump_bound |>.1
  have hsum := shearSliceFiniteTermSum_eLpNorm_bound (N := N) t
  have hsum' : (∑ n ∈ Finset.range N,
      ENNReal.ofReal (4 * C * shearWeight n * shearScale n)) ≤
      ENNReal.ofReal (16 / 3 * C) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (4 * C * shearScale n) := by
        apply Finset.sum_le_sum
        intro n hn
        apply ENNReal.ofReal_le_ofReal
        have hw := shearWeight_le_one_spatial n
        have hr := shearScale_pos n
        calc
          4 * C * shearWeight n * shearScale n ≤ 4 * C * 1 * shearScale n := by
            gcongr
          _ = 4 * C * shearScale n := by ring
      _ = ENNReal.ofReal (∑ n ∈ Finset.range N, 4 * C * shearScale n) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro n hn
        exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) hC)
          (shearScale_pos n).le
      _ ≤ ENNReal.ofReal (16 / 3 * C) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          ∑ n ∈ Finset.range N, 4 * C * shearScale n =
              4 * C * (∑ n ∈ Finset.range N, shearScale n) := by rw [Finset.mul_sum]
          _ ≤ 4 * C * (4 / 3) := mul_le_mul_of_nonneg_left
            (shearScale_sum_range_le N) (by positivity)
          _ = 16 / 3 * C := by ring
  have hsumBound : ∑ n ∈ Finset.range N,
      ENNReal.ofReal (4 * shearUnitBump_bound.choose * shearWeight n * shearScale n) ≤
      ENNReal.ofReal (16 / 3 * shearUnitBump_bound.choose) := by
    simpa [C] using hsum'
  exact hsum.trans hsumBound

theorem shearReducedBumpSeries_slice_eLpNorm_bound {t : ℝ} (ht : t ≠ 0) :
    eLpNorm (fun x : Vec 2 => shearReducedBumpSeries (x, t)) 2 volume ≤
      ENNReal.ofReal (16 / 3 * shearUnitBump_bound.choose) := by
  obtain ⟨N, hN⟩ := shearReducedBumpSeries_eq_finite_of_time_nezero ht
  have heq : (fun x : Vec 2 => shearReducedBumpSeries (x, t)) =
      (fun x => ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, t)) := by
    funext x
    exact hN x
  rw [heq]
  exact shearSliceFiniteTermSum_eLpNorm_uniform

theorem shearReducedBumpSeries_slice_integral_bound {t : ℝ} (ht : t ≠ 0) :
    ∫⁻ x : Vec 2, ‖shearReducedBumpSeries (x, t)‖ₑ ^ (2 : ℝ) ∂volume ≤
      ENNReal.ofReal ((16 / 3 * shearUnitBump_bound.choose) ^ 2) := by
  let K := 16 / 3 * shearUnitBump_bound.choose
  have hC : 0 ≤ shearUnitBump_bound.choose :=
    (Classical.choose_spec shearUnitBump_bound).1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg : AEStronglyMeasurable (fun x : Vec 2 => shearReducedBumpSeries (x, t)) volume :=
    (shearReducedBumpSeries_measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hnorm := shearReducedBumpSeries_slice_eLpNorm_bound ht
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg] at hnorm
  have hnorm' :
      (∫⁻ x : Vec 2, ‖shearReducedBumpSeries (x, t)‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal K := by
    simpa only [ENNReal.toReal_ofNat, K] using hnorm
  have hsq := ENNReal.rpow_le_rpow hnorm' (by norm_num : (0 : ℝ) ≤ 2)
  have hsq' :
      (∫⁻ x : Vec 2, ‖shearReducedBumpSeries (x, t)‖ₑ ^ (2 : ℝ) ∂volume) ≤
        ENNReal.ofReal K ^ (2 : ℝ) := by
    simpa only [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      ENNReal.rpow_one] using hsq
  calc
    _ ≤ ENNReal.ofReal K ^ (2 : ℝ) := hsq'
    _ = ENNReal.ofReal (K ^ 2) := by
      simpa only [show (2 : ℝ) = (↑(2 : ℕ) : ℝ) by norm_num,
        ENNReal.rpow_natCast] using (ENNReal.ofReal_pow hK 2).symm
    _ = _ := by rfl

end CKN
