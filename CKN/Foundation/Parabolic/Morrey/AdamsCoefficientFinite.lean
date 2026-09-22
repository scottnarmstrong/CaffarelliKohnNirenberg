-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.AdamsM4
import CKN.Foundation.Parabolic.Morrey.AdamsConstantFinite

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace CKN.Foundation.Parabolic.Morrey

/-- The Adams maximal constant is finite when `1 < P`. -/
theorem parabolicAdamsMaximalConstant_ne_top {P τ : ℝ} (hP : 1 < P) :
    parabolicAdamsMaximalConstant P τ ≠ ∞ := by
  unfold parabolicAdamsMaximalConstant
  have hP0 : 0 < P := by linarith only [hP]
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  have h_vol_lt_top : volume (parabolicCylinder (0 : Vec3) 0 1) < ∞ :=
    Integration.volume_parabolicCylinder_lt_top (x := 0) (t := 0) (r := 1)
  have h_vol_ne_top : volume (parabolicCylinder (0 : Vec3) 0 1) ≠ ∞ := h_vol_lt_top.ne
  have h_vol_pos : 0 < volume (parabolicCylinder (0 : Vec3) 0 1) :=
    Integration.volume_parabolicCylinder_pos (hr := by norm_num)
  have h_vol_ne_zero : volume (parabolicCylinder (0 : Vec3) 0 1) ≠ 0 := h_vol_pos.ne'
  have h_ofReal8_ne_zero : ENNReal.ofReal (8 : ℝ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 8)).ne'
  have h_ofReal8_ne_top : ENNReal.ofReal (8 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  have h_ofReal2_ne_zero : ENNReal.ofReal (2 : ℝ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h_rpow1 : (2 : ℝ≥0∞) ^ (P - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith only [hP]) h_two_ne_top
  have h_strong : parabolicMaximalStrongConstant P ≠ ∞ := by
    unfold parabolicMaximalStrongConstant
    apply ENNReal.div_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg hP0.le h_two_ne_top
        · exact ENNReal.ofReal_ne_top
      · exact ENNReal.ofReal_ne_top
    · exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hP)).ne'
  have h_ofReal8_rpow : ENNReal.ofReal (8 : ℝ) ^ (5 * (1 - P / τ)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero h_ofReal8_ne_zero h_ofReal8_ne_top
  have h_exp_nonneg : 0 ≤ 1 - 1 / P := by
    have h : 1 / P ≤ 1 := (div_le_one hP0).mpr (by linarith only [hP])
    linarith only [h]
  have h_inner_mul : ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / τ)) /
      volume (parabolicCylinder 0 0 1)) *
      (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.div_ne_top
      · exact ENNReal.rpow_ne_top_of_ne_zero h_ofReal2_ne_zero ENNReal.ofReal_ne_top
      · exact h_vol_ne_zero
    · exact ENNReal.rpow_ne_top_of_nonneg h_exp_nonneg h_vol_ne_top
  have h_inner_pow : (((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / τ)) /
      volume (parabolicCylinder 0 0 1)) *
      (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P)) ^ P ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hP0.le h_inner_mul
  have h_volume_term : volume (parabolicCylinder 0 0 1) *
      (((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / τ)) /
        volume (parabolicCylinder 0 0 1)) *
        (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P)) ^ P ≠ ∞ :=
    ENNReal.mul_ne_top h_vol_ne_top h_inner_pow
  have h_sum : parabolicMaximalStrongConstant P *
      ENNReal.ofReal (8 : ℝ) ^ (5 * (1 - P / τ)) +
      volume (parabolicCylinder 0 0 1) *
        (((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / τ)) /
          volume (parabolicCylinder 0 0 1)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P)) ^ P ≠ ∞ := by
    apply ENNReal.add_ne_top.2
    exact ⟨ENNReal.mul_ne_top h_strong h_ofReal8_rpow, h_volume_term⟩
  exact ENNReal.mul_ne_top h_rpow1 h_sum

end CKN.Foundation.Parabolic.Morrey
