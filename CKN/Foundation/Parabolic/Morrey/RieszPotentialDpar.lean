-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Kernel

/-!
# The parabolic Riesz potential with the maximum gauge

This module defines the potential using `parabolicDist` and compares it with
the equivalent sum-gauge potential.
-/

open MeasureTheory
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The parabolic Riesz potential formed with the maximum parabolic gauge. -/
def parabolicRieszPotentialDpar (a : ℝ) (g : ParabolicPoint → ℝ)
    (z : ParabolicPoint) : ℝ≥0∞ :=
  ∫⁻ w, (ENNReal.ofReal (parabolicDist z w)) ^ (-(5 - a)) *
    ENNReal.ofReal |g w|

private theorem parabolicRho₂_le_two_parabolicDist (z w : ParabolicPoint) :
    parabolicRho₂ z w ≤ 2 * parabolicDist z w := by
  rw [parabolicRho₂, parabolicDist]
  have htime : Real.sqrt |z.2 - w.2| ≤
      max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) :=
    le_max_right _ _
  have hspace : vec3EuclideanNorm (z.1 - w.1) ≤
      max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) :=
    le_max_left _ _
  calc
    Real.sqrt |z.2 - w.2| + vec3EuclideanNorm (z.1 - w.1) ≤
        max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) +
          max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) :=
      add_le_add htime hspace
    _ = 2 * max (vec3EuclideanNorm (z.1 - w.1))
          (Real.sqrt |z.2 - w.2|) := by ring

private theorem parabolicRieszKernel_le_dpar {a : ℝ} (ha : 0 < a) (ha5 : a < 5)
    (z w : ParabolicPoint) :
    parabolicRieszKernel a z w ≤
      (ENNReal.ofReal (parabolicDist z w)) ^ (-(5 - a)) := by
  let c : ℝ := 5 - a
  have h05 : (0 : ℝ) < 5 := ha.trans ha5
  have hc : 0 < c := by dsimp [c]; linarith only [h05, ha5]
  let x : ℝ≥0∞ := ENNReal.ofReal (parabolicRho₂ z w)
  let y : ℝ≥0∞ := ENNReal.ofReal (parabolicDist z w)
  have hyx : y ≤ x := by
    dsimp [x, y]
    exact ENNReal.ofReal_le_ofReal (parabolicDist_le_parabolicRho₂ z w)
  have hpow : y ^ c ≤ x ^ c := ENNReal.rpow_le_rpow hyx hc.le
  have hinv : (x ^ c)⁻¹ ≤ (y ^ c)⁻¹ := ENNReal.inv_le_inv.mpr hpow
  have hkernel : parabolicRieszKernel a z w = x ^ (-c) := by
    rfl
  rw [hkernel, ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact hinv

private theorem dparKernel_le_scaled_parabolicRieszKernel {a : ℝ}
    (ha : 0 < a) (ha5 : a < 5) (z w : ParabolicPoint) :
    (ENNReal.ofReal (parabolicDist z w)) ^ (-(5 - a)) ≤
      (2 : ℝ≥0∞) ^ (5 - a) * parabolicRieszKernel a z w := by
  let c : ℝ := 5 - a
  have h05 : (0 : ℝ) < 5 := ha.trans ha5
  have hc : 0 < c := by dsimp [c]; linarith only [h05, ha5]
  let x : ℝ≥0∞ := ENNReal.ofReal (parabolicRho₂ z w)
  let y : ℝ≥0∞ := ENNReal.ofReal (parabolicDist z w)
  have hxy : x ≤ 2 * y := by
    dsimp [x, y]
    calc
      ENNReal.ofReal (parabolicRho₂ z w) ≤
          ENNReal.ofReal (2 * parabolicDist z w) :=
        ENNReal.ofReal_le_ofReal (parabolicRho₂_le_two_parabolicDist z w)
      _ = 2 * ENNReal.ofReal (parabolicDist z w) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have hpow : x ^ c ≤ (2 : ℝ≥0∞) ^ c * y ^ c := by
    calc
      x ^ c ≤ (2 * y) ^ c := ENNReal.rpow_le_rpow hxy hc.le
      _ = (2 : ℝ≥0∞) ^ c * y ^ c := ENNReal.mul_rpow_of_nonneg _ _ hc.le
  have hfactor_ne_zero : ((2 : ℝ≥0∞) ^ c) ≠ 0 :=
    (ENNReal.rpow_pos (by norm_num : (0 : ℝ≥0∞) < 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).ne'
  have hfactor_ne_top : ((2 : ℝ≥0∞) ^ c) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hc.le (by norm_num)
  have hinv : ((2 : ℝ≥0∞) ^ c * y ^ c)⁻¹ ≤ (x ^ c)⁻¹ :=
    ENNReal.inv_le_inv.mpr hpow
  have hkernel : parabolicRieszKernel a z w = x ^ (-c) := by
    rfl
  rw [hkernel, ENNReal.rpow_neg]
  calc
    (y ^ c)⁻¹ = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ c * y ^ c)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hfactor_ne_zero) (Or.inl hfactor_ne_top),
        ← mul_assoc, ENNReal.mul_inv_cancel hfactor_ne_zero hfactor_ne_top, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ c * (x ^ c)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv bot_le
    _ = (2 : ℝ≥0∞) ^ (5 - a) * x ^ (-c) := by
      simp only [c]
      congr 1
      rw [ENNReal.rpow_neg]
    _ = (2 : ℝ≥0∞) ^ (5 - a) * parabolicRieszKernel a z w := by
      rw [← hkernel]

/-- The sum-gauge and maximum-gauge potentials satisfy the sharp gauge comparison. -/
theorem parabolicRieszPotential_le_dpar_le (a : ℝ) (ha : 0 < a) (ha5 : a < 5)
    (g : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    parabolicRieszPotential a g z ≤ parabolicRieszPotentialDpar a g z ∧
      parabolicRieszPotentialDpar a g z ≤
        (2 : ℝ≥0∞) ^ (5 - a) * parabolicRieszPotential a g z := by
  constructor
  · unfold parabolicRieszPotential parabolicRieszPotentialDpar
    refine lintegral_mono fun w => ?_
    simpa [mul_comm] using
      (mul_le_mul_right (parabolicRieszKernel_le_dpar ha ha5 z w)
        (ENNReal.ofReal |g w|))
  · have hfactor_ne_top : ((2 : ℝ≥0∞) ^ (5 - a)) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr ha5.le) (by norm_num)
    unfold parabolicRieszPotentialDpar parabolicRieszPotential
    rw [← lintegral_const_mul' _ _ hfactor_ne_top]
    refine lintegral_mono fun w => ?_
    calc
      (ENNReal.ofReal (parabolicDist z w)) ^ (-(5 - a)) *
          ENNReal.ofReal |g w| ≤
          ((2 : ℝ≥0∞) ^ (5 - a) * parabolicRieszKernel a z w) *
            ENNReal.ofReal |g w| := by
        gcongr
        exact dparKernel_le_scaled_parabolicRieszKernel ha ha5 z w
      _ = (2 : ℝ≥0∞) ^ (5 - a) *
          (parabolicRieszKernel a z w * ENNReal.ofReal |g w|) := by
        rw [mul_assoc]

end CKN.Foundation.Parabolic.Morrey
