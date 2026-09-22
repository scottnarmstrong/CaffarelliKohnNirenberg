-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.InterpolationInstancesSharpness
import CKN.Foundation.Parabolic.Vec3Norm

/-! # Two interpolation instances and the failure of swapped exponents

The spatial gradient magnitude is Euclidean. Comparisons with the native
coordinate norm retain uniform constants and preserve the endpoint q = 6.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN

private theorem gradient_norm_comparison {B : Set Vec3} (v : H1Function B) :
    weakGradientLpNormOn 2 B v.grad ≤
        eLpNorm (fun y => vec3EuclideanNorm (v.grad y)) 2 (volume.restrict B) ∧
      eLpNorm (fun y => vec3EuclideanNorm (v.grad y)) 2 (volume.restrict B) ≤
        ENNReal.ofReal (Real.sqrt 3) * weakGradientLpNormOn 2 B v.grad := by
  have hm : MemLp v.grad 2 (volume.restrict B) := memLp_pi_iff.mpr v.gradMemL2
  have he := continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hm.aestronglyMeasurable
  constructor
  · exact eLpNorm_mono_real hm.aestronglyMeasurable
      (fun y => norm_le_vec3EuclideanNorm (v.grad y))
  · calc
      _ ≤ eLpNorm (fun y => Real.sqrt 3 • v.grad y) 2 (volume.restrict B) := by
        apply eLpNorm_mono he
        intro y
        rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
          norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact vec3EuclideanNorm_le_sqrt_three_mul_norm _
      _ = _ := by
        change eLpNorm (Real.sqrt 3 • v.grad) 2 (volume.restrict B) = _
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
        rfl

/-- The ten-thirds specialization of the ball interpolation estimate. -/
theorem interpolationBall_ten_thirds_finite :
    ∃ C₆ : ℝ≥0∞, C₆ ≠ ∞ ∧
      ∀ {x₀ : Vec3} {r : ℝ}, 0 < r →
        ∀ v : H1Function (euclideanBall x₀ r),
          lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r) v.toFun ^
                (10 / 3 : ℝ) ≤
            C₆ * eLpNorm (fun y => vec3EuclideanNorm (v.grad y)) 2
                (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (4 / 3 : ℝ) +
            C₆ * (ENNReal.ofReal r) ^ (-2 : ℝ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (10 / 3 : ℝ) := by
  obtain ⟨C₆, hfin, hC⟩ := interpolationBall_finite
  refine ⟨C₆, hfin, ?_⟩
  intro x₀ r hr v
  have hC' : ∀ q : ℝ, 2 ≤ q → q ≤ 6 →
      ∀ {x₀ : Vec3} {r : ℝ}, 0 < r → ∀ v : H1Function (euclideanBall x₀ r),
      lpNormOn (ENNReal.ofReal q) (euclideanBall x₀ r) v.toFun ^ q ≤
        C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
            (2 * (3 * (q - 2) / 4)) *
          lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
            (q - 2 * (3 * (q - 2) / 4)) +
        C₆ * (ENNReal.ofReal r) ^ (-(2 * (3 * (q - 2) / 4))) *
          lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ q := hC
  have hh := hC' (10 / 3) (by norm_num) (by norm_num) hr v
  norm_num at hh
  apply hh.trans
  gcongr
  simpa only [ENNReal.rpow_two] using
    (ENNReal.rpow_le_rpow (gradient_norm_comparison v).1
      (by norm_num : (0 : ℝ) ≤ 2))

private theorem positive_interpolation_instances :
    ∃ C₆ : ℝ≥0∞, C₆ ≠ ∞ ∧
      (∀ (x₀ : Vec3) (r : ℝ), 0 < r →
        ∀ v : H1Function (euclideanBall x₀ r),
          lpNormOn 3 (euclideanBall x₀ r) v.toFun ^ (3 : ℝ) ≤
            C₆ * eLpNorm (fun y => vec3EuclideanNorm (v.grad y)) 2
              (volume.restrict (euclideanBall x₀ r)) ^ (3/2 : ℝ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (3/2 : ℝ) +
            C₆ * ENNReal.ofReal r ^ (-(3/2 : ℝ)) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (3 : ℝ)) ∧
      (∀ (x₀ : Vec3) (r : ℝ), 0 < r →
        ∀ v : H1Function (euclideanBall x₀ r),
          lpNormOn (ENNReal.ofReal (10/3 : ℝ)) (euclideanBall x₀ r) v.toFun ^ (10/3 : ℝ) ≤
            C₆ * eLpNorm (fun y => vec3EuclideanNorm (v.grad y)) 2
              (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (4/3 : ℝ) +
            C₆ * ENNReal.ofReal r ^ (-2 : ℝ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (10/3 : ℝ)) := by
  obtain ⟨C₆, hfin, hC⟩ := interpolationBall_finite
  have hC' : ∀ q : ℝ, 2 ≤ q → q ≤ 6 →
      ∀ {x₀ : Vec3} {r : ℝ}, 0 < r → ∀ v : H1Function (euclideanBall x₀ r),
      lpNormOn (ENNReal.ofReal q) (euclideanBall x₀ r) v.toFun ^ q ≤
        C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^ (2 * (3 * (q-2)/4)) *
          lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (q - 2 * (3 * (q-2)/4)) +
        C₆ * ENNReal.ofReal r ^ (-(2 * (3 * (q-2)/4))) *
          lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ q := hC
  refine ⟨C₆, hfin, ?_, ?_⟩
  · intro x₀ r hr v
    have hh := hC' 3 (by norm_num) (by norm_num) hr v
    have hcast : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
    rw [hcast] at hh
    norm_num only at hh
    apply hh.trans
    gcongr
    exact (gradient_norm_comparison v).1
  · intro x₀ r hr v
    have hh := hC' (10/3) (by norm_num) (by norm_num) hr v
    norm_num only at hh
    apply hh.trans
    gcongr
    exact (gradient_norm_comparison v).1

private theorem swapped_bound_transfer (q : ℝ) (hq6 : q ≤ 6)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ v : H1Function (euclideanBall (0 : Vec3) 1),
      lpNormOn (ENNReal.ofReal q) (euclideanBall (0 : Vec3) 1) v.toFun ^ q ≤
        C * eLpNorm (fun y => vec3EuclideanNorm (v.grad y)) 2
            (volume.restrict (euclideanBall (0 : Vec3) 1)) ^
            (2 * (q / 2 - 3 * (q - 2) / 4)) *
          lpNormOn 2 (euclideanBall (0 : Vec3) 1) v.toFun ^ (2 * (3 * (q - 2) / 4)) +
        C * lpNormOn 2 (euclideanBall (0 : Vec3) 1) v.toFun ^ q) :
    ∃ D : ℝ≥0∞, D ≠ ∞ ∧ ∀ v : H1Function (euclideanBall (0 : Vec3) 1),
      lpNormOn (ENNReal.ofReal q) (euclideanBall (0 : Vec3) 1) v.toFun ^ q ≤
        D * weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) 1) v.grad ^
            (2 * (q / 2 - 3 * (q - 2) / 4)) *
          lpNormOn 2 (euclideanBall (0 : Vec3) 1) v.toFun ^ (2 * (3 * (q - 2) / 4)) +
        D * lpNormOn 2 (euclideanBall (0 : Vec3) 1) v.toFun ^ q := by
  let a : ℝ := 2 * (q / 2 - 3 * (q - 2) / 4)
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt 3)
  let D : ℝ≥0∞ := C * (K ^ a + 1)
  have ha : 0 ≤ a := by dsimp [a]; nlinarith only [hq6]
  have hK : K ^ a ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha ENNReal.ofReal_ne_top
  have hD : D ≠ ∞ := ENNReal.mul_ne_top hC
    (ENNReal.add_ne_top.mpr ⟨hK, by simp⟩)
  have hCD : C ≤ D := by
    calc
      C = C * 1 := (mul_one C).symm
      _ ≤ D := mul_le_mul_right (le_add_self : (1 : ℝ≥0∞) ≤ K ^ a + 1) C
  have hCK : C * K ^ a ≤ D := mul_le_mul_right le_self_add C
  refine ⟨D, hD, ?_⟩
  intro v
  have hg := ENNReal.rpow_le_rpow (gradient_norm_comparison v).2 ha
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha] at hg
  apply (hbound v).trans
  apply add_le_add
  · apply mul_le_mul_left
    calc
      _ ≤ C * (K ^ a * weakGradientLpNormOn 2 _ v.grad ^ a) := mul_le_mul_right hg C
      _ = (C * K ^ a) * weakGradientLpNormOn 2 _ v.grad ^ a := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_left hCK _
  · exact mul_le_mul_left hCD _

/-- The cubic and ten-thirds interpolation estimates share a finite constant;
the swapped exponents fail for every exponent strictly above three up to six. -/
theorem interpolation_instances_and_swapped_failure :
    ∃ C₆ : ℝ≥0∞, C₆ ≠ ∞ ∧
      (∀ (x₀ : Vec3) (r : ℝ), 0 < r →
        ∀ v : H1Function (euclideanBall x₀ r),
          lpNormOn 3 (euclideanBall x₀ r) v.toFun ^ (3 : ℝ) ≤
            C₆ * eLpNorm (fun y => vec3EuclideanNorm (v.grad y)) 2
              (volume.restrict (euclideanBall x₀ r)) ^ (3/2 : ℝ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (3/2 : ℝ) +
            C₆ * ENNReal.ofReal r ^ (-(3/2 : ℝ)) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (3 : ℝ)) ∧
      (∀ (x₀ : Vec3) (r : ℝ), 0 < r →
        ∀ v : H1Function (euclideanBall x₀ r),
          lpNormOn (ENNReal.ofReal (10/3 : ℝ)) (euclideanBall x₀ r) v.toFun ^ (10/3 : ℝ) ≤
            C₆ * eLpNorm (fun y => vec3EuclideanNorm (v.grad y)) 2
              (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (4/3 : ℝ) +
            C₆ * ENNReal.ofReal r ^ (-2 : ℝ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (10/3 : ℝ)) ∧
      (∀ q : ℝ, 3 < q → q ≤ 6 →
        ¬ ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ v : H1Function (euclideanBall (0 : Vec3) 1),
          lpNormOn (ENNReal.ofReal q) (euclideanBall (0 : Vec3) 1) v.toFun ^ q ≤
            C * eLpNorm (fun y => vec3EuclideanNorm (v.grad y)) 2
                (volume.restrict (euclideanBall (0 : Vec3) 1)) ^
                (2 * (q / 2 - 3 * (q - 2) / 4)) *
              lpNormOn 2 (euclideanBall (0 : Vec3) 1) v.toFun ^ (2 * (3 * (q - 2) / 4)) +
            C * lpNormOn 2 (euclideanBall (0 : Vec3) 1) v.toFun ^ q) := by
  obtain ⟨C₆, hfin, hthree, hten⟩ := positive_interpolation_instances
  refine ⟨C₆, hfin, hthree, hten, ?_⟩
  intro q hq3 hq6
  rintro ⟨C, hC, hbound⟩
  exact lin_swapped_interpolation_false q hq3 hq6
    (swapped_bound_transfer q hq6 C hC hbound)

end CKN
