-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelHighSymbolBounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Derivative bounds for the frequency Gaussian
-/

open scoped BigOperators
open Set MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat

/-- The complex extension of the squared Euclidean norm on frequency space. -/
def complexEuclideanSquare (ξ : Vec3) : ℂ :=
  (vec3EuclideanNorm ξ ^ 2 : ℝ)

/-- The squared Euclidean norm has a smooth complex-valued extension. -/
theorem complexEuclideanSquare_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) complexEuclideanSquare := by
  have hsum : complexEuclideanSquare = fun ξ : Vec3 =>
      ((∑ j : Fin 3, ξ j ^ 2 : ℝ) : ℂ) := by
    funext ξ
    simp [complexEuclideanSquare, vec3EuclideanNorm_sq]
  rw [hsum]
  have hterm : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun ξ : Vec3 => ξ j ^ 2) := by
    intro j
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp
    (ContDiff.sum (s := Finset.univ) (fun j hj => hterm j))

/-- Homogeneity of the complex squared norm under real dilations. -/
theorem complexEuclideanSquare_homogeneous :
    ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      complexEuclideanSquare (a • ξ) = (a ^ 2 : ℝ) • complexEuclideanSquare ξ := by
  intro a ha ξ
  rw [complexEuclideanSquare, vec3EuclideanNorm_smul, abs_of_pos ha,
    complexEuclideanSquare]
  simp only [RCLike.real_smul_eq_coe_mul]
  calc
    Complex.ofReal ((a * vec3EuclideanNorm ξ) ^ 2) =
        Complex.ofReal (a ^ 2 * vec3EuclideanNorm ξ ^ 2) := by
      congr 1
      ring
    _ = Complex.ofReal (a ^ 2) * Complex.ofReal (vec3EuclideanNorm ξ ^ 2) :=
      Complex.ofReal_mul _ _

private noncomputable def complexEuclideanSquareGrowth (k : ℕ) : ℝ :=
  Classical.choose (exists_norm_iteratedFDeriv_growth 2 complexEuclideanSquare_contDiff.contDiffOn
    complexEuclideanSquare_homogeneous k)

private theorem complexEuclideanSquareGrowth_nonneg (k : ℕ) :
    0 ≤ complexEuclideanSquareGrowth k := by
  exact (Classical.choose_spec (exists_norm_iteratedFDeriv_growth 2
    complexEuclideanSquare_contDiff.contDiffOn
      complexEuclideanSquare_homogeneous k)).1

private theorem complexEuclideanSquare_iteratedFDeriv_bound (k : ℕ) {ξ : Vec3}
    (hξ : ξ ≠ 0) :
    ‖iteratedFDeriv ℝ k complexEuclideanSquare ξ‖ ≤
      complexEuclideanSquareGrowth k * vec3EuclideanNorm ξ ^ 2 /
        vec3EuclideanNorm ξ ^ k := by
  exact (Classical.choose_spec (exists_norm_iteratedFDeriv_growth 2
    complexEuclideanSquare_contDiff.contDiffOn
      complexEuclideanSquare_homogeneous k)).2 ξ hξ

private noncomputable def complexExpDerivativeBound : ℝ :=
  1 + ∑ i ∈ Finset.range 8,
    ‖iteratedFDeriv ℝ i Complex.exp (0 : ℂ)‖

private theorem complexExpDerivativeBound_nonneg : 0 ≤ complexExpDerivativeBound := by
  dsimp [complexExpDerivativeBound]
  positivity

private theorem complexExp_iteratedFDeriv_at_zero_bound {i : ℕ} (hi : i ≤ 7) :
    ‖iteratedFDeriv ℝ i Complex.exp (0 : ℂ)‖ ≤ complexExpDerivativeBound := by
  unfold complexExpDerivativeBound
  have hsum := Finset.single_le_sum
    (s := Finset.range 8) (f := fun j => ‖iteratedFDeriv ℝ j Complex.exp (0 : ℂ)‖)
    (fun j hj => norm_nonneg _)
    (Finset.mem_range.mpr (by omega : i < 8))
  exact hsum.trans (le_add_of_nonneg_left (by positivity))

private def complexEuclideanSquareDifference (ξ y : Vec3) : ℂ :=
  -(complexEuclideanSquare y - complexEuclideanSquare ξ)

private theorem complexEuclideanSquareDifference_contDiff (ξ : Vec3) :
    ContDiff ℝ (⊤ : ℕ∞) (complexEuclideanSquareDifference ξ) := by
  have hq := complexEuclideanSquare_contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 => complexEuclideanSquare ξ) :=
    contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun y : Vec3 => -(complexEuclideanSquare y - complexEuclideanSquare ξ))
  exact (hq.sub hc).neg

private theorem complexEuclideanSquareDifference_zero (ξ : Vec3) :
    complexEuclideanSquareDifference ξ ξ = 0 := by
  simp [complexEuclideanSquareDifference]

private theorem complexEuclideanSquareDifference_iteratedFDeriv_bound
    (ξ : Vec3) {i : ℕ} (hi : 1 ≤ i) (hi7 : i ≤ 7)
    (hξ : 1 / 2 ≤ vec3EuclideanNorm ξ) :
    ‖iteratedFDeriv ℝ i (complexEuclideanSquareDifference ξ) ξ‖ ≤
      complexEuclideanSquareGrowth i * 2 ^ i * (1 + vec3EuclideanNorm ξ) := by
  have hr : 0 < vec3EuclideanNorm ξ := by linarith only [hξ]
  have hξ0 : ξ ≠ 0 := by
    intro hzero
    rw [hzero, vec3EuclideanNorm_zero] at hξ
    norm_num at hξ
  have hsub : iteratedFDeriv ℝ i (complexEuclideanSquareDifference ξ) ξ =
      -(iteratedFDeriv ℝ i complexEuclideanSquare ξ) := by
    have hi0 : i ≠ 0 := by omega
    have hiTop : (↑(i : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
      WithTop.coe_le_coe.mpr le_top
    have hfun : complexEuclideanSquareDifference ξ =
        fun y : Vec3 => complexEuclideanSquare ξ - complexEuclideanSquare y := by
      funext y
      simp [complexEuclideanSquareDifference]
    rw [hfun]
    change iteratedFDeriv ℝ i
      ((fun _ : Vec3 => complexEuclideanSquare ξ) - complexEuclideanSquare) ξ = _
    rw [iteratedFDeriv_sub_apply
      (contDiff_const.contDiffAt.of_le hiTop)
      (complexEuclideanSquare_contDiff.contDiffAt.of_le hiTop)]
    rw [iteratedFDeriv_const_of_ne hi0]
    simp
  rw [hsub, norm_neg]
  have hgrowth := complexEuclideanSquare_iteratedFDeriv_bound i hξ0
  have hrbound : (vec3EuclideanNorm ξ ^ 2) / vec3EuclideanNorm ξ ^ i ≤
      2 ^ i * (1 + vec3EuclideanNorm ξ) := by
    have hpowpos : 0 < vec3EuclideanNorm ξ ^ i := pow_pos hr _
    rw [div_le_iff₀ hpowpos]
    by_cases hrone : vec3EuclideanNorm ξ ≤ 1
    · have hlow : (1 / 2 : ℝ) ^ i ≤ vec3EuclideanNorm ξ ^ i :=
        pow_le_pow_left₀ (by norm_num) hξ i
      have hcancel : (1 / 2 : ℝ) ^ i * (2 : ℝ) ^ i = 1 := by
        rw [div_pow, one_pow, div_eq_mul_inv, one_mul]
        exact inv_mul_cancel₀ (pow_ne_zero i (by norm_num))
      have hmul : 1 ≤ (2 : ℝ) ^ i * vec3EuclideanNorm ξ ^ i := by
        calc
          1 = (1 / 2 : ℝ) ^ i * (2 : ℝ) ^ i := hcancel.symm
          _ ≤ vec3EuclideanNorm ξ ^ i * (2 : ℝ) ^ i :=
            mul_le_mul_of_nonneg_right hlow (pow_nonneg (by norm_num) _)
          _ = _ := by ring
      have hone : vec3EuclideanNorm ξ ^ 2 ≤ 1 := by
        nlinarith only [hrone, hr, sq_nonneg (vec3EuclideanNorm ξ - 1)]
      have hscalar : (2 : ℝ) ^ i ≤
          (2 : ℝ) ^ i * (1 + vec3EuclideanNorm ξ) := by
        calc
          (2 : ℝ) ^ i = (2 : ℝ) ^ i * 1 := by ring
          _ ≤ (2 : ℝ) ^ i * (1 + vec3EuclideanNorm ξ) :=
            mul_le_mul_of_nonneg_left (by linarith only [hr]) (by positivity)
      calc
        vec3EuclideanNorm ξ ^ 2 ≤ 1 := hone
        _ ≤ (2 : ℝ) ^ i * vec3EuclideanNorm ξ ^ i := hmul
        _ ≤ (2 : ℝ) ^ i * (1 + vec3EuclideanNorm ξ) *
            vec3EuclideanNorm ξ ^ i := by
          calc
            (2 : ℝ) ^ i * vec3EuclideanNorm ξ ^ i ≤
                ((2 : ℝ) ^ i * (1 + vec3EuclideanNorm ξ)) *
                  vec3EuclideanNorm ξ ^ i :=
              mul_le_mul_of_nonneg_right hscalar (pow_nonneg hr.le _)
            _ = _ := by ring
    · have hrone' : 1 < vec3EuclideanNorm ξ := lt_of_not_ge hrone
      by_cases hi1 : i = 1
      · subst i
        nlinarith only [hrone', hr, sq_nonneg (vec3EuclideanNorm ξ)]
      · have hi2 : 2 ≤ i := by omega
        have hpow : vec3EuclideanNorm ξ ^ 2 ≤ vec3EuclideanNorm ξ ^ i :=
          pow_le_pow_right₀ hrone'.le hi2
        have hpowtwo : 1 ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
        have hone : 1 ≤ 1 + vec3EuclideanNorm ξ := by linarith only [hr]
        have hscalar : 1 ≤ (2 : ℝ) ^ i * (1 + vec3EuclideanNorm ξ) := by
          calc
            1 ≤ (2 : ℝ) ^ i := hpowtwo
            _ ≤ (2 : ℝ) ^ i * (1 + vec3EuclideanNorm ξ) :=
              by
                simpa only [mul_one] using
                  mul_le_mul_of_nonneg_left hone
                    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i)
        calc
          vec3EuclideanNorm ξ ^ 2 ≤ vec3EuclideanNorm ξ ^ i := hpow
          _ ≤ (2 : ℝ) ^ i * (1 + vec3EuclideanNorm ξ) *
              vec3EuclideanNorm ξ ^ i := by
            calc
              vec3EuclideanNorm ξ ^ i = 1 * vec3EuclideanNorm ξ ^ i := by ring
              _ ≤ (2 : ℝ) ^ i * (1 + vec3EuclideanNorm ξ) *
                  vec3EuclideanNorm ξ ^ i :=
                mul_le_mul_of_nonneg_right hscalar (pow_nonneg hr.le _)
  rw [mul_div_assoc] at hgrowth
  exact hgrowth.trans (by
    calc
      complexEuclideanSquareGrowth i * (vec3EuclideanNorm ξ ^ 2 /
          vec3EuclideanNorm ξ ^ i) ≤
          complexEuclideanSquareGrowth i * (2 ^ i * (1 + vec3EuclideanNorm ξ)) :=
        mul_le_mul_of_nonneg_left hrbound (complexEuclideanSquareGrowth_nonneg i)
      _ = complexEuclideanSquareGrowth i * 2 ^ i *
          (1 + vec3EuclideanNorm ξ) := by ring)

private noncomputable def complexEuclideanSquareDifferenceDerivativeConstant
    (n : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (n + 1), complexEuclideanSquareGrowth i * 2 ^ i

private theorem complexEuclideanSquareDifferenceDerivativeConstant_nonneg (n : ℕ) :
    0 ≤ complexEuclideanSquareDifferenceDerivativeConstant n := by
  unfold complexEuclideanSquareDifferenceDerivativeConstant
  refine add_nonneg (by norm_num) (Finset.sum_nonneg fun i hi => ?_)
  exact mul_nonneg (complexEuclideanSquareGrowth_nonneg i) (pow_nonneg (by norm_num) _)

private theorem complexGaussian_iteratedFDeriv_bound (ξ : Vec3)
    {i : ℕ} (hi : i ≤ 7) (hξ : 1 / 2 ≤ vec3EuclideanNorm ξ) :
    ‖iteratedFDeriv ℝ i
      (fun y : Vec3 => Complex.exp (-complexEuclideanSquare y)) ξ‖ ≤
      (i.factorial : ℝ) * complexExpDerivativeBound *
        (complexEuclideanSquareDifferenceDerivativeConstant i *
          (1 + vec3EuclideanNorm ξ)) ^ i *
        Real.exp (-(vec3EuclideanNorm ξ ^ 2)) := by
  let D : ℝ := complexEuclideanSquareDifferenceDerivativeConstant i *
    (1 + vec3EuclideanNorm ξ)
  have hD : 1 ≤ D := by
    have hK := complexEuclideanSquareDifferenceDerivativeConstant_nonneg i
    have hKone : 1 ≤ complexEuclideanSquareDifferenceDerivativeConstant i := by
      unfold complexEuclideanSquareDifferenceDerivativeConstant
      have hsum : 0 ≤ ∑ j ∈ Finset.range (i + 1),
          complexEuclideanSquareGrowth j * 2 ^ j :=
        Finset.sum_nonneg fun j hj =>
          mul_nonneg (complexEuclideanSquareGrowth_nonneg j) (pow_nonneg (by norm_num) _)
      linarith only [hsum]
    have hone : 1 ≤ 1 + vec3EuclideanNorm ξ := by
      have hr := vec3EuclideanNorm_nonneg ξ
      linarith only [hr]
    dsimp [D]
    calc
      1 = 1 * 1 := by ring
      _ ≤ complexEuclideanSquareDifferenceDerivativeConstant i *
          (1 + vec3EuclideanNorm ξ) :=
        mul_le_mul hKone hone (by norm_num) hK
  have hK : ∀ j : ℕ, 1 ≤ j → j ≤ i →
      complexEuclideanSquareGrowth j * 2 ^ j ≤
        complexEuclideanSquareDifferenceDerivativeConstant i := by
    intro j hj1 hji
    unfold complexEuclideanSquareDifferenceDerivativeConstant
    have hsum := Finset.single_le_sum
      (s := Finset.range (i + 1))
      (f := fun m => complexEuclideanSquareGrowth m * 2 ^ m)
      (fun m hm => mul_nonneg (complexEuclideanSquareGrowth_nonneg m)
        (pow_nonneg (by norm_num) _))
      (Finset.mem_range.mpr (by omega : j < i + 1))
    linarith only [hsum]
  have hinner : ∀ j : ℕ, 1 ≤ j → j ≤ i →
      ‖iteratedFDeriv ℝ j (complexEuclideanSquareDifference ξ) ξ‖ ≤ D ^ j := by
    intro j hj1 hji
    have hj7 : j ≤ 7 := hji.trans hi
    have hbase := complexEuclideanSquareDifference_iteratedFDeriv_bound
      ξ hj1 hj7 hξ
    have hcoeff := hK j hj1 hji
    have hr : 0 ≤ 1 + vec3EuclideanNorm ξ := by positivity
    have hD' : complexEuclideanSquareGrowth j * 2 ^ j *
        (1 + vec3EuclideanNorm ξ) ≤ D := by
      dsimp [D]
      exact mul_le_mul_of_nonneg_right hcoeff hr
    calc
      ‖iteratedFDeriv ℝ j (complexEuclideanSquareDifference ξ) ξ‖ ≤
          complexEuclideanSquareGrowth j * 2 ^ j *
            (1 + vec3EuclideanNorm ξ) := hbase
      _ ≤ D := hD'
      _ ≤ D ^ j := by
        calc
          D = D ^ 1 := by simp
          _ ≤ D ^ j := pow_le_pow_right₀ hD hj1
  have hcomp : ‖iteratedFDeriv ℝ i
      (Complex.exp ∘ complexEuclideanSquareDifference ξ) ξ‖ ≤
      (i.factorial : ℝ) * complexExpDerivativeBound * D ^ i := by
    apply norm_iteratedFDeriv_comp_le Complex.contDiff_exp
      (complexEuclideanSquareDifference_contDiff ξ)
      (WithTop.coe_le_coe.mpr (le_top : (i : ℕ∞) ≤ (⊤ : ℕ∞))) ξ
    · intro j hji
      rw [complexEuclideanSquareDifference_zero]
      exact complexExp_iteratedFDeriv_at_zero_bound (hji.trans hi)
    · intro j hj1 hji
      exact hinner j hj1 hji
  have hCexp : Complex.exp (-complexEuclideanSquare ξ) =
      (Real.exp (-(vec3EuclideanNorm ξ ^ 2)) : ℂ) := by
    rw [complexEuclideanSquare, ← Complex.ofReal_neg, Complex.ofReal_exp]
  have hfun : (fun y : Vec3 => Complex.exp (-complexEuclideanSquare y)) =
      fun y => (Real.exp (-(vec3EuclideanNorm ξ ^ 2)) : ℝ) •
        Complex.exp (complexEuclideanSquareDifference ξ y) := by
    funext y
    calc
      Complex.exp (-complexEuclideanSquare y) =
          Complex.exp (-complexEuclideanSquare ξ) *
            Complex.exp (complexEuclideanSquareDifference ξ y) := by
        rw [← Complex.exp_add]
        congr 1
        simp only [complexEuclideanSquareDifference]
        ring
      _ = (Real.exp (-(vec3EuclideanNorm ξ ^ 2)) : ℝ) •
          Complex.exp (complexEuclideanSquareDifference ξ y) := by
        rw [hCexp, RCLike.real_smul_eq_coe_mul]
        rfl
  have hiTop : (↑(i : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have hExpCont : ContDiffAt ℝ (↑(i : ℕ∞) : WithTop ℕ∞)
      (fun y : Vec3 => Complex.exp (complexEuclideanSquareDifference ξ y)) ξ :=
    (Complex.contDiff_exp.comp (complexEuclideanSquareDifference_contDiff ξ)).contDiffAt.of_le
      hiTop
  have hIter := iteratedFDeriv_const_smul_apply'
    (f := fun y : Vec3 => Complex.exp (complexEuclideanSquareDifference ξ y))
    (a := Real.exp (-(vec3EuclideanNorm ξ ^ 2))) hExpCont
  have hIter' : iteratedFDeriv ℝ i
      (fun y : Vec3 => Real.exp (-(vec3EuclideanNorm ξ ^ 2)) •
        Complex.exp (complexEuclideanSquareDifference ξ y)) ξ =
      Real.exp (-(vec3EuclideanNorm ξ ^ 2)) •
        iteratedFDeriv ℝ i
          (fun y : Vec3 => Complex.exp (complexEuclideanSquareDifference ξ y)) ξ := by
    simpa only [Pi.smul_apply] using hIter
  rw [hfun, hIter', norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (-(vec3EuclideanNorm ξ ^ 2)) *
        ‖iteratedFDeriv ℝ i
          (Complex.exp ∘ complexEuclideanSquareDifference ξ) ξ‖ ≤
        Real.exp (-(vec3EuclideanNorm ξ ^ 2)) *
          ((i.factorial : ℝ) * complexExpDerivativeBound * D ^ i) :=
      mul_le_mul_of_nonneg_left hcomp (Real.exp_nonneg _)
    _ = (i.factorial : ℝ) * complexExpDerivativeBound * D ^ i *
        Real.exp (-(vec3EuclideanNorm ξ ^ 2)) := by ring

/-- A symbol-free bound for every fixed derivative of the standard frequency Gaussian. -/
theorem exists_norm_iteratedFDeriv_complexGaussian_le {i : ℕ} (hi : i ≤ 7) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3, 1 / 2 ≤ vec3EuclideanNorm ξ →
      ‖iteratedFDeriv ℝ i
        (fun y : Vec3 => Complex.exp (-complexEuclideanSquare y)) ξ‖ ≤
        C * (1 + vec3EuclideanNorm ξ) ^ i *
          Real.exp (-(vec3EuclideanNorm ξ ^ 2)) := by
  let C : ℝ := (i.factorial : ℝ) * complexExpDerivativeBound *
    complexEuclideanSquareDifferenceDerivativeConstant i ^ i
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by positivity) complexExpDerivativeBound_nonneg)
      (pow_nonneg (complexEuclideanSquareDifferenceDerivativeConstant_nonneg i) _)
  refine ⟨C, hC, ?_⟩
  intro ξ hξ
  have h := complexGaussian_iteratedFDeriv_bound ξ hi hξ
  dsimp [C]
  calc
    ‖iteratedFDeriv ℝ i
        (fun y : Vec3 => Complex.exp (-complexEuclideanSquare y)) ξ‖ ≤
        (i.factorial : ℝ) * complexExpDerivativeBound *
          (complexEuclideanSquareDifferenceDerivativeConstant i *
            (1 + vec3EuclideanNorm ξ)) ^ i *
          Real.exp (-(vec3EuclideanNorm ξ ^ 2)) := h
    _ = (i.factorial : ℝ) * complexExpDerivativeBound *
        complexEuclideanSquareDifferenceDerivativeConstant i ^ i *
        (1 + vec3EuclideanNorm ξ) ^ i *
        Real.exp (-(vec3EuclideanNorm ξ ^ 2)) := by rw [mul_pow]; ring


end CKN.Foundation.Euclidean
