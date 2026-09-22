-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelBoundsProof
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Oscillatory estimates for homogeneous multiplier kernels

This module develops the integration-by-parts estimates for the smooth
high-frequency part of a homogeneous multiplier.
-/

open scoped BigOperators
open MeasureTheory Set Module

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier

/-- Derivatives of the cut-off homogeneous symbol have polynomial growth on all frequency space. -/
theorem exists_norm_iteratedFDeriv_highFrequencySymbol_global_bound
    {τ : Vec3 → ℂ} (d k : ℕ)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3,
      ‖iteratedFDeriv ℝ k (highFrequencySymbol τ) ξ‖ ≤
        C * (1 + vec3EuclideanNorm ξ) ^ d := by
  obtain ⟨Cc, hCc, hcompact⟩ :=
    exists_norm_iteratedFDeriv_high_bound_on_twoBall hτ k
  obtain ⟨Ca, hCa, hannulus⟩ :=
    exists_norm_iteratedFDeriv_high_bound_on_annulus d k hτ hhom
  let C : ℝ := max Cc Ca
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ξ
  let r : ℝ := vec3EuclideanNorm ξ
  have hr : 0 ≤ r := vec3EuclideanNorm_nonneg ξ
  have hpowone : 1 ≤ (1 + r) ^ d := one_le_pow₀ (by linarith only [hr])
  by_cases hlarge : 2 < r
  · have hrhalf : 1 / 2 ≤ r := by linarith only [hlarge]
    have htail := hannulus ξ (by simpa [r] using hrhalf)
    have hpowr : r ^ d / r ^ k ≤ (1 + r) ^ d := by
      rw [div_le_iff₀ (pow_pos (by linarith only [hlarge]) k)]
      have hk : 1 ≤ r ^ k := one_le_pow₀ (by linarith only [hlarge])
      have hbase : r ^ d ≤ (1 + r) ^ d :=
        pow_le_pow_left₀ hr (by linarith only [hr]) d
      calc
        r ^ d = r ^ d * 1 := by ring
        _ ≤ r ^ d * r ^ k :=
          mul_le_mul_of_nonneg_left hk (pow_nonneg hr d)
        _ ≤ (1 + r) ^ d * r ^ k :=
          mul_le_mul_of_nonneg_right hbase (pow_nonneg hr k)
    calc
      ‖iteratedFDeriv ℝ k (highFrequencySymbol τ) ξ‖ ≤ Ca * (r ^ d / r ^ k) := by
        calc
          ‖iteratedFDeriv ℝ k (highFrequencySymbol τ) ξ‖ ≤
              Ca * r ^ d / r ^ k := htail
          _ = Ca * (r ^ d / r ^ k) := by ring
      _ ≤ C * (1 + r) ^ d := by
        exact mul_le_mul (le_max_right _ _) hpowr
          (div_nonneg (pow_nonneg hr _) (pow_nonneg hr _)) hC
  · have hsmall : r ≤ 2 := le_of_not_gt hlarge
    have h := hcompact ξ (by simpa [r] using hsmall)
    calc
      ‖iteratedFDeriv ℝ k (highFrequencySymbol τ) ξ‖ ≤ Cc := h
      _ ≤ C := le_max_left _ _
      _ ≤ C * (1 + r) ^ d := by
        calc
          C = C * 1 := by ring
          _ ≤ C * (1 + r) ^ d := mul_le_mul_of_nonneg_left hpowone hC

private theorem integrable_one_add_euclideanNorm_pow_gaussian
    {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Integrable (fun ξ : Vec3 => (1 + vec3EuclideanNorm ξ) ^ m *
      Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) volume := by
  have h0 := integrable_frequency_gaussian_moment_all ht 0
  have hm := integrable_frequency_gaussian_moment_all ht m
  have h0' : Integrable (fun ξ : Vec3 =>
      Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) volume := by
    simpa only [pow_zero, one_mul] using h0
  have hsum : Integrable (fun ξ : Vec3 =>
      Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) +
        vec3EuclideanNorm ξ ^ m * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) volume := by
    exact h0'.add hm
  have hmajor : Integrable (fun ξ : Vec3 =>
      (2 : ℝ) ^ m * (Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) +
        vec3EuclideanNorm ξ ^ m * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)))) volume :=
    hsum.const_mul _
  have hmeas : Measurable (fun ξ : Vec3 => (1 + vec3EuclideanNorm ξ) ^ m *
      Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) := by
    unfold vec3EuclideanNorm
    fun_prop
  refine Integrable.mono' hmajor hmeas.aestronglyMeasurable ?_
  filter_upwards with ξ
  let r := vec3EuclideanNorm ξ
  have hr : 0 ≤ r := vec3EuclideanNorm_nonneg ξ
  have he : 0 ≤ Real.exp (-(t * r ^ 2)) := Real.exp_nonneg _
  have hpow : (1 + r) ^ m ≤ (2 : ℝ) ^ m * (1 + r ^ m) := by
    by_cases hsmall : r ≤ 1
    · have hbase : 1 + r ≤ 2 := by linarith only [hsmall]
      have hpow' := pow_le_pow_left₀ (by positivity) hbase m
      calc
        (1 + r) ^ m ≤ 2 ^ m := hpow'
        _ ≤ 2 ^ m * (1 + r ^ m) := by
          calc
            2 ^ m = 2 ^ m * 1 := by ring
            _ ≤ 2 ^ m * (1 + r ^ m) := by
              exact mul_le_mul_of_nonneg_left
                (by have := pow_nonneg hr m; linarith only [this])
                (pow_nonneg (by norm_num) _)
    · have hlarge : 1 ≤ r := le_of_not_ge hsmall
      have hbase : 1 + r ≤ 2 * r := by linarith only [hlarge]
      have hpow' := pow_le_pow_left₀ (by positivity) hbase m
      calc
        (1 + r) ^ m ≤ (2 * r) ^ m := hpow'
        _ = 2 ^ m * r ^ m := by rw [mul_pow]
        _ ≤ 2 ^ m * (1 + r ^ m) := by
          have hrm : 0 ≤ r ^ m := pow_nonneg hr m
          exact mul_le_mul_of_nonneg_left
            (by linarith only [hrm])
            (pow_nonneg (by norm_num) _)
  have hnormLeft : ‖(1 + r) ^ m * Real.exp (-(t * r ^ 2))‖ =
      (1 + r) ^ m * Real.exp (-(t * r ^ 2)) :=
    Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity) _) he)
  rw [hnormLeft]
  have hfinal := calc
    (1 + r) ^ m * Real.exp (-(t * r ^ 2)) ≤
        (2 : ℝ) ^ m * (1 + r ^ m) * Real.exp (-(t * r ^ 2)) :=
      mul_le_mul_of_nonneg_right hpow he
    _ = (2 : ℝ) ^ m *
        (Real.exp (-(t * r ^ 2)) + r ^ m * Real.exp (-(t * r ^ 2))) := by ring
  simpa [r] using hfinal

private theorem exists_norm_iteratedFDeriv_scaledFrequencyGaussian_uniform
    {i : ℕ} (hi : i ≤ 7) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ ξ : Vec3,
      ‖iteratedFDeriv ℝ i (scaledFrequencyGaussian t) ξ‖ ≤
        C * (1 + vec3EuclideanNorm ξ) ^ i *
          Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
  obtain ⟨Clocal, hClocal, hlocal⟩ :=
    exists_norm_iteratedFDeriv_standardFrequencyGaussian_on_ball i
  obtain ⟨Cfar, hCfar, hfar⟩ := exists_norm_iteratedFDeriv_complexGaussian_le hi
  let Csmall : ℝ := Clocal * Real.exp (1 / 4)
  let C : ℝ := max Csmall Cfar
  have hCsmall : 0 ≤ Csmall := by dsimp [Csmall]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht ht1 ξ
  let a : ℝ := Real.sqrt t
  let r : ℝ := vec3EuclideanNorm ξ
  let s : ℝ := a * r
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact Real.sqrt_le_one.mpr ht1
  have hr : 0 ≤ r := vec3EuclideanNorm_nonneg ξ
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsval : vec3EuclideanNorm (a • ξ) = s := by
    dsimp [s, a]
    rw [vec3EuclideanNorm_smul, abs_of_nonneg (Real.sqrt_nonneg t)]
  have hsq : s ^ 2 = t * r ^ 2 := by
    dsimp [s, a, r]
    rw [mul_pow, Real.sq_sqrt ht.le]
  have hscaled : iteratedFDeriv ℝ i (scaledFrequencyGaussian t) ξ =
      a ^ i • iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ) := by
    rw [scaledFrequencyGaussian_eq_comp_smul ht]
    have hiTop : (↑(i : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
      WithTop.coe_le_coe.mpr le_top
    exact congrFun (iteratedFDeriv_comp_const_smul a
      (standardFrequencyGaussian_contDiff.of_le hiTop)) ξ
  have hnormscaled :
      ‖iteratedFDeriv ℝ i (scaledFrequencyGaussian t) ξ‖ =
        a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ := by
    rw [hscaled, norm_smul, Real.norm_of_nonneg (pow_nonneg ha _)]
  have honeR : 1 ≤ (1 + r) ^ i := one_le_pow₀ (by linarith only [hr])
  have haPow : a ^ i ≤ 1 := pow_le_one₀ ha ha1
  by_cases hsmall : s ≤ 1 / 2
  · have hloc := hlocal (a • ξ) (by simpa [hsval] using hsmall)
    have hfactor : 1 ≤ Real.exp (1 / 4) * Real.exp (-s ^ 2) := by
      rw [← Real.exp_add]
      have hu : 0 ≤ 1 / 4 - s ^ 2 := by nlinarith only [hsmall, hs]
      have hule := Real.add_one_le_exp (1 / 4 - s ^ 2)
      calc
        1 ≤ 1 + (1 / 4 - s ^ 2) := by linarith only [hu]
        _ ≤ Real.exp (1 / 4 - s ^ 2) := by simpa only [add_comm] using hule
    have hlocalBound :
        a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
          Csmall * (1 + r) ^ i * Real.exp (-s ^ 2) := by
      calc
        a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
            a ^ i * Clocal := mul_le_mul_of_nonneg_left hloc (pow_nonneg ha _)
        _ ≤ Clocal := by
          calc
            a ^ i * Clocal ≤ 1 * Clocal := mul_le_mul_of_nonneg_right haPow hClocal
            _ = Clocal := by ring
        _ ≤ Clocal * (Real.exp (1 / 4) * Real.exp (-s ^ 2)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hClocal
        _ ≤ Clocal * (Real.exp (1 / 4) *
              ((1 + r) ^ i * Real.exp (-s ^ 2))) := by
          have hinner : Real.exp (-s ^ 2) ≤ (1 + r) ^ i * Real.exp (-s ^ 2) := by
            calc
              Real.exp (-s ^ 2) = 1 * Real.exp (-s ^ 2) := by ring
              _ ≤ (1 + r) ^ i * Real.exp (-s ^ 2) :=
                mul_le_mul_of_nonneg_right honeR (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner (Real.exp_nonneg _)) hClocal
        _ = Csmall * (1 + r) ^ i * Real.exp (-s ^ 2) := by
          dsimp [Csmall]
          ring
    rw [hnormscaled]
    have hfinal := calc
      a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
          Csmall * (1 + r) ^ i * Real.exp (-s ^ 2) := hlocalBound
      _ ≤ C * (1 + r) ^ i * Real.exp (-s ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith only [hr]) _))
          (Real.exp_nonneg _)
    simpa [r, hsq] using hfinal
  · have hslarge : 1 / 2 ≤ s := le_of_not_ge hsmall
    have hfar' := hfar (a • ξ) (by simpa [hsval] using hslarge)
    have hfar'' :
        ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
          Cfar * (1 + s) ^ i * Real.exp (-s ^ 2) := by
      change ‖iteratedFDeriv ℝ i
        (fun y : Vec3 => Complex.exp (-complexEuclideanSquare y)) (a • ξ)‖ ≤ _
      simpa only [hsval] using hfar'
    have hlinear : 1 + s ≤ 1 + r := by
      dsimp [s]
      nlinarith only [ha1, hr]
    have hfarBound :
        a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
          Cfar * (1 + r) ^ i * Real.exp (-s ^ 2) := by
      calc
        a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
            a ^ i * (Cfar * (1 + s) ^ i * Real.exp (-s ^ 2)) :=
          mul_le_mul_of_nonneg_left hfar'' (pow_nonneg ha _)
        _ ≤ Cfar * (1 + r) ^ i * Real.exp (-s ^ 2) := by
          calc
            a ^ i * (Cfar * (1 + s) ^ i * Real.exp (-s ^ 2)) ≤
                1 * (Cfar * (1 + r) ^ i * Real.exp (-s ^ 2)) := by
              gcongr
            _ = Cfar * (1 + r) ^ i * Real.exp (-s ^ 2) := by ring
    rw [hnormscaled]
    have hfinal := calc
      a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
          Cfar * (1 + r) ^ i * Real.exp (-s ^ 2) := hfarBound
      _ ≤ C * (1 + r) ^ i * Real.exp (-s ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith only [hr]) _))
          (Real.exp_nonneg _)
    simpa [r, hsq] using hfinal

private noncomputable def highFrequencySymbolDerivativeConstant
    {τ : Vec3 → ℂ} (d k : ℕ)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) : ℝ :=
  Classical.choose (exists_norm_iteratedFDeriv_highFrequencySymbol_global_bound
    (τ := τ) d k hτ hhom)

private theorem highFrequencySymbolDerivativeConstant_spec
    {τ : Vec3 → ℂ} (d k : ℕ)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3)
    ) (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    0 ≤ highFrequencySymbolDerivativeConstant d k hτ hhom ∧
      ∀ ξ : Vec3, ‖iteratedFDeriv ℝ k (highFrequencySymbol τ) ξ‖ ≤
        highFrequencySymbolDerivativeConstant d k hτ hhom *
          (1 + vec3EuclideanNorm ξ) ^ d :=
  Classical.choose_spec (exists_norm_iteratedFDeriv_highFrequencySymbol_global_bound
    (τ := τ) d k hτ hhom)

private noncomputable def scaledGaussianPolynomialConstant
    (k : ℕ) (hk : k ≤ 7) (t : ℝ) (ht : 0 < t) : ℝ :=
  Classical.choose (exists_norm_iteratedFDeriv_scaledFrequencyGaussian_global hk t ht)

private theorem scaledGaussianPolynomialConstant_spec
    (k : ℕ) (hk : k ≤ 7) (t : ℝ) (ht : 0 < t) :
    0 ≤ scaledGaussianPolynomialConstant k hk t ht ∧
      ∀ ξ : Vec3, ‖iteratedFDeriv ℝ k (scaledFrequencyGaussian t) ξ‖ ≤
        scaledGaussianPolynomialConstant k hk t ht *
          (1 + vec3EuclideanNorm ξ) ^ k *
            Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) :=
  Classical.choose_spec (exists_norm_iteratedFDeriv_scaledFrequencyGaussian_global hk t ht)

private noncomputable def scaledGaussianUniformConstant (k : ℕ) (hk : k ≤ 7) : ℝ :=
  Classical.choose (exists_norm_iteratedFDeriv_scaledFrequencyGaussian_uniform hk)

private theorem scaledGaussianUniformConstant_spec (k : ℕ) (hk : k ≤ 7) :
    0 ≤ scaledGaussianUniformConstant k hk ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ ξ : Vec3,
        ‖iteratedFDeriv ℝ k (scaledFrequencyGaussian t) ξ‖ ≤
          scaledGaussianUniformConstant k hk * (1 + vec3EuclideanNorm ξ) ^ k *
            Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) :=
  Classical.choose_spec (exists_norm_iteratedFDeriv_scaledFrequencyGaussian_uniform hk)

private noncomputable def highFrequencySymbolAnnulusDerivativeConstant
    {τ : Vec3 → ℂ} (d k : ℕ)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) : ℝ :=
  Classical.choose (exists_norm_iteratedFDeriv_high_bound_on_annulus d k hτ hhom)

private theorem highFrequencySymbolAnnulusDerivativeConstant_spec
    {τ : Vec3 → ℂ} (d k : ℕ)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    0 ≤ highFrequencySymbolAnnulusDerivativeConstant d k hτ hhom ∧
      ∀ ξ : Vec3, 1 / 2 ≤ vec3EuclideanNorm ξ →
        ‖iteratedFDeriv ℝ k (highFrequencySymbol τ) ξ‖ ≤
          highFrequencySymbolAnnulusDerivativeConstant d k hτ hhom *
            vec3EuclideanNorm ξ ^ d / vec3EuclideanNorm ξ ^ k :=
  Classical.choose_spec (exists_norm_iteratedFDeriv_high_bound_on_annulus d k hτ hhom)

private noncomputable def scaledGaussianAnnulusDerivativeConstant
    (k : ℕ) (hk : k ≤ 7) : ℝ :=
  Classical.choose (exists_norm_iteratedFDeriv_scaledFrequencyGaussian_le hk)

private theorem scaledGaussianAnnulusDerivativeConstant_spec
    (k : ℕ) (hk : k ≤ 7) :
    0 ≤ scaledGaussianAnnulusDerivativeConstant k hk ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ ξ : Vec3,
        1 / 2 ≤ vec3EuclideanNorm ξ →
          ‖iteratedFDeriv ℝ k (scaledFrequencyGaussian t) ξ‖ ≤
            scaledGaussianAnnulusDerivativeConstant k hk *
              (vec3EuclideanNorm ξ ^ k)⁻¹ :=
  Classical.choose_spec (exists_norm_iteratedFDeriv_scaledFrequencyGaussian_le hk)

def highDampedFrequencyFunction (τ : Vec3 → ℂ) (t : ℝ) (ξ : Vec3) : ℂ :=
  highFrequencySymbol τ ξ * scaledFrequencyGaussian t ξ

theorem highDampedFrequencyFunction_contDiff
    {τ : Vec3 → ℂ} (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (highDampedFrequencyFunction τ t) :=
  (highFrequencySymbol_contDiff hτ).mul (scaledFrequencyGaussian_contDiff t)

private noncomputable def highDampedCompactDerivativeConstant
    {τ : Vec3 → ℂ} (d n : ℕ) (hn : n ≤ 7)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    highFrequencySymbolDerivativeConstant d i hτ hhom *
      scaledGaussianUniformConstant (n - i) (by omega) *
        (3 : ℝ) ^ (d + (n - i))

private noncomputable def highDampedTailDerivativeConstant
    {τ : Vec3 → ℂ} (d n : ℕ) (hn : n ≤ 7)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    highFrequencySymbolAnnulusDerivativeConstant d i hτ hhom *
      scaledGaussianAnnulusDerivativeConstant (n - i) (by omega)

private theorem highDampedCompactDerivativeConstant_nonneg
    {τ : Vec3 → ℂ} (d n : ℕ) (hn : n ≤ 7)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    0 ≤ highDampedCompactDerivativeConstant d n hn hτ hhom := by
  unfold highDampedCompactDerivativeConstant
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (highFrequencySymbolDerivativeConstant_spec d i hτ hhom).1)
      (scaledGaussianUniformConstant_spec (n - i) (by omega)).1)
    (pow_nonneg (by norm_num) _)

private theorem highDampedTailDerivativeConstant_nonneg
    {τ : Vec3 → ℂ} (d n : ℕ) (hn : n ≤ 7)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    0 ≤ highDampedTailDerivativeConstant d n hn hτ hhom := by
  unfold highDampedTailDerivativeConstant
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (highFrequencySymbolAnnulusDerivativeConstant_spec
      d i hτ hhom).1)
    ((scaledGaussianAnnulusDerivativeConstant_spec (n - i) (by omega)).1)

private theorem highDampedFrequency_compact_bound
    {τ : Vec3 → ℂ} (d n : ℕ) (hn : n ≤ 7)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (ξ : Vec3)
    (hξ : vec3EuclideanNorm ξ ≤ 2) :
        ‖iteratedFDeriv ℝ n (highDampedFrequencyFunction τ t) ξ‖ ≤
      highDampedCompactDerivativeConstant d n hn hτ hhom := by
  let r := vec3EuclideanNorm ξ
  let b := 1 + r
  let e := Real.exp (-(t * r ^ 2))
  have hr : 0 ≤ r := vec3EuclideanNorm_nonneg ξ
  have hb1 : 1 ≤ b := by dsimp [b]; linarith only [hr]
  have hb0 : 0 ≤ b := by linarith only [hb1]
  have hb3 : b ≤ 3 := by dsimp [b]; linarith only [hξ]
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have he1 : e ≤ 1 := by
    dsimp [e]
    exact Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg r, ht, hr])
  have hprod := norm_iteratedFDeriv_mul_le
    (highFrequencySymbol_contDiff hτ) (scaledFrequencyGaussian_contDiff t) ξ
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hterms : ∀ i : ℕ, i ∈ Finset.range (n + 1) →
      (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) (scaledFrequencyGaussian t) ξ‖ ≤
        (n.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianUniformConstant (n - i) (by omega) *
            (3 : ℝ) ^ (d + (n - i)) := by
    intro i hi
    have hik : i ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    let j := n - i
    have hj : j ≤ 7 := by dsimp [j]; omega
    have hτi := (highFrequencySymbolDerivativeConstant_spec d i hτ hhom).2 ξ
    have hgi := (scaledGaussianUniformConstant_spec j hj).2 t ht ht1 ξ
    have hτi' : ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ ≤
        highFrequencySymbolDerivativeConstant d i hτ hhom * b ^ d := by
      simpa [b, r] using hτi
    have hgi' : ‖iteratedFDeriv ℝ j (scaledFrequencyGaussian t) ξ‖ ≤
        scaledGaussianUniformConstant j hj * b ^ j * e := by
      simpa [j, b, r, e] using hgi
    have hbd : b ^ d ≤ 3 ^ d := pow_le_pow_left₀ (by linarith only [hr]) hb3 d
    have hbj : b ^ j ≤ 3 ^ j := pow_le_pow_left₀ (by linarith only [hr]) hb3 j
    have hcoeff : 0 ≤ (n.choose i : ℝ) *
        highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianUniformConstant j hj :=
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (highFrequencySymbolDerivativeConstant_spec
          d i hτ hhom).1)
        (scaledGaussianUniformConstant_spec j hj).1
    calc
      (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) (scaledFrequencyGaussian t) ξ‖ ≤
        (n.choose i : ℝ) *
          (highFrequencySymbolDerivativeConstant d i hτ hhom * b ^ d) *
          ‖iteratedFDeriv ℝ j (scaledFrequencyGaussian t) ξ‖ := by
        rw [show n - i = j by rfl]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hτi' (Nat.cast_nonneg _)) (norm_nonneg _)
      _ ≤ (n.choose i : ℝ) *
          (highFrequencySymbolDerivativeConstant d i hτ hhom * b ^ d) *
          (scaledGaussianUniformConstant j hj * b ^ j * e) := by
        exact mul_le_mul_of_nonneg_left hgi'
          (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (highFrequencySymbolDerivativeConstant_spec d i hτ hhom).1
              (pow_nonneg hb0 _)))
      _ = ((n.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianUniformConstant j hj) * (b ^ d * b ^ j * e) := by ring
      _ ≤ ((n.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianUniformConstant j hj) * (3 : ℝ) ^ (d + j) := by
        have hpow : b ^ d * b ^ j * e ≤ (3 : ℝ) ^ (d + j) := by
          calc
            b ^ d * b ^ j * e = (b ^ d * b ^ j) * e := by ring
            _ ≤ (b ^ d * b ^ j) * 1 :=
              mul_le_mul_of_nonneg_left he1
                (mul_nonneg (pow_nonneg hb0 d) (pow_nonneg hb0 j))
            _ = b ^ d * b ^ j := by ring
            _ ≤ 3 ^ d * 3 ^ j := mul_le_mul hbd hbj
              (pow_nonneg hb0 j) (pow_nonneg (by norm_num) d)
            _ = 3 ^ (d + j) := by rw [← pow_add]
        exact mul_le_mul_of_nonneg_left hpow hcoeff
      _ = (n.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianUniformConstant j hj * 3 ^ (d + j) := by ring
  have hsum := Finset.sum_le_sum hterms
  change ‖iteratedFDeriv ℝ n (highDampedFrequencyFunction τ t) ξ‖ ≤ _ at hprod
  have hres := calc
    ‖iteratedFDeriv ℝ n (highDampedFrequencyFunction τ t) ξ‖ ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) (scaledFrequencyGaussian t) ξ‖ := hprod
    _ ≤ highDampedCompactDerivativeConstant d n hn hτ hhom := by
      simpa [highDampedCompactDerivativeConstant] using hsum
  exact hres

private theorem highDampedFrequency_tail_bound
    {τ : Vec3 → ℂ} (d : ℕ) (hd : d ≤ 3)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (ξ : Vec3)
    (hξ : 1 / 2 ≤ vec3EuclideanNorm ξ) :
    ‖iteratedFDeriv ℝ (d + 4) (highDampedFrequencyFunction τ t) ξ‖ ≤
      highDampedTailDerivativeConstant d (d + 4) (by omega) hτ hhom *
        (vec3EuclideanNorm ξ ^ 4)⁻¹ := by
  let n := d + 4
  let r := vec3EuclideanNorm ξ
  have hr : 0 < r := by linarith only [hξ]
  have hn : n ≤ 7 := by dsimp [n]; omega
  have hprod := norm_iteratedFDeriv_mul_le
    (highFrequencySymbol_contDiff hτ) (scaledFrequencyGaussian_contDiff t) ξ
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hterms : ∀ i : ℕ, i ∈ Finset.range (n + 1) →
      (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) (scaledFrequencyGaussian t) ξ‖ ≤
        ((n.choose i : ℝ) *
          highFrequencySymbolAnnulusDerivativeConstant d i hτ hhom *
          scaledGaussianAnnulusDerivativeConstant (n - i) (by omega)) *
          (r ^ 4)⁻¹ := by
    intro i hi
    have hik : i ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    let j := n - i
    have hj : j ≤ 7 := by dsimp [j, n]; omega
    have hτi := (highFrequencySymbolAnnulusDerivativeConstant_spec d i hτ hhom).2 ξ
      (by simpa [r] using show 1 / 2 ≤ r from hξ)
    have hgi := (scaledGaussianAnnulusDerivativeConstant_spec j hj).2 t ht ht1 ξ
      (by simpa [r] using show 1 / 2 ≤ r from hξ)
    have hpower : (r ^ d / r ^ i) * (r ^ j)⁻¹ = (r ^ 4)⁻¹ := by
      have hsum : i + j = n := by dsimp [j]; omega
      calc
        (r ^ d / r ^ i) * (r ^ j)⁻¹ = r ^ d / (r ^ i * r ^ j) := by
          field_simp [pow_ne_zero i hr.ne', pow_ne_zero j hr.ne']
        _ = r ^ d / r ^ n := by rw [← pow_add, hsum]
        _ = r ^ d / (r ^ d * r ^ 4) := by
          rw [show n = d + 4 by dsimp [n]]
          rw [pow_add]
        _ = (r ^ 4)⁻¹ := by
          field_simp [hr.ne']
    have hcoeff : 0 ≤ (n.choose i : ℝ) *
        highFrequencySymbolAnnulusDerivativeConstant d i hτ hhom *
          scaledGaussianAnnulusDerivativeConstant j hj :=
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (highFrequencySymbolAnnulusDerivativeConstant_spec
          d i hτ hhom).1)
        (scaledGaussianAnnulusDerivativeConstant_spec j hj).1
    have hτcoef : 0 ≤ highFrequencySymbolAnnulusDerivativeConstant d i hτ hhom *
        r ^ d / r ^ i :=
      div_nonneg
        (mul_nonneg (highFrequencySymbolAnnulusDerivativeConstant_spec d i hτ hhom).1
          (pow_nonneg hr.le d))
        (pow_nonneg hr.le i)
    calc
      (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) (scaledFrequencyGaussian t) ξ‖ ≤
        (n.choose i : ℝ) *
          (highFrequencySymbolAnnulusDerivativeConstant d i hτ hhom * r ^ d / r ^ i) *
          ‖iteratedFDeriv ℝ j (scaledFrequencyGaussian t) ξ‖ := by
        rw [show n - i = j by rfl]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hτi (Nat.cast_nonneg _)) (norm_nonneg _)
      _ ≤ (n.choose i : ℝ) *
          (highFrequencySymbolAnnulusDerivativeConstant d i hτ hhom * r ^ d / r ^ i) *
          (scaledGaussianAnnulusDerivativeConstant j hj * (r ^ j)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hgi
          (mul_nonneg (Nat.cast_nonneg _) hτcoef)
      _ = ((n.choose i : ℝ) *
          highFrequencySymbolAnnulusDerivativeConstant d i hτ hhom *
          scaledGaussianAnnulusDerivativeConstant j hj) *
          ((r ^ d / r ^ i) * (r ^ j)⁻¹) := by ring
      _ = ((n.choose i : ℝ) *
          highFrequencySymbolAnnulusDerivativeConstant d i hτ hhom *
          scaledGaussianAnnulusDerivativeConstant j hj) * (r ^ 4)⁻¹ := by rw [hpower]
  have hsum := Finset.sum_le_sum hterms
  change ‖iteratedFDeriv ℝ n (highDampedFrequencyFunction τ t) ξ‖ ≤ _ at hprod
  have hres := calc
    ‖iteratedFDeriv ℝ n (highDampedFrequencyFunction τ t) ξ‖ ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) (scaledFrequencyGaussian t) ξ‖ := hprod
    _ ≤ highDampedTailDerivativeConstant d n hn hτ hhom * (r ^ 4)⁻¹ := by
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1),
            (((n.choose i : ℝ) *
              highFrequencySymbolAnnulusDerivativeConstant d i hτ hhom *
              scaledGaussianAnnulusDerivativeConstant (n - i) (by omega)) *
              (r ^ 4)⁻¹) := hsum
        _ = highDampedTailDerivativeConstant d n hn hτ hhom * (r ^ 4)⁻¹ := by
          dsimp [highDampedTailDerivativeConstant]
          rw [Finset.sum_mul]
  simpa [n, r] using hres

private theorem exists_norm_iteratedFDeriv_highDampedFrequency_bound
    {τ : Vec3 → ℂ} (d k : ℕ) (hk : k ≤ 7)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ)
    (t : ℝ) (ht : 0 < t) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ξ : Vec3,
      ‖iteratedFDeriv ℝ k (highDampedFrequencyFunction τ t) ξ‖ ≤
        K * (1 + vec3EuclideanNorm ξ) ^ (d + k) *
          Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
  let K : ℝ := ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
      scaledGaussianPolynomialConstant (k - i) (by omega) t ht
  have hK : 0 ≤ K := by
    dsimp [K]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (highFrequencySymbolDerivativeConstant_spec
        d i hτ hhom).1)
      (scaledGaussianPolynomialConstant_spec (k - i) (by omega) t ht).1
  refine ⟨K, hK, ?_⟩
  intro ξ
  let r : ℝ := vec3EuclideanNorm ξ
  let b : ℝ := 1 + r
  let e : ℝ := Real.exp (-(t * r ^ 2))
  have hr : 0 ≤ r := vec3EuclideanNorm_nonneg ξ
  have hb : 1 ≤ b := by dsimp [b]; linarith only [hr]
  have he : 0 ≤ e := Real.exp_nonneg _
  have hprod := norm_iteratedFDeriv_mul_le
    (highFrequencySymbol_contDiff hτ) (scaledFrequencyGaussian_contDiff t) ξ
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hterms : ∀ i : ℕ, i ∈ Finset.range (k + 1) →
      (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ *
          ‖iteratedFDeriv ℝ (k - i) (scaledFrequencyGaussian t) ξ‖ ≤
        ((k.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianPolynomialConstant (k - i) (by omega) t ht) *
          (b ^ (d + k) * e) := by
    intro i hi
    have hik : i ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    let j := k - i
    have hjk : j ≤ k := by dsimp [j]; omega
    have hτi := (highFrequencySymbolDerivativeConstant_spec d i hτ hhom).2 ξ
    have hgi := (scaledGaussianPolynomialConstant_spec j (by omega) t ht).2 ξ
    have hτi' : ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ ≤
        highFrequencySymbolDerivativeConstant d i hτ hhom * b ^ d := by
      simpa [b, r] using hτi
    have hgi' : ‖iteratedFDeriv ℝ j (scaledFrequencyGaussian t) ξ‖ ≤
        scaledGaussianPolynomialConstant j (by omega) t ht * b ^ j * e := by
      simpa [j, b, r, e] using hgi
    have hpow : b ^ d * b ^ j ≤ b ^ (d + k) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hb (by omega)
    have hcoef : 0 ≤ (k.choose i : ℝ) *
        highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianPolynomialConstant j (by omega) t ht :=
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (highFrequencySymbolDerivativeConstant_spec
          d i hτ hhom).1)
        (scaledGaussianPolynomialConstant_spec j (by omega) t ht).1
    calc
      (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ *
          ‖iteratedFDeriv ℝ (k - i) (scaledFrequencyGaussian t) ξ‖ ≤
        (k.choose i : ℝ) *
          (highFrequencySymbolDerivativeConstant d i hτ hhom * b ^ d) *
          ‖iteratedFDeriv ℝ j (scaledFrequencyGaussian t) ξ‖ := by
        rw [show k - i = j by rfl]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hτi' (Nat.cast_nonneg _))
          (norm_nonneg _)
      _ ≤ (k.choose i : ℝ) *
          (highFrequencySymbolDerivativeConstant d i hτ hhom * b ^ d) *
          (scaledGaussianPolynomialConstant j (by omega) t ht * b ^ j * e) := by
        exact mul_le_mul_of_nonneg_left hgi'
          (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (highFrequencySymbolDerivativeConstant_spec d i hτ hhom).1
              (pow_nonneg (by linarith only [hr]) _)))
      _ = ((k.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianPolynomialConstant j (by omega) t ht) *
          (b ^ d * b ^ j * e) := by ring
      _ ≤ ((k.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianPolynomialConstant j (by omega) t ht) *
          (b ^ (d + k) * e) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow he) hcoef
      _ = ((k.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianPolynomialConstant j (by omega) t ht) *
          (b ^ (d + k) * e) := rfl
  have hsum := Finset.sum_le_sum hterms
  change ‖iteratedFDeriv ℝ k (highDampedFrequencyFunction τ t) ξ‖ ≤ _ at hprod
  have hbound := calc
    ‖iteratedFDeriv ℝ k (highDampedFrequencyFunction τ t) ξ‖ ≤
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (highFrequencySymbol τ) ξ‖ *
          ‖iteratedFDeriv ℝ (k - i) (scaledFrequencyGaussian t) ξ‖ := by
      exact hprod
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        ((k.choose i : ℝ) * highFrequencySymbolDerivativeConstant d i hτ hhom *
          scaledGaussianPolynomialConstant (k - i) (by omega) t ht) *
          (b ^ (d + k) * e) := hsum
    _ = K * (b ^ (d + k) * e) := by
      dsimp [K]
      rw [Finset.sum_mul]
  simpa [b, e, r, mul_assoc] using hbound

theorem integrable_iteratedFDeriv_highDampedFrequency
    {τ : Vec3 → ℂ} (d k : ℕ) (hk : k ≤ 7)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ)
    (t : ℝ) (ht : 0 < t) :
    Integrable (iteratedFDeriv ℝ k (highDampedFrequencyFunction τ t)) volume := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_norm_iteratedFDeriv_highDampedFrequency_bound d k hk hτ hhom t ht
  have hmoment := integrable_one_add_euclideanNorm_pow_gaussian ht (d + k)
  have hmajor : Integrable (fun ξ : Vec3 => K *
      ((1 + vec3EuclideanNorm ξ) ^ (d + k) *
        Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)))) volume := by
    exact hmoment.const_mul K
  have hcont : Continuous (fun ξ : Vec3 =>
      iteratedFDeriv ℝ k (highDampedFrequencyFunction τ t) ξ) :=
    (highDampedFrequencyFunction_contDiff hτ t).continuous_iteratedFDeriv (by simp)
  refine Integrable.mono' hmajor hcont.aestronglyMeasurable ?_
  filter_upwards with ξ
  calc
    ‖iteratedFDeriv ℝ k (highDampedFrequencyFunction τ t) ξ‖ ≤
        K * (1 + vec3EuclideanNorm ξ) ^ (d + k) *
          Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := hbound ξ
    _ = K * ((1 + vec3EuclideanNorm ξ) ^ (d + k) *
          Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) := by ring

/-- A uniform compact-frequency bound for the critical derivatives of a damped symbol. -/
theorem exists_uniform_norm_iteratedFDeriv_highDampedFrequency_compact
    {τ : Vec3 → ℂ} (d n : ℕ) (hn : n ≤ 7)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ ξ : Vec3,
      vec3EuclideanNorm ξ ≤ 2 →
      ‖iteratedFDeriv ℝ n (highDampedFrequencyFunction τ t) ξ‖ ≤ C := by
  let C := highDampedCompactDerivativeConstant d n hn hτ hhom
  have hC : 0 ≤ C := by
    exact highDampedCompactDerivativeConstant_nonneg d n hn hτ hhom
  exact ⟨C, hC, by
    intro t ht ht1 ξ hξ
    exact highDampedFrequency_compact_bound d n hn hτ hhom t ht ht1 ξ hξ⟩

/-- A uniform annular bound for the critical derivatives of a damped symbol. -/
theorem exists_uniform_norm_iteratedFDeriv_highDampedFrequency_tail
    {τ : Vec3 → ℂ} (d : ℕ) (hd : d ≤ 3)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ ξ : Vec3,
      1 / 2 ≤ vec3EuclideanNorm ξ →
      ‖iteratedFDeriv ℝ (d + 4) (highDampedFrequencyFunction τ t) ξ‖ ≤
        C * (vec3EuclideanNorm ξ ^ 4)⁻¹ := by
  let C := highDampedTailDerivativeConstant d (d + 4) (by omega) hτ hhom
  have hC : 0 ≤ C := by
    exact highDampedTailDerivativeConstant_nonneg d (d + 4) (by omega) hτ hhom
  exact ⟨C, hC, by
    intro t ht ht1 ξ hξ
    exact highDampedFrequency_tail_bound d hd hτ hhom t ht ht1 ξ hξ⟩

end CKN.Foundation.Euclidean
