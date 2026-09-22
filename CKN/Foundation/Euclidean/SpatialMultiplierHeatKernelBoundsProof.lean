-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelBounds
import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelHighSymbolBounds
import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelGaussianDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Fourier estimates for the spatial multiplier heat kernel

This module proves the pointwise estimates for smooth degree-one homogeneous
frequency symbols by cutting off the origin and integrating by parts in the
Fourier variable.
-/

open scoped BigOperators
open scoped FourierTransform
open Set MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier

private def frequencyPairingLinear :
    Vec3 →ₗ[ℝ] Vec3 →L[ℝ] ℝ where
  toFun := frequencyPairingCLM
  map_add' a b := by
    ext x
    change frequencyPairingCLM (a + b) x =
      frequencyPairingCLM a x + frequencyPairingCLM b x
    rw [frequencyPairingCLM_apply, frequencyPairingCLM_apply,
      frequencyPairingCLM_apply]
    simp only [Pi.add_apply]
    calc
      ∑ j : Fin 3, (a j + b j) * x j =
          ∑ j : Fin 3, (a j * x j + b j * x j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ j : Fin 3, a j * x j) +
          (∑ j : Fin 3, b j * x j) := by
            rw [← Finset.sum_add_distrib]
  map_smul' c a := by
    ext x
    change frequencyPairingCLM (c • a) x = c • frequencyPairingCLM a x
    rw [frequencyPairingCLM_apply, frequencyPairingCLM_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      ∑ j : Fin 3, (c * a j) * x j =
          c * ∑ j : Fin 3, a j * x j := by
            calc
              ∑ j : Fin 3, (c * a j) * x j =
                  ∑ j : Fin 3, c * (a j * x j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = c * ∑ j : Fin 3, a j * x j := by rw [Finset.mul_sum]
      _ = c • ∑ j : Fin 3, a j * x j := by rw [smul_eq_mul]

private theorem frequencyPairingLinear_norm_le (ξ : Vec3) :
    ‖frequencyPairingCLM ξ‖ ≤ 6 * ‖ξ‖ := by
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  calc
    ‖frequencyPairingCLM ξ‖ ≤ 3 * vec3EuclideanNorm ξ :=
      frequencyPairingCLM_norm_le ξ
    _ ≤ 3 * (Real.sqrt 3 * ‖ξ‖) := by
      exact mul_le_mul_of_nonneg_left (vec3EuclideanNorm_le_sqrt_three_mul_norm ξ)
        (by norm_num)
    _ ≤ 6 * ‖ξ‖ := by
      calc
        3 * (Real.sqrt 3 * ‖ξ‖) ≤ 3 * (2 * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg ξ)) (by norm_num)
        _ = 6 * ‖ξ‖ := by ring

private def frequencyPairingBilinear :
    Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ :=
  frequencyPairingLinear.mkContinuous 6 frequencyPairingLinear_norm_le

private theorem frequencyPairingBilinear_apply (a b : Vec3) :
    frequencyPairingBilinear a b = ∑ j : Fin 3, a j * b j := by
  rfl

private theorem frequencyPairingBilinear_symm (a b : Vec3) :
    frequencyPairingBilinear a b = frequencyPairingBilinear b a := by
  rw [frequencyPairingBilinear_apply, frequencyPairingBilinear_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The bilinear form giving the inverse Fourier phase in the paper's normalization. -/
def frequencyFourierBilinear :
    Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ :=
  (-((2 * Real.pi)⁻¹)) • frequencyPairingBilinear

theorem frequencyFourierBilinear_apply (a b : Vec3) :
    frequencyFourierBilinear a b =
      -((2 * Real.pi)⁻¹) * ∑ j : Fin 3, a j * b j := by
  simp [frequencyFourierBilinear, frequencyPairingBilinear_apply]

/-- The inverse Fourier phase is symmetric in its two vector variables. -/
theorem frequencyFourierBilinear_symm (a b : Vec3) :
    frequencyFourierBilinear a b = frequencyFourierBilinear b a := by
  rw [frequencyFourierBilinear_apply, frequencyFourierBilinear_apply]
  have hsum : (∑ j : Fin 3, a j * b j : ℝ) =
      ∑ j : Fin 3, b j * a j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]

/-- The normalized vector Fourier integral is the positive-sign exponential integral. -/
theorem vectorFourierIntegral_eq_exp_integral (f : Vec3 → ℂ) (x : Vec3) :
    fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂ f x =
      ∫ ξ : Vec3, Complex.exp
        (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) * f ξ := by
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  rw [frequencyFourierBilinear_apply]
  have hsum : (∑ j : Fin 3, ξ j * x j : ℝ) =
      ∑ j : Fin 3, x j * ξ j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  push_cast
  field_simp
  simp only [smul_eq_mul]

/-- The unit-scale Gaussian in frequency space. -/
def standardFrequencyGaussian (ξ : Vec3) : ℂ :=
  Complex.exp (-complexEuclideanSquare ξ)

/-- The unit-scale frequency Gaussian is smooth. -/
theorem standardFrequencyGaussian_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) standardFrequencyGaussian :=
  Complex.contDiff_exp.comp complexEuclideanSquare_contDiff.neg

/-- A positive-time Gaussian in frequency space. -/
def scaledFrequencyGaussian (t : ℝ) (ξ : Vec3) : ℂ :=
  Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))

/-- Gaussian frequency scaling is composition with the positive square-root dilation. -/
theorem scaledFrequencyGaussian_eq_comp_smul {t : ℝ} (ht : 0 < t) :
    scaledFrequencyGaussian t =
      standardFrequencyGaussian ∘ fun ξ : Vec3 => Real.sqrt t • ξ := by
  funext ξ
  have hsq : complexEuclideanSquare (Real.sqrt t • ξ) =
      ((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ) := by
    rw [complexEuclideanSquare_homogeneous]
    · rw [Real.sq_sqrt ht.le]
      simp [complexEuclideanSquare, RCLike.real_smul_eq_coe_mul]
    · exact Real.sqrt_pos.2 ht
  simp only [scaledFrequencyGaussian, standardFrequencyGaussian, Function.comp_apply]
  rw [← hsq]

/-- Each fixed derivative of the standard Gaussian is bounded on the half ball. -/
theorem exists_norm_iteratedFDeriv_standardFrequencyGaussian_on_ball
    (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3, vec3EuclideanNorm ξ ≤ 1 / 2 →
      ‖iteratedFDeriv ℝ i standardFrequencyGaussian ξ‖ ≤ C := by
  have hderiv : Continuous (fun ξ : Vec3 =>
      iteratedFDeriv ℝ i standardFrequencyGaussian ξ) :=
    standardFrequencyGaussian_contDiff.continuous_iteratedFDeriv (by simp)
  have hcompact : IsCompact (Metric.closedBall (0 : Vec3) 1) :=
    isCompact_closedBall (0 : Vec3) 1
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (hderiv.continuousOn.mono (Set.subset_univ _))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ξ hξ
  have hnorm : ‖ξ‖ ≤ 1 := by
    calc
      ‖ξ‖ ≤ vec3EuclideanNorm ξ := norm_le_vec3EuclideanNorm ξ
      _ ≤ 1 / 2 := hξ
      _ ≤ 1 := by norm_num
  have hball : ξ ∈ Metric.closedBall (0 : Vec3) 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
  exact (hC ξ hball).trans (le_max_left _ _)

/-- For time at most one, Gaussian derivatives on the outer annulus have uniform inverse-radius bounds. -/
theorem exists_norm_iteratedFDeriv_scaledFrequencyGaussian_le
    {i : ℕ} (hi : i ≤ 7) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ ξ : Vec3,
      1 / 2 ≤ vec3EuclideanNorm ξ →
      ‖iteratedFDeriv ℝ i (scaledFrequencyGaussian t) ξ‖ ≤
        C * (vec3EuclideanNorm ξ ^ i)⁻¹ := by
  obtain ⟨Clocal, hClocal, hlocal⟩ :=
    exists_norm_iteratedFDeriv_standardFrequencyGaussian_on_ball i
  obtain ⟨Cfar, hCfar, hfar⟩ := exists_norm_iteratedFDeriv_complexGaussian_le hi
  let Ctail : ℝ := Cfar * 3 ^ i *
    (1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i))
  let C : ℝ := max Clocal Ctail
  have hCtail : 0 ≤ Ctail := by dsimp [Ctail]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht ht1 ξ hξ
  let a : ℝ := Real.sqrt t
  let r : ℝ := vec3EuclideanNorm ξ
  let s : ℝ := a * r
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hr : 0 < r := by linarith only [hξ]
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsval : vec3EuclideanNorm (a • ξ) = s := by
    dsimp [s, a]
    rw [vec3EuclideanNorm_smul, abs_of_nonneg (Real.sqrt_nonneg t)]
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
  by_cases hsmall : s ≤ 1 / 2
  · have hloc := hlocal (a • ξ) (by simpa [hsval] using hsmall)
    have ha_le : a ≤ r⁻¹ := by
      dsimp [s] at hsmall
      have hmul : a * r ≤ 1 := by nlinarith only [hsmall]
      simpa [one_div] using (le_div_iff₀ hr).2 hmul
    have hpow : a ^ i ≤ (r ^ i)⁻¹ := by
      calc
        a ^ i ≤ (r⁻¹) ^ i := pow_le_pow_left₀ ha ha_le _
        _ = (r ^ i)⁻¹ := by rw [inv_pow]
    have hfinal : a ^ i *
        ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
        Clocal * (r ^ i)⁻¹ := by
      calc
        a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
            a ^ i * Clocal := mul_le_mul_of_nonneg_left hloc (pow_nonneg ha _)
        _ ≤ (r ^ i)⁻¹ * Clocal :=
          mul_le_mul_of_nonneg_right hpow hClocal
        _ = Clocal * (r ^ i)⁻¹ := by ring
    calc
      ‖iteratedFDeriv ℝ i (scaledFrequencyGaussian t) ξ‖ ≤
          Clocal * (r ^ i)⁻¹ := by rw [hnormscaled]; exact hfinal
      _ ≤ C * (r ^ i)⁻¹ := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (pow_nonneg hr.le _))
  · have hslarge : 1 / 2 ≤ s := le_of_not_ge hsmall
    have hfar' := hfar (a • ξ) (by simpa [hsval] using hslarge)
    have h1s : 1 + s ≤ 3 * s := by nlinarith only [hslarge]
    have hpolyExp := power_mul_exp_bound (a := 1) (r := s)
      (by norm_num) hs (2 * i)
    have hexp_le : Real.exp (-(1 / 2 * s ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith only [sq_nonneg s])
    have hpoly : s ^ i * (1 + s) ^ i * Real.exp (-(s ^ 2)) ≤
        3 ^ i * (1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i)) := by
      calc
        s ^ i * (1 + s) ^ i * Real.exp (-(s ^ 2)) ≤
            s ^ i * (3 * s) ^ i * Real.exp (-(s ^ 2)) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hs]) h1s i)
                  (pow_nonneg hs _)) (Real.exp_nonneg _)
        _ = 3 ^ i * (s ^ (2 * i) * Real.exp (-(s ^ 2))) := by
              rw [mul_pow]
              ring
        _ ≤ 3 ^ i * (1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i)) := by
              calc
                _ ≤ 3 ^ i *
                    ((1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i)) *
                      Real.exp (-(1 / 2 * s ^ 2))) :=
                  mul_le_mul_of_nonneg_left
                  (by simpa only [one_mul, div_one, Nat.cast_mul, Nat.cast_ofNat]
                    using hpolyExp)
                    (pow_nonneg (by norm_num) _)
                _ ≤ 3 ^ i * (1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i)) := by
                  have hK : 0 ≤ 1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i) := by positivity
                  calc
                    3 ^ i *
                        ((1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i)) *
                          Real.exp (-(1 / 2 * s ^ 2))) ≤
                        3 ^ i *
                          ((1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i)) * 1) :=
                      mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_left hexp_le hK)
                        (pow_nonneg (by norm_num) _)
                    _ = _ := by ring
    have hscale : a ^ i = s ^ i * (r ^ i)⁻¹ := by
      dsimp [s]
      rw [mul_pow]
      field_simp [hr.ne']
    have hfinal : a ^ i * ((1 + s) ^ i * Real.exp (-(s ^ 2))) ≤
        (r ^ i)⁻¹ *
          (3 ^ i * (1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i))) := by
      rw [hscale]
      have hnonneg : 0 ≤ (r ^ i)⁻¹ := inv_nonneg.mpr (pow_nonneg hr.le _)
      calc
        s ^ i * (r ^ i)⁻¹ * ((1 + s) ^ i * Real.exp (-(s ^ 2))) =
            (r ^ i)⁻¹ * (s ^ i * (1 + s) ^ i * Real.exp (-(s ^ 2))) := by ring
        _ ≤ (r ^ i)⁻¹ *
            (3 ^ i * (1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i))) :=
          mul_le_mul_of_nonneg_left hpoly hnonneg
    have hfar'' :
        ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
        Cfar * (1 + s) ^ i * Real.exp (-(s ^ 2)) := by
      change ‖iteratedFDeriv ℝ i
          (fun y : Vec3 => Complex.exp (-complexEuclideanSquare y)) (a • ξ)‖ ≤ _
      simpa [hsval] using hfar'
    have hbig : a ^ i *
        ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
        Ctail * (r ^ i)⁻¹ := by
      calc
        _ ≤ a ^ i * (Cfar * (1 + s) ^ i * Real.exp (-(s ^ 2))) :=
          mul_le_mul_of_nonneg_left hfar'' (pow_nonneg ha _)
        _ = Cfar * ((r ^ i)⁻¹ *
            (s ^ i * (1 + s) ^ i * Real.exp (-(s ^ 2)))) := by
          rw [hscale]
          ring
        _ = Cfar * (a ^ i * ((1 + s) ^ i * Real.exp (-(s ^ 2)))) := by
          rw [hscale]
          ring
        _ ≤ Cfar * ((r ^ i)⁻¹ *
            (3 ^ i * (1 + 2 ^ (2 * i) * (2 * i : ℝ) ^ (2 * i)))) :=
          mul_le_mul_of_nonneg_left hfinal hCfar
        _ = Ctail * (r ^ i)⁻¹ := by dsimp [Ctail]; ring
    calc
      ‖iteratedFDeriv ℝ i (scaledFrequencyGaussian t) ξ‖ ≤
          Ctail * (r ^ i)⁻¹ := by rw [hnormscaled]; exact hbig
      _ ≤ C * (r ^ i)⁻¹ := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _)
          (inv_nonneg.mpr (pow_nonneg hr.le _))

/-- The scaled frequency Gaussian is smooth in frequency. -/
theorem scaledFrequencyGaussian_contDiff (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledFrequencyGaussian t) := by
  have hfun : scaledFrequencyGaussian t =
      fun ξ : Vec3 => Complex.exp (-((t : ℂ) * complexEuclideanSquare ξ)) := by
    funext ξ
    simp [scaledFrequencyGaussian, complexEuclideanSquare]
  rw [hfun]
  exact Complex.contDiff_exp.comp
    ((contDiff_const.mul complexEuclideanSquare_contDiff).neg)

/-- Every fixed Gaussian derivative has a polynomial-times-Gaussian bound. -/
theorem exists_norm_iteratedFDeriv_scaledFrequencyGaussian_global
    {i : ℕ} (hi : i ≤ 7) (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3,
      ‖iteratedFDeriv ℝ i (scaledFrequencyGaussian t) ξ‖ ≤
        C * (1 + vec3EuclideanNorm ξ) ^ i *
          Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
  obtain ⟨Clocal, hClocal, hlocal⟩ :=
    exists_norm_iteratedFDeriv_standardFrequencyGaussian_on_ball i
  obtain ⟨Cfar, hCfar, hfar⟩ := exists_norm_iteratedFDeriv_complexGaussian_le hi
  let a : ℝ := Real.sqrt t
  let Csmall : ℝ := a ^ i * Clocal * Real.exp (1 / 4)
  let Cbig : ℝ := a ^ i * Cfar * max 1 a ^ i
  let C : ℝ := max Csmall Cbig
  have ha : 0 < a := by dsimp [a]; positivity
  have ha0 : 0 ≤ a := ha.le
  have hCsmall : 0 ≤ Csmall := by dsimp [Csmall]; positivity
  have hCbig : 0 ≤ Cbig := by dsimp [Cbig]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ξ
  let r : ℝ := vec3EuclideanNorm ξ
  let s : ℝ := a * r
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
    rw [hscaled, norm_smul, Real.norm_of_nonneg (pow_nonneg ha0 _)]
  have honeR : 1 ≤ (1 + r) ^ i :=
    one_le_pow₀ (by linarith only [hr])
  by_cases hsmall : s ≤ 1 / 2
  · have hloc := hlocal (a • ξ) (by simpa [hsval] using hsmall)
    have hexp : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-s ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hsmall, hs]
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
            a ^ i * Clocal := mul_le_mul_of_nonneg_left hloc (pow_nonneg ha0 _)
        _ ≤ a ^ i * Clocal * (Real.exp (1 / 4) * Real.exp (-s ^ 2)) :=
          by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hfactor
                (mul_nonneg (pow_nonneg ha0 _) hClocal)
        _ ≤ a ^ i * Clocal * (Real.exp (1 / 4) *
              ((1 + r) ^ i * Real.exp (-s ^ 2))) := by
          have hinner : Real.exp (-s ^ 2) ≤ (1 + r) ^ i * Real.exp (-s ^ 2) := by
            calc
              Real.exp (-s ^ 2) = 1 * Real.exp (-s ^ 2) := by ring
              _ ≤ (1 + r) ^ i * Real.exp (-s ^ 2) :=
                mul_le_mul_of_nonneg_right honeR (Real.exp_nonneg _)
          have houter := mul_le_mul_of_nonneg_left hinner (Real.exp_nonneg (1 / 4))
          have hcoeff : 0 ≤ a ^ i * Clocal :=
            mul_nonneg (pow_nonneg ha0 _) hClocal
          calc
            a ^ i * Clocal * (Real.exp (1 / 4) * Real.exp (-s ^ 2)) =
                (a ^ i * Clocal) * (Real.exp (1 / 4) * Real.exp (-s ^ 2)) := by ring
            _ ≤ (a ^ i * Clocal) *
                (Real.exp (1 / 4) * ((1 + r) ^ i * Real.exp (-s ^ 2))) :=
              mul_le_mul_of_nonneg_left houter hcoeff
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
    have hlinear : 1 + s ≤ max 1 a * (1 + r) := by
      by_cases ha1 : a ≤ 1
      · rw [max_eq_left ha1]
        dsimp [s]
        nlinarith only [ha1, hr]
      · have ha1' : 1 ≤ a := le_of_not_ge ha1
        rw [max_eq_right ha1']
        dsimp [s]
        nlinarith only [ha1', hr]
    have hfarBound :
        a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
          Cbig * (1 + r) ^ i * Real.exp (-s ^ 2) := by
      have hpow : (1 + s) ^ i ≤ (max 1 a) ^ i * (1 + r) ^ i := by
        calc
          (1 + s) ^ i ≤ (max 1 a * (1 + r)) ^ i :=
            pow_le_pow_left₀ (by positivity) hlinear i
          _ = (max 1 a) ^ i * (1 + r) ^ i := by rw [mul_pow]
      have hcoeff : 0 ≤ a ^ i * Cfar := mul_nonneg (pow_nonneg ha0 _) hCfar
      calc
        a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
            a ^ i * (Cfar * (1 + s) ^ i * Real.exp (-s ^ 2)) :=
          mul_le_mul_of_nonneg_left hfar'' (pow_nonneg ha0 _)
        _ ≤ a ^ i * Cfar * (max 1 a) ^ i *
              (1 + r) ^ i * Real.exp (-s ^ 2) := by
          calc
            a ^ i * (Cfar * (1 + s) ^ i * Real.exp (-s ^ 2)) =
                (a ^ i * Cfar) * (1 + s) ^ i * Real.exp (-s ^ 2) := by ring
            _ ≤ (a ^ i * Cfar) * ((max 1 a) ^ i * (1 + r) ^ i) *
                Real.exp (-s ^ 2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow hcoeff) (Real.exp_nonneg _)
            _ = a ^ i * Cfar * (max 1 a) ^ i *
                (1 + r) ^ i * Real.exp (-s ^ 2) := by ring
        _ = Cbig * (1 + r) ^ i * Real.exp (-s ^ 2) := by
          rfl
    rw [hnormscaled]
    have hfinal := calc
      a ^ i * ‖iteratedFDeriv ℝ i standardFrequencyGaussian (a • ξ)‖ ≤
          Cbig * (1 + r) ^ i * Real.exp (-s ^ 2) := hfarBound
      _ ≤ C * (1 + r) ^ i * Real.exp (-s ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith only [hr]) _))
          (Real.exp_nonneg _)
    simpa [r, hsq] using hfinal

/-- Iterated integration by parts bounds a Fourier integral by the derivative's L¹ norm. -/
theorem norm_fourierIntegral_by_iteratedFDeriv
    (L : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ) (f : Vec3 → ℂ) (n : ℕ)
    (hL : ∀ a b : Vec3, L a b = L b a)
    (hf : ContDiff ℝ (n : ℕ∞) f)
    (h'f : ∀ k : ℕ, k ≤ n → Integrable (iteratedFDeriv ℝ k f) volume)
    (v w : Vec3) (hv : ‖v‖ ≤ 1) :
    (2 * Real.pi) ^ n * |L w v| ^ n *
        ‖fourierIntegral 𝐞 volume L.toLinearMap₁₂ f w‖ ≤
      ∫ ξ : Vec3, ‖iteratedFDeriv ℝ n f ξ‖ := by
  have hfourier := VectorFourier.fourierIntegral_iteratedFDeriv
    (L := L) (μ := volume) hf (fun k hk => h'f k (by exact_mod_cast hk))
    (n := n) le_rfl
  have hpoint := congrFun hfourier w
  have hEval := congrArg (fun A => A (fun _ : Fin n => v)) hpoint
  have hnorm := VectorFourier.norm_fourierIntegral_le_integral_norm
    (e := 𝐞) (μ := volume) (L := L.toLinearMap₁₂)
    (f := iteratedFDeriv ℝ n f) w
  have hleft :
      ‖fourierIntegral 𝐞 volume L.toLinearMap₁₂
        (iteratedFDeriv ℝ n f) w‖ ≤
        ∫ ξ : Vec3, ‖iteratedFDeriv ℝ n f ξ‖ := by
    simpa using hnorm
  have hop :
      ‖(fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (iteratedFDeriv ℝ n f) w) (fun _ : Fin n => v)‖ ≤
        ‖fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (iteratedFDeriv ℝ n f) w‖ * ‖v‖ ^ n := by
    simpa [Finset.prod_const, Fintype.card_fin] using
      (ContinuousMultilinearMap.le_opNorm
        (fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (iteratedFDeriv ℝ n f) w) (fun _ : Fin n => v))
  have hvpow : ‖v‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
  have hEvalNorm := congrArg norm hEval
  have hRhsNorm :
      ‖fourierPowSMulRight (-L.flip)
        (fourierIntegral 𝐞 volume L.toLinearMap₁₂ f) w n
        (fun _ : Fin n => v)‖ =
      (2 * Real.pi) ^ n * |L w v| ^ n *
        ‖fourierIntegral 𝐞 volume L.toLinearMap₁₂ f w‖ := by
    simp [VectorFourier.fourierPowSMulRight_apply,
      ContinuousLinearMap.flip_apply, hL]
    ring
  rw [hRhsNorm] at hEvalNorm
  calc
    (2 * Real.pi) ^ n * |L w v| ^ n *
        ‖fourierIntegral 𝐞 volume L.toLinearMap₁₂ f w‖ =
        ‖(fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (iteratedFDeriv ℝ n f) w) (fun _ : Fin n => v)‖ := hEvalNorm.symm
    _ ≤ ‖fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (iteratedFDeriv ℝ n f) w‖ * ‖v‖ ^ n := hop
    _ ≤ ‖fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (iteratedFDeriv ℝ n f) w‖ :=
      by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hvpow (norm_nonneg
            (fourierIntegral 𝐞 volume L.toLinearMap₁₂
              (iteratedFDeriv ℝ n f) w))
    _ ≤ ∫ ξ : Vec3, ‖iteratedFDeriv ℝ n f ξ‖ := hleft

end CKN.Foundation.Euclidean
