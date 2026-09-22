-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelScaling
import CKN.Foundation.Sobolev.Ambient.Basis
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Spatial differentiability of multiplier heat kernels
-/

open scoped BigOperators FourierTransform
open MeasureTheory

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier

/-- The frequency amplitude whose inverse Fourier transform is the multiplier kernel. -/
def multiplierHeatFrequencyAmplitude (σ : Vec3 → ℂ) (t : ℝ) (ξ : Vec3) : ℂ :=
  σ ξ * scaledFrequencyGaussian t ξ

/-- Multiplication of a symbol by one spatial frequency. -/
def spatialMultiplierCoordinateSymbol (σ : Vec3 → ℂ) (j : Fin 3) (ξ : Vec3) : ℂ :=
  (Complex.I * (ξ j : ℂ)) * σ ξ

/-- A smooth degree-`d` symbol remains smooth after one coordinate-frequency factor. -/
theorem spatialMultiplierCoordinateSymbol_contDiffOn
    {σ : Vec3 → ℂ} (j : Fin 3)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (spatialMultiplierCoordinateSymbol σ j) ({0}ᶜ : Set Vec3) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun ξ : Vec3 => Complex.I * (ξ j : ℂ)) := by
    have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec3 => ξ j) := by fun_prop
    have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec3 => (ξ j : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hproj
    exact contDiff_const.mul hcoord
  exact hc.contDiffOn.mul hσ

/-- Homogeneity degree increases by one after a spatial frequency factor. -/
theorem spatialMultiplierCoordinateSymbol_homogeneous
    {σ : Vec3 → ℂ} (d : ℕ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    (j : Fin 3) :
    ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      spatialMultiplierCoordinateSymbol σ j (a • ξ) =
        (a ^ (d + 1) : ℝ) • spatialMultiplierCoordinateSymbol σ j ξ := by
  intro a ha ξ
  simp only [spatialMultiplierCoordinateSymbol, Pi.smul_apply, hhom a ha ξ]
  simp only [RCLike.real_smul_eq_coe_mul]
  push_cast
  rw [pow_succ]
  ac_rfl

private theorem multiplierHeatFrequencyAmplitude_aestronglyMeasurable
    {σ : Vec3 → ℂ}
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (t : ℝ) : AEStronglyMeasurable (multiplierHeatFrequencyAmplitude σ t) volume := by
  have hσmeas : AEStronglyMeasurable σ volume := by
    have h := hσ.continuousOn.aestronglyMeasurable
      (μ := volume) (measurableSet_singleton (0 : Vec3)).compl
    rwa [restrict_compl_singleton (0 : Vec3)] at h
  have hg : Continuous (scaledFrequencyGaussian t) :=
    (scaledFrequencyGaussian_contDiff t).continuous
  exact hσmeas.mul hg.aestronglyMeasurable

private theorem scaledFrequencyGaussian_norm_local {t : ℝ} (ξ : Vec3) :
    ‖scaledFrequencyGaussian t ξ‖ = Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
  rw [scaledFrequencyGaussian, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]

private theorem norm_multiplierHeatFrequencyAmplitude
    (σ : Vec3 → ℂ) (t : ℝ) (ξ : Vec3) :
    ‖multiplierHeatFrequencyAmplitude σ t ξ‖ =
      ‖σ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
  rw [multiplierHeatFrequencyAmplitude, norm_mul, scaledFrequencyGaussian_norm_local]

private theorem integrable_multiplierHeatFrequencyAmplitude
    {σ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (multiplierHeatFrequencyAmplitude σ t) volume := by
  have hbase := integrable_spatialMultiplierHeatIntegrand_of_homogeneous
    d hd hσ hhom 0 ht
  have hEq : multiplierHeatFrequencyAmplitude σ t =
      spatialMultiplierHeatIntegrand σ 0 t := by
    funext ξ
    simp [multiplierHeatFrequencyAmplitude, spatialMultiplierHeatIntegrand,
      scaledFrequencyGaussian]
  rw [hEq]
  exact hbase

private theorem integrable_weighted_multiplierHeatFrequencyAmplitude
    {σ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Vec3 => ‖ξ‖ *
      ‖multiplierHeatFrequencyAmplitude σ t ξ‖) volume := by
  obtain ⟨Cσ, hCσ, hσbound⟩ := exists_norm_homogeneousSymbol_le d hd hσ hhom
  have hmajor : Integrable (fun ξ : Vec3 => Cσ *
      (vec3EuclideanNorm ξ ^ (d + 1) *
        Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)))) volume :=
    (integrable_frequency_gaussian_moment_all ht (d + 1)).const_mul Cσ
  have hmeas : AEStronglyMeasurable (fun ξ : Vec3 => ‖ξ‖ *
      ‖multiplierHeatFrequencyAmplitude σ t ξ‖) volume :=
    continuous_norm.aestronglyMeasurable.mul
      (multiplierHeatFrequencyAmplitude_aestronglyMeasurable hσ t).norm
  refine hmajor.mono' hmeas ?_
  filter_upwards with ξ
  change ‖‖ξ‖ * ‖multiplierHeatFrequencyAmplitude σ t ξ‖‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [norm_multiplierHeatFrequencyAmplitude]
  have hr := vec3EuclideanNorm_nonneg ξ
  have hcoord : ‖ξ‖ ≤ vec3EuclideanNorm ξ := norm_le_vec3EuclideanNorm ξ
  have hprod : ‖ξ‖ * ‖σ ξ‖ ≤ Cσ * vec3EuclideanNorm ξ ^ (d + 1) := by
    calc
      ‖ξ‖ * ‖σ ξ‖ ≤ vec3EuclideanNorm ξ *
          (Cσ * vec3EuclideanNorm ξ ^ d) :=
        mul_le_mul hcoord (hσbound ξ) (norm_nonneg (σ ξ)) hr
      _ = Cσ * vec3EuclideanNorm ξ ^ (d + 1) := by rw [pow_succ]; ring
  calc
    ‖ξ‖ * (‖σ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) ≤
        (Cσ * vec3EuclideanNorm ξ ^ (d + 1)) *
          Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) :=
      calc
        _ = (‖ξ‖ * ‖σ ξ‖) * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
    _ = Cσ * (vec3EuclideanNorm ξ ^ (d + 1) *
        Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) := by ring

private theorem integrable_fourierDerivativeAmplitude
    {σ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Vec3 => fourierSMulRight frequencyFourierBilinear
      (multiplierHeatFrequencyAmplitude σ t) ξ) volume := by
  let f := multiplierHeatFrequencyAmplitude σ t
  have hweighted := integrable_weighted_multiplierHeatFrequencyAmplitude d hd hσ hhom ht
  refine (hweighted.const_mul (2 * Real.pi * ‖frequencyFourierBilinear‖)).mono'
    (multiplierHeatFrequencyAmplitude_aestronglyMeasurable hσ t |>.fourierSMulRight) ?_
  filter_upwards with ξ
  exact (norm_fourierSMulRight_le frequencyFourierBilinear f ξ).trans
    (le_of_eq (by dsimp [f]; ring))

/-- The multiplier heat kernel is differentiable in space at every positive time. -/
theorem spatialMultiplierHeatKernel_hasFDerivAt_spatial
    {σ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    {t : ℝ} (ht : 0 < t) (x : Vec3) :
    HasFDerivAt (fun y => spatialMultiplierHeatKernel σ y t)
      (fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) x := by
  have hInt := integrable_multiplierHeatFrequencyAmplitude d hd hσ hhom ht
  have hWeighted := integrable_weighted_multiplierHeatFrequencyAmplitude d hd hσ hhom ht
  have hhas := VectorFourier.hasFDerivAt_fourierIntegral frequencyFourierBilinear
    hInt hWeighted x
  let N : ℂ := (2 * Real.pi : ℂ) ^ (-3 : ℤ)
  have hkernel (y : Vec3) : spatialMultiplierHeatKernel σ y t =
      N * fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂
        (multiplierHeatFrequencyAmplitude σ t) y := by
    simp [spatialMultiplierHeatKernel, ht]
    rw [vectorFourierIntegral_eq_exp_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    simp [multiplierHeatFrequencyAmplitude, spatialMultiplierHeatIntegrand,
      scaledFrequencyGaussian]
    ring
  have hfun : (fun y => spatialMultiplierHeatKernel σ y t) =
      fun y => N * fourierIntegral 𝐞 volume
        frequencyFourierBilinear.toLinearMap₁₂
          (multiplierHeatFrequencyAmplitude σ t) y := by
    funext y
    exact hkernel y
  rw [hfun]
  convert hhas.const_mul N using 1
  exact (hhas.const_mul N).fderiv

/-- The spatial derivative of the kernel is the kernel of the coordinate-multiplied symbol. -/
theorem spatialMultiplierHeatKernel_fderiv_apply_basis
    {σ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    {t : ℝ} (ht : 0 < t) (x : Vec3) (j : Fin 3) :
    (fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j) =
      spatialMultiplierHeatKernel (spatialMultiplierCoordinateSymbol σ j) x t := by
  have hInt := integrable_multiplierHeatFrequencyAmplitude d hd hσ hhom ht
  have hWeighted := integrable_weighted_multiplierHeatFrequencyAmplitude d hd hσ hhom ht
  have hSMul := integrable_fourierDerivativeAmplitude d hd hσ hhom ht
  let f := multiplierHeatFrequencyAmplitude σ t
  let N : ℂ := (2 * Real.pi : ℂ) ^ (-3 : ℤ)
  have hkernel (y : Vec3) : spatialMultiplierHeatKernel σ y t =
      N * fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂ f y := by
    simp [spatialMultiplierHeatKernel, ht]
    rw [vectorFourierIntegral_eq_exp_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    simp [f, multiplierHeatFrequencyAmplitude, spatialMultiplierHeatIntegrand,
      scaledFrequencyGaussian]
    ring
  have hhas := VectorFourier.hasFDerivAt_fourierIntegral frequencyFourierBilinear
    hInt hWeighted x
  have hfun : (fun y => spatialMultiplierHeatKernel σ y t) =
      fun y => N * fourierIntegral 𝐞 volume
        frequencyFourierBilinear.toLinearMap₁₂ f y := funext hkernel
  have hdiff : fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x =
      N • fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂
        (fourierSMulRight frequencyFourierBilinear f) x := by
    calc
      fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x =
          fderiv ℝ (fun y => N * fourierIntegral 𝐞 volume
            frequencyFourierBilinear.toLinearMap₁₂ f y) x :=
        congrArg (fun g : Vec3 → ℂ => fderiv ℝ g x) hfun
      _ = N • fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂
          (fourierSMulRight frequencyFourierBilinear f) x := by
        simpa only [f] using (hhas.const_mul N).fderiv
  have hEval := congrArg (fun L : Vec3 →L[ℝ] ℂ => L (basisVec j)) hdiff
  simp only [smul_apply, smul_eq_mul] at hEval
  rw [VectorFourier.fourierIntegral_continuousLinearMap_apply
      Real.continuous_fourierChar hSMul] at hEval
  rw [vectorFourierIntegral_eq_exp_integral] at hEval
  have hcoeff (ξ : Vec3) :
      fourierSMulRight frequencyFourierBilinear f ξ (basisVec j) =
        (Complex.I * (ξ j : ℂ)) * f ξ := by
    rw [VectorFourier.fourierSMulRight_apply, frequencyFourierBilinear_apply]
    simp only [basisVec_apply]
    simp
    field_simp [Real.pi_ne_zero]
  have hIntEq : (∫ ξ : Vec3, Complex.exp
      (Complex.I * ((∑ k : Fin 3, x k * ξ k : ℝ) : ℂ)) *
        fourierSMulRight frequencyFourierBilinear f ξ (basisVec j)) =
      ∫ ξ : Vec3, spatialMultiplierHeatIntegrand
        (spatialMultiplierCoordinateSymbol σ j) x t ξ := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hcoeff]
    simp [f, multiplierHeatFrequencyAmplitude, spatialMultiplierCoordinateSymbol,
      spatialMultiplierHeatIntegrand, scaledFrequencyGaussian]
    ring
  rw [hIntEq] at hEval
  calc
    (fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j) =
        N * ∫ ξ : Vec3, spatialMultiplierHeatIntegrand
          (spatialMultiplierCoordinateSymbol σ j) x t ξ := hEval
    _ = spatialMultiplierHeatKernel (spatialMultiplierCoordinateSymbol σ j) x t := by
      simp [spatialMultiplierHeatKernel, ht, N]

end CKN.Foundation.Euclidean
