-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbol
import CKN.Core.HeatPotential.GeneralSymbolHeatKernelSplitData
import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelBounds
import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelBoundsProof
import CKN.Foundation.Heat.SpatialSliceMultiplier
import Mathlib.Analysis.Fourier.FourierTransformDeriv

open scoped BigOperators FourierTransform
open MeasureTheory Set

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open VectorFourier
open CKN

/-- The coordinate symbol used for a spatial derivative of the heat kernel. -/
def coordinateMultiplierSymbol (k : Fin 3) : Vec3 → ℂ :=
  fun ξ => Complex.I * (ξ k : ℂ)

theorem coordinateMultiplierSymbol_smoothOffOrigin (k : Fin 3) :
    SmoothOffOrigin (coordinateMultiplierSymbol k) := by
  intro n
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec3 => ξ k) := by
    fun_prop
  have hcoord : ContDiff ℝ (⊤ : ℕ∞)
      (fun ξ : Vec3 => (ξ k : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hproj
  exact (contDiff_const.mul hcoord).of_le (by simp) |>.contDiffOn

theorem coordinateMultiplierSymbol_isDegreeOneHomogeneous (k : Fin 3) :
    IsDegreeOneHomogeneous (coordinateMultiplierSymbol k) := by
  intro a ha ξ
  simp only [coordinateMultiplierSymbol, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem inverse_gaussian_integral_as_heat_transform
    {x : Vec3} {t : ℝ} (ht : 0 < t) :
    ∫ ξ : Vec3,
        Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) *
          Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) =
      (((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (-((vec3EuclideanNorm x ^ 2 / (4 * t) : ℝ) : ℂ)) := by
  let s : ℝ := 1 / (4 * t)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hfourier := spatialFourierIntegral_heatKernel hs (-x)
  have hheat : ∀ ξ : Vec3,
      (heatKernel ξ s : ℂ) =
        ((Real.pi / t) ^ ((-3 : ℝ) / 2) : ℝ) *
          Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) := by
    intro ξ
    rw [heatKernel_eq_formula_sum hs]
    have hcoef : (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) =
        (Real.pi / t) ^ (-(3 : ℝ) / 2) := by
      dsimp [s]
      congr 1
      field_simp
    have hexp : -(∑ i, ξ i ^ 2) / (4 * s) =
        -(t * vec3EuclideanNorm ξ ^ 2) := by
      rw [vec3EuclideanNorm_sq]
      dsimp [s]
      field_simp
    rw [hcoef, hexp, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  have hscale :
      ((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) *
        ((Real.pi / t) ^ ((-3 : ℝ) / 2) : ℝ) = 1 := by
    have hpos : 0 < Real.pi / t := by positivity
    rw [← Real.rpow_add hpos]
    norm_num
  have hphase : ∀ ξ : Vec3,
      Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) =
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, (-x) j * ξ j : ℝ) : ℂ))) := by
    intro ξ
    congr 1
    have hsum : (∑ j : Fin 3, (-x) j * ξ j : ℝ) =
        -(∑ j : Fin 3, x j * ξ j : ℝ) := by
      simp only [Pi.neg_apply, neg_mul, ← Finset.sum_neg_distrib]
    rw [hsum]
    push_cast
    ring
  let phase : Vec3 → ℂ := fun ξ =>
    Complex.exp (-(Complex.I * ((∑ j : Fin 3, (-x) j * ξ j : ℝ) : ℂ)))
  have hrew :
      (fun ξ : Vec3 =>
        Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) *
          Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))) =
      fun ξ : Vec3 =>
        (((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
          ((heatKernel ξ s : ℂ) * phase ξ) := by
    funext ξ
    dsimp [phase]
    rw [hheat ξ, hphase ξ]
    have hscaleC :
        (((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
          (((Real.pi / t) ^ ((-3 : ℝ) / 2) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hscale, Complex.ofReal_one]
    calc
      Complex.exp (-(Complex.I * ((∑ j : Fin 3, (-x) j * ξ j : ℝ) : ℂ))) *
          Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) =
          Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) *
            Complex.exp (-(Complex.I * ((∑ j : Fin 3, (-x) j * ξ j : ℝ) : ℂ))) := by
              ring
      _ = (((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
          (((Real.pi / t) ^ ((-3 : ℝ) / 2) : ℝ) : ℂ) *
            (Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) *
              Complex.exp (-(Complex.I * ((∑ j : Fin 3, (-x) j * ξ j : ℝ) : ℂ)))) := by
                rw [hscaleC]
                ring
      _ = (((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
          ((((Real.pi / t) ^ ((-3 : ℝ) / 2) : ℝ) : ℂ) *
            Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) *
              Complex.exp (-(Complex.I * ((∑ j : Fin 3, (-x) j * ξ j : ℝ) : ℂ)))) := by
                ring
  rw [show (∫ ξ : Vec3,
      Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) *
        Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))) =
      ∫ ξ : Vec3, (((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
        ((heatKernel ξ s : ℂ) * phase ξ) by
        exact integral_congr_ae (Filter.Eventually.of_forall (fun ξ => congrFun hrew ξ))]
  rw [integral_const_mul]
  have hfourier' : spatialFourierIntegral
      (fun y => (heatKernel y s : ℂ)) (-x) =
      Complex.exp (-((s * vec3EuclideanNorm (-x) ^ 2 : ℝ) : ℂ)) := hfourier
  change (((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
      ∫ ξ : Vec3, (heatKernel ξ s : ℂ) * phase ξ = _
  dsimp [phase]
  have hphaseInt :
      (∫ ξ : Vec3, (heatKernel ξ s : ℂ) *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, -x j * ξ j : ℝ) : ℂ)))) =
        spatialFourierIntegral (fun y => (heatKernel y s : ℂ)) (-x) := by
    unfold spatialFourierIntegral
    apply integral_congr_ae
    filter_upwards with ξ
    congr 2
    push_cast
    have hsum : (∑ j : Fin 3, (-x j : ℂ) * ξ j) =
        ∑ j : Fin 3, (ξ j : ℂ) * (-x j : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hneg : ∀ j : Fin 3, ((-x) j : ℂ) = -(x j : ℂ) := by
      intro j
      change ((-(x j) : ℝ) : ℂ) = -(x j : ℂ)
      rw [Complex.ofReal_neg]
    simp_rw [hneg]
    rw [hsum]
  rw [hphaseInt]
  rw [hfourier', vec3EuclideanNorm_neg]
  congr 2
  dsimp [s]
  field_simp

private theorem spatialMultiplierHeatKernel_one
    (x : Vec3) {t : ℝ} (ht : 0 < t) :
    spatialMultiplierHeatKernel (fun _ : Vec3 => (1 : ℂ)) x t =
      (heatKernel x t : ℂ) := by
  rw [spatialMultiplierHeatKernel]
  simp only [ht, ↓reduceIte]
  rw [show (fun ξ : Vec3 => spatialMultiplierHeatIntegrand
      (fun _ : Vec3 => (1 : ℂ)) x t ξ) =
      fun ξ : Vec3 =>
        Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) *
          Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) by
    funext ξ
    simp [spatialMultiplierHeatIntegrand]]
  rw [inverse_gaussian_integral_as_heat_transform ht]
  push_cast
  rw [heatKernel_eq_formula_sum ht]
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have ht0 : 0 ≤ t := ht.le
  have hdiv : (Real.pi / t) ^ ((3 : ℝ) / 2) =
      Real.pi ^ ((3 : ℝ) / 2) / t ^ ((3 : ℝ) / 2) :=
    Real.div_rpow hpi ht0 _
  have hmul : (4 * Real.pi * t) ^ ((-3 : ℝ) / 2) =
      (4 : ℝ) ^ ((-3 : ℝ) / 2) *
        Real.pi ^ ((-3 : ℝ) / 2) * t ^ ((-3 : ℝ) / 2) := by
    rw [show 4 * Real.pi * t = 4 * (Real.pi * t) by ring,
      Real.mul_rpow (by norm_num) (mul_nonneg hpi ht0),
      Real.mul_rpow hpi ht0]
    ring
  have h4 : (4 : ℝ) ^ ((-3 : ℝ) / 2) = (2 : ℝ) ^ (-3 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpi_neg : Real.pi ^ ((-3 : ℝ) / 2) =
      (Real.pi ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [show (-3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
      Real.rpow_neg hpi]
  have ht_neg : t ^ ((-3 : ℝ) / 2) =
      (t ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [show (-3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
      Real.rpow_neg ht0]
  have h2_neg : (2 : ℝ) ^ (-3 : ℝ) = ((2 : ℝ) ^ 3)⁻¹ := by
    rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg (by norm_num)]
    norm_num [Real.rpow_natCast]
  have hreal : ((2 * Real.pi : ℝ) ^ (3 : ℕ))⁻¹ *
      (Real.pi / t) ^ ((3 : ℝ) / 2) =
        (4 * Real.pi * t) ^ ((-3 : ℝ) / 2) := by
    rw [hdiv, hmul, h4, hpi_neg, ht_neg, h2_neg]
    have hp : Real.pi ^ ((3 : ℝ) / 2) * Real.pi ^ ((-3 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add Real.pi_pos]
      norm_num
    field_simp [Real.pi_ne_zero, ne_of_gt ht]
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    norm_num
  have hcoef : (2 * Real.pi : ℂ) ^ (-3 : ℤ) *
      (((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) =
        (((4 * Real.pi * t) ^ ((-3 : ℝ) / 2) : ℝ) : ℂ) := by
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
    simpa [zpow_neg, Complex.ofReal_mul, Complex.ofReal_inv] using hc
  have hexp : -(↑(vec3EuclideanNorm x) ^ 2 / (4 * (t : ℂ))) =
      ((-∑ i : Fin 3, x i ^ 2 / (4 * t) : ℝ) : ℂ) := by
    have hnormC : (↑(vec3EuclideanNorm x) : ℂ) ^ 2 =
        ((∑ i : Fin 3, x i ^ 2 : ℝ) : ℂ) := by
      calc
        (↑(vec3EuclideanNorm x) : ℂ) ^ 2 =
            ((vec3EuclideanNorm x) ^ 2 : ℝ) :=
              (Complex.ofReal_pow _ _).symm
        _ = ∑ i : Fin 3, x i ^ 2 := by
          congr 1
          exact vec3EuclideanNorm_sq x
        _ = ((∑ i : Fin 3, x i ^ 2 : ℝ) : ℂ) := by rfl
    rw [hnormC]
    push_cast
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    field_simp [htC]
    ring_nf
    field_simp [htC]
    have hden : (t : ℂ) * 4 ≠ 0 := mul_ne_zero htC (by norm_num)
    congr 2
    rw [← Finset.sum_div]
    simpa only [mul_div_assoc] using
      (mul_div_cancel_left₀ (∑ i : Fin 3, (x i : ℂ) ^ 2) hden).symm
  rw [hexp]
  calc
    (2 * Real.pi : ℂ) ^ (-3 : ℤ) *
        ((((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp ((-∑ i : Fin 3, x i ^ 2 / (4 * t) : ℝ) : ℂ)) =
        ((2 * Real.pi : ℂ) ^ (-3 : ℤ) *
          (((Real.pi / t) ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) *
          Complex.exp ((-∑ i : Fin 3, x i ^ 2 / (4 * t) : ℝ) : ℂ) := by ring
    _ = (((4 * Real.pi * t) ^ ((-3 : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (((-∑ i : Fin 3, x i ^ 2) / (4 * t) : ℝ) : ℂ) := by
            rw [hcoef]
            congr 2
            push_cast
            have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
            field_simp [htC]
            ring_nf
            field_simp [htC]
            have hden : (t : ℂ) * 4 ≠ 0 := mul_ne_zero htC (by norm_num)
            congr 2
            rw [← Finset.sum_div]
            simpa only [mul_div_assoc] using
              (mul_div_cancel_left₀ (∑ i : Fin 3, (x i : ℂ) ^ 2) hden)

private theorem coordinate_frequency_gaussian_integrable
    {t : ℝ} (ht : 0 < t) :
    Integrable (scaledFrequencyGaussian t) volume := by
  have hmajor := integrable_frequency_gaussian_moment_all ht 0
  have hmeas : AEStronglyMeasurable (scaledFrequencyGaussian t) volume :=
    (scaledFrequencyGaussian_contDiff t).continuous.aestronglyMeasurable
  refine hmajor.mono' hmeas ?_
  filter_upwards with ξ
  rw [scaledFrequencyGaussian, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re, pow_zero, one_mul]
  exact le_rfl

private theorem coordinate_frequency_gaussian_weighted_integrable
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Vec3 => ‖ξ‖ * ‖scaledFrequencyGaussian t ξ‖) volume := by
  have hmajor := integrable_frequency_gaussian_moment_all ht 1
  have hmeas : AEStronglyMeasurable
      (fun ξ : Vec3 => ‖ξ‖ * ‖scaledFrequencyGaussian t ξ‖) volume :=
    continuous_norm.aestronglyMeasurable.mul
      ((scaledFrequencyGaussian_contDiff t).continuous.aestronglyMeasurable.norm)
  refine hmajor.mono' hmeas ?_
  filter_upwards with ξ
  rw [scaledFrequencyGaussian, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re, pow_one]
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg ξ) (Real.exp_nonneg _))]
  exact mul_le_mul_of_nonneg_right (norm_le_vec3EuclideanNorm ξ)
    (Real.exp_nonneg _)

private theorem coordinate_fourier_derivative_integrable
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Vec3 => fourierSMulRight frequencyFourierBilinear
      (scaledFrequencyGaussian t) ξ) volume := by
  have hweighted := coordinate_frequency_gaussian_weighted_integrable ht
  have hmeas : AEStronglyMeasurable (scaledFrequencyGaussian t) volume :=
    (scaledFrequencyGaussian_contDiff t).continuous.aestronglyMeasurable
  refine (hweighted.const_mul (2 * Real.pi * ‖frequencyFourierBilinear‖)).mono'
    (hmeas.fourierSMulRight) ?_
  filter_upwards with ξ
  exact (norm_fourierSMulRight_le frequencyFourierBilinear
    (scaledFrequencyGaussian t) ξ).trans (le_of_eq (by ring))

private theorem spatialMultiplierHeatKernel_one_fderiv_apply_basis
    {x : Vec3} {t : ℝ} (ht : 0 < t) (j : Fin 3) :
    (fderiv ℝ (fun y : Vec3 =>
      spatialMultiplierHeatKernel (fun _ : Vec3 => (1 : ℂ)) y t) x)
        (basisVec j) =
      spatialMultiplierHeatKernel (coordinateMultiplierSymbol j) x t := by
  let f := scaledFrequencyGaussian t
  have hInt : Integrable f volume := by
    simpa [f] using coordinate_frequency_gaussian_integrable ht
  have hWeighted : Integrable (fun ξ : Vec3 => ‖ξ‖ * ‖f ξ‖) volume := by
    simpa [f] using coordinate_frequency_gaussian_weighted_integrable ht
  have hSMul : Integrable (fun ξ : Vec3 => fourierSMulRight
      frequencyFourierBilinear f ξ) volume := by
    simpa [f] using coordinate_fourier_derivative_integrable ht
  let N : ℂ := (2 * Real.pi : ℂ) ^ (-3 : ℤ)
  have hkernel (y : Vec3) :
      spatialMultiplierHeatKernel (fun _ : Vec3 => (1 : ℂ)) y t =
        N * fourierIntegral 𝐞 volume
          frequencyFourierBilinear.toLinearMap₁₂ f y := by
    simp [spatialMultiplierHeatKernel, ht, N]
    rw [vectorFourierIntegral_eq_exp_integral]
    congr 1
    funext ξ
    simp [f, spatialMultiplierHeatIntegrand, scaledFrequencyGaussian]
  have hhas := VectorFourier.hasFDerivAt_fourierIntegral
    frequencyFourierBilinear hInt hWeighted x
  have hfun : (fun y : Vec3 =>
      spatialMultiplierHeatKernel (fun _ : Vec3 => (1 : ℂ)) y t) =
      fun y : Vec3 => N * fourierIntegral 𝐞 volume
        frequencyFourierBilinear.toLinearMap₁₂ f y := funext hkernel
  have hdiff : fderiv ℝ (fun y : Vec3 =>
      spatialMultiplierHeatKernel (fun _ : Vec3 => (1 : ℂ)) y t) x =
      N • fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂
        (fourierSMulRight frequencyFourierBilinear f) x := by
    calc
      fderiv ℝ (fun y : Vec3 =>
          spatialMultiplierHeatKernel (fun _ : Vec3 => (1 : ℂ)) y t) x =
          fderiv ℝ (fun y : Vec3 => N * fourierIntegral 𝐞 volume
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
  have hIntEq :
      (∫ ξ : Vec3, Complex.exp
          (Complex.I * ((∑ k : Fin 3, x k * ξ k : ℝ) : ℂ)) *
        fourierSMulRight frequencyFourierBilinear f ξ (basisVec j)) =
      ∫ ξ : Vec3, spatialMultiplierHeatIntegrand
        (coordinateMultiplierSymbol j) x t ξ := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hcoeff]
    simp [f, coordinateMultiplierSymbol, spatialMultiplierHeatIntegrand,
      scaledFrequencyGaussian]
    ring
  rw [hIntEq] at hEval
  calc
    (fderiv ℝ (fun y : Vec3 =>
        spatialMultiplierHeatKernel (fun _ : Vec3 => (1 : ℂ)) y t) x)
        (basisVec j) =
        N * ∫ ξ : Vec3, spatialMultiplierHeatIntegrand
          (coordinateMultiplierSymbol j) x t ξ := hEval
    _ = spatialMultiplierHeatKernel (coordinateMultiplierSymbol j) x t := by
      simp [spatialMultiplierHeatKernel, ht, N]

theorem spatialMultiplierHeatKernel_coordinate
    (k : Fin 3) (x : Vec3) (t : ℝ) :
    spatialMultiplierHeatKernel (coordinateMultiplierSymbol k) x t =
      (heatKernelSpaceDerivative x t k : ℂ) := by
  by_cases ht : 0 < t
  · have hbase := spatialMultiplierHeatKernel_one_fderiv_apply_basis (x := x) ht k
    have hfun : (fun y : Vec3 =>
        spatialMultiplierHeatKernel (fun _ : Vec3 => (1 : ℂ)) y t) =
        fun y : Vec3 => (heatKernel y t : ℂ) := by
      funext y
      exact spatialMultiplierHeatKernel_one y ht
    rw [hfun] at hbase
    have hdiff : DifferentiableAt ℝ (fun y : Vec3 => heatKernel y t) x := by
      rw [show (fun y : Vec3 => heatKernel y t) = fun y : Vec3 =>
          (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, y j ^ 2) / (4 * t)) by
        funext y
        exact heatKernel_eq_formula_sum ht]
      fun_prop (disch := positivity)
    have hcast :
        fderiv ℝ (fun y : Vec3 => (heatKernel y t : ℂ)) x =
          Complex.ofRealCLM ∘L fderiv ℝ (fun y : Vec3 => heatKernel y t) x := by
      have h := (ContinuousLinearMap.hasFDerivAt Complex.ofRealCLM).comp x
        hdiff.hasFDerivAt
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h.fderiv
    rw [hcast] at hbase
    have hbase' :
        ((fderiv ℝ (fun y : Vec3 => heatKernel y t) x) (basisVec k) : ℂ) =
          spatialMultiplierHeatKernel (coordinateMultiplierSymbol k) x t := by
      simpa only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply] using hbase
    rw [heatKernel_fderiv_apply_basisVec ht k] at hbase'
    exact hbase'.symm
  · rw [spatialMultiplierHeatKernel_of_nonpos _ _ (le_of_not_gt ht),
      heatKernelSpaceDerivative, ite_eq_right ht]
    norm_num

theorem multiplierHeatPotential_coordinate_eq_heatPotential
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    (w : ParabolicPoint) :
    multiplierHeatPotential (fun k => coordinateMultiplierSymbol k) F G w =
      (heatPotential F G w : ℂ) := by
  unfold multiplierHeatPotential heatPotential
  have hF :
      (∫ v, (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ)) =
        ((∫ v, heatPotentialKernel w v * F v : ℝ) : ℂ) := by
    calc
      (∫ v, (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ)) =
          ∫ v, ((heatPotentialKernel w v * F v : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with v
        simp only [heatPotentialKernel, Complex.ofReal_mul]
      _ = ((∫ v, heatPotentialKernel w v * F v : ℝ) : ℂ) := integral_ofReal
  have hG :
      (∑ k, ∫ v,
        spatialMultiplierHeatKernel ((fun k => coordinateMultiplierSymbol k) k)
          (pointSub w v).1 (pointSub w v).2 * (G k v : ℂ)) =
        ((∑ k, ∫ v, heatPotentialSpatialKernel k w v * G k v : ℝ) : ℂ) := by
    calc
      (∑ k, ∫ v,
          spatialMultiplierHeatKernel ((fun k => coordinateMultiplierSymbol k) k)
            (pointSub w v).1 (pointSub w v).2 * (G k v : ℂ)) =
          ∑ k, ((∫ v, heatPotentialSpatialKernel k w v * G k v : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          (∫ v,
              spatialMultiplierHeatKernel ((fun k => coordinateMultiplierSymbol k) k)
                (pointSub w v).1 (pointSub w v).2 * (G k v : ℂ)) =
              ∫ v, ((heatPotentialSpatialKernel k w v * G k v : ℝ) : ℂ) := by
            apply integral_congr_ae
            filter_upwards with v
            have hk' := spatialMultiplierHeatKernel_coordinate k
              (pointSub w v).1 (pointSub w v).2
            rw [hk']
            simp [heatPotentialSpatialKernel, pointSub, Complex.ofReal_mul]
          _ = ((∫ v, heatPotentialSpatialKernel k w v * G k v : ℝ) : ℂ) :=
            integral_ofReal
      _ = ((∑ k, ∫ v, heatPotentialSpatialKernel k w v * G k v : ℝ) : ℂ) := by
        simp
  rw [hF, hG, Complex.ofReal_add]

end CKN.Core.HeatPotential
