-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelSpatialDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Time differentiability of multiplier heat kernels
-/

open scoped BigOperators
open MeasureTheory
open Filter
open TopologicalSpace

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat

/-- Multiplication of a symbol by the negative squared frequency. -/
def spatialMultiplierTimeSymbol (σ : Vec3 → ℂ) (ξ : Vec3) : ℂ :=
  -complexEuclideanSquare ξ * σ ξ

/-- The time-differentiated symbol stays smooth away from the origin. -/
theorem spatialMultiplierTimeSymbol_contDiffOn
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (spatialMultiplierTimeSymbol σ) ({0}ᶜ : Set Vec3) := by
  exact complexEuclideanSquare_contDiff.contDiffOn.neg.mul hσ

/-- Multiplication by the negative squared frequency raises homogeneity by two. -/
theorem spatialMultiplierTimeSymbol_homogeneous
    {σ : Vec3 → ℂ} (d : ℕ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ) :
    ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      spatialMultiplierTimeSymbol σ (a • ξ) =
        (a ^ (d + 2) : ℝ) • spatialMultiplierTimeSymbol σ ξ := by
  intro a ha ξ
  simp only [spatialMultiplierTimeSymbol, complexEuclideanSquare_homogeneous a ha ξ,
    hhom a ha ξ]
  simp only [RCLike.real_smul_eq_coe_mul]
  push_cast
  rw [pow_add]
  ring

private def multiplierHeatTimeIntegrand
    (σ : Vec3 → ℂ) (x : Vec3) (z : ℂ) (ξ : Vec3) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) * σ ξ *
    Complex.exp (-(z * complexEuclideanSquare ξ))

private def multiplierHeatTimeDerivativeIntegrand
    (σ : Vec3 → ℂ) (x : Vec3) (z : ℂ) (ξ : Vec3) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) *
    spatialMultiplierTimeSymbol σ ξ * Complex.exp (-(z * complexEuclideanSquare ξ))

private theorem multiplierHeatTimePhase_norm (x ξ : Vec3) :
    ‖Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I *
      ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

private theorem multiplierHeatTimePhase_continuous (x : Vec3) :
    Continuous (fun ξ : Vec3 =>
      Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ))) := by
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  exact Complex.continuous_ofReal.comp
    (continuous_finsetSum _ fun j _ => (continuous_apply j).const_mul _)

private theorem spatialMultiplierHeatKernel_eq_timeIntegral
    {σ : Vec3 → ℂ}
    (x : Vec3) {t : ℝ} (ht : 0 < t) :
    spatialMultiplierHeatKernel σ x t =
      (2 * Real.pi : ℂ) ^ (-3 : ℤ) *
        ∫ ξ : Vec3, multiplierHeatTimeIntegrand σ x (t : ℂ) ξ := by
  simp [spatialMultiplierHeatKernel, ht]
  congr 1
  funext ξ
  simp [multiplierHeatTimeIntegrand, spatialMultiplierHeatIntegrand,
    complexEuclideanSquare]

/-- The time derivative is the kernel of the symbol multiplied by `-|ξ|²`. -/
theorem spatialMultiplierHeatKernel_hasDerivAt_time
    {σ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    {t : ℝ} (ht : 0 < t) (x : Vec3) :
    HasDerivAt (fun s => spatialMultiplierHeatKernel σ x s)
      (spatialMultiplierHeatKernel (spatialMultiplierTimeSymbol σ) x t) t := by
  obtain ⟨Cσ, hCσ, hσbound⟩ := exists_norm_homogeneousSymbol_le d hd hσ hhom
  have hσmeas : AEStronglyMeasurable σ volume := by
    have h := hσ.continuousOn.aestronglyMeasurable
      (μ := volume) (measurableSet_singleton (0 : Vec3)).compl
    rwa [restrict_compl_singleton (0 : Vec3)] at h
  have hphaseCont := multiplierHeatTimePhase_continuous x
  have hQcont : Continuous complexEuclideanSquare := complexEuclideanSquare_contDiff.continuous
  have hGmeas : AEStronglyMeasurable (spatialMultiplierTimeSymbol σ) volume := by
    exact hQcont.neg.aestronglyMeasurable.mul hσmeas
  have htimeGaussCont (z : ℂ) :
      Continuous (fun ξ : Vec3 => Complex.exp (-(z * complexEuclideanSquare ξ))) := by
    apply Complex.continuous_exp.comp
    exact (continuous_const.mul hQcont).neg
  let F : ℂ → Vec3 → ℂ := multiplierHeatTimeIntegrand σ x
  let F' : ℂ → Vec3 → ℂ := multiplierHeatTimeDerivativeIntegrand σ x
  let N : ℂ := (2 * Real.pi : ℂ) ^ (-3 : ℤ)
  have hFmeas (z : ℂ) : AEStronglyMeasurable (F z) volume := by
    dsimp [F, multiplierHeatTimeIntegrand]
    exact (hphaseCont.aestronglyMeasurable.mul hσmeas).mul
      (htimeGaussCont z).aestronglyMeasurable
  have hF'int : Integrable (F (t : ℂ)) volume := by
    have hbase := integrable_spatialMultiplierHeatIntegrand_of_homogeneous
      d hd hσ hhom x ht
    have hEq : F (t : ℂ) = spatialMultiplierHeatIntegrand σ x t := by
      funext ξ
      simp [F, multiplierHeatTimeIntegrand, spatialMultiplierHeatIntegrand,
        complexEuclideanSquare]
    rw [hEq]
    exact hbase
  have hF'data : AEStronglyMeasurable (F' (t : ℂ)) volume := by
    dsimp [F', multiplierHeatTimeDerivativeIntegrand]
    exact (hphaseCont.aestronglyMeasurable.mul hGmeas).mul
      (htimeGaussCont (t : ℂ)).aestronglyMeasurable
  have hmajor : Integrable (fun ξ : Vec3 => Cσ *
      (vec3EuclideanNorm ξ ^ (d + 2) *
        Real.exp (-((t / 2) * vec3EuclideanNorm ξ ^ 2)))) volume := by
    have ht2 : 0 < t / 2 := by positivity
    exact (integrable_frequency_gaussian_moment_all ht2 (d + 2)).const_mul Cσ
  have hradius : 0 < t / 2 := by positivity
  have hball : Metric.ball (t : ℂ) (t / 2) ∈ nhds (t : ℂ) :=
    Metric.ball_mem_nhds _ (by simpa using hradius)
  have hbound : ∀ᵐ ξ ∂volume, ∀ z ∈ Metric.ball (t : ℂ) (t / 2),
      ‖F' z ξ‖ ≤ Cσ * (vec3EuclideanNorm ξ ^ (d + 2) *
        Real.exp (-((t / 2) * vec3EuclideanNorm ξ ^ 2))) := by
    filter_upwards [] with ξ
    intro z hz
    have hzdist : ‖z - (t : ℂ)‖ < t / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hreClose : |z.re - t| ≤ ‖z - (t : ℂ)‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - (t : ℂ))
    have hreLower : -(z.re - t) ≤ ‖z - (t : ℂ)‖ := by
      nlinarith only [(abs_le.mp hreClose).1]
    have hre : t / 2 < z.re := by nlinarith only [hzdist, hreLower]
    have hr := vec3EuclideanNorm_nonneg ξ
    have hQ : complexEuclideanSquare ξ =
        (vec3EuclideanNorm ξ ^ 2 : ℝ) := rfl
    have hQnorm : ‖complexEuclideanSquare ξ‖ = vec3EuclideanNorm ξ ^ 2 := by
      rw [hQ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hexpRe : (-(z * complexEuclideanSquare ξ)).re =
        -(z.re * vec3EuclideanNorm ξ ^ 2) := by
      rw [Complex.neg_re, Complex.mul_re, hQ]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hexpBound : Real.exp (-(z.re * vec3EuclideanNorm ξ ^ 2)) ≤
        Real.exp (-((t / 2) * vec3EuclideanNorm ξ ^ 2)) :=
      Real.exp_le_exp.mpr (by nlinarith only [hre, sq_nonneg (vec3EuclideanNorm ξ)])
    have hsymbol : ‖spatialMultiplierTimeSymbol σ ξ‖ =
        vec3EuclideanNorm ξ ^ 2 * ‖σ ξ‖ := by
      rw [spatialMultiplierTimeSymbol, norm_mul, norm_neg, hQnorm]
    dsimp only [F', multiplierHeatTimeDerivativeIntegrand]
    rw [norm_mul, norm_mul,
      multiplierHeatTimePhase_norm, Complex.norm_exp, hexpRe, hsymbol]
    simp only [one_mul]
    have hprod : vec3EuclideanNorm ξ ^ 2 * ‖σ ξ‖ ≤
        Cσ * vec3EuclideanNorm ξ ^ (d + 2) := by
      calc
        vec3EuclideanNorm ξ ^ 2 * ‖σ ξ‖ ≤
            vec3EuclideanNorm ξ ^ 2 * (Cσ * vec3EuclideanNorm ξ ^ d) :=
          mul_le_mul_of_nonneg_left (hσbound ξ)
            (sq_nonneg (vec3EuclideanNorm ξ))
        _ = Cσ * vec3EuclideanNorm ξ ^ (d + 2) := by
          rw [pow_add]
          ring
    calc
      vec3EuclideanNorm ξ ^ 2 * ‖σ ξ‖ *
          Real.exp (-(z.re * vec3EuclideanNorm ξ ^ 2)) ≤
        Cσ * vec3EuclideanNorm ξ ^ (d + 2) *
          Real.exp (-((t / 2) * vec3EuclideanNorm ξ ^ 2)) := by
        calc
          _ ≤ (Cσ * vec3EuclideanNorm ξ ^ (d + 2)) *
              Real.exp (-(z.re * vec3EuclideanNorm ξ ^ 2)) :=
            mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hexpBound
            (mul_nonneg hCσ (pow_nonneg hr _))
      _ = Cσ * (vec3EuclideanNorm ξ ^ (d + 2) *
          Real.exp (-((t / 2) * vec3EuclideanNorm ξ ^ 2))) := by ring
  have hdiff : ∀ᵐ ξ ∂volume, ∀ z ∈ Metric.ball (t : ℂ) (t / 2),
      HasDerivAt (F · ξ) (F' z ξ) z := by
    filter_upwards [] with ξ
    intro z hz
    have harg : HasDerivAt (fun w : ℂ => -(w * complexEuclideanSquare ξ))
        (-complexEuclideanSquare ξ) z := by
      convert (hasDerivAt_id z).mul_const (-complexEuclideanSquare ξ) using 1
      · funext w
        simp only [id_eq]
        ring
      · ring
    have hexp := (Complex.hasDerivAt_exp _).comp z harg
    have hmul := hexp.const_mul
      (Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) *
        σ ξ)
    convert hmul using 1
    · funext w
      simp [F, multiplierHeatTimeIntegrand]
    · simp [F', multiplierHeatTimeDerivativeIntegrand, spatialMultiplierTimeSymbol]
      ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (x₀ := (t : ℂ))
    (s := Metric.ball (t : ℂ) (t / 2)) hball
    (Eventually.of_forall hFmeas) hF'int hF'data hbound hmajor hdiff
  have hcomplex : HasDerivAt (fun z : ℂ =>
      N * ∫ ξ : Vec3, F z ξ) (N * ∫ ξ : Vec3, F' (t : ℂ) ξ) (t : ℂ) := by
    convert hmain.2.const_mul N using 1
  have hreal : HasDerivAt (fun s : ℝ =>
      N * ∫ ξ : Vec3, F (s : ℂ) ξ)
      (N * ∫ ξ : Vec3, F' (t : ℂ) ξ) t := by
    exact HasDerivAt.comp_ofReal hcomplex
  have hkernelEq : (fun s : ℝ => spatialMultiplierHeatKernel σ x s) =ᶠ[nhds t]
      (fun s => N * ∫ ξ : Vec3, F (s : ℂ) ξ) := by
    filter_upwards [Metric.ball_mem_nhds t hradius] with s hs
    have hsdist : |s - t| < t / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs
    have hslow : -(t / 2) < s - t := (abs_lt.mp hsdist).1
    have hlow : t / 2 < s := by linarith only [hslow]
    have hspos : 0 < s := by linarith only [hlow, ht]
    have hEq := spatialMultiplierHeatKernel_eq_timeIntegral (σ := σ) x hspos
    simpa [F, multiplierHeatTimeIntegrand, N] using hEq
  have hrealKernel := hreal.congr_of_eventuallyEq hkernelEq
  have hderivEq : N * ∫ ξ : Vec3, F' (t : ℂ) ξ =
      spatialMultiplierHeatKernel (spatialMultiplierTimeSymbol σ) x t := by
    simp only [spatialMultiplierHeatKernel, ht]
    congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    simp [F', multiplierHeatTimeDerivativeIntegrand, spatialMultiplierHeatIntegrand,
      spatialMultiplierTimeSymbol, complexEuclideanSquare,
      Complex.ofReal_mul]
  exact hrealKernel.congr_deriv hderivEq

end CKN.Foundation.Euclidean
