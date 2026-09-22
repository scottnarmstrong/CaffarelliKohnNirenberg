-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelHighFrequencyFourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Compact-frequency bounds for homogeneous multiplier kernels
-/

open scoped BigOperators FourierTransform
open MeasureTheory Set

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier

/-- A positive-degree homogeneous symbol has the expected pointwise growth at every frequency. -/
theorem exists_norm_homogeneousSymbol_le
    {τ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3,
      ‖τ ξ‖ ≤ C * vec3EuclideanNorm ξ ^ d := by
  obtain ⟨C, hC, hgrowth⟩ := exists_norm_iteratedFDeriv_growth d hτ hhom 0
  have hzero : τ 0 = 0 := by
    have hscale := hhom 2 (by norm_num) 0
    have hEq : τ 0 = (2 ^ d : ℝ) • τ 0 := by simpa using hscale
    have hnorm : ‖τ 0‖ = (2 ^ d : ℝ) * ‖τ 0‖ := by
      calc
        ‖τ 0‖ = ‖(2 ^ d : ℝ) • τ 0‖ := congrArg norm hEq
        _ = (2 ^ d : ℝ) * ‖τ 0‖ := by
          rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (by norm_num) d)]
    have htwo : 1 < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hd)
    have hnormzero : ‖τ 0‖ = 0 := by
      nlinarith only [hnorm, htwo, norm_nonneg (τ 0)]
    exact norm_eq_zero.mp hnormzero
  refine ⟨C, hC, ?_⟩
  intro ξ
  by_cases hξ : ξ = 0
  · rw [hξ, hzero, vec3EuclideanNorm_zero]
    simp [hd.ne']
  · have h := hgrowth ξ hξ
    simpa only [norm_iteratedFDeriv_zero, pow_zero, div_one] using h

/-- Homogeneous symbols of positive degree give absolutely convergent frequency integrals. -/
theorem integrable_spatialMultiplierHeatIntegrand_of_homogeneous
    {τ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ)
    (x : Vec3) {t : ℝ} (ht : 0 < t) :
    Integrable (spatialMultiplierHeatIntegrand τ x t) volume := by
  obtain ⟨C, hC, hτbound⟩ := exists_norm_homogeneousSymbol_le d hd hτ hhom
  have hτmeas : AEStronglyMeasurable τ volume := by
    have h := hτ.continuousOn.aestronglyMeasurable
      (μ := volume) (measurableSet_singleton (0 : Vec3)).compl
    rwa [restrict_compl_singleton (0 : Vec3)] at h
  have hphase : Continuous fun ξ : Vec3 => Complex.exp
      (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) := by
    apply Complex.continuous_exp.comp
    apply continuous_const.mul
    exact Complex.continuous_ofReal.comp
      (continuous_finsetSum _ fun j _ => (continuous_apply j).const_mul _)
  have hgauss : Continuous fun ξ : Vec3 => Complex.exp
      (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) := by
    apply Complex.continuous_exp.comp
    exact (Complex.continuous_ofReal.comp
      ((continuous_vec3EuclideanNorm.pow 2).const_mul t)).neg
  have hmeas : AEStronglyMeasurable (spatialMultiplierHeatIntegrand τ x t) volume :=
    (hphase.aestronglyMeasurable.mul hτmeas).mul hgauss.aestronglyMeasurable
  have hmajor : Integrable (fun ξ : Vec3 => C *
      (vec3EuclideanNorm ξ ^ d * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)))) volume :=
    (integrable_frequency_gaussian_moment_all ht d).const_mul C
  refine Integrable.mono' hmajor hmeas ?_
  filter_upwards with ξ
  rw [norm_spatialMultiplierHeatIntegrand]
  calc
    ‖τ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) ≤
        (C * vec3EuclideanNorm ξ ^ d) * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) :=
      mul_le_mul_of_nonneg_right (hτbound ξ) (Real.exp_nonneg _)
    _ = C * (vec3EuclideanNorm ξ ^ d *
        Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) := by ring

/-- The part of the symbol removed by the cutoff, including its Gaussian factor. -/
def lowSpatialMultiplierHeatIntegrand
    (τ : Vec3 → ℂ) (x : Vec3) (t : ℝ) (ξ : Vec3) : ℂ :=
  spatialMultiplierHeatIntegrand (fun η => τ η - highFrequencySymbol τ η) x t ξ

private def frequencyPhase (x ξ : Vec3) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ))

/-- The compact-frequency contribution is uniformly bounded at unit time scales. -/
theorem exists_uniform_integral_lowSpatialMultiplierHeatIntegrand
    {τ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec3, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖∫ ξ : Vec3, lowSpatialMultiplierHeatIntegrand τ x t ξ‖ ≤ C := by
  obtain ⟨Cτ, hCτ, hτbound⟩ := exists_norm_homogeneousSymbol_le d hd hτ hhom
  let A : ℝ := Cτ * 2 ^ d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hphaseNorm (x ξ : Vec3) : ‖frequencyPhase x ξ‖ = 1 := by
    rw [frequencyPhase, Complex.norm_exp]
    have hre : (Complex.I *
        ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero]
  let s : Set Vec3 := {ξ | vec3EuclideanNorm ξ ≤ 2}
  have hsClosed : IsClosed s := by
    change IsClosed (vec3EuclideanNorm ⁻¹' Set.Iic 2)
    exact isClosed_Iic.preimage continuous_vec3EuclideanNorm
  have hsBounded : Bornology.IsBounded s := by
    apply (Metric.isBounded_iff_subset_closedBall (0 : Vec3)).2
    refine ⟨2, ?_⟩
    intro ξ hξ
    have hnorm : dist ξ 0 ≤ 2 := by
      simpa [dist_eq_norm] using (norm_le_vec3EuclideanNorm ξ).trans hξ
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
  have hsCompact : IsCompact s := Metric.isCompact_of_isClosed_isBounded hsClosed hsBounded
  have hsFinite : volume s < ⊤ := hsCompact.measure_lt_top
  let K : ℝ := A * (volume s).toReal
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro x t ht ht1
  let f := lowSpatialMultiplierHeatIntegrand τ x t
  have hτint := integrable_spatialMultiplierHeatIntegrand_of_homogeneous
    d hd hτ hhom x ht
  have hhighCont : Continuous (highDampedFrequencyFunction τ t) :=
    (highDampedFrequencyFunction_contDiff hτ t).continuous
  have hhighFunction : Integrable (highDampedFrequencyFunction τ t) volume := by
    have hmajor : Integrable (fun ξ : Vec3 => Cτ *
        (vec3EuclideanNorm ξ ^ d * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)))) volume :=
      (integrable_frequency_gaussian_moment_all ht d).const_mul Cτ
    have hgauss (ξ : Vec3) :
        ‖scaledFrequencyGaussian t ξ‖ = Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
      rw [scaledFrequencyGaussian, Complex.norm_exp]
      simp only [Complex.neg_re, Complex.ofReal_re]
    refine Integrable.mono' hmajor hhighCont.aestronglyMeasurable ?_
    filter_upwards with ξ
    rw [highDampedFrequencyFunction, norm_mul, hgauss]
    calc
      ‖highFrequencySymbol τ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) ≤
          (Cτ * vec3EuclideanNorm ξ ^ d) *
            Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) :=
        mul_le_mul_of_nonneg_right
          ((norm_highFrequencySymbol_le τ ξ).trans (hτbound ξ)) (Real.exp_nonneg _)
      _ = Cτ * (vec3EuclideanNorm ξ ^ d *
          Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) := by ring
  have hphaseCont : Continuous (frequencyPhase x) := by
    apply Complex.continuous_exp.comp
    apply continuous_const.mul
    exact Complex.continuous_ofReal.comp
      (continuous_finsetSum _ fun j _ => (continuous_apply j).const_mul _)
  have hphaseHighMeas : AEStronglyMeasurable
      (fun ξ : Vec3 => frequencyPhase x ξ * highDampedFrequencyFunction τ t ξ) volume :=
    hphaseCont.aestronglyMeasurable.mul hhighFunction.aestronglyMeasurable
  have hphaseHigh : Integrable
      (fun ξ : Vec3 => frequencyPhase x ξ * highDampedFrequencyFunction τ t ξ) volume := by
    refine Integrable.mono' hhighFunction.norm hphaseHighMeas ?_
    filter_upwards with ξ
    change ‖frequencyPhase x ξ * highDampedFrequencyFunction τ t ξ‖ ≤
      ‖highDampedFrequencyFunction τ t ξ‖
    calc
      ‖frequencyPhase x ξ * highDampedFrequencyFunction τ t ξ‖ =
          ‖frequencyPhase x ξ‖ * ‖highDampedFrequencyFunction τ t ξ‖ := norm_mul _ _
      _ = ‖highDampedFrequencyFunction τ t ξ‖ := by rw [hphaseNorm x ξ]; ring
      _ ≤ ‖highDampedFrequencyFunction τ t ξ‖ := le_rfl
  have hfrepr : f = fun ξ : Vec3 => spatialMultiplierHeatIntegrand τ x t ξ -
      frequencyPhase x ξ * highDampedFrequencyFunction τ t ξ := by
    funext ξ
    simp only [f, lowSpatialMultiplierHeatIntegrand, spatialMultiplierHeatIntegrand,
      frequencyPhase, highDampedFrequencyFunction, scaledFrequencyGaussian]
    ring
  have hf : Integrable f volume := by
    rw [hfrepr]
    exact hτint.sub hphaseHigh
  have hzero : ∀ ξ, ξ ∉ s → f ξ = 0 := by
    intro ξ hξ
    have hr : 2 < vec3EuclideanNorm ξ := lt_of_not_ge hξ
    have heuc := vec3EuclideanNorm_le_sqrt_three_mul_norm ξ
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    have hle : vec3EuclideanNorm ξ ≤ 2 * ‖ξ‖ :=
      heuc.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg ξ))
    have hnorm : 1 < ‖ξ‖ := by nlinarith only [hr, hle]
    have hcut : τ ξ - highFrequencySymbol τ ξ = 0 :=
      sub_highFrequencySymbol_eq_zero_of_one_le_dist τ ξ
        (by simpa [dist_eq_norm] using hnorm.le)
    simp [f, lowSpatialMultiplierHeatIntegrand, spatialMultiplierHeatIntegrand, hcut]
  have hpoint : ∀ ξ ∈ s, ‖f ξ‖ ≤ A := by
    intro ξ hξ
    have hlow := norm_sub_highFrequencySymbol_le τ ξ
    have hexp : Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht.le (sq_nonneg _)))
    have hτball : ‖τ ξ‖ ≤ Cτ * 2 ^ d := by
      calc
        ‖τ ξ‖ ≤ Cτ * vec3EuclideanNorm ξ ^ d := hτbound ξ
        _ ≤ Cτ * 2 ^ d := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (vec3EuclideanNorm_nonneg ξ) hξ d) hCτ
    change ‖spatialMultiplierHeatIntegrand
      (fun η => τ η - highFrequencySymbol τ η) x t ξ‖ ≤ A
    rw [norm_spatialMultiplierHeatIntegrand]
    calc
      ‖τ ξ - highFrequencySymbol τ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) ≤
          ‖τ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) :=
        mul_le_mul_of_nonneg_right hlow (Real.exp_nonneg _)
      _ ≤ Cτ * 2 ^ d := by
        calc
          ‖τ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) ≤
              (Cτ * 2 ^ d) * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) :=
            mul_le_mul_of_nonneg_right hτball (Real.exp_nonneg _)
          _ ≤ Cτ * 2 ^ d := by
            calc
              (Cτ * 2 ^ d) * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) ≤
                  (Cτ * 2 ^ d) * 1 :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
              _ = Cτ * 2 ^ d := by ring
      _ = A := by dsimp [A]
  have hcompl : ∫ ξ in sᶜ, f ξ = 0 := by
    calc
      ∫ ξ in sᶜ, f ξ = ∫ ξ in sᶜ, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hsClosed.measurableSet.compl] with ξ hξ
        exact hzero ξ hξ
      _ = 0 := by simp
  have hset := norm_setIntegral_le_of_norm_le_const_ae'
    (μ := volume) (s := s) hsFinite (ae_of_all volume fun ξ hξ => hpoint ξ hξ)
  have hsplit := integral_add_compl hsClosed.measurableSet hf
  rw [hcompl, add_zero] at hsplit
  change ‖∫ ξ : Vec3, f ξ‖ ≤ K
  calc
    ‖∫ ξ : Vec3, f ξ‖ = ‖∫ ξ in s, f ξ‖ := by rw [← hsplit]
    _ ≤ A * (volume s).toReal := hset
    _ = K := rfl

end CKN.Foundation.Euclidean
