-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelLowFrequency

/-!
# Unit-scale estimates for multiplier heat kernels
-/

open scoped BigOperators FourierTransform
open MeasureTheory

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier

private def multiplierKernelPhase (x ξ : Vec3) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ))

private theorem multiplierKernelPhase_norm (x ξ : Vec3) :
    ‖multiplierKernelPhase x ξ‖ = 1 := by
  rw [multiplierKernelPhase, Complex.norm_exp]
  have hre : (Complex.I *
      ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

private theorem scaledFrequencyGaussian_norm {t : ℝ} (ξ : Vec3) :
    ‖scaledFrequencyGaussian t ξ‖ =
      Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) := by
  rw [scaledFrequencyGaussian, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]

/-- The defining frequency integral has a symbol-dependent bound on the parabolic unit sphere. -/
theorem exists_uniform_integral_spatialMultiplierHeatIntegrand_unit
    {τ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d) (hd3 : d ≤ 3)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec3, ∀ t : ℝ, 0 < t →
      max (vec3EuclideanNorm x) (Real.sqrt t) = 1 →
      ‖∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ‖ ≤ C := by
  obtain ⟨Cτ, hCτ, hτbound⟩ := exists_norm_homogeneousSymbol_le d hd hτ hhom
  obtain ⟨Clow, hClow, hlow⟩ := exists_uniform_integral_lowSpatialMultiplierHeatIntegrand
    d hd hτ hhom
  obtain ⟨Chigh, hChigh, hhigh⟩ := exists_uniform_fourierIntegral_highDampedFrequency
    d hd3 hτ hhom
  have hbase : Integrable (spatialMultiplierHeatIntegrand τ 0 1) volume :=
    integrable_spatialMultiplierHeatIntegrand_of_homogeneous d hd hτ hhom 0 one_pos
  let A : ℝ := ∫ ξ : Vec3, ‖spatialMultiplierHeatIntegrand τ 0 1 ξ‖
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg_of_ae (ae_of_all volume fun ξ => norm_nonneg _)
  have hAbound (x : Vec3) :
      ‖∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x 1 ξ‖ ≤ A := by
    have hxint := integrable_spatialMultiplierHeatIntegrand_of_homogeneous
      d hd hτ hhom x one_pos
    have hnormEq : (fun ξ : Vec3 =>
        ‖spatialMultiplierHeatIntegrand τ x 1 ξ‖) = fun ξ =>
        ‖spatialMultiplierHeatIntegrand τ 0 1 ξ‖ := by
      funext ξ
      rw [norm_spatialMultiplierHeatIntegrand, norm_spatialMultiplierHeatIntegrand]
    calc
      ‖∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x 1 ξ‖ ≤
          ∫ ξ : Vec3, ‖spatialMultiplierHeatIntegrand τ x 1 ξ‖ :=
        norm_integral_le_integral_norm (spatialMultiplierHeatIntegrand τ x 1)
      _ = A := by rw [hnormEq]
  let C : ℝ := max (Clow + Chigh) A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x t ht hunit
  by_cases hx : vec3EuclideanNorm x = 1
  · have ht1 : t ≤ 1 := by
      have hsqrt : Real.sqrt t ≤ 1 := by
        have h := le_max_right (vec3EuclideanNorm x) (Real.sqrt t)
        rw [hunit] at h
        exact h
      have hsqrt0 := Real.sqrt_nonneg t
      have hsquare := Real.sq_sqrt ht.le
      nlinarith only [hsqrt, hsqrt0, hsquare]
    have hlowBound := hlow x t ht ht1
    have hphaseCont : Continuous (multiplierKernelPhase x) := by
      apply Complex.continuous_exp.comp
      apply continuous_const.mul
      exact Complex.continuous_ofReal.comp
        (continuous_finsetSum _ fun j _ => (continuous_apply j).const_mul _)
    have hhighCont : Continuous (highDampedFrequencyFunction τ t) :=
      (highDampedFrequencyFunction_contDiff hτ t).continuous
    have hhighInt : Integrable (highDampedFrequencyFunction τ t) volume := by
      have hmajor : Integrable (fun ξ : Vec3 => Cτ *
          (vec3EuclideanNorm ξ ^ d * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)))) volume :=
        (integrable_frequency_gaussian_moment_all ht d).const_mul Cτ
      refine Integrable.mono' hmajor hhighCont.aestronglyMeasurable ?_
      filter_upwards with ξ
      rw [highDampedFrequencyFunction, norm_mul, scaledFrequencyGaussian_norm]
      calc
        ‖highFrequencySymbol τ ξ‖ * Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) ≤
            (Cτ * vec3EuclideanNorm ξ ^ d) *
              Real.exp (-(t * vec3EuclideanNorm ξ ^ 2)) :=
          mul_le_mul_of_nonneg_right
            ((norm_highFrequencySymbol_le τ ξ).trans (hτbound ξ))
            (Real.exp_nonneg _)
        _ = Cτ * (vec3EuclideanNorm ξ ^ d *
            Real.exp (-(t * vec3EuclideanNorm ξ ^ 2))) := by ring
    have hphaseHigh : Integrable
        (fun ξ : Vec3 => multiplierKernelPhase x ξ *
          highDampedFrequencyFunction τ t ξ) volume := by
      refine Integrable.mono' hhighInt.norm
        (hphaseCont.aestronglyMeasurable.mul hhighInt.aestronglyMeasurable) ?_
      filter_upwards with ξ
      rw [norm_mul, multiplierKernelPhase_norm]
      simp
    have hlowInt : Integrable (lowSpatialMultiplierHeatIntegrand τ x t) volume := by
      have hOrig := integrable_spatialMultiplierHeatIntegrand_of_homogeneous
        d hd hτ hhom x ht
      have hrepr : lowSpatialMultiplierHeatIntegrand τ x t = fun ξ =>
          spatialMultiplierHeatIntegrand τ x t ξ -
            multiplierKernelPhase x ξ * highDampedFrequencyFunction τ t ξ := by
        funext ξ
        simp [lowSpatialMultiplierHeatIntegrand, spatialMultiplierHeatIntegrand,
          multiplierKernelPhase, highDampedFrequencyFunction, scaledFrequencyGaussian]
        ring
      rw [hrepr]
      exact hOrig.sub hphaseHigh
    have hsplit : (∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ) =
        (∫ ξ : Vec3, lowSpatialMultiplierHeatIntegrand τ x t ξ) +
          ∫ ξ : Vec3, multiplierKernelPhase x ξ *
            highDampedFrequencyFunction τ t ξ := by
      have hrepr : spatialMultiplierHeatIntegrand τ x t = fun ξ =>
          lowSpatialMultiplierHeatIntegrand τ x t ξ +
            multiplierKernelPhase x ξ * highDampedFrequencyFunction τ t ξ := by
        funext ξ
        simp [lowSpatialMultiplierHeatIntegrand, spatialMultiplierHeatIntegrand,
          multiplierKernelPhase, highDampedFrequencyFunction, scaledFrequencyGaussian]
        ring
      rw [hrepr, integral_add hlowInt hphaseHigh]
    have hFourier : (∫ ξ : Vec3, multiplierKernelPhase x ξ *
        highDampedFrequencyFunction τ t ξ) =
        fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂
          (highDampedFrequencyFunction τ t) x := by
      rw [vectorFourierIntegral_eq_exp_integral]
      rfl
    have hhighBound := hhigh t ht ht1 x hx
    calc
      ‖∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ‖ ≤
          ‖∫ ξ : Vec3, lowSpatialMultiplierHeatIntegrand τ x t ξ‖ +
            ‖∫ ξ : Vec3, multiplierKernelPhase x ξ *
              highDampedFrequencyFunction τ t ξ‖ := by rw [hsplit]; exact norm_add_le _ _
      _ ≤ Clow + Chigh := add_le_add hlowBound (by rw [hFourier]; exact hhighBound)
      _ ≤ C := le_max_left _ _
  · have hsqrt : Real.sqrt t = 1 := by
      rcases le_total (vec3EuclideanNorm x) (Real.sqrt t) with hle | hle
      · rw [max_eq_right hle] at hunit
        exact hunit
      · have hmax : max (vec3EuclideanNorm x) (Real.sqrt t) = vec3EuclideanNorm x :=
          max_eq_left hle
        have hx' : vec3EuclideanNorm x = 1 := by rw [hmax] at hunit; exact hunit
        exact (hx hx').elim
    have ht1 : t = 1 := by
      have hsquare := Real.sq_sqrt ht.le
      rw [hsqrt] at hsquare
      nlinarith only [hsquare]
    rw [ht1]
    exact (hAbound x).trans (le_max_right _ _)

end CKN.Foundation.Euclidean
