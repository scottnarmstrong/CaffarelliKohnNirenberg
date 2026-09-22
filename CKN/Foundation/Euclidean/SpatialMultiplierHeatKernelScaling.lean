-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelUnitBound
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Parabolic scaling for multiplier heat kernels
-/

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat

private theorem finrank_vec3 : Module.finrank ℝ Vec3 = 3 := by
  simp [Vec3]

/-- Change of frequency scale for a homogeneous symbol. -/
theorem integral_spatialMultiplierHeatIntegrand_scaling
    {τ : Vec3 → ℂ} (d : ℕ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ)
    (x : Vec3) {t R : ℝ} (ht : 0 < t) (hR : 0 < R) :
    (∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ) =
      (R ^ d)⁻¹ • ((R ^ 3)⁻¹ •
        ∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ
          (R⁻¹ • x) (t / R ^ 2) ξ) := by
  let f : Vec3 → ℂ := spatialMultiplierHeatIntegrand τ
    (R⁻¹ • x) (t / R ^ 2)
  have hpoint (ξ : Vec3) : f (R • ξ) = (R ^ d : ℝ) •
      spatialMultiplierHeatIntegrand τ x t ξ := by
    have hphase :
        Complex.exp (Complex.I *
          ((∑ j : Fin 3, (R⁻¹ • x) j * (R • ξ) j : ℝ) : ℂ)) =
        Complex.exp (Complex.I *
          ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) := by
      congr 1
      apply congrArg (fun q : ℝ => Complex.I * (q : ℂ))
      simp only [Pi.smul_apply]
      have hs : (∑ j : Fin 3, (R⁻¹ * x j) * (R * ξ j) : ℝ) =
          ∑ j : Fin 3, x j * ξ j := by
        apply Finset.sum_congr rfl
        intro j hj
        field_simp [hR.ne']
      exact hs
    have hnorm : vec3EuclideanNorm (R • ξ) = R * vec3EuclideanNorm ξ := by
      rw [vec3EuclideanNorm_smul, abs_of_pos hR]
    have hgauss : (t / R ^ 2) * vec3EuclideanNorm (R • ξ) ^ 2 =
        t * vec3EuclideanNorm ξ ^ 2 := by
      rw [hnorm]
      field_simp
    have hgaussC : Complex.exp
        (-(((t / R ^ 2) * vec3EuclideanNorm (R • ξ) ^ 2 : ℝ) : ℂ)) =
        Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) := by
      rw [hgauss]
    simp only [f, spatialMultiplierHeatIntegrand, hphase, hhom R hR ξ, hgaussC]
    simp only [RCLike.real_smul_eq_coe_mul]
    ring
  have hchange : (∫ ξ : Vec3, f (R • ξ)) =
      (R ^ 3)⁻¹ • ∫ ξ : Vec3, f ξ := by
    simpa [finrank_vec3] using
      (MeasureTheory.Measure.integral_comp_smul_of_nonneg volume f R (hR := hR.le))
  have hintegral : (∫ ξ : Vec3, f (R • ξ)) =
      (R ^ d : ℝ) • ∫ ξ : Vec3,
        spatialMultiplierHeatIntegrand τ x t ξ := by
    calc
      (∫ ξ : Vec3, f (R • ξ)) =
          ∫ ξ : Vec3, (R ^ d : ℝ) •
            spatialMultiplierHeatIntegrand τ x t ξ :=
        integral_congr_ae (ae_of_all volume fun ξ => hpoint ξ)
      _ = (R ^ d : ℝ) •
          ∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ := integral_smul _ _
  calc
    (∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ) =
        (R ^ d : ℝ)⁻¹ • ((R ^ d : ℝ) •
          ∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ) := by
            rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero d hR.ne'), one_smul]
    _ = (R ^ d : ℝ)⁻¹ • ((R ^ 3 : ℝ)⁻¹ • ∫ ξ : Vec3, f ξ) := by
      rw [← hintegral, hchange]

/-- A homogeneous degree-`d` symbol has the scale-invariant kernel bound of order `d+3`. -/
theorem exists_spatialMultiplierHeatKernel_bound_of_homogeneous
    {τ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d) (hd3 : d ≤ 3)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec3, ∀ t : ℝ, 0 < t →
      ‖spatialMultiplierHeatKernel τ x t‖ ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-(d + 3 : ℝ)) := by
  obtain ⟨Cunit, hCunit, hunit⟩ :=
    exists_uniform_integral_spatialMultiplierHeatIntegrand_unit d hd hd3 hτ hhom
  let N : ℝ := ‖(2 * Real.pi : ℂ) ^ (-3 : ℤ)‖
  let C : ℝ := N * Cunit
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x t ht
  let R : ℝ := max (vec3EuclideanNorm x) (Real.sqrt t)
  have hR : 0 < R := by
    dsimp [R]
    exact (Real.sqrt_pos.2 ht).trans_le (le_max_right _ _)
  have hnormScale : vec3EuclideanNorm (R⁻¹ • x) =
      vec3EuclideanNorm x / R := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR)]
    field_simp
  have hsqrtScale : Real.sqrt (t / R ^ 2) = Real.sqrt t / R := by
    rw [Real.sqrt_div ht.le, Real.sqrt_sq hR.le]
  have hunitScale :
      max (vec3EuclideanNorm (R⁻¹ • x)) (Real.sqrt (t / R ^ 2)) = 1 := by
    rw [hnormScale, hsqrtScale]
    by_cases hab : vec3EuclideanNorm x ≤ Real.sqrt t
    · have hRval : R = Real.sqrt t := by dsimp [R]; exact max_eq_right hab
      rw [max_eq_right (div_le_div_of_nonneg_right hab hR.le)]
      rw [hRval, div_self (ne_of_gt (Real.sqrt_pos.2 ht))]
    · have hba : Real.sqrt t ≤ vec3EuclideanNorm x := le_of_not_ge hab
      have hRval : R = vec3EuclideanNorm x := by dsimp [R]; exact max_eq_left hba
      rw [max_eq_left (div_le_div_of_nonneg_right hba hR.le)]
      rw [hRval, div_self (ne_of_gt (lt_of_lt_of_le (Real.sqrt_pos.2 ht) hba))]
  have hscaled := integral_spatialMultiplierHeatIntegrand_scaling
    d hhom x ht hR
  have hscaledNorm :
      ‖∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ‖ =
        (R ^ d)⁻¹ * (R ^ 3)⁻¹ *
          ‖∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ
            (R⁻¹ • x) (t / R ^ 2) ξ‖ := by
    rw [hscaled, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hR.le _)),
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hR.le _))]
    ring
  have hunitBound := hunit (R⁻¹ • x) (t / R ^ 2) (by positivity) hunitScale
  have hpower : (R ^ d)⁻¹ * (R ^ 3)⁻¹ =
      R ^ (-(d + 3 : ℝ)) := by
    have hcast : (d + 3 : ℝ) = ((d + 3 : ℕ) : ℝ) := by norm_num
    rw [show -(d + 3 : ℝ) = -((d + 3 : ℕ) : ℝ) by rw [hcast]]
    rw [Real.rpow_neg hR.le, Real.rpow_natCast]
    rw [pow_add]
    field_simp
  have hkernel : spatialMultiplierHeatKernel τ x t =
      (2 * Real.pi : ℂ) ^ (-3 : ℤ) *
        ∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ := by
    simp [spatialMultiplierHeatKernel, ht]
  rw [hkernel, norm_mul]
  change N * ‖∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ x t ξ‖ ≤ _
  rw [hscaledNorm, hpower]
  have hcoeff : 0 ≤ N * R ^ (-(d + 3 : ℝ)) :=
    mul_nonneg hN (Real.rpow_nonneg hR.le _)
  have hinner : R ^ (-(d + 3 : ℝ)) *
      ‖∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ
        (R⁻¹ • x) (t / R ^ 2) ξ‖ ≤
      R ^ (-(d + 3 : ℝ)) * Cunit :=
    mul_le_mul_of_nonneg_left hunitBound (Real.rpow_nonneg hR.le _)
  calc
    N * (R ^ (-(d + 3 : ℝ)) *
        ‖∫ ξ : Vec3, spatialMultiplierHeatIntegrand τ
          (R⁻¹ • x) (t / R ^ 2) ξ‖) ≤
      N * (R ^ (-(d + 3 : ℝ)) * Cunit) :=
        mul_le_mul_of_nonneg_left hinner hN
    _ = C * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-(d + 3 : ℝ)) := by
      dsimp [C, R]
      ring

end CKN.Foundation.Euclidean
