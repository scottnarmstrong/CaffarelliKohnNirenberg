-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelTimeDerivative

/-!
# Bounds for degree-one multiplier heat kernels

The frequency representation gives the size, spatial-gradient, and time-derivative
bounds for every smooth degree-one symbol, with one symbol-dependent constant.
-/

open scoped BigOperators

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat

/-- A smooth degree-one multiplier heat kernel and its first derivatives have
the parabolic bounds of orders four, five, and six, with one constant fixed
before the space-time point. -/
theorem exists_spatialMultiplierHeatKernel_bounds_of_degreeOne
    (σ : Vec3 → ℂ)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec3, ∀ t : ℝ, 0 < t →
      DifferentiableAt ℝ (fun y => spatialMultiplierHeatKernel σ y t) x ∧
      DifferentiableAt ℝ (fun s => spatialMultiplierHeatKernel σ x s) t ∧
      ‖spatialMultiplierHeatKernel σ x t‖ ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-4 : ℝ) ∧
      Real.sqrt (∑ j : Fin 3,
        ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ^ 2) ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-5 : ℝ) ∧
      ‖deriv (fun s => spatialMultiplierHeatKernel σ x s) t‖ ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-6 : ℝ) := by
  have hhom1 : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ 1 : ℝ) • σ ξ := by
    intro a ha ξ
    simpa [pow_one, RCLike.real_smul_eq_coe_mul] using hhom a ha ξ
  obtain ⟨C₀, hC₀, hB₀⟩ := exists_spatialMultiplierHeatKernel_bound_of_homogeneous
    (τ := σ) 1 (by norm_num) (by norm_num) hσ hhom1
  have htimeCont : ContDiffOn ℝ (⊤ : ℕ∞)
      (spatialMultiplierTimeSymbol σ) ({0}ᶜ : Set Vec3) :=
    spatialMultiplierTimeSymbol_contDiffOn hσ
  have htimeHom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      spatialMultiplierTimeSymbol σ (a • ξ) =
        (a ^ 3 : ℝ) • spatialMultiplierTimeSymbol σ ξ := by
    intro a ha ξ
    simpa using
      (spatialMultiplierTimeSymbol_homogeneous (σ := σ) 1 hhom1 a ha ξ)
  obtain ⟨Cₜ, hCₜ, hBₜ⟩ := exists_spatialMultiplierHeatKernel_bound_of_homogeneous
    (τ := spatialMultiplierTimeSymbol σ) 3 (by norm_num) (by norm_num)
      htimeCont htimeHom
  let Ecoord : Fin 3 → Prop := fun j =>
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Vec3, ∀ t : ℝ, 0 < t →
      ‖spatialMultiplierHeatKernel (spatialMultiplierCoordinateSymbol σ j) x t‖ ≤
        c * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-5 : ℝ)
  have hEcoord : ∀ j : Fin 3, Ecoord j := by
    intro j
    obtain ⟨c, hc, hbound⟩ := exists_spatialMultiplierHeatKernel_bound_of_homogeneous
      (τ := spatialMultiplierCoordinateSymbol σ j) 2 (by norm_num) (by norm_num)
      (spatialMultiplierCoordinateSymbol_contDiffOn j hσ)
      (spatialMultiplierCoordinateSymbol_homogeneous 1 hhom1 j)
    refine ⟨c, hc, ?_⟩
    intro x t ht
    convert hbound x t ht using 1
    congr 1
    norm_num
  let Cj : Fin 3 → ℝ := fun j => Classical.choose (hEcoord j)
  have hCj : ∀ j : Fin 3, 0 ≤ Cj j := by
    intro j
    exact (Classical.choose_spec (hEcoord j)).1
  have hBcoord : ∀ j : Fin 3, ∀ x : Vec3, ∀ t : ℝ, 0 < t →
      ‖spatialMultiplierHeatKernel (spatialMultiplierCoordinateSymbol σ j) x t‖ ≤
        Cj j * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-5 : ℝ) := by
    intro j x t ht
    exact (Classical.choose_spec (hEcoord j)).2 x t ht
  let Ccoord : ℝ := ∑ j : Fin 3, Cj j
  let Cgrad : ℝ := Real.sqrt 3 * Ccoord
  let C : ℝ := max C₀ (max Cₜ Cgrad)
  have hCcoord : 0 ≤ Ccoord := by
    dsimp [Ccoord]
    exact Finset.sum_nonneg fun j _ => hCj j
  have hCgrad : 0 ≤ Cgrad := by dsimp [Cgrad]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x t ht
  let R : ℝ := max (vec3EuclideanNorm x) (Real.sqrt t)
  have hR : 0 < R := by
    dsimp [R]
    exact (Real.sqrt_pos.2 ht).trans_le (le_max_right _ _)
  have hp4 : 0 ≤ R ^ (-4 : ℝ) := Real.rpow_nonneg hR.le _
  have hp5 : 0 ≤ R ^ (-5 : ℝ) := Real.rpow_nonneg hR.le _
  have hp6 : 0 ≤ R ^ (-6 : ℝ) := Real.rpow_nonneg hR.le _
  have hkernel0 : ‖spatialMultiplierHeatKernel σ x t‖ ≤ C₀ * R ^ (-4 : ℝ) := by
    dsimp [R]
    convert hB₀ x t ht using 1
    norm_num
  have hkernelTime :
      ‖spatialMultiplierHeatKernel (spatialMultiplierTimeSymbol σ) x t‖ ≤
        Cₜ * R ^ (-6 : ℝ) := by
    dsimp [R]
    convert hBₜ x t ht using 1
    norm_num
  have hcoord : ∀ j : Fin 3,
      ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ≤
        Cj j * R ^ (-5 : ℝ) := by
    intro j
    rw [spatialMultiplierHeatKernel_fderiv_apply_basis
      1 (by norm_num) hσ hhom1 ht x j]
    simpa [R] using hBcoord j x t ht
  let B : ℝ := Ccoord * R ^ (-5 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcoordB : ∀ j : Fin 3,
      ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ≤ B := by
    intro j
    have hsum : Cj j ≤ Ccoord := by
      dsimp [Ccoord]
      exact Finset.single_le_sum (fun i _ => hCj i) (Finset.mem_univ j)
    dsimp [B]
    exact (hcoord j).trans (mul_le_mul_of_nonneg_right hsum hp5)
  have hsumSq :
      (∑ j : Fin 3,
        ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ^ 2) ≤
        3 * B ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin 3, B ^ 2 := Finset.sum_le_sum fun j _ => by
        have hnonneg := norm_nonneg
          ((fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j))
        nlinarith only [hnonneg, hB, hcoordB j]
      _ = 3 * B ^ 2 := by simp
  have hgrad :
      Real.sqrt (∑ j : Fin 3,
        ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ^ 2) ≤
        Cgrad * R ^ (-5 : ℝ) := by
    calc
      _ ≤ Real.sqrt (3 * B ^ 2) := Real.sqrt_le_sqrt hsumSq
      _ = Cgrad * R ^ (-5 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs, abs_of_nonneg hB]
        dsimp [Cgrad, B]
        ring
  have htimeDeriv := spatialMultiplierHeatKernel_hasDerivAt_time
    1 (by norm_num) hσ hhom1 ht x
  have htimeDerivEq : deriv (fun s => spatialMultiplierHeatKernel σ x s) t =
      spatialMultiplierHeatKernel (spatialMultiplierTimeSymbol σ) x t :=
    htimeDeriv.deriv
  have htime : ‖deriv (fun s => spatialMultiplierHeatKernel σ x s) t‖ ≤
      C * R ^ (-6 : ℝ) := by
    rw [htimeDerivEq]
    exact hkernelTime.trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left Cₜ Cgrad) (le_max_right C₀ (max Cₜ Cgrad))) hp6)
  have hspaceDiff := spatialMultiplierHeatKernel_hasFDerivAt_spatial
    1 (by norm_num) hσ hhom1 ht x
  refine ⟨hspaceDiff.differentiableAt, htimeDeriv.differentiableAt, ?_, ?_, ?_⟩
  · exact hkernel0.trans (mul_le_mul_of_nonneg_right
      (le_max_left C₀ (max Cₜ Cgrad)) hp4)
  · exact hgrad.trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right Cₜ Cgrad) (le_max_right C₀ (max Cₜ Cgrad))) hp5)
  · simpa [R] using htime

end CKN.Foundation.Euclidean
