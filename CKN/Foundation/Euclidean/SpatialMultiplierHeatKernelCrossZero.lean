-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelLocalIntegrable

/-!
# Cross-zero estimates for multiplier heat kernels

The kernel value and spatial gradient satisfy their parabolic bounds on the
whole time axis. Its time derivative bound is extended to nonzero times.
-/

open scoped BigOperators Topology

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat

/-- The value and spatial-gradient bounds hold for every time. The time-derivative
bound holds away from the causal interface `t = 0`, with one symbol-dependent
constant fixed before the space-time point. -/
theorem exists_spatialMultiplierHeatKernel_crossZero_bounds
    (σ : Vec3 → ℂ)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec3, ∀ t : ℝ,
      ‖spatialMultiplierHeatKernel σ x t‖ ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt |t|)) ^ (-4 : ℝ) ∧
      Real.sqrt (∑ j : Fin 3,
        ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x)
          (basisVec j)‖ ^ 2) ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt |t|)) ^ (-5 : ℝ) ∧
      (t ≠ 0 →
        DifferentiableAt ℝ (fun s => spatialMultiplierHeatKernel σ x s) t ∧
        ‖deriv (fun s => spatialMultiplierHeatKernel σ x s) t‖ ≤
          C * (max (vec3EuclideanNorm x) (Real.sqrt |t|)) ^ (-6 : ℝ)) := by
  obtain ⟨C, hC, hbounds⟩ :=
    exists_spatialMultiplierHeatKernel_bounds_of_degreeOne σ hσ hhom
  refine ⟨C, hC, ?_⟩
  intro x t
  by_cases ht : 0 < t
  · obtain ⟨_, htimeDiff, hvalue, hgradient, htime⟩ := hbounds x t ht
    refine ⟨?_, ?_, ?_⟩
    · simpa only [abs_of_pos ht] using hvalue
    · simpa only [abs_of_pos ht] using hgradient
    · intro _
      exact ⟨htimeDiff, by simpa only [abs_of_pos ht] using htime⟩
  · have htn : t ≤ 0 := le_of_not_gt ht
    have hbase : 0 ≤ max (vec3EuclideanNorm x) (Real.sqrt |t|) :=
      (vec3EuclideanNorm_nonneg x).trans (le_max_left _ _)
    have hzeroValue :
        ‖spatialMultiplierHeatKernel σ x t‖ ≤
          C * (max (vec3EuclideanNorm x) (Real.sqrt |t|)) ^ (-4 : ℝ) := by
      rw [spatialMultiplierHeatKernel_of_nonpos σ x htn]
      simp only [norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg hbase _)
    have hzeroFun :
        (fun y : Vec3 => spatialMultiplierHeatKernel σ y t) = fun _ => (0 : ℂ) := by
      funext y
      exact spatialMultiplierHeatKernel_of_nonpos σ y htn
    have hzeroGradient :
        Real.sqrt (∑ j : Fin 3,
          ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x)
            (basisVec j)‖ ^ 2) ≤
          C * (max (vec3EuclideanNorm x) (Real.sqrt |t|)) ^ (-5 : ℝ) := by
      have hgradzero : Real.sqrt (∑ j : Fin 3,
          ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x)
            (basisVec j)‖ ^ 2) = 0 := by
        rw [hzeroFun]
        simp
      rw [hgradzero]
      exact mul_nonneg hC (Real.rpow_nonneg hbase _)
    have hzeroTime : t ≠ 0 →
        DifferentiableAt ℝ (fun s => spatialMultiplierHeatKernel σ x s) t ∧
        ‖deriv (fun s => spatialMultiplierHeatKernel σ x s) t‖ ≤
          C * (max (vec3EuclideanNorm x) (Real.sqrt |t|)) ^ (-6 : ℝ) := by
      intro hne
      have htn' : t < 0 := by
        by_contra hnot
        have hnonneg : 0 ≤ t := le_of_not_gt hnot
        exact hne (le_antisymm htn hnonneg)
      have hevent :
          (fun s : ℝ => spatialMultiplierHeatKernel σ x s) =ᶠ[𝓝 t]
            fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds htn'] with s hs
        exact spatialMultiplierHeatKernel_of_nonpos σ x (le_of_lt hs)
      have hderiv : HasDerivAt
          (fun s : ℝ => spatialMultiplierHeatKernel σ x s) 0 t :=
        (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hevent
      refine ⟨hderiv.differentiableAt, ?_⟩
      rw [hderiv.deriv, norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg hbase _)
    exact ⟨hzeroValue, hzeroGradient, hzeroTime⟩

end CKN.Foundation.Euclidean
