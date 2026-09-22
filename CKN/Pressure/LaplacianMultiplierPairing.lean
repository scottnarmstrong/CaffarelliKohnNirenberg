-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.LeibnizLaplacian

/-! # The Laplacian product rule under a linear pairing

The smooth product identity can be paired with any scalar linear functional.
In particular, its algebraic form does not require a locally integrable
function representing the functional.
-/

open CKN.Foundation.Parabolic
open scoped BigOperators

namespace CKN

/-- The Laplacian multiplier identity paired against a linear functional,
with a smooth compactly supported test function. -/
theorem laplacian_multiplier_pairing
    (T : (Vec3 → ℝ) →ₗ[ℝ] ℝ) (η ψ : Vec3 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    T (fun x => η x * spatialLaplacian ψ x) =
      T (spatialLaplacian (fun x => η x * ψ x)) -
        2 * ∑ j : Fin 3, T (spatialDeriv (fun x => spatialDeriv η j x * ψ x) j) +
        T (fun x => spatialLaplacian η x * ψ x) := by
  -- Compact support specifies the test class; the identity itself is algebraic.
  have _ := hψc
  have hsum : (∑ j : Fin 3, spatialDeriv (fun x => spatialDeriv η j x * ψ x) j) =
      fun x => spatialLaplacian η x * ψ x + spatialGradDot η ψ x := by
    funext x
    simp only [Finset.sum_apply]
    have hderiv (j : Fin 3) := spatialDeriv_mul
      ((contDiff_spatialDeriv_smooth hη j).differentiable (by simp)).differentiableAt
      (hψ.differentiable (by simp)).differentiableAt j (x := x)
    simp_rw [hderiv]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, spatialLaplacian, spatialGradDot]
  have hid : (fun x => η x * spatialLaplacian ψ x) =
      spatialLaplacian (fun x => η x * ψ x) -
        (2 : ℝ) • (∑ j : Fin 3, spatialDeriv (fun x => spatialDeriv η j x * ψ x) j) +
        (fun x => spatialLaplacian η x * ψ x) := by
    rw [hsum, spatialLaplacian_mul_smooth hη hψ]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hpair := congrArg T hid
  simpa only [map_add, map_sub, map_smul, map_sum, smul_eq_mul] using hpair

end CKN
