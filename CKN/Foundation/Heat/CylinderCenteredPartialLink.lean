-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.CylinderCentered

open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN.Foundation.Heat

/-- The first spatial derivative of the backward Gaussian test function based at
`z₀ = (x₀, t₀)` equals the corresponding translate of
`heatKernelSpaceDerivative`, scaled by `r²`, without any time restriction. -/
theorem centeredBackwardHeatTest_spatialPartial_eq (x₀ : Vec3) (t₀ r : ℝ)
    (z : ParabolicPoint) (i : Fin 3) :
    spatialPartial (centeredBackwardHeatTest x₀ t₀ r) i z =
      r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) i := by
  by_cases h : z.2 - t₀ < r ^ 2
  · exact centeredBackwardHeatTest_spatialPartial h i
  · have hτ : r ^ 2 - (z.2 - t₀) ≤ 0 := by linarith only [not_lt.1 h]
    have hzero : (fun x : Vec3 => centeredBackwardHeatTest x₀ t₀ r (x, z.2)) = fun _ => 0 := by
      ext x
      simp [centeredBackwardHeatTest, backwardHeatTestFunction,
        heatKernel_eq_zero_of_nonpos hτ]
    have hright : r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) i = 0 := by
      simp [heatKernelSpaceDerivative, not_lt.mpr hτ]
    unfold spatialPartial
    rw [hzero, hright]
    simp

/-- The gradient norm of the backward Gaussian test function based at
`z₀ = (x₀, t₀)` equals the sum of the absolute values of its spatial partial
derivatives. -/
theorem centeredBackwardHeatTestGradientNorm_eq_sum_abs_spatialPartial (x₀ : Vec3)
    (t₀ r : ℝ) (z : ParabolicPoint) :
    centeredBackwardHeatTestGradientNorm x₀ t₀ r z =
      ∑ i, |spatialPartial (centeredBackwardHeatTest x₀ t₀ r) i z| := by
  unfold centeredBackwardHeatTestGradientNorm backwardHeatTestGradientNorm heatKernelGradientNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [centeredBackwardHeatTest_spatialPartial_eq x₀ t₀ r z i,
    abs_mul, abs_of_nonneg (sq_nonneg r)]

end CKN.Foundation.Heat
