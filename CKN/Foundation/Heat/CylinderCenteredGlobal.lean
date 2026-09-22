-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.CylinderCentered

open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Heat

/-- `eq:psi-upper`: the backward Gaussian test function based at
`z₀ = (x₀, t₀)` is bounded above by `1000/r` for every `x` and every
`t ≤ t₀`. -/
theorem centeredBackwardHeatTest_le_of_le {x₀ : Vec3} {t₀ r : ℝ} (hr : 0 < r)
    {z : ParabolicPoint} (ht : z.2 ≤ t₀) :
    centeredBackwardHeatTest x₀ t₀ r z ≤ 1000 / r := by
  have hupp : z.2 - t₀ ≤ 0 := sub_nonpos.2 ht
  have hτ : 0 < r ^ 2 - (z.2 - t₀) := by
    nlinarith only [sq_pos_of_pos hr, hupp]
  have hsqrt : r ≤ Real.sqrt (r ^ 2 - (z.2 - t₀)) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (r ^ 2 - (z.2 - t₀)) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (r ^ 2 - (z.2 - t₀))) ^ 2 = r ^ 2 - (z.2 - t₀) :=
      Real.sq_sqrt hτ.le
    apply (sq_le_sq₀ hr.le hsqrt_nonneg).mp
    nlinarith only [hupp, hsqrt_sq]
  have hrho : r ≤ rhoTwo (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) := by
    unfold rhoTwo
    exact hsqrt.trans (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg _))
  have hG := heatKernel_le_rho_inv_cube (x := z.1 - x₀) hτ
  have hdiv : 1000 / rhoTwo (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) ^ 3 ≤ 1000 / r ^ 3 := by
    gcongr
  unfold centeredBackwardHeatTest
  rw [backwardHeatTestFunction]
  calc
    r ^ 2 * heatKernel (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) ≤
        r ^ 2 * (1000 / rhoTwo (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) ^ 3) := by gcongr
    _ ≤ r ^ 2 * (1000 / r ^ 3) := by gcongr
    _ = 1000 / r := by field_simp [hr.ne']

/-- `eq:grad-psi` upper bound: the gradient norm of the backward Gaussian test
function based at `z₀ = (x₀, t₀)` is bounded above by `300000/r²` for every
`x` and every `t ≤ t₀`. -/
theorem centeredBackwardHeatTestGradientNorm_le_of_le {x₀ : Vec3} {t₀ r : ℝ} (hr : 0 < r)
    {z : ParabolicPoint} (ht : z.2 ≤ t₀) :
    centeredBackwardHeatTestGradientNorm x₀ t₀ r z ≤ 300000 / r ^ 2 := by
  have hupp : z.2 - t₀ ≤ 0 := sub_nonpos.2 ht
  have hτ : 0 < r ^ 2 - (z.2 - t₀) := by
    nlinarith only [sq_pos_of_pos hr, hupp]
  have hsqrt : r ≤ Real.sqrt (r ^ 2 - (z.2 - t₀)) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (r ^ 2 - (z.2 - t₀)) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (r ^ 2 - (z.2 - t₀))) ^ 2 = r ^ 2 - (z.2 - t₀) :=
      Real.sq_sqrt hτ.le
    apply (sq_le_sq₀ hr.le hsqrt_nonneg).mp
    nlinarith only [hupp, hsqrt_sq]
  have hrho : r ≤ rhoTwo (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) := by
    unfold rhoTwo
    exact hsqrt.trans (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg _))
  have hG := heatKernelGradientNorm_le_rho_inv_four (x := z.1 - x₀) hτ
  have hdiv : 300000 / rhoTwo (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) ^ 4 ≤ 300000 / r ^ 4 := by
    gcongr
  unfold centeredBackwardHeatTestGradientNorm
  rw [backwardHeatTestGradientNorm]
  calc
    r ^ 2 * heatKernelGradientNorm (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) ≤
        r ^ 2 * (300000 / rhoTwo (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) ^ 4) := by gcongr
    _ ≤ r ^ 2 * (300000 / r ^ 4) := by gcongr
    _ = 300000 / r ^ 2 := by field_simp [hr.ne']

end CKN.Foundation.Heat
