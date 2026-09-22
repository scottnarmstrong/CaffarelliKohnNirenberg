-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.CylinderCenteredGlobal
import CKN.Foundation.Heat.CylinderCenteredPartialLink
import CKN.Foundation.Heat.SqrtExpSup
import CKN.Foundation.Parabolic.Vec3Norm

open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Heat

/-- The Euclidean norm of the spatial gradient of the centred backward heat
test function equals the closed-form expression
`r² (4π)^{-3/2} τ^{-2} √(|y|²/(4τ)) e^{-|y|²/(4τ)}` where
`τ = r² − (t − t₀)` and `y = x − x₀`. -/
theorem vec3EuclideanNorm_spatialPartial_centeredBackwardHeatTest (x₀ : Vec3)
    (t₀ r : ℝ) (z : ParabolicPoint) :
    vec3EuclideanNorm (fun i => spatialPartial (centeredBackwardHeatTest x₀ t₀ r) i z) =
      r ^ 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2) * ((r ^ 2 - (z.2 - t₀)) ^ 2)⁻¹ *
        (Real.sqrt (vec3EuclideanNorm (z.1 - x₀) ^ 2 / (4 * (r ^ 2 - (z.2 - t₀)))) *
          Real.exp (-(vec3EuclideanNorm (z.1 - x₀) ^ 2 / (4 * (r ^ 2 - (z.2 - t₀)))))) := by
  set τ := r ^ 2 - (z.2 - t₀) with hτ_def
  set y := z.1 - x₀ with hy_def
  by_cases hτ : 0 < τ
  · -- case τ > 0: the partials are nonzero
    have h_abs_y_nonneg : 0 ≤ vec3EuclideanNorm y := vec3EuclideanNorm_nonneg _
    -- the vector of partials equals a scalar multiple of y
    have hvec_eq : (fun i => spatialPartial (centeredBackwardHeatTest x₀ t₀ r) i z) =
        (-(r ^ 2 * heatKernel y τ) / (2 * τ)) • y := by
      ext i
      rw [centeredBackwardHeatTest_spatialPartial_eq x₀ t₀ r z i,
        heatKernelSpaceDerivative, ite_eq_left hτ]
      dsimp [y, τ]
      ring_nf
    rw [hvec_eq, vec3EuclideanNorm_smul]
    have h_abs_scalar : |-(r ^ 2 * heatKernel y τ) / (2 * τ)| =
        r ^ 2 * heatKernel y τ / (2 * τ) := by
      rw [abs_div, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg r) (heatKernel_nonneg y τ)),
        abs_of_pos (by positivity : 0 < 2 * τ)]
    rw [h_abs_scalar, heatKernel_eq_formula hτ]
    -- now we have: (r² * G / (2τ)) * |y| where G = (4πτ)^{-3/2} * exp(-|y|²/(4τ))
    -- we need to rewrite to the target form
    -- first, rewrite the exp argument to match the goal
    have h_exp_eq : Real.exp (-(vec3EuclideanNorm y) ^ 2 / (4 * τ)) =
        Real.exp (-(vec3EuclideanNorm y ^ 2 / (4 * τ))) := by ring_nf
    rw [h_exp_eq]
    -- goal: (r^2 * G/(2τ)) * |y| = r^2 * (4π)^{-3/2} * τ^{-2} * sqrt(...) * exp(...)
    -- use Real.mul_rpow to split (4π·τ)^{-3/2}
    have hG : (4 * Real.pi * τ) ^ (-(3 : ℝ) / 2) =
        (4 * Real.pi) ^ (-(3 : ℝ) / 2) * τ ^ (-(3 : ℝ) / 2) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) hτ.le]
    rw [hG]
    -- after hG: (r^2 * (4π)^{-3/2} * τ^{-3/2} * exp(...))/(2τ) * |y| = ...
    -- key identity: τ^{-3/2}/(2τ) * |y| = (4π)^{-3/2} * τ^{-2} * sqrt(|y|^2/(4τ))
    -- This is the key identity.
    have h_main : (τ ^ (-(3 : ℝ) / 2)) * (2 * τ)⁻¹ * vec3EuclideanNorm y =
        ((τ ^ 2)⁻¹) * Real.sqrt (vec3EuclideanNorm y ^ 2 / (4 * τ)) := by
      have hy_nonneg : 0 ≤ vec3EuclideanNorm y := h_abs_y_nonneg
      have hτ_nonneg : 0 ≤ τ := hτ.le
      -- rewrite RHS: (τ²)⁻¹ * √(|y|²/(4τ)) = (τ²)⁻¹ * |y| * (√(4τ))⁻¹
      have h_rhs : ((τ ^ 2)⁻¹) * Real.sqrt (vec3EuclideanNorm y ^ 2 / (4 * τ)) =
          ((τ ^ 2)⁻¹) * vec3EuclideanNorm y * (Real.sqrt (4 * τ))⁻¹ := by
        rw [Real.sqrt_div (sq_nonneg _) (4 * τ),
          Real.sqrt_sq hy_nonneg]
        ring_nf
      rw [h_rhs]
      -- key identity: τ^{-3/2} * (2τ)⁻¹ = (τ²)⁻¹ * (√(4τ))⁻¹
      -- both sides equal 2⁻¹ * τ^{-5/2}
      have h_eq : (τ ^ (-(3 : ℝ) / 2)) * (2 * τ)⁻¹ = (τ ^ 2)⁻¹ * (Real.sqrt (4 * τ))⁻¹ := by
        have hL : (τ ^ (-(3 : ℝ) / 2)) * (2 * τ)⁻¹ = (2⁻¹ : ℝ) * (τ ^ (-(5 : ℝ) / 2)) := by
          calc
            (τ ^ (-(3 : ℝ) / 2)) * (2 * τ)⁻¹ = (τ ^ (-(3 : ℝ) / 2)) * (2⁻¹ * τ⁻¹) := by ring_nf
            _ = 2⁻¹ * (τ ^ (-(3 : ℝ) / 2) * τ⁻¹) := by ring_nf
            _ = 2⁻¹ * (τ ^ (-(3 : ℝ) / 2) * τ ^ (-1 : ℝ)) := by rw [Real.rpow_neg_one τ]
            _ = 2⁻¹ * (τ ^ ((-(3 : ℝ) / 2) + (-1 : ℝ))) := by
              rw [Real.rpow_add hτ (-(3 : ℝ) / 2) (-1 : ℝ)]
            _ = 2⁻¹ * (τ ^ (-(5 : ℝ) / 2)) := by ring_nf
        have hR : (τ ^ 2)⁻¹ * (Real.sqrt (4 * τ))⁻¹ = (2⁻¹ : ℝ) * (τ ^ (-(5 : ℝ) / 2)) := by
          have h_sqrt : Real.sqrt (4 * τ) = 2 * Real.sqrt τ := by
            calc
              Real.sqrt (4 * τ) = Real.sqrt 4 * Real.sqrt τ := by
                rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) τ]
              _ = 2 * Real.sqrt τ := by
                have h_sqrt4 : Real.sqrt (4 : ℝ) = 2 := by
                  have h : (2 : ℝ) ^ 2 = 4 := by norm_num
                  rw [← h, Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))]
                rw [h_sqrt4]
          rw [h_sqrt]
          calc
            (τ ^ 2)⁻¹ * (2 * Real.sqrt τ)⁻¹ = (τ ^ 2)⁻¹ * (2⁻¹ * (Real.sqrt τ)⁻¹) := by rw [mul_inv]
            _ = 2⁻¹ * ((τ ^ 2)⁻¹ * (Real.sqrt τ)⁻¹) := by ring_nf
            _ = 2⁻¹ * ((τ ^ (2 : ℝ))⁻¹ * (τ ^ (1/2 : ℝ))⁻¹) := by
              rw [show (τ ^ 2)⁻¹ = (τ ^ (2 : ℝ))⁻¹ by simp,
                show (Real.sqrt τ)⁻¹ = (τ ^ (1/2 : ℝ))⁻¹ by rw [Real.sqrt_eq_rpow]]
            _ = 2⁻¹ * (τ ^ (-2 : ℝ) * τ ^ (-(1/2 : ℝ))) := by
              rw [Real.rpow_neg hτ_nonneg (2 : ℝ), Real.rpow_neg hτ_nonneg (1/2 : ℝ)]
            _ = 2⁻¹ * (τ ^ ((-2 : ℝ) + (-(1/2 : ℝ)))) := by
              rw [Real.rpow_add hτ (-2 : ℝ) (-(1/2 : ℝ))]
            _ = 2⁻¹ * (τ ^ (-(5 : ℝ) / 2)) := by ring_nf
        rw [hL, hR]
      calc
        (τ ^ (-(3 : ℝ) / 2)) * (2 * τ)⁻¹ * vec3EuclideanNorm y =
            ((τ ^ (-(3 : ℝ) / 2)) * (2 * τ)⁻¹) * vec3EuclideanNorm y := by ring_nf
        _ = ((τ ^ 2)⁻¹ * (Real.sqrt (4 * τ))⁻¹) * vec3EuclideanNorm y := by rw [h_eq]
        _ = ((τ ^ 2)⁻¹) * vec3EuclideanNorm y * (Real.sqrt (4 * τ))⁻¹ := by ring_nf
    -- Now use h_main to rewrite the goal
    calc
      (r ^ 2 * ((4 * Real.pi) ^ (-(3 : ℝ) / 2) * τ ^ (-(3 : ℝ) / 2) *
          Real.exp (-(vec3EuclideanNorm y ^ 2 / (4 * τ)))) / (2 * τ)) * vec3EuclideanNorm y =
        r ^ 2 * ((4 * Real.pi) ^ (-(3 : ℝ) / 2)) *
          ((τ ^ (-(3 : ℝ) / 2)) * (2 * τ)⁻¹ * vec3EuclideanNorm y) *
          Real.exp (-(vec3EuclideanNorm y ^ 2 / (4 * τ))) := by ring_nf
      _ = r ^ 2 * ((4 * Real.pi) ^ (-(3 : ℝ) / 2)) *
          (((τ ^ 2)⁻¹) * Real.sqrt (vec3EuclideanNorm y ^ 2 / (4 * τ))) *
          Real.exp (-(vec3EuclideanNorm y ^ 2 / (4 * τ))) := by rw [h_main]
      _ = r ^ 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2) * ((r ^ 2 - (z.2 - t₀)) ^ 2)⁻¹ *
          (Real.sqrt (vec3EuclideanNorm (z.1 - x₀) ^ 2 / (4 * (r ^ 2 - (z.2 - t₀)))) *
            Real.exp (-(vec3EuclideanNorm (z.1 - x₀) ^ 2 / (4 * (r ^ 2 - (z.2 - t₀)))))) := by
        dsimp [τ, y]
        ring_nf
  · -- case τ ≤ 0: all partials vanish
    have hτ_le : τ ≤ 0 := le_of_not_gt hτ
    have hzero : (fun i => spatialPartial (centeredBackwardHeatTest x₀ t₀ r) i z) = 0 := by
      ext i
      rw [centeredBackwardHeatTest_spatialPartial_eq x₀ t₀ r z i,
        heatKernelSpaceDerivative, ite_eq_right (not_lt.mpr hτ_le)]
      simp
    rw [hzero, vec3EuclideanNorm_zero]
    have h_nonpos : 4 * τ ≤ 0 := by nlinarith only [hτ_le]
    have h_div_nonpos : vec3EuclideanNorm (z.1 - x₀) ^ 2 / (4 * τ) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h_nonpos
    have h_sqrt_zero : Real.sqrt (vec3EuclideanNorm (z.1 - x₀) ^ 2 / (4 * τ)) = 0 :=
      Real.sqrt_eq_zero_of_nonpos h_div_nonpos
    dsimp [τ, y]
    rw [h_sqrt_zero]
    simp

/-- `eq:grad-psi` sharp upper bound: the Euclidean norm of the spatial gradient
of the centred backward heat test function is bounded by
`r² (4π)^{-3/2} (2e)^{-1/2} τ^{-2}`. -/
theorem vec3EuclideanNorm_spatialPartial_centeredBackwardHeatTest_le_sharp (x₀ : Vec3)
    (t₀ r : ℝ) (z : ParabolicPoint) :
    vec3EuclideanNorm (fun i => spatialPartial (centeredBackwardHeatTest x₀ t₀ r) i z) ≤
      r ^ 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2) * ((r ^ 2 - (z.2 - t₀)) ^ 2)⁻¹ *
        (Real.sqrt (2 * Real.exp 1))⁻¹ := by
  rw [vec3EuclideanNorm_spatialPartial_centeredBackwardHeatTest x₀ t₀ r z]
  have hABC : 0 ≤ r ^ 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2) * ((r ^ 2 - (z.2 - t₀)) ^ 2)⁻¹ := by
    positivity
  have hDE : Real.sqrt (vec3EuclideanNorm (z.1 - x₀) ^ 2 / (4 * (r ^ 2 - (z.2 - t₀)))) *
    Real.exp (-(vec3EuclideanNorm (z.1 - x₀) ^ 2 / (4 * (r ^ 2 - (z.2 - t₀))))) ≤
    (Real.sqrt (2 * Real.exp 1))⁻¹ :=
    sqrt_mul_exp_neg_le _
  exact mul_le_mul_of_nonneg_left hDE hABC

end CKN.Foundation.Heat
