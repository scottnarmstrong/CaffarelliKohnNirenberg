-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.CylinderCenteredGradient

open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN.Foundation.Heat

/-- Combined gradient norm identity and sharp bound for the
centred backward heat test function, expressed with `rpow` powers
of `τ = r² − (t − t₀)` and of `2e`. -/
theorem centeredBackwardHeatTestGradient_norm_eq_and_le
    {x₀ : Vec3} {t₀ r : ℝ} {z : ParabolicPoint}
    (ht : z.2 - t₀ < r ^ 2) :
    vec3EuclideanNorm
        (fun i => spatialPartial (centeredBackwardHeatTest x₀ t₀ r) i z) =
      r ^ 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2)
        * (r ^ 2 - (z.2 - t₀)) ^ (-(2 : ℝ))
        * Real.sqrt (vec3EuclideanNorm (z.1 - x₀) ^ 2
            / (4 * (r ^ 2 - (z.2 - t₀))))
        * Real.exp (-(vec3EuclideanNorm (z.1 - x₀) ^ 2
            / (4 * (r ^ 2 - (z.2 - t₀))))) ∧
      vec3EuclideanNorm
        (fun i => spatialPartial (centeredBackwardHeatTest x₀ t₀ r) i z) ≤
      r ^ 2 * (4 * Real.pi) ^ (-(3 : ℝ) / 2)
        * (2 * Real.exp 1) ^ (-(1 : ℝ) / 2)
        * (r ^ 2 - (z.2 - t₀)) ^ (-(2 : ℝ)) := by
  set τ := r ^ 2 - (z.2 - t₀) with hτ_def
  have hτ : 0 < τ := by linarith only [ht]
  have hτ_nonneg : 0 ≤ τ := hτ.le
  have hτ_nonneg' : 0 ≤ r ^ 2 - (z.2 - t₀) := by linarith only [ht]
  have h_scalar1 : (r ^ 2 - (z.2 - t₀)) ^ (-(2 : ℝ)) = ((r ^ 2 - (z.2 - t₀)) ^ 2)⁻¹ := by
    calc
      (r ^ 2 - (z.2 - t₀)) ^ (-(2 : ℝ)) = ((r ^ 2 - (z.2 - t₀)) ^ (2 : ℝ))⁻¹ := by
        rw [Real.rpow_neg hτ_nonneg']
      _ = ((r ^ 2 - (z.2 - t₀)) ^ 2)⁻¹ := by simp
  have h_scalar2 : (2 * Real.exp 1) ^ (-(1 : ℝ) / 2) = (Real.sqrt (2 * Real.exp 1))⁻¹ := by
    have h_nonneg : 0 ≤ 2 * Real.exp 1 := by positivity
    calc
      (2 * Real.exp 1) ^ (-(1 : ℝ) / 2) = (2 * Real.exp 1) ^ (-((1 : ℝ) / 2)) := by
        rw [neg_div]
      _ = ((2 * Real.exp 1) ^ ((1 : ℝ) / 2))⁻¹ := by rw [Real.rpow_neg h_nonneg]
      _ = (Real.sqrt (2 * Real.exp 1))⁻¹ := by rw [Real.sqrt_eq_rpow]
  constructor
  · rw [vec3EuclideanNorm_spatialPartial_centeredBackwardHeatTest x₀ t₀ r z]
    rw [h_scalar1]
    rw [← mul_assoc]
  · apply (vec3EuclideanNorm_spatialPartial_centeredBackwardHeatTest_le_sharp x₀ t₀ r z).trans
    rw [h_scalar1, h_scalar2]
    simp [mul_assoc, mul_comm, mul_left_comm]

end CKN.Foundation.Heat
