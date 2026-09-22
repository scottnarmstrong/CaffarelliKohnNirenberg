-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Topology
import CKN.Foundation.Parabolic.BallDisplays
import CKN.Foundation.Parabolic.Vec3Norm

/-!
# Geometry of a parabolic cylinder inside a metric ball

Three elementary facts comparing a parabolic cylinder `C_ρ(x, t)` with a
metric ball `𝔅_{2R}(z)` of the space-time metric, and comparing the Euclidean
ball `vec3Ball x₀ R` with the concentric ball of its own half-radius.

* `cylinder_radius_lt_of_closure_subset_metricBall`: if the closure of
  `C_ρ(x₀, t₁)` lies in `𝔅_{2R}(z₀)`, then `ρ < 2R`.  The two antipodal
  points `x₀ ± (ρ,0,0)` of the closed spatial ball lie in that closure, so
  their mutual distance `2ρ` is at most `4R` by the triangle inequality
  through `z₀`.
* `vec3Ball_not_subset_of_lt`: a ball of radius `R` is never contained in the
  concentric ball of the smaller radius `ρ/2` whenever `ρ < 2R`, since the
  intermediate radius `(ρ/2 + R)/2` produces a witness in the larger ball but
  not in the smaller one.
* `carrier_radius_lt_of_closure_subset_metricBall`: the conclusion of the
  first fact, rewritten as `ρ/2 < R`.
-/

open Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- The vector `(ρ, 0, 0)`, the axis vector of length `ρ` used to realize a
diameter of the Euclidean ball. -/
private def carrierAxis (ρ : ℝ) : Vec3 := fun k => if k = 0 then ρ else 0

/-- The axis vector has Euclidean norm `ρ` when `ρ` is positive. -/
private theorem carrierAxis_norm {ρ : ℝ} (hρ : 0 < ρ) :
    vec3EuclideanNorm (carrierAxis ρ) = ρ := by
  have h0 : carrierAxis ρ 0 = ρ := by simp [carrierAxis]
  have h1 : carrierAxis ρ 1 = 0 := by simp [carrierAxis]
  have h2 : carrierAxis ρ 2 = 0 := by simp [carrierAxis]
  have hsum : ∑ i : Fin 3, carrierAxis ρ i ^ 2 = ρ ^ 2 := by
    rw [Fin.sum_univ_three, h0, h1, h2]
    ring
  rw [vec3EuclideanNorm, hsum, Real.sqrt_sq_eq_abs, abs_of_pos hρ]

/-- If the closure of the parabolic cylinder `C_ρ(x₀, t₁)` is contained in the
metric ball `𝔅_{2R}(z₀)`, then its radius obeys `ρ < 2R`. -/
theorem cylinder_radius_lt_of_closure_subset_metricBall
    {z₀ : ParabolicPoint} {x₀ : Vec3} {t₁ R ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₁ ρ) ⊆ Metric.ball z₀ (2 * R)) :
    ρ < 2 * R := by
  have haxis : vec3EuclideanNorm (carrierAxis ρ) = ρ := carrierAxis_norm hρ
  have hplus_mem : ((x₀ + carrierAxis ρ, t₁) : ParabolicPoint) ∈
      closure (parabolicCylinder x₀ t₁ ρ) := by
    rw [closure_parabolicCylinder hρ]
    refine ⟨?_, ?_⟩
    · change vec3EuclideanNorm ((x₀ + carrierAxis ρ) - x₀) ≤ ρ
      have h : (x₀ + carrierAxis ρ) - x₀ = carrierAxis ρ := by abel
      rw [h, haxis]
    · exact ⟨by linarith only [sq_nonneg ρ], le_rfl⟩
  have hminus_mem : ((x₀ - carrierAxis ρ, t₁) : ParabolicPoint) ∈
      closure (parabolicCylinder x₀ t₁ ρ) := by
    rw [closure_parabolicCylinder hρ]
    refine ⟨?_, ?_⟩
    · change vec3EuclideanNorm ((x₀ - carrierAxis ρ) - x₀) ≤ ρ
      have h : (x₀ - carrierAxis ρ) - x₀ = -carrierAxis ρ := by abel
      rw [h, vec3EuclideanNorm_neg, haxis]
    · exact ⟨by linarith only [sq_nonneg ρ], le_rfl⟩
  have hplus_ball := hsub hplus_mem
  have hminus_ball := hsub hminus_mem
  rw [metricBall_eq_parabolicBall] at hplus_ball hminus_ball
  have hplus_norm : vec3EuclideanNorm ((x₀ + carrierAxis ρ) - z₀.1) < 2 * R :=
    hplus_ball.1
  have hminus_norm : vec3EuclideanNorm ((x₀ - carrierAxis ρ) - z₀.1) < 2 * R :=
    hminus_ball.1
  have htri : vec3EuclideanNorm ((x₀ + carrierAxis ρ) - (x₀ - carrierAxis ρ)) ≤
      vec3EuclideanNorm ((x₀ + carrierAxis ρ) - z₀.1) +
        vec3EuclideanNorm (z₀.1 - (x₀ - carrierAxis ρ)) := by
    have h := vec3EuclideanNorm_add_le ((x₀ + carrierAxis ρ) - z₀.1)
      (z₀.1 - (x₀ - carrierAxis ρ))
    have harg : ((x₀ + carrierAxis ρ) - z₀.1) + (z₀.1 - (x₀ - carrierAxis ρ)) =
        (x₀ + carrierAxis ρ) - (x₀ - carrierAxis ρ) := by abel
    simpa only [harg] using h
  have hdist : vec3EuclideanNorm ((x₀ + carrierAxis ρ) - (x₀ - carrierAxis ρ)) =
      2 * ρ := by
    have hvec : (x₀ + carrierAxis ρ) - (x₀ - carrierAxis ρ) =
        (2 : ℝ) • carrierAxis ρ := by
      rw [two_smul]
      abel
    rw [hvec, vec3EuclideanNorm_smul, haxis]
    norm_num
  have hsym : vec3EuclideanNorm (z₀.1 - (x₀ - carrierAxis ρ)) =
      vec3EuclideanNorm ((x₀ - carrierAxis ρ) - z₀.1) := by
    have h : z₀.1 - (x₀ - carrierAxis ρ) = -((x₀ - carrierAxis ρ) - z₀.1) := by
      abel
    rw [h, vec3EuclideanNorm_neg]
  have hkey : 2 * ρ < 4 * R := by
    calc
      2 * ρ = vec3EuclideanNorm ((x₀ + carrierAxis ρ) - (x₀ - carrierAxis ρ)) :=
        hdist.symm
      _ ≤ vec3EuclideanNorm ((x₀ + carrierAxis ρ) - z₀.1) +
            vec3EuclideanNorm (z₀.1 - (x₀ - carrierAxis ρ)) := htri
      _ = vec3EuclideanNorm ((x₀ + carrierAxis ρ) - z₀.1) +
            vec3EuclideanNorm ((x₀ - carrierAxis ρ) - z₀.1) := by rw [hsym]
      _ < 2 * R + 2 * R := add_lt_add hplus_norm hminus_norm
      _ = 4 * R := by ring
  linarith only [hkey]

/-- A Euclidean ball of radius `R` is not contained in the concentric ball of
radius `ρ/2` when `ρ < 2R`. -/
theorem vec3Ball_not_subset_of_lt
    {x₀ : Vec3} {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < 2 * R) :
    ¬ (vec3Ball x₀ R ⊆ vec3Ball x₀ (ρ / 2)) := by
  have hR : 0 < R := by linarith only [hρ, hρR]
  have hρ2R : ρ / 2 < R := by linarith only [hρR]
  set c : ℝ := (ρ / 2 + R) / 2 with hc
  have hc_gt : ρ / 2 < c := by rw [hc]; linarith only [hρ2R]
  have hc_lt : c < R := by rw [hc]; linarith only [hρ2R]
  have hc_pos : 0 < c := by
    rw [hc]
    exact div_pos (add_pos (by linarith only [hρ]) hR) (by norm_num)
  intro hcontra
  have hmem : x₀ + carrierAxis c ∈ vec3Ball x₀ R := by
    rw [mem_vec3Ball]
    have h : (x₀ + carrierAxis c) - x₀ = carrierAxis c := by abel
    rw [h, carrierAxis_norm hc_pos]
    exact hc_lt
  have hmem' : x₀ + carrierAxis c ∈
      vec3Ball x₀ (ρ / 2) := hcontra hmem
  rw [mem_vec3Ball] at hmem'
  have h : (x₀ + carrierAxis c) - x₀ = carrierAxis c := by abel
  rw [h, carrierAxis_norm hc_pos] at hmem'
  linarith only [hmem', hc_gt]

/-- If the closure of the parabolic cylinder `C_ρ(x₀, t₁)` is contained in the
metric ball `𝔅_{2R}(z₀)`, then `ρ/2 < R`. -/
theorem carrier_radius_lt_of_closure_subset_metricBall
    {z₀ : ParabolicPoint} {x₀ : Vec3} {t₁ R ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₁ ρ) ⊆ Metric.ball z₀ (2 * R)) :
    ρ / 2 < R := by
  have h := cylinder_radius_lt_of_closure_subset_metricBall (z₀ := z₀) (x₀ := x₀)
    (t₁ := t₁) (R := R) (ρ := ρ) hρ hsub
  linarith only [h]

end CKN.Foundation.Parabolic
