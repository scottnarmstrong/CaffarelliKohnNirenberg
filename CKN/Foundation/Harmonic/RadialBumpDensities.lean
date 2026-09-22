-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.InteriorBasic
import CKN.Foundation.Sobolev.Cutoff.BallTopology
import CKN.Foundation.Harmonic.Commutator.SphereTransport
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped Topology
open CKN.Foundation.Parabolic CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

/-!
# Smooth radial bump functions on Euclidean balls

This file provides smooth radial bump functions, used to approximate point
evaluation and solid-ball averages.
-/

namespace CKN.Foundation.Harmonic

private def scalarRadialBump (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) : ContDiffBump (0 : ℝ) :=
  ⟨α * r ^ 2, r ^ 2, mul_pos hα (sq_pos_of_pos hr), by
    nlinarith only [hα1, sq_pos_of_pos hr]⟩

/-- A smooth radial bump which equals one on the `sqrt α` fraction of a ball. -/
def radialQBump (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) : Vec3 → ℝ :=
  fun y => scalarRadialBump r α hr hα hα1 (q y)

lemma radialQBump_contDiff (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (radialQBump r α hr hα hα1) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := by
    unfold q
    exact ContDiff.sum (fun i hi => (contDiff_apply ℝ ℝ i).pow 2)
  exact (scalarRadialBump r α hr hα hα1).contDiff.comp hq

lemma radialQBump_nonneg (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) (y : Vec3) :
    0 ≤ radialQBump r α hr hα hα1 y := by
  exact (scalarRadialBump r α hr hα hα1).nonneg

lemma radialQBump_le_one (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) (y : Vec3) :
    radialQBump r α hr hα hα1 y ≤ 1 := by
  exact (scalarRadialBump r α hr hα hα1).le_one

lemma radialQBump_one_of_norm_le_inner (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) {y : Vec3}
    (hy : vec3EuclideanNorm y ^ 2 ≤ α * r ^ 2) :
    radialQBump r α hr hα hα1 y = 1 := by
  apply (scalarRadialBump r α hr hα hα1).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  have hq := q_eq_vec3Norm_sq y
  change |q y| ≤ α * r ^ 2
  rw [abs_of_nonneg]
  · rw [hq]
    exact hy
  · unfold q
    exact Finset.sum_nonneg (fun i hi => sq_nonneg (y i))

lemma radialQBump_support_subset (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) :
    Function.support (radialQBump r α hr hα hα1) ⊆ euclideanBall 0 r := by
  intro y hy
  have hsource : q y ∈ Function.support (scalarRadialBump r α hr hα hα1) :=
    Function.mem_support.mpr hy
  rw [(scalarRadialBump r α hr hα hα1).support_eq] at hsource
  have hqbound : q y < r ^ 2 := by
    have hdist := Metric.mem_ball.mp hsource
    have hqnonneg : 0 ≤ q y := by
      unfold q
      exact Finset.sum_nonneg (fun i hi => sq_nonneg (y i))
    have hdist' : |q y| < r ^ 2 := by
      simpa [dist_eq_norm, Real.norm_eq_abs, scalarRadialBump] using hdist
    rwa [abs_of_nonneg hqnonneg] at hdist'
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
  have hq := q_eq_vec3Norm_sq y
  have hnorm : vec3EuclideanNorm y < r := by
    nlinarith only [hq, hqbound, hr]
  have hnormEq : vec3EuclideanNorm y = CKN.vecEuclideanNorm (y - 0) := by
    rw [sub_zero, vec3EuclideanNorm_eq_l2,
      CKN.Foundation.Harmonic.Commutator.vecEuclideanNorm_eq_l2]
  rw [← hnormEq]
  exact hnorm

lemma radialQBump_hasCompactSupport (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) :
    HasCompactSupport (radialQBump r α hr hα hα1) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_euclideanClosedBall 0 hr.le) (by
      intro y hy
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
      exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1
        (radialQBump_support_subset r α hr hα hα1 hy)).le)

lemma radialQBump_tsupport_subset (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) :
    tsupport (radialQBump r α hr hα hα1) ⊆ euclideanClosedBall 0 r :=
  closure_minimal (by
    intro y hy
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1
      (radialQBump_support_subset r α hr hα hα1 hy)).le)
    (isClosed_euclideanClosedBall 0 r)

lemma radialQBump_radial (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) {y z : Vec3}
    (hyz : vec3EuclideanNorm y = vec3EuclideanNorm z) :
    radialQBump r α hr hα hα1 y = radialQBump r α hr hα hα1 z := by
  have hq : q y = q z := by rw [q_eq_vec3Norm_sq, q_eq_vec3Norm_sq, hyz]
  simp [radialQBump, hq]

lemma radialQBump_integral_pos (r α : ℝ) (hr : 0 < r)
    (hα : 0 < α) (hα1 : α < 1) :
    0 < ∫ y, radialQBump r α hr hα hα1 y := by
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((radialQBump_contDiff r α hr hα hα1).continuous)
    (radialQBump_hasCompactSupport r α hr hα hα1)
    (radialQBump_nonneg r α hr hα hα1)
  have hval : radialQBump r α hr hα hα1 0 = 1 := by
    apply radialQBump_one_of_norm_le_inner r α hr hα hα1
    simp [vec3EuclideanNorm_zero]
    positivity
  rw [hval]
  norm_num

end CKN.Foundation.Harmonic
