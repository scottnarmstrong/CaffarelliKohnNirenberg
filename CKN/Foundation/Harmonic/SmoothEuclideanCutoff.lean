-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.InteriorBasic
import CKN.Foundation.Harmonic.Commutator.SphereTransport
import CKN.Foundation.Sobolev.Cutoff.BallTopology
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

open Set
open scoped Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

/-!
# Smooth cutoffs on Euclidean balls

This file constructs a smooth cutoff on a Euclidean ball, with a plateau on a smaller
closed ball and compact support in the larger closed ball.
-/

namespace CKN.Foundation.Harmonic

private abbrev E3 := WithLp 2 Vec3

private def centeredHarmonicBump (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ContDiffBump (0 : E3) := ⟨a, b, ha, hab⟩

/-- A smooth cutoff equal to one on the closed ball of radius `a` and supported in the
closed ball of radius `b`. -/
def harmonicBumpCutoff (a b : ℝ) (ha : 0 < a) (hab : a < b) : Vec3 → ℝ :=
  fun y => centeredHarmonicBump a b ha hab (WithLp.toLp 2 y)

lemma harmonicBumpCutoff_contDiff (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicBumpCutoff a b ha hab) := by
  have hto : ContDiff ℝ (⊤ : ℕ∞) (WithLp.toLp 2 : Vec3 → E3) := by fun_prop
  exact (centeredHarmonicBump a b ha hab).contDiff.comp hto

lemma harmonicBumpCutoff_support_subset (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Function.support (harmonicBumpCutoff a b ha hab) ⊆ euclideanBall 0 b := by
  intro y hy
  have hmem : WithLp.toLp 2 y ∈ Function.support (centeredHarmonicBump a b ha hab) :=
    Function.mem_support.mpr hy
  rw [(centeredHarmonicBump a b ha hab).support_eq] at hmem
  have hnorm : ‖WithLp.toLp 2 y‖ < b := by
    rw [Metric.mem_ball, dist_zero_right, centeredHarmonicBump] at hmem
    exact hmem
  have hnormEq : CKN.vecEuclideanNorm (y - 0) = ‖WithLp.toLp 2 y‖ := by
    rw [sub_zero, CKN.Foundation.Harmonic.Commutator.vecEuclideanNorm_eq_l2]
  have hb : 0 < b := lt_trans ha hab
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hb).2
  simpa only [← hnormEq] using hnorm

lemma harmonicBumpCutoff_tsupport_subset (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    tsupport (harmonicBumpCutoff a b ha hab) ⊆ euclideanClosedBall 0 b :=
  closure_minimal (by
    intro y hy
    have hb : 0 < b := lt_trans ha hab
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hb.le).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hb).1
      (harmonicBumpCutoff_support_subset a b ha hab hy)).le)
    (isClosed_euclideanClosedBall 0 b)

lemma harmonicBumpCutoff_hasCompactSupport (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    HasCompactSupport (harmonicBumpCutoff a b ha hab) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_euclideanClosedBall 0
    (R := b) (le_of_lt (lt_trans ha hab))) (by
      intro y hy
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (R := b) (le_of_lt (lt_trans ha hab))).2
      exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt
        (R := b) (lt_trans ha hab)).1
        (harmonicBumpCutoff_support_subset a b ha hab hy)).le)

lemma harmonicBumpCutoff_eq_one (a b : ℝ) (ha : 0 < a) (hab : a < b)
    {y : Vec3} (hy : y ∈ euclideanClosedBall 0 a) :
    harmonicBumpCutoff a b ha hab y = 1 := by
  apply (centeredHarmonicBump a b ha hab).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnormEq : CKN.vecEuclideanNorm (y - 0) = ‖WithLp.toLp 2 y‖ := by
    rw [sub_zero, CKN.Foundation.Harmonic.Commutator.vecEuclideanNorm_eq_l2]
  have hy' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le ha.le).1 hy
  calc
    ‖WithLp.toLp 2 y‖ = CKN.vecEuclideanNorm (y - 0) := hnormEq.symm
    _ ≤ a := hy'

end CKN.Foundation.Harmonic
