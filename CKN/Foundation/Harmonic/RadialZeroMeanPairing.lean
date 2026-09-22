-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.CompactTestPairing

open MeasureTheory Set
open scoped Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

/-!
# Pairing harmonic functions with radial zero-mass data

The Newtonian potential of smooth, compactly supported radial data with integral zero is
compactly supported. Pairing its Laplacian with a harmonic function therefore vanishes.
-/

namespace CKN.Foundation.Harmonic

/-- A smooth harmonic function pairs to zero with smooth radial compactly supported data
of integral zero. -/
theorem harmonic_radial_zeroMean_test_pairing
    {H g : Vec3 → ℝ} {R : ℝ}
    (hH : ContDiff ℝ 2 H)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hrad : ∀ y z, vec3EuclideanNorm y = vec3EuclideanNorm z → g y = g z)
    (hmean : ∫ y, g y = 0) (hR : 0 < R)
    (hsupp : tsupport g ⊆ euclideanClosedBall (0 : Vec3) R)
    (hHarm : ∀ y ∈ euclideanClosedBall (0 : Vec3) R,
      CKN.spatialLaplacian H y = 0) :
    ∫ y, H y * g y = 0 := by
  let w : Vec3 → ℝ := CKN.pressureNewtonianPotential g
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := by
    exact CKN.pressureNewtonianPotential_smooth hg hgc
  have hsuppMetric : tsupport g ⊆ Metric.closedBall (0 : Vec3) R := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hEucl₀ : CKN.vecEuclideanNorm y ≤ R := by
      simpa using (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).1 (hsupp hy)
    have hnormEq : vec3EuclideanNorm y = CKN.vecEuclideanNorm y := by
      rw [vec3EuclideanNorm_eq_l2,
        CKN.Foundation.Harmonic.Commutator.vecEuclideanNorm_eq_l2]
    have hEucl : vec3EuclideanNorm y ≤ R := hnormEq.le.trans hEucl₀
    exact (CKN.space_norm_le_euclideanNorm y).trans hEucl
  have hwout : ∀ y, R < vec3EuclideanNorm y → w y = 0 := by
    intro y hy
    exact radial_zeroMean_potential_vanishes hrad hg hgc hmean hR hsuppMetric hy
  have hwsuppFun : Function.support w ⊆ euclideanClosedBall 0 R := by
    intro y hy
    change w y ≠ 0 at hy
    by_contra hnot
    have hnorm : R < vec3EuclideanNorm y := by
      by_contra hle
      apply hnot
      have hnormEq : vec3EuclideanNorm y = CKN.vecEuclideanNorm (y - 0) := by
        rw [sub_zero, vec3EuclideanNorm_eq_l2,
          CKN.Foundation.Harmonic.Commutator.vecEuclideanNorm_eq_l2]
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).2
        (by rw [← hnormEq]; exact le_of_not_gt hle)
    exact hy (hwout y hnorm)
  have hwc : HasCompactSupport w :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_euclideanClosedBall 0 hR.le) hwsuppFun
  have hwsupp : tsupport w ⊆ euclideanClosedBall 0 R :=
    closure_minimal hwsuppFun (isClosed_euclideanClosedBall 0 R)
  have hwlap := CKN.pressureNewtonianPotential_laplacian_eq hg hgc
  have hpair := harmonic_laplacian_compact_test_pairing hH hw hwc
    (fun y hy => hHarm y (hwsupp hy))
  calc
    ∫ y, H y * g y = ∫ y, H y * CKN.spatialLaplacian w y := by
      congr 1
      funext y
      rw [show CKN.spatialLaplacian w y =
        CKN.spatialLaplacian (CKN.pressureNewtonianPotential g) y by rfl,
        hwlap y]
    _ = 0 := hpair

end CKN.Foundation.Harmonic
