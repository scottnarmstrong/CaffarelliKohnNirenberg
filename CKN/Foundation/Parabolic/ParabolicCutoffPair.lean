-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.BallBasics
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth cutoff pairs on parabolic balls

The cutoffs are smooth and compactly supported in a larger parabolic ball,
with the second cutoff equal to one near the support of the first.
-/

open Set Metric
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

private def parabolicHomeomorphL2Real : ParabolicPoint ≃ₜ L2Vec3 × ℝ :=
  parabolicHomeomorph.trans
    (Homeomorph.prodCongr vec3Homeomorph (Homeomorph.refl ℝ))

private theorem isCompact_parabolicClosedBall {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) : IsCompact (Metric.closedBall z r) := by
  let R : ℝ := max r (r ^ 2) + r
  have hmax : max r (r ^ 2) ≤ R := by
    dsimp [R]
    exact le_add_of_nonneg_right hr.le
  have hprod : IsCompact (Metric.closedBall (parabolicHomeomorphL2Real z) R) :=
    isCompact_closedBall _ _
  have hsub : parabolicHomeomorphL2Real '' Metric.closedBall z r ⊆
      Metric.closedBall (parabolicHomeomorphL2Real z) R := by
    rintro q ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, Prod.dist_eq]
    rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp
    rcases max_le_iff.mp hp with ⟨hspace, htime⟩
    have hsq : |p.2 - z.2| ≤ r ^ 2 := (Real.sqrt_le_iff.mp htime).2
    apply max_le
    · change dist (WithLp.toLp 2 p.1) (WithLp.toLp 2 z.1) ≤ R
      rw [dist_eq_norm]
      have hspace' : ‖WithLp.toLp 2 (p.1 - z.1)‖ ≤ r := by
        simpa only [vec3EuclideanNorm_eq_l2] using hspace
      simpa only [WithLp.toLp_sub] using
        hspace'.trans ((le_max_left r (r ^ 2)).trans hmax)
    · change |p.2 - z.2| ≤ R
      exact hsq.trans ((le_max_right r (r ^ 2)).trans hmax)
  have himage : IsCompact (parabolicHomeomorphL2Real '' Metric.closedBall z r) := by
    apply hprod.of_isClosed_subset
    · exact parabolicHomeomorphL2Real.isClosed_image.mpr isClosed_closedBall
    · exact hsub
  exact (parabolicHomeomorphL2Real.isCompact_image).mp (by simpa using himage)

private theorem exists_smooth_cutoff_with_open_plateau
    {K U : Set (Vec3 × ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ (χ : Vec3 × ℝ → ℝ) (V : Set (Vec3 × ℝ)),
      IsOpen V ∧ K ⊆ V ∧ ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ ∀ x ∈ V, χ x = 1 := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hW, hVW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hVc hU hVU
  obtain ⟨χ, hχsmooth, -, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW
      (isClosed_closure (s := V)) hVW
  have hts : tsupport χ = closure W := by
    rw [tsupport, hχsupport]
  refine ⟨χ, V, hV, hKV, hχsmooth, ?_, ?_, ?_⟩
  · rw [HasCompactSupport, hts]
    exact hWc
  · rw [hts]
    exact hWU
  · intro x hx
    exact (hχone x).mp (subset_closure hx)

/-- Smooth compactly supported cutoffs adapted to two nested parabolic balls. -/
theorem exists_phi_zeta_of_parabolic_balls
    {z₀ : ParabolicPoint} {r₂ r₃ : ℝ} (hr₃ : 0 < r₃) (hr : r₃ < r₂ / 4) :
    ∃ φ ζ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      (∀ w ∈ Metric.ball z₀ r₃, φ w = 1) ∧
      tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (r₂ / 4) ∧
      (∃ V : Set ParabolicPoint, IsOpen V ∧ tsupport φ ⊆ V ∧
        ∀ w ∈ V, ζ w = 1) ∧
      tsupport ζ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (r₂ / 4) := by
  let U : Set (Vec3 × ℝ) := parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (r₂ / 4)
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph '' Metric.closedBall z₀ r₃
  have hU : IsOpen U := by
    exact Metric.isOpen_ball.preimage parabolicHomeomorph.symm.continuous
  have hK : IsCompact K := by
    exact parabolicHomeomorph.isCompact_image.mpr (isCompact_parabolicClosedBall hr₃)
  have hKU : K ⊆ U := by
    rintro w ⟨p, hp, rfl⟩
    change parabolicHomeomorph.symm (parabolicHomeomorph p) ∈ Metric.ball z₀ (r₂ / 4)
    exact Metric.closedBall_subset_ball hr hp
  obtain ⟨φ, Vφ, hVφ, hKφ, hφsmooth, hφcompact, hφsupport, hφone⟩ :=
    exists_smooth_cutoff_with_open_plateau hK hU hKU
  have hφone_ball : ∀ w ∈ Metric.ball z₀ r₃, φ w = 1 := by
    intro w hw
    have hwK : w ∈ K := by
      refine ⟨parabolicHomeomorph.symm w, Metric.ball_subset_closedBall hw, ?_⟩
      exact parabolicHomeomorph.apply_symm_apply w
    exact hφone w (hKφ hwK)
  have hφcompactSet : IsCompact (tsupport φ) := hφcompact
  obtain ⟨ζ, Vζ, hVζ, hKζ, hζsmooth, hζcompact, hζsupport, hζone⟩ :=
    exists_smooth_cutoff_with_open_plateau hφcompactSet hU hφsupport
  refine ⟨φ, ζ, hφsmooth, hφcompact, hζsmooth, hζcompact,
    hφone_ball, hφsupport, ?_, hζsupport⟩
  let V : Set ParabolicPoint := parabolicHomeomorph.symm '' Vζ
  refine ⟨V, parabolicHomeomorph.symm.isOpenMap Vζ hVζ, ?_, ?_⟩
  · intro x hx
    exact ⟨parabolicHomeomorph x, hKζ hx,
      parabolicHomeomorph.apply_symm_apply x⟩
  · intro w hw
    rcases hw with ⟨y, hy, hyw⟩
    rw [← hyw]
    exact hζone y hy

end CKN.Foundation.Parabolic
