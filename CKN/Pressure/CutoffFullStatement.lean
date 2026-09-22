-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Cutoff

/-! # A single cutoff with all annulus properties

The uniform derivative bounds and annular vanishing belong to the same
smooth compactly supported cutoff. Continuity of each derivative extends
its vanishing from the inner open ball to the closed inner ball.
-/

open Set Filter
open scoped Topology
open CKN.Foundation.Parabolic

namespace CKN

/-- A smooth spatial cutoff with uniform all-order bounds, vanishing derivatives
outside the closed-inner annulus, and the annulus separation estimate. -/
theorem exists_cutoff_with_annulus :
    ∃ C₁₀ : ℕ → ℝ, ∀ (x₀ : Vec3) (ρ : ℝ), 0 < ρ →
      ∃ η : Vec3 → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
        (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
        (∀ x ∈ vec3Ball x₀ (13 * ρ / 20), η x = 1) ∧
        tsupport η ⊆ vec3Ball x₀ (3 * ρ / 4) ∧
        (∀ k x, ‖iteratedFDeriv ℝ k η x‖ ≤ C₁₀ k * ρ ^ (-(k : ℝ))) ∧
        (∀ k : ℕ, 1 ≤ k → ∀ x,
          x ∉ vec3Ball x₀ (3 * ρ / 4) \
            euclideanClosedBall x₀ (13 * ρ / 20) →
          iteratedFDeriv ℝ k η x = 0) ∧
        (∀ r : ℝ, r ≤ ρ / 2 → ∀ x ∈ vec3Ball x₀ r,
          ∀ y ∈ vec3Ball x₀ (3 * ρ / 4) \
            euclideanClosedBall x₀ (13 * ρ / 20),
          3 * ρ / 20 ≤ vec3EuclideanNorm (x - y)) := by
  obtain ⟨C₁₀, hC⟩ := exists_cutoff
  refine ⟨C₁₀, ?_⟩
  intro x₀ ρ hρ
  obtain ⟨η, hsmooth, hcompact, hrange, hone, hsupp, hbound⟩ := hC x₀ ρ hρ
  refine ⟨η, hsmooth, hcompact, hrange, hone, hsupp, hbound, ?_, ?_⟩
  · intro k hk x hx
    by_cases hi : x ∈ euclideanClosedBall x₀ (13 * ρ / 20)
    · have hz : vec3Ball x₀ (13 * ρ / 20) ⊆
          {y | iteratedFDeriv ℝ k η y = 0} := by
        intro y hy
        have heq : η =ᶠ[𝓝 y] (fun _ : Vec3 => (1 : ℝ)) := by
          filter_upwards [(isOpen_vec3Ball x₀ (13 * ρ / 20)).mem_nhds hy] with w hw
          exact hone w hw
        calc
          iteratedFDeriv ℝ k η y = iteratedFDeriv ℝ k (fun _ : Vec3 => (1 : ℝ)) y :=
            (Filter.EventuallyEq.iteratedFDeriv ℝ heq k).eq_of_nhds
          _ = 0 := congrFun (iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk) (1 : ℝ)) y
      have hclosed : IsClosed {y | iteratedFDeriv ℝ k η y = 0} :=
        isClosed_eq (hsmooth.continuous_iteratedFDeriv (by simp)) continuous_const
      apply closure_minimal hz hclosed
      rw [closure_vec3Ball (by positivity)]
      have hn := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).mp hi
      simpa only [mem_ofPred_eq, vec3EuclideanNorm, vecEuclideanNorm, vecNormSq,
        vecDot, pow_two] using hn
    · have ho : x ∉ vec3Ball x₀ (3 * ρ / 4) := fun ho => hx ⟨ho, hi⟩
      by_contra hne
      exact ho (hsupp ((support_iteratedFDeriv_subset (𝕜 := ℝ) k) hne))
  · intro r hhalf x hx y hy
    have hr : 0 < r := (vec3EuclideanNorm_nonneg (x - x₀)).trans_lt (mem_vec3Ball.mp hx)
    apply cutoff_annulus_separation hρ hr hhalf hx
    refine ⟨hy.1, ?_⟩
    intro hi
    apply hy.2
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).mpr
    have hn := (mem_vec3Ball.mp hi).le
    simpa only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hn

end CKN
