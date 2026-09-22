-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Vec3Norm

/-!
# Symbols homogeneous of degree one

External Input `ext:heat-kernel` of `paper/ckn.tex` quantifies over every Fourier
multiplier `ς(D)` whose symbol `ς` is smooth on `ℝ³ ∖ {0}` and homogeneous of
degree one, and the manuscript's pressure-multiplier discussion uses the concrete symbols
`ς_{jl}(ξ) = i ξ ξ_j ξ_l / |ξ|²` of that class.  This file records the
homogeneity predicate for such a symbol and proves the linear growth bound
`‖ς ξ‖ ≤ C |ξ|` that makes the associated Fourier integrals absolutely
convergent.  Symbols are complex valued, as `ς_{jl}` is.
-/

open scoped BigOperators
open Set

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- A complex symbol on `Vec3` is homogeneous of degree one when
`ς (a • ξ) = a • ς ξ` for every positive real dilation `a`.  This is the
homogeneity hypothesis of External Input `ext:heat-kernel`. -/
def IsDegreeOneHomogeneous (σ : Vec3 → ℂ) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ ξ : Vec3, σ (a • ξ) = (a : ℂ) * σ ξ

private theorem norm_le_euclidean (v : Vec3) : ‖v‖ ≤ vec3EuclideanNorm v := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg v)]
  intro i
  change |v i| ≤ vec3EuclideanNorm v
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _hj => sq_nonneg (v j))
    (Finset.mem_univ i)

private theorem isCompact_euclideanSphere :
    IsCompact {ξ : Vec3 | vec3EuclideanNorm ξ = 1} := by
  have hclosed : IsClosed {ξ : Vec3 | vec3EuclideanNorm ξ = 1} :=
    isClosed_eq continuous_vec3EuclideanNorm continuous_const
  have hbdd : Bornology.IsBounded {ξ : Vec3 | vec3EuclideanNorm ξ = 1} := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : Vec3)).2 ⟨1, ?_⟩
    intro ξ hξ
    have hle : ‖ξ‖ ≤ 1 := by
      have h := norm_le_euclidean ξ
      rw [hξ] at h
      exact h
    simpa [Metric.mem_closedBall, dist_eq_norm] using hle
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

/-- A symbol that is continuous away from the origin and homogeneous of degree
one grows at most linearly:  there is one nonnegative constant `C`, fixed before
the frequency, with `‖ς ξ‖ ≤ C |ξ|` for every `ξ`, including `ξ = 0`, where both
sides vanish.  This is the quantitative content of the symbol class of External
Input `ext:heat-kernel`; it makes the frequency integral defining `ς(D)W₊`
absolutely convergent against a Gaussian. -/
theorem norm_le_of_isDegreeOneHomogeneous {σ : Vec3 → ℂ}
    (hcont : ContinuousOn σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3, ‖σ ξ‖ ≤ C * vec3EuclideanNorm ξ := by
  have hsub : {ξ : Vec3 | vec3EuclideanNorm ξ = 1} ⊆ ({0}ᶜ : Set Vec3) := by
    intro ξ hξ
    simp only [mem_compl_iff, mem_singleton_iff]
    intro h
    rw [h] at hξ
    simp [vec3EuclideanNorm_zero] at hξ
  obtain ⟨C, hC⟩ := isCompact_euclideanSphere.exists_bound_of_continuousOn
    (hcont.mono hsub)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ξ
  by_cases hξ : ξ = 0
  · have hzero : σ 0 = 0 := by
      have h2 := hhom 2 (by norm_num) 0
      simp only [smul_zero] at h2
      push_cast at h2
      linear_combination -h2
    rw [hξ, hzero]
    simp [vec3EuclideanNorm_zero]
  · have hpos : 0 < vec3EuclideanNorm ξ := by
      rcases lt_or_eq_of_le (vec3EuclideanNorm_nonneg ξ) with h | h
      · exact h
      · exfalso
        apply hξ
        have hz : vec3EuclideanNorm ξ = 0 := h.symm
        unfold vec3EuclideanNorm at hz
        have hsum : ∑ i, ξ i ^ 2 = 0 := by
          have hnn : (0 : ℝ) ≤ ∑ i, ξ i ^ 2 :=
            Finset.sum_nonneg fun i _ => sq_nonneg _
          exact (Real.sqrt_eq_zero hnn).1 hz
        funext i
        have hi := Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_ : j ∈ Finset.univ) => sq_nonneg (ξ j)) |>.1 hsum i
          (Finset.mem_univ i)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hi
    set a := vec3EuclideanNorm ξ with ha
    have hunit : vec3EuclideanNorm (a⁻¹ • ξ) = 1 := by
      rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.2 hpos), ← ha]
      field_simp
    have heq : ξ = a • (a⁻¹ • ξ) := by
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    have hval : σ ξ = (a : ℂ) * σ (a⁻¹ • ξ) := by
      conv_lhs => rw [heq]
      exact hhom a hpos _
    rw [hval, norm_mul]
    have hb := hC _ hunit
    calc ‖(a : ℂ)‖ * ‖σ (a⁻¹ • ξ)‖ ≤ ‖(a : ℂ)‖ * C := by
          gcongr
      _ ≤ a * max C 0 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
          gcongr
          exact le_max_left _ _
      _ = max C 0 * vec3EuclideanNorm ξ := by rw [← ha]; ring

end CKN.Foundation.Euclidean
