-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelBounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# High-frequency symbol estimates
-/

open scoped BigOperators
open Set MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat

private def unitFrequencyCutoff : ContDiffBump (0 : Vec3) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The symbol with its singularity at the origin removed by a smooth cutoff. -/
def highFrequencySymbol (σ : Vec3 → ℂ) (ξ : Vec3) : ℂ :=
  (1 - (unitFrequencyCutoff ξ : ℂ)) * σ ξ

private theorem unitFrequencyCutoff_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (unitFrequencyCutoff : Vec3 → ℝ) :=
  unitFrequencyCutoff.contDiff

private theorem unitFrequencyCutoff_one {ξ : Vec3}
    (hξ : ξ ∈ Metric.closedBall 0 (1 / 2)) : unitFrequencyCutoff ξ = 1 :=
  unitFrequencyCutoff.one_of_mem_closedBall hξ

private theorem unitFrequencyCutoff_zero {ξ : Vec3}
    (hξ : 1 ≤ dist ξ 0) : unitFrequencyCutoff ξ = 0 :=
  unitFrequencyCutoff.zero_of_le_dist hξ

/-- Removing the smooth cutoff changes a symbol by no more than its own size. -/
theorem norm_sub_highFrequencySymbol_le (σ : Vec3 → ℂ) (ξ : Vec3) :
    ‖σ ξ - highFrequencySymbol σ ξ‖ ≤ ‖σ ξ‖ := by
  have hdecomp : σ ξ - highFrequencySymbol σ ξ =
      (unitFrequencyCutoff ξ : ℂ) * σ ξ := by
    simp only [highFrequencySymbol]
    ring
  rw [hdecomp, norm_mul, Complex.norm_of_nonneg (unitFrequencyCutoff.nonneg)]
  exact mul_le_of_le_one_left (norm_nonneg _) unitFrequencyCutoff.le_one

/-- The cutoff high-frequency symbol has no larger size than the original symbol. -/
theorem norm_highFrequencySymbol_le (σ : Vec3 → ℂ) (ξ : Vec3) :
    ‖highFrequencySymbol σ ξ‖ ≤ ‖σ ξ‖ := by
  have hcoef : ‖1 - (unitFrequencyCutoff ξ : ℂ)‖ = 1 - unitFrequencyCutoff ξ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg]
    exact sub_nonneg.mpr unitFrequencyCutoff.le_one
  rw [highFrequencySymbol, norm_mul, hcoef]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (sub_le_self _ unitFrequencyCutoff.nonneg)

/-- The part removed by the cutoff vanishes outside its unit support. -/
theorem sub_highFrequencySymbol_eq_zero_of_one_le_dist
    (σ : Vec3 → ℂ) (ξ : Vec3) (hξ : 1 ≤ dist ξ 0) :
    σ ξ - highFrequencySymbol σ ξ = 0 := by
  simp [highFrequencySymbol, unitFrequencyCutoff_zero hξ]

/-- The cutoff high-frequency part is globally smooth. -/
theorem highFrequencySymbol_contDiff
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3)) :
    ContDiff ℝ (⊤ : ℕ∞) (highFrequencySymbol σ) := by
  have hbump : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec3 => (unitFrequencyCutoff ξ : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp unitFrequencyCutoff_contDiff
  have hpunct : ContDiffOn ℝ (⊤ : ℕ∞) (highFrequencySymbol σ) ({0}ᶜ : Set Vec3) := by
    exact (contDiffOn_const.sub hbump.contDiffOn).mul hσ
  have hball : ContDiffOn ℝ (⊤ : ℕ∞) (highFrequencySymbol σ) (Metric.ball 0 (1 / 2)) := by
    have hz : EqOn (highFrequencySymbol σ) (fun _ : Vec3 => (0 : ℂ))
        (Metric.ball 0 (1 / 2)) := by
      intro ξ hξ
      have hdist : dist ξ 0 < 1 / 2 := by
        simpa [Metric.mem_ball, dist_comm] using hξ
      have hclosed : ξ ∈ Metric.closedBall (0 : Vec3) (1 / 2) := by
        exact Metric.mem_closedBall.mpr hdist.le
      simp [highFrequencySymbol, unitFrequencyCutoff_one hclosed]
    exact contDiffOn_const.congr hz
  have hopen₁ : IsOpen (Metric.ball (0 : Vec3) (1 / 2)) := Metric.isOpen_ball
  have hopen₂ : IsOpen ({0}ᶜ : Set Vec3) := isOpen_compl_singleton
  have hunion : Metric.ball (0 : Vec3) (1 / 2) ∪ ({0}ᶜ : Set Vec3) = Set.univ := by
    ext ξ
    by_cases hξ : ξ = 0
    · subst ξ
      simp [Metric.mem_ball]
    · simp [hξ]
  exact contDiff_of_contDiffOn_union_of_isOpen hball hpunct hunion hopen₁ hopen₂

private theorem highFrequencySymbol_zero_near_origin
    (σ : Vec3 → ℂ) {ξ : Vec3} (hξ : dist ξ 0 ≤ 1 / 2) :
    highFrequencySymbol σ ξ = 0 := by
  have hclosed : ξ ∈ Metric.closedBall (0 : Vec3) (1 / 2) :=
    Metric.mem_closedBall.mpr hξ
  simp [highFrequencySymbol, unitFrequencyCutoff_one hclosed]

private theorem highFrequencySymbol_eq_symbol_outside
    (σ : Vec3 → ℂ) {ξ : Vec3} (hξ : 1 ≤ dist ξ 0) :
    highFrequencySymbol σ ξ = σ ξ := by
  simp [highFrequencySymbol, unitFrequencyCutoff_zero hξ]

private theorem iteratedFDeriv_high_eq_symbol
    {σ : Vec3 → ℂ}
    {ξ : Vec3} (hξ : 1 < dist ξ 0) (k : ℕ) :
    iteratedFDeriv ℝ k (highFrequencySymbol σ) ξ = iteratedFDeriv ℝ k σ ξ := by
  let S : Set Vec3 := {y | 1 < dist y 0}
  have hopen : IsOpen S := isOpen_Ioi.preimage (continuous_id.dist continuous_const)
  have hxS : ξ ∈ S := hξ
  have hfun : EqOn (highFrequencySymbol σ) σ S := by
    intro y hy
    exact highFrequencySymbol_eq_symbol_outside σ (by dsimp [S] at hy; exact le_of_lt hy)
  have hwithin := iteratedFDerivWithin_congr (𝕜 := ℝ) hfun hxS k
  have hhigh : iteratedFDerivWithin ℝ k (highFrequencySymbol σ) S ξ =
      iteratedFDeriv ℝ k (highFrequencySymbol σ) ξ :=
    iteratedFDerivWithin_of_isOpen k hopen hxS
  have hsymbol : iteratedFDerivWithin ℝ k σ S ξ = iteratedFDeriv ℝ k σ ξ := by
    exact iteratedFDerivWithin_of_isOpen k hopen hxS
  rw [hhigh, hsymbol] at hwithin
  exact hwithin

private theorem iteratedFDeriv_scale_on_punctured
    {σ : Vec3 → ℂ} (d : ℕ) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ) {a : ℝ} (ha : 0 < a)
    (x : Vec3) (hx : x ≠ 0) (k : ℕ) :
    (iteratedFDerivWithin ℝ k σ ({0}ᶜ : Set Vec3) (a • x)).compContinuousLinearMap
        (fun _ : Fin k => a • (ContinuousLinearMap.id ℝ Vec3)) =
      (a ^ d : ℝ) • iteratedFDerivWithin ℝ k σ ({0}ᶜ : Set Vec3) x := by
  let S : Set Vec3 := ({0}ᶜ : Set Vec3)
  let A : Vec3 →L[ℝ] Vec3 := a • ContinuousLinearMap.id ℝ Vec3
  have hA : ∀ y, A y = a • y := by intro y; simp [A]
  have hpre : A ⁻¹' S = S := by
    ext y
    simp [S, hA, ha.ne']
  have hS : IsOpen S := isOpen_compl_singleton
  have huS : UniqueDiffOn ℝ S := hS.uniqueDiffOn
  have huPre : UniqueDiffOn ℝ (A ⁻¹' S) := by rw [hpre]; exact huS
  have hxS : x ∈ S := by simpa [S] using hx
  have hAxS : A x ∈ S := by
    rw [hA]
    simp only [S, mem_compl_iff, mem_singleton_iff]
    intro hzero
    exact hx ((smul_eq_zero.mp hzero).resolve_left ha.ne')
  have hfun : EqOn (fun y : Vec3 => σ (A y)) (fun y => (a ^ d : ℝ) • σ y) S := by
    intro y hy
    change σ (A y) = (a ^ d : ℝ) • σ y
    rw [hA y]
    exact hhom a ha y
  have hcongr := iteratedFDerivWithin_congr (𝕜 := ℝ) hfun hxS k
  have hcomp := A.iteratedFDerivWithin_comp_right (s := S) (i := k)
    hσ huS huPre hAxS (by simp)
  have hcomp' : iteratedFDerivWithin ℝ k (fun y : Vec3 => σ (A y)) S x =
      (iteratedFDerivWithin ℝ k σ S (a • x)).compContinuousLinearMap
        (fun _ : Fin k => A) := by
    simpa only [Function.comp_def, hpre, hA] using hcomp
  rw [hcomp'] at hcongr
  change (iteratedFDerivWithin ℝ k σ S (a • x)).compContinuousLinearMap
      (fun _ : Fin k => A) = _
  rw [hcongr]
  exact iteratedFDerivWithin_const_smul_apply (a := (a ^ d : ℝ))
    ((hσ x hxS).of_le (by simp)) huS hxS

private theorem isCompact_euclideanUnitSphere :
    IsCompact {ξ : Vec3 | vec3EuclideanNorm ξ = 1} := by
  let S : Set Vec3 := {ξ | vec3EuclideanNorm ξ = 1}
  have hclosed : IsClosed S := by
    exact isClosed_eq continuous_vec3EuclideanNorm continuous_const
  have hbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : Vec3)).2 ⟨1, ?_⟩
    intro ξ hξ
    have hle : ‖ξ‖ ≤ 1 := by
      calc
        ‖ξ‖ ≤ vec3EuclideanNorm ξ := norm_le_vec3EuclideanNorm ξ
        _ = 1 := hξ
    simpa [Metric.mem_closedBall, dist_eq_norm] using hle
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

/-- Homogeneous smooth functions have the expected derivative growth away from the origin. -/
theorem exists_norm_iteratedFDeriv_growth
    {σ : Vec3 → ℂ} (d : ℕ) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ k σ ξ‖ ≤
        C * (vec3EuclideanNorm ξ) ^ d / (vec3EuclideanNorm ξ) ^ k := by
  let S : Set Vec3 := ({0}ᶜ : Set Vec3)
  let sphere : Set Vec3 := {ξ | vec3EuclideanNorm ξ = 1}
  have hS : IsOpen S := isOpen_compl_singleton
  have huS : UniqueDiffOn ℝ S := hS.uniqueDiffOn
  have hunit : sphere ⊆ S := by
    intro ξ hξ hz
    rcases mem_singleton_iff.mp hz with rfl
    change vec3EuclideanNorm (0 : Vec3) = 1 at hξ
    rw [vec3EuclideanNorm_zero] at hξ
    norm_num at hξ
  have hderCont : ContinuousOn (iteratedFDerivWithin ℝ k σ S) S :=
    hσ.continuousOn_iteratedFDerivWithin (by simp) huS
  obtain ⟨C, hC⟩ := isCompact_euclideanUnitSphere.exists_bound_of_continuousOn
    (hderCont.mono hunit)
  have hCnonneg : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0, hCnonneg, ?_⟩
  intro ξ hξ
  have hrpos : 0 < vec3EuclideanNorm ξ := by
    rcases lt_or_eq_of_le (vec3EuclideanNorm_nonneg ξ) with h | h
    · exact h
    · exfalso
      apply hξ
      have hz : vec3EuclideanNorm ξ = 0 := h.symm
      have hsum : ∑ i : Fin 3, ξ i ^ 2 = 0 := by
        have hnonneg : 0 ≤ ∑ i : Fin 3, ξ i ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg _
        unfold vec3EuclideanNorm at hz
        exact (Real.sqrt_eq_zero hnonneg).1 hz
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => sq_nonneg (ξ j))).1 hsum i (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hi
  let a : ℝ := vec3EuclideanNorm ξ
  let η : Vec3 := a⁻¹ • ξ
  have ha : 0 < a := hrpos
  have hηunit : vec3EuclideanNorm η = 1 := by
    dsimp [η]
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.2 ha)]
    dsimp [a]
    field_simp
  have hηne : η ≠ 0 := by
    intro hz
    rw [hz, vec3EuclideanNorm_zero] at hηunit
    norm_num at hηunit
  have hscaled := iteratedFDeriv_scale_on_punctured d hσ hhom ha η hηne k
  have hglobalξ : iteratedFDerivWithin ℝ k σ S ξ = iteratedFDeriv ℝ k σ ξ :=
    iteratedFDerivWithin_of_isOpen k hS (by simpa [S] using hξ)
  have hglobalη : iteratedFDerivWithin ℝ k σ S η = iteratedFDeriv ℝ k σ η :=
    iteratedFDerivWithin_of_isOpen k hS (by simpa [S] using hηne)
  have hAη : a • η = ξ := by
    dsimp [η]
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  rw [hAη, hglobalξ, hglobalη] at hscaled
  have hmap :
      (iteratedFDeriv ℝ k σ ξ).compContinuousLinearMap
          (fun _ : Fin k => a • (ContinuousLinearMap.id ℝ Vec3)) =
    a ^ k • iteratedFDeriv ℝ k σ ξ := by
    ext v
    change (iteratedFDeriv ℝ k σ ξ) (fun i => a • v i) =
      a ^ k • (iteratedFDeriv ℝ k σ ξ) v
    simpa using (iteratedFDeriv ℝ k σ ξ).map_smul_univ
      (fun _ : Fin k => a) v
  rw [hmap] at hscaled
  have hn := congrArg norm hscaled
  simp [norm_smul, Real.norm_of_nonneg (pow_nonneg ha.le _)] at hn
  have hunitBound : ‖iteratedFDeriv ℝ k σ η‖ ≤ max C 0 := by
    have hbound := hC η hηunit
    have hwithin : iteratedFDerivWithin ℝ k σ S η = iteratedFDeriv ℝ k σ η :=
      iteratedFDerivWithin_of_isOpen k hS (by simpa [S] using hηne)
    calc
      ‖iteratedFDeriv ℝ k σ η‖ =
          ‖iteratedFDerivWithin ℝ k σ S η‖ := by rw [hwithin]
      _ ≤ C := hbound
      _ ≤ max C 0 := le_max_left _ _
  have hdenpos : 0 < a ^ k := pow_pos ha _
  have hnorm : ‖iteratedFDeriv ℝ k σ ξ‖ ≤
      max C 0 * a ^ d / a ^ k := by
    have hn' : a ^ k * ‖iteratedFDeriv ℝ k σ ξ‖ =
        a ^ d * ‖iteratedFDeriv ℝ k σ η‖ := by exact hn
    rw [le_div_iff₀ hdenpos]
    calc
      ‖iteratedFDeriv ℝ k σ ξ‖ * a ^ k = a ^ k *
          ‖iteratedFDeriv ℝ k σ ξ‖ := by ring
      _ = a ^ d * ‖iteratedFDeriv ℝ k σ η‖ := hn'
      _ ≤ a ^ d * max C 0 := by gcongr
      _ = max C 0 * a ^ d := by ring
  simpa [a] using hnorm

private theorem exists_norm_iteratedFDeriv_growth_degreeOne
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ k σ ξ‖ ≤
        C * (vec3EuclideanNorm ξ) / (vec3EuclideanNorm ξ) ^ k := by
  have hhom' : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ 1 : ℝ) • σ ξ := by
    intro a ha ξ
    rw [pow_one, RCLike.real_smul_eq_coe_mul]
    exact hhom a ha ξ
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_growth 1 hσ hhom' k
  refine ⟨C, hC, ?_⟩
  intro ξ hξ
  simpa only [pow_one] using hbound ξ hξ

private theorem exists_norm_iteratedFDeriv_high_growth_outside
    {σ : Vec3 → ℂ} (d k : ℕ)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3, 1 < dist ξ 0 →
      ‖iteratedFDeriv ℝ k (highFrequencySymbol σ) ξ‖ ≤
        C * (vec3EuclideanNorm ξ) ^ d / (vec3EuclideanNorm ξ) ^ k := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_growth d hσ hhom k
  refine ⟨C, hC, ?_⟩
  intro ξ hξ
  rw [iteratedFDeriv_high_eq_symbol (σ := σ) hξ k]
  exact hbound ξ (by
    intro hzero
    subst ξ
    have hfalse : ¬ 1 < (0 : ℝ) := by norm_num
    have hcontr : 1 < (0 : ℝ) := by simpa using hξ
    exact hfalse hcontr)

/-- Derivatives of the cutoff symbol are bounded on a fixed compact frequency ball. -/
theorem exists_norm_iteratedFDeriv_high_bound_on_twoBall
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3, vec3EuclideanNorm ξ ≤ 2 →
      ‖iteratedFDeriv ℝ k (highFrequencySymbol σ) ξ‖ ≤ C := by
  have hhigh := highFrequencySymbol_contDiff hσ
  have hder : Continuous (fun ξ : Vec3 => iteratedFDeriv ℝ k (highFrequencySymbol σ) ξ) :=
    hhigh.continuous_iteratedFDeriv (by simp)
  have hcompact : IsCompact (Metric.closedBall (0 : Vec3) 2) :=
    isCompact_closedBall (0 : Vec3) 2
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (hder.continuousOn.mono (Set.subset_univ _))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ξ hξ
  have hnorm : ‖ξ‖ ≤ 2 := (norm_le_vec3EuclideanNorm ξ).trans hξ
  have hball : ξ ∈ Metric.closedBall (0 : Vec3) 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
  exact (hC ξ hball).trans (le_max_left _ _)

/-- Derivatives of a cutoff homogeneous symbol have their homogeneous bounds outside a ball. -/
theorem exists_norm_iteratedFDeriv_high_bound_on_annulus
    {σ : Vec3 → ℂ} (d k : ℕ)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3, 1 / 2 ≤ vec3EuclideanNorm ξ →
      ‖iteratedFDeriv ℝ k (highFrequencySymbol σ) ξ‖ ≤
        C * (vec3EuclideanNorm ξ) ^ d / (vec3EuclideanNorm ξ) ^ k := by
  obtain ⟨Cg, hCg, hg⟩ :=
    exists_norm_iteratedFDeriv_high_growth_outside d k hσ hhom
  obtain ⟨Cc, hCc, hc⟩ := exists_norm_iteratedFDeriv_high_bound_on_twoBall hσ k
  let P : ℝ := 2 ^ d * 2 ^ k
  let C : ℝ := max Cg (Cc * P)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ξ hξ
  have hr : 0 < vec3EuclideanNorm ξ := by linarith only [hξ]
  by_cases hlarge : 2 < vec3EuclideanNorm ξ
  · have hout : 1 < dist ξ 0 := by
      have heuc := vec3EuclideanNorm_le_sqrt_three_mul_norm ξ
      have hsqrt : Real.sqrt 3 ≤ 2 := by
        rw [Real.sqrt_le_iff]
        norm_num
      have hnorm : 1 < ‖ξ‖ := by
        have hmul := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg ξ)
        linarith only [hlarge, heuc, hmul]
      simpa [dist_eq_norm] using hnorm
    have h := hg ξ hout
    calc
      ‖iteratedFDeriv ℝ k (highFrequencySymbol σ) ξ‖ ≤
          Cg * (vec3EuclideanNorm ξ) ^ d / (vec3EuclideanNorm ξ) ^ k := h
      _ ≤ C * (vec3EuclideanNorm ξ) ^ d / (vec3EuclideanNorm ξ) ^ k := by
        rw [div_eq_mul_inv]
        have hcoeff : Cg * (vec3EuclideanNorm ξ) ^ d ≤
            C * (vec3EuclideanNorm ξ) ^ d :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr.le _)
        exact mul_le_mul_of_nonneg_right hcoeff
          (inv_nonneg.mpr (pow_nonneg hr.le _))
  · have hsmall : vec3EuclideanNorm ξ ≤ 2 := le_of_not_gt hlarge
    have h := hc ξ hsmall
    have hratio : (1 / 2 : ℝ) ^ d / (2 : ℝ) ^ k ≤
        (vec3EuclideanNorm ξ) ^ d / (vec3EuclideanNorm ξ) ^ k := by
      exact div_le_div₀ (pow_nonneg (vec3EuclideanNorm_nonneg ξ) d)
        (pow_le_pow_left₀ (by norm_num) hξ d) (pow_pos hr k)
        (pow_le_pow_left₀ (vec3EuclideanNorm_nonneg ξ) hsmall k)
    have hPpos : 0 < P := by dsimp [P]; positivity
    have hfloor : (1 / 2 : ℝ) ^ d / (2 : ℝ) ^ k = P⁻¹ := by
      have hInv : (1 / 2 : ℝ) ^ d = ((2 : ℝ) ^ d)⁻¹ := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, ← inv_pow]
      rw [hInv, div_eq_mul_inv]
      dsimp [P]
      field_simp
    have hCcC : Cc * P ≤ C := le_max_right _ _
    have hfactor : Cc ≤ C * ((1 / 2 : ℝ) ^ d / (2 : ℝ) ^ k) := by
      calc
        Cc = (Cc * P) * P⁻¹ := by field_simp
        _ ≤ C * P⁻¹ := mul_le_mul_of_nonneg_right hCcC (inv_nonneg.mpr hPpos.le)
        _ = C * ((1 / 2 : ℝ) ^ d / (2 : ℝ) ^ k) := by rw [hfloor]
    calc
      ‖iteratedFDeriv ℝ k (highFrequencySymbol σ) ξ‖ ≤ Cc := h
      _ ≤ C * ((1 / 2 : ℝ) ^ d / (2 : ℝ) ^ k) := hfactor
      _ ≤ C * ((vec3EuclideanNorm ξ) ^ d / (vec3EuclideanNorm ξ) ^ k) :=
        mul_le_mul_of_nonneg_left hratio hC
      _ = C * (vec3EuclideanNorm ξ) ^ d / (vec3EuclideanNorm ξ) ^ k := by
        rw [mul_div_assoc]


end CKN.Foundation.Euclidean
