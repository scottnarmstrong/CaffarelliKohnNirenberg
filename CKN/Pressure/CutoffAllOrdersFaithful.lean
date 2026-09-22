-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.Cutoff
import CKN.Foundation.Parabolic.Basic
import CKN.Foundation.Sobolev.Cutoff.BallTopology

/-!
# All-order derivative bounds for the mollified ball cut-off

`CKN/Pressure/Cutoff.lean` builds the smooth radial cut-off `mollifiedBallCutoff x₀ hρ`,
which is identically `1` on the inner ball, vanishes outside the outer ball, and has
quantitative bounds for its first and second derivatives.  The cut-off is by construction one
fixed profile composed with `x ↦ ρ⁻¹ • (x - x₀)`, so every order obeys the same scaling: the
`k`-th derivative is bounded by a `k`-only constant times `ρ ^ (-k)`, and vanishes off the
annulus where the profile is not locally constant.  This file records those two all-order
statements together with the three value clauses, in the single display used by the pressure
decomposition.
-/

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology

open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The two Euclidean norms of the repository agree on `Fin 3 → ℝ`. -/
private lemma vecEuclideanNorm_eq_vec3EuclideanNorm (x : Vec 3) :
    vecEuclideanNorm x = vec3EuclideanNorm x := by
  simp [vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot, pow_two]

/-- The fixed unit profile: the cut-off at the origin and at radius one. -/
private def unitProfile : Vec 3 → ℝ := mollifiedBallCutoff (0 : Vec 3) one_pos

private lemma unitProfile_smooth : ContDiff ℝ (⊤ : ℕ∞) unitProfile :=
  mollifiedBallCutoff_smooth (0 : Vec 3) one_pos

private lemma unitProfile_hasCompactSupport : HasCompactSupport unitProfile :=
  mollifiedBallCutoff_hasCompactSupport (0 : Vec 3) one_pos

/-- Every cut-off is the unit profile read at the rescaled, recentred point. -/
private lemma mollifiedBallCutoff_eq_unitProfile (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Vec 3) :
    mollifiedBallCutoff x₀ hρ x = unitProfile (ρ⁻¹ • (x - x₀)) := by
  simp [mollifiedBallCutoff, unitProfile]

/-- Each derivative order of the unit profile is bounded, being continuous with compact
support. -/
private lemma unitProfile_iteratedFDeriv_bounded (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ y : Vec 3, ‖iteratedFDeriv ℝ k unitProfile y‖ ≤ c := by
  have hcont : Continuous (iteratedFDeriv ℝ k unitProfile) :=
    unitProfile_smooth.continuous_iteratedFDeriv (mod_cast le_top)
  have hsupp : HasCompactSupport (iteratedFDeriv ℝ k unitProfile) :=
    unitProfile_hasCompactSupport.iteratedFDeriv k
  obtain ⟨c, hc⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨max c 0, le_max_right _ _, fun y => (hc y).trans (le_max_left _ _)⟩

/-- The `k`-th derivative of the cut-off is the `k`-th derivative of the unit profile,
rescaled by `ρ⁻¹ ^ k`. -/
private lemma iteratedFDeriv_mollifiedBallCutoff (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ)
    (k : ℕ) (x : Vec 3) :
    iteratedFDeriv ℝ k (mollifiedBallCutoff x₀ hρ) x =
      (ρ⁻¹) ^ k • iteratedFDeriv ℝ k unitProfile (ρ⁻¹ • (x - x₀)) := by
  have hfun : mollifiedBallCutoff x₀ hρ =
      fun y : Vec 3 => unitProfile (ρ⁻¹ • (y - x₀)) := by
    funext y
    exact mollifiedBallCutoff_eq_unitProfile x₀ hρ y
  have h1 : iteratedFDeriv ℝ k (fun y : Vec 3 => unitProfile (ρ⁻¹ • (y - x₀))) x =
      iteratedFDeriv ℝ k (fun z : Vec 3 => unitProfile (ρ⁻¹ • z)) (x - x₀) :=
    iteratedFDeriv_comp_sub (f := fun z : Vec 3 => unitProfile (ρ⁻¹ • z)) k x₀ x
  have h2 : iteratedFDeriv ℝ k (fun z : Vec 3 => unitProfile (ρ⁻¹ • z)) =
      fun y : Vec 3 => (ρ⁻¹) ^ k • iteratedFDeriv ℝ k unitProfile (ρ⁻¹ • y) :=
    iteratedFDeriv_comp_const_smul (ρ⁻¹) (unitProfile_smooth.of_le (mod_cast le_top))
  rw [hfun, h1, h2]

/-- The cut-off equals `1` on the *closed* inner ball; the established value clause covers the
open ball, and the boundary follows from continuity along the radial segment. -/
private lemma mollifiedBallCutoff_eq_one_on_closed_inner (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ)
    {x : Vec 3} (hx : vec3EuclideanNorm (x - x₀) ≤ 13 * ρ / 20) :
    mollifiedBallCutoff x₀ hρ x = 1 := by
  have hnorm : vecEuclideanNorm (x - x₀) ≤ 13 * ρ / 20 := by
    rw [vecEuclideanNorm_eq_vec3EuclideanNorm]; exact hx
  have hnn : 0 ≤ vecEuclideanNorm (x - x₀) := Real.sqrt_nonneg _
  set g : ℝ → Vec 3 := fun t => x₀ + t • (x - x₀) with hgdef
  have hgcont : Continuous g := by
    apply continuous_const.add
    exact (continuous_id.smul continuous_const)
  have hg1 : g 1 = x := by simp [hgdef]
  have hgt : ∀ t : ℝ, |t| < 1 → mollifiedBallCutoff x₀ hρ (g t) = 1 := by
    intro t ht
    apply mollifiedBallCutoff_eq_one_on_inner
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hsub : g t - x₀ = t • (x - x₀) := by simp [hgdef]
    rw [hsub, vecEuclideanNorm_smul]
    rcases eq_or_lt_of_le hnn with h0 | h0
    · rw [← h0]
      have : |t| * 0 = 0 := by ring
      rw [this]
      positivity
    · calc |t| * vecEuclideanNorm (x - x₀) < 1 * vecEuclideanNorm (x - x₀) := by
            exact mul_lt_mul_of_pos_right ht h0
        _ = vecEuclideanNorm (x - x₀) := one_mul _
        _ ≤ 13 * ρ / 20 := hnorm
  have hseq : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n + 1)) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using hc.sub h
  have hlim : Tendsto
      (fun n : ℕ => mollifiedBallCutoff x₀ hρ (g ((1 : ℝ) - 1 / (n + 1)))) atTop
      (𝓝 (mollifiedBallCutoff x₀ hρ x)) := by
    have hcomp : Continuous (fun t : ℝ => mollifiedBallCutoff x₀ hρ (g t)) :=
      ((mollifiedBallCutoff_smooth x₀ hρ).continuous).comp hgcont
    have := (hcomp.tendsto (1 : ℝ)).comp hseq
    rwa [hg1] at this
  have hconst : (fun n : ℕ => mollifiedBallCutoff x₀ hρ (g ((1 : ℝ) - 1 / (n + 1)))) =
      fun _ : ℕ => (1 : ℝ) := by
    funext n
    apply hgt
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      simp only [le_add_iff_nonneg_left]
      positivity
    rw [abs_of_nonneg (by linarith only [hpos, hle])]
    linarith only [hpos]
  rw [hconst] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- The cut-off vanishes outside the outer ball. -/
private lemma mollifiedBallCutoff_notMem_tsupport (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ)
    {x : Vec 3} (hx : 3 * ρ / 4 ≤ vec3EuclideanNorm (x - x₀)) :
    x ∉ tsupport (mollifiedBallCutoff x₀ hρ) := by
  intro hmem
  have hball := mollifiedBallCutoff_tsupport_subset_outer x₀ hρ hmem
  have hlt := (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (x₀ := x₀) (x := x) (by positivity)).mp hball
  rw [vecEuclideanNorm_eq_vec3EuclideanNorm] at hlt
  linarith only [hx, hlt]

/-- Higher derivatives of a function that is constant on an open set vanish there. -/
private lemma iteratedFDeriv_eq_zero_of_eqOn_const {U : Set (Vec 3)} (hU : IsOpen U)
    {f : Vec 3 → ℝ} {c : ℝ} (hf : EqOn f (fun _ => c) U) {k : ℕ} (hk : k ≠ 0)
    {x : Vec 3} (hx : x ∈ U) :
    iteratedFDeriv ℝ k f x = 0 := by
  have h₁ : iteratedFDerivWithin ℝ k f U x = iteratedFDeriv ℝ k f x :=
    iteratedFDerivWithin_of_isOpen k hU hx
  have h₂ : iteratedFDerivWithin ℝ k f U x =
      iteratedFDerivWithin ℝ k (fun _ : Vec 3 => c) U x :=
    iteratedFDerivWithin_congr hf hx k
  have h₃ : iteratedFDerivWithin ℝ k (fun _ : Vec 3 => c) U x =
      iteratedFDeriv ℝ k (fun _ : Vec 3 => c) x :=
    iteratedFDerivWithin_of_isOpen k hU hx
  have h₄ : iteratedFDeriv ℝ k (fun _ : Vec 3 => c) x = 0 := by
    rw [iteratedFDeriv_const_of_ne hk]
    rfl
  rw [← h₁, h₂, h₃, h₄]

/-- `step:cutoff-mollifier`: the mollified ball cut-off is smooth, takes values in `[0, 1]`,
equals `1` on the closed inner ball, vanishes on the outer region, obeys the `k`-only
derivative bound `C k * ρ ^ (-k)` at every order, and has all its positive-order derivatives
vanishing off the annulus. -/
theorem cutoff_all_orders_source :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ (x₀ : Vec3) (ρ : ℝ) (hρ : 0 < ρ),
        ContDiff ℝ (⊤ : ℕ∞) (mollifiedBallCutoff x₀ hρ) ∧
        (∀ x, 0 ≤ mollifiedBallCutoff x₀ hρ x ∧ mollifiedBallCutoff x₀ hρ x ≤ 1) ∧
        (∀ x, vec3EuclideanNorm (x - x₀) ≤ 13 * ρ / 20 →
          mollifiedBallCutoff x₀ hρ x = 1) ∧
        (∀ x, 3 * ρ / 4 ≤ vec3EuclideanNorm (x - x₀) →
          mollifiedBallCutoff x₀ hρ x = 0) ∧
        (∀ k x, ‖iteratedFDeriv ℝ k (mollifiedBallCutoff x₀ hρ) x‖ ≤
          C k * ρ ^ (-(k : ℝ))) ∧
        (∀ k, 0 < k → ∀ x, vec3EuclideanNorm (x - x₀) < 13 * ρ / 20 ∨
          3 * ρ / 4 < vec3EuclideanNorm (x - x₀) →
          iteratedFDeriv ℝ k (mollifiedBallCutoff x₀ hρ) x = 0) := by
  refine ⟨fun k => Classical.choose (unitProfile_iteratedFDeriv_bounded k),
    fun k => (Classical.choose_spec (unitProfile_iteratedFDeriv_bounded k)).1, ?_⟩
  intro x₀ ρ hρ
  refine ⟨mollifiedBallCutoff_smooth x₀ hρ,
    fun x => ⟨mollifiedBallCutoff_nonneg x₀ hρ x, mollifiedBallCutoff_le_one x₀ hρ x⟩,
    fun x hx => mollifiedBallCutoff_eq_one_on_closed_inner x₀ hρ hx,
    fun x hx => image_eq_zero_of_notMem_tsupport
      (mollifiedBallCutoff_notMem_tsupport x₀ hρ hx), ?_, ?_⟩
  · intro k x
    have hbound := (Classical.choose_spec (unitProfile_iteratedFDeriv_bounded k)).2
      (ρ⁻¹ • (x - x₀))
    have hpow : ρ ^ (-(k : ℝ)) = (ρ⁻¹) ^ k := by
      rw [Real.rpow_neg hρ.le, Real.rpow_natCast, ← inv_pow]
    rw [iteratedFDeriv_mollifiedBallCutoff x₀ hρ k x, norm_smul, hpow]
    rw [norm_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
    calc (ρ⁻¹) ^ k * ‖iteratedFDeriv ℝ k unitProfile (ρ⁻¹ • (x - x₀))‖ ≤
        (ρ⁻¹) ^ k * Classical.choose (unitProfile_iteratedFDeriv_bounded k) := by
          exact mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = Classical.choose (unitProfile_iteratedFDeriv_bounded k) * (ρ⁻¹) ^ k := by ring
  · intro k hk x hx
    rcases hx with hin | hout
    · refine iteratedFDeriv_eq_zero_of_eqOn_const
        (CKN.isOpen_euclideanBall x₀ (13 * ρ / 20)) (c := (1 : ℝ)) ?_ hk.ne' ?_
      · intro y hy
        exact mollifiedBallCutoff_eq_one_on_inner x₀ hρ hy
      · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
        rw [vecEuclideanNorm_eq_vec3EuclideanNorm]
        exact hin
    · refine iteratedFDeriv_eq_zero_of_eqOn_const
        (isClosed_tsupport (mollifiedBallCutoff x₀ hρ)).isOpen_compl (c := (0 : ℝ)) ?_
        hk.ne' ?_
      · intro y hy
        exact image_eq_zero_of_notMem_tsupport hy
      · exact mollifiedBallCutoff_notMem_tsupport x₀ hρ hout.le

end CKN

end
