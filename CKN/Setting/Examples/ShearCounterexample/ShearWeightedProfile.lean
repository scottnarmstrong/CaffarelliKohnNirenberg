-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Cutoff.SpaceTime
import CKN.Foundation.Parabolic.Basic
import CKN.Foundation.Parabolic.BallDisplays
import CKN.Foundation.Parabolic.Vec3Norm
import CKN.Statements.ParabolicHolderVecOn
import CKN.Statements.RegularPoint
import Mathlib.Analysis.PSeries

/-! # The weighted parabolic shear profile and its singularity. -/

open Set
open Filter
open MeasureTheory
open CKN.Foundation.Parabolic
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace CKN

private theorem euclideanSqDist_nonneg_local {d : ℕ} (x y : Vec d) :
    0 ≤ euclideanSqDist x y := by
  unfold euclideanSqDist
  exact vecNormSq_nonneg _

private def shearSpaceProjection (x : Vec3) : Vec 2 :=
  fun i => x i.castSucc

/-- A compact parabolic cutoff independent of the shear direction. -/
def shearParabolicBump (r : ℝ) (z : ParabolicPoint) : ℝ :=
  canonicalBallCutoff (0 : Vec 2) (r / 2) r (shearSpaceProjection z.1) *
    timeCutoff (r ^ 2 / 8) (r / 2) r z.2


theorem shearParabolicBump_eq_one_on_inner {r : ℝ} (hr : 0 < r)
    {z : ParabolicPoint}
    (hx : euclideanSqDist (shearSpaceProjection z.1) 0 < (r / 2) ^ 2)
    (ht : z.2 ∈ Icc (-(r ^ 2 / 8)) (r ^ 2 / 8)) :
    shearParabolicBump r z = 1 := by
  unfold shearParabolicBump
  rw [canonicalBallCutoff_eq_one_on_inner
    (by positivity : 0 ≤ r / 2) (by linarith only [hr]) hx,
    timeCutoff_eq_one_on (by positivity : 0 ≤ r / 2)
      (by linarith only [hr])]
  · norm_num
  · have hleft : r ^ 2 / 8 - (r / 2) ^ 2 = -(r ^ 2 / 8) := by ring
    constructor
    · rw [hleft]
      exact ht.1
    · exact ht.2


theorem shearParabolicBump_nonneg (r : ℝ) (z : ParabolicPoint) :
    0 ≤ shearParabolicBump r z := by
  unfold shearParabolicBump
  exact mul_nonneg (canonicalBallCutoff_nonneg _ _ _ _)
    (timeCutoff_nonneg _ _ _ _)

def shearScale (n : ℕ) : ℝ := (1 / 4 : ℝ) ^ n

theorem shearScale_pos (n : ℕ) : 0 < shearScale n := by
  unfold shearScale
  positivity

theorem shearScale_antitone {m n : ℕ} (hmn : m ≤ n) :
    shearScale n ≤ shearScale m := by
  unfold shearScale
  exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1) hmn

def shearSeriesTerm (n : ℕ) (z : ParabolicPoint) : ℝ :=
  (1 / (n + 1 : ℝ) ^ (3 / 4 : ℝ)) * shearParabolicBump (shearScale n) z

def shearSeries (z : ParabolicPoint) : ℝ :=
  ∑' n, shearSeriesTerm n z

def shearVelocity (z : ParabolicPoint) : Vec3 :=
  shearSeries z • basisVec (2 : Fin 3)

@[simp]
theorem shearVelocity_third (z : ParabolicPoint) :
    shearVelocity z 2 = shearSeries z := by
  simp [shearVelocity, basisVec_apply]

def shearHarmonicPartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (1 / (n + 1 : ℝ) ^ (3 / 4 : ℝ))

private theorem shearWeight_ge_harmonic (n : ℕ) :
    (1 / (n + 1 : ℝ)) ≤ (1 / (n + 1 : ℝ) ^ (3 / 4 : ℝ)) := by
  have hb : 1 ≤ (n + 1 : ℝ) := by
    exact_mod_cast (Nat.le_add_left 1 n)
  have hp : (n + 1 : ℝ) ^ (3 / 4 : ℝ) ≤ (n + 1 : ℝ) := by
    calc
      (n + 1 : ℝ) ^ (3 / 4 : ℝ) ≤ (n + 1 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
      _ = (n + 1 : ℝ) := by simp
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _) hp

private theorem shearHarmonicPartial_eventually_gt (M : ℝ) :
    ∀ᶠ N : ℕ in atTop, M < shearHarmonicPartial N := by
  have hdom (N : ℕ) :
      (∑ n ∈ Finset.range N, (1 / (n + 1 : ℝ))) ≤
        shearHarmonicPartial N := by
    unfold shearHarmonicPartial
    exact Finset.sum_le_sum fun n hn => shearWeight_ge_harmonic n
  have hlarge : ∀ᶠ N : ℕ in atTop,
      M < ∑ n ∈ Finset.range N, (1 / (n + 1 : ℝ)) :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
      (Ioi_mem_atTop M)
  exact hlarge.mono fun N hN => lt_of_lt_of_le hN (hdom N)

theorem shearSeriesTerm_nonneg (n : ℕ) (z : ParabolicPoint) :
    0 ≤ shearSeriesTerm n z := by
  unfold shearSeriesTerm
  exact mul_nonneg (by positivity) (shearParabolicBump_nonneg _ _)

theorem shearParabolicBump_nonzero_bounds {r : ℝ} (hr : 0 < r)
    {z : ParabolicPoint} (hz : shearParabolicBump r z ≠ 0) :
    euclideanSqDist (shearSpaceProjection z.1) 0 < r ^ 2 ∧ |z.2| < r ^ 2 := by
  have hxsupport : shearSpaceProjection z.1 ∈
      Function.support (canonicalBallCutoff (0 : Vec 2) (r / 2) r) := by
    apply Function.mem_support.mpr
    intro hzero
    apply hz
    simp [shearParabolicBump, hzero]
  have hx := canonicalBallCutoff_tsupport_subset_outer
      (by positivity : 0 ≤ r / 2) (by linarith only [hr])
      (subset_tsupport _ hxsupport)
  have htsupport : z.2 ∈ Function.support (timeCutoff (r ^ 2 / 8) (r / 2) r) := by
    apply Function.mem_support.mpr
    intro hzero
    apply hz
    simp [shearParabolicBump, hzero]
  have ht := timeCutoff_support_subset
      (by positivity : 0 ≤ r / 2) (by linarith only [hr]) htsupport
  constructor
  · change euclideanSqDist (shearSpaceProjection z.1) 0 < r ^ 2 at hx
    exact hx
  · have hlo : r ^ 2 / 8 - r ^ 2 < z.2 := ht.1
    have hupp : z.2 < r ^ 2 / 8 + (r ^ 2 - (r / 2) ^ 2) := ht.2
    have habs : |z.2| < r ^ 2 := by
      rw [abs_lt]
      constructor <;> nlinarith only [hlo, hupp, sq_nonneg r]
    exact habs

def shearReducedParabolicDist (z : ParabolicPoint) : ℝ :=
  max (Real.sqrt (euclideanSqDist (shearSpaceProjection z.1) 0))
    (Real.sqrt |z.2|)

theorem shearParabolicBump_eq_zero_of_dist_le {r : ℝ} (hr : 0 < r)
    {z : ParabolicPoint} (hd : r ≤ shearReducedParabolicDist z) :
    shearParabolicBump r z = 0 := by
  by_contra hne
  have hb := shearParabolicBump_nonzero_bounds hr hne
  have hspace : Real.sqrt (euclideanSqDist (shearSpaceProjection z.1) 0) < r :=
    (Real.sqrt_lt' hr).mpr hb.1
  have htime : Real.sqrt |z.2| < r := (Real.sqrt_lt' hr).mpr hb.2
  have hdist := max_lt hspace htime
  change r ≤ max (Real.sqrt (euclideanSqDist (shearSpaceProjection z.1) 0))
    (Real.sqrt |z.2|) at hd
  exact (not_lt_of_ge hd) hdist

theorem shearReducedParabolicDist_pos {z : ParabolicPoint}
    (hz : z.1 0 ≠ 0 ∨ z.1 1 ≠ 0 ∨ z.2 ≠ 0) :
    0 < shearReducedParabolicDist z := by
  unfold shearReducedParabolicDist
  rcases hz with hx0 | hx1 | ht
  · have hsq : euclideanSqDist (shearSpaceProjection z.1) 0 ≠ 0 := by
      intro heq
      have hv : shearSpaceProjection z.1 = 0 := by
        apply vecNormSq_eq_zero
        simpa [euclideanSqDist, sub_zero] using heq
      have hv0 : z.1 0 = 0 := by simpa [shearSpaceProjection] using congrFun hv 0
      exact hx0 hv0
    have hpos : 0 < euclideanSqDist (shearSpaceProjection z.1) 0 :=
      lt_of_le_of_ne (euclideanSqDist_nonneg_local _ _) (Ne.symm hsq)
    have hsqrt : 0 < Real.sqrt (euclideanSqDist (shearSpaceProjection z.1) 0) :=
      Real.sqrt_pos.2 hpos
    exact lt_of_lt_of_le hsqrt (le_max_left _ _)
  · have hsq : euclideanSqDist (shearSpaceProjection z.1) 0 ≠ 0 := by
      intro heq
      have hv : shearSpaceProjection z.1 = 0 := by
        apply vecNormSq_eq_zero
        simpa [euclideanSqDist, sub_zero] using heq
      have hv1 : z.1 1 = 0 := by simpa [shearSpaceProjection] using congrFun hv 1
      exact hx1 hv1
    have hpos : 0 < euclideanSqDist (shearSpaceProjection z.1) 0 :=
      lt_of_le_of_ne (euclideanSqDist_nonneg_local _ _) (Ne.symm hsq)
    have hsqrt : 0 < Real.sqrt (euclideanSqDist (shearSpaceProjection z.1) 0) :=
      Real.sqrt_pos.2 hpos
    exact lt_of_lt_of_le hsqrt (le_max_left _ _)
  · have habs : 0 < |z.2| := abs_pos.mpr ht
    have hsqrt : 0 < Real.sqrt |z.2| := Real.sqrt_pos.2 habs
    exact lt_of_lt_of_le hsqrt (le_max_right _ _)

theorem shearSeriesTerm_eq_zero_of_dist_le {n : ℕ} {z : ParabolicPoint}
    (hd : shearScale n ≤ shearReducedParabolicDist z) :
    shearSeriesTerm n z = 0 := by
  unfold shearSeriesTerm
  rw [shearParabolicBump_eq_zero_of_dist_le (shearScale_pos n) hd, mul_zero]

theorem shearSeriesTerm_summable_off_axis {z : ParabolicPoint}
    (hz : z.1 0 ≠ 0 ∨ z.1 1 ≠ 0 ∨ z.2 ≠ 0) :
    Summable (fun n => shearSeriesTerm n z) := by
  have hd : 0 < shearReducedParabolicDist z := shearReducedParabolicDist_pos hz
  have hscale : Tendsto shearScale atTop (𝓝 0) := by
    unfold shearScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop, shearScale n < shearReducedParabolicDist z :=
    hscale.eventually (Iio_mem_nhds hd)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  have hsubset : Function.support (fun n => shearSeriesTerm n z) ⊆ Set.Iio N := by
    intro n hn
    change shearSeriesTerm n z ≠ 0 at hn
    by_contra hnN
    have hle : N ≤ n := Nat.le_of_not_gt hnN
    have hzero := shearSeriesTerm_eq_zero_of_dist_le (z := z) (hN n hle).le
    exact hn hzero
  exact summable_of_hasFiniteSupport ((Set.finite_Iio N).subset hsubset)

theorem shearParabolicBump_eq_one_of_earlier_scale_core {n N : ℕ}
    (hnN : n ≤ N) {z : ParabolicPoint}
    (hx : euclideanSqDist (shearSpaceProjection z.1) 0 <
      (shearScale N / 2) ^ 2)
    (ht : z.2 ∈ Icc (-(shearScale N ^ 2 / 8)) (shearScale N ^ 2 / 8)) :
    shearParabolicBump (shearScale n) z = 1 := by
  have hscale : shearScale N ≤ shearScale n := shearScale_antitone hnN
  have hscaleN : 0 ≤ shearScale N := (shearScale_pos N).le
  have hscalen : 0 ≤ shearScale n := (shearScale_pos n).le
  have hrad : shearScale N / 2 ≤ shearScale n / 2 := by linarith only [hscale]
  have hradSq : (shearScale N / 2) ^ 2 ≤ (shearScale n / 2) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hrad
  have hscaleSq : shearScale N ^ 2 ≤ shearScale n ^ 2 := by
    exact (sq_le_sq₀ hscaleN hscalen).2 hscale
  apply shearParabolicBump_eq_one_on_inner (shearScale_pos n)
  · exact lt_of_lt_of_le hx hradSq
  · constructor
    · have hl := ht.1
      nlinarith only [hl, hscaleSq]
    · have hu := ht.2
      nlinarith only [hu, hscaleSq]

theorem shearSeriesTerm_eq_harmonic_of_core {n N : ℕ}
    (hnN : n ≤ N) {z : ParabolicPoint}
    (hx : euclideanSqDist (shearSpaceProjection z.1) 0 <
      (shearScale N / 2) ^ 2)
    (ht : z.2 ∈ Icc (-(shearScale N ^ 2 / 8)) (shearScale N ^ 2 / 8)) :
    shearSeriesTerm n z = 1 / (n + 1 : ℝ) ^ (3 / 4 : ℝ) := by
  unfold shearSeriesTerm
  rw [shearParabolicBump_eq_one_of_earlier_scale_core hnN hx ht]
  ring

theorem shearSeries_lower_bound_on_core {N : ℕ} {z : ParabolicPoint}
    (hz : z.1 0 ≠ 0 ∨ z.1 1 ≠ 0 ∨ z.2 ≠ 0)
    (hx : euclideanSqDist (shearSpaceProjection z.1) 0 <
      (shearScale N / 2) ^ 2)
    (ht : z.2 ∈ Icc (-(shearScale N ^ 2 / 8)) (shearScale N ^ 2 / 8)) :
    (∑ n ∈ Finset.range N, (1 / (n + 1 : ℝ) ^ (3 / 4 : ℝ))) ≤
      shearSeries z := by
  have hterm : ∑ n ∈ Finset.range N, shearSeriesTerm n z =
      ∑ n ∈ Finset.range N, (1 / (n + 1 : ℝ) ^ (3 / 4 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnN : n ≤ N := Nat.le_of_lt (Finset.mem_range.mp hn)
    exact shearSeriesTerm_eq_harmonic_of_core hnN hx ht
  rw [← hterm, show shearSeries z = ∑' n, shearSeriesTerm n z by rfl]
  exact (shearSeriesTerm_summable_off_axis hz).sum_le_tsum _
    (fun n _hn => shearSeriesTerm_nonneg n z)



theorem exists_shear_small_scale_with_large_harmonic
    {δ M : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, shearScale N < δ ∧ M < shearHarmonicPartial N := by
  have hlarge := shearHarmonicPartial_eventually_gt M
  have hscale : Tendsto shearScale atTop (𝓝 0) := by
    unfold shearScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ N : ℕ in atTop, shearScale N < δ :=
    hscale.eventually (Iio_mem_nhds hδ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hlarge
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hsmall
  let N := max N₀ N₁
  have hN₀N : N₀ ≤ N := Nat.le_max_left _ _
  have hN₁N : N₁ ≤ N := Nat.le_max_right _ _
  refine ⟨N, ?_, ?_⟩
  · exact (shearScale_antitone hN₁N).trans_lt (hN₁ N₁ le_rfl)
  · exact hN₀ N hN₀N

theorem exists_arbitrarily_small_high_shear_core
    {δ M : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, shearScale N < δ ∧ ∀ z : ParabolicPoint,
      euclideanSqDist (shearSpaceProjection z.1) 0 <
          (shearScale N / 2) ^ 2 →
      z.2 ∈ Icc (-(shearScale N ^ 2 / 8)) (shearScale N ^ 2 / 8) →
      (z.1 0 ≠ 0 ∨ z.1 1 ≠ 0 ∨ z.2 ≠ 0) →
      M < shearSeries z := by
  obtain ⟨N, hscale, hsum⟩ := exists_shear_small_scale_with_large_harmonic hδ
  refine ⟨N, hscale, fun z hx ht hz => ?_⟩
  exact hsum.trans_le (shearSeries_lower_bound_on_core hz hx ht)

def shearHighSet (r : ℝ) : Set ParabolicPoint :=
  vec3Ball ((r / 8) • basisVec (0 : Fin 3)) (r / 16) ×ˢ
    Ioo (-(r ^ 2 / 16)) (r ^ 2 / 16)

theorem shearHighSet_subset_core {r : ℝ} (hr : 0 < r) :
    shearHighSet r ⊆ {z : ParabolicPoint |
      euclideanSqDist (shearSpaceProjection z.1) 0 < (r / 2) ^ 2 ∧
        z.2 ∈ Icc (-(r ^ 2 / 8)) (r ^ 2 / 8) ∧ z.1 0 ≠ 0} := by
  intro z hz
  rcases hz with ⟨hx, ht⟩
  change vec3EuclideanNorm (z.1 - (r / 8) • basisVec 0) < r / 16 at hx
  have hc : vec3EuclideanNorm ((r / 8) • basisVec (0 : Fin 3)) = r / 8 := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (by positivity : 0 < r / 8)]
    simp [basisVec_apply, vec3EuclideanNorm]
  have htri : vec3EuclideanNorm z.1 ≤
      vec3EuclideanNorm (z.1 - (r / 8) • basisVec 0) +
        vec3EuclideanNorm ((r / 8) • basisVec 0) := by
    have := vec3EuclideanNorm_add_le (z.1 - (r / 8) • basisVec 0)
      ((r / 8) • basisVec 0)
    have heq : (z.1 - (r / 8) • basisVec 0) +
        (r / 8) • basisVec 0 = z.1 := by abel
    rw [heq] at this
    exact this
  have hnorm : vec3EuclideanNorm z.1 < 3 * r / 16 := by
    rw [hc] at htri
    linarith only [htri, hx]
  have hcoord0 := abs_apply_le_vec3EuclideanNorm z.1 (0 : Fin 3)
  have hcoord1 := abs_apply_le_vec3EuclideanNorm z.1 (1 : Fin 3)
  have hcoord0_shift := abs_apply_le_vec3EuclideanNorm
    (z.1 - (r / 8) • basisVec 0) (0 : Fin 3)
  have hcoord0_pos : 0 < z.1 0 := by
    have hdiff : |z.1 0 - r / 8| < r / 16 := by
      have hcoord : |z.1 0 - r / 8| ≤
          vec3EuclideanNorm (z.1 - (r / 8) • basisVec 0) := by
        simpa [basisVec_apply] using hcoord0_shift
      exact lt_of_le_of_lt hcoord hx
    rw [abs_lt] at hdiff
    linarith only [hdiff.1, hr]
  have hdist : euclideanSqDist (shearSpaceProjection z.1) 0 < (r / 2) ^ 2 := by
    have hformula : euclideanSqDist (shearSpaceProjection z.1) 0 =
        (z.1 0) ^ 2 + (z.1 1) ^ 2 := by
      simp [euclideanSqDist, vecNormSq_eq_sum_sq, shearSpaceProjection,
        Fin.sum_univ_succ]
    rw [hformula]
    have h0 : |z.1 0| < 3 * r / 16 := lt_of_le_of_lt hcoord0 hnorm
    have h1 : |z.1 1| < 3 * r / 16 := lt_of_le_of_lt hcoord1 hnorm
    have h0sq : (z.1 0) ^ 2 < (3 * r / 16) ^ 2 := by
      have h := (sq_lt_sq₀ (abs_nonneg (z.1 0)) (by positivity)).2 h0
      simpa only [sq_abs] using h
    have h1sq : (z.1 1) ^ 2 < (3 * r / 16) ^ 2 := by
      have h := (sq_lt_sq₀ (abs_nonneg (z.1 1)) (by positivity)).2 h1
      simpa only [sq_abs] using h
    nlinarith only [h0sq, h1sq, hr]
  have htIcc : z.2 ∈ Icc (-(r ^ 2 / 8)) (r ^ 2 / 8) := by
    rcases ht with ⟨htl, htu⟩
    constructor <;> nlinarith only [htl, htu, sq_nonneg r]
  exact ⟨hdist, htIcc, ne_of_gt hcoord0_pos⟩

theorem volume_shearHighSet_ne_zero {r : ℝ} (hr : 0 < r) :
    volume (shearHighSet r) ≠ 0 := by
  unfold shearHighSet
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
    (vec3Ball ((r / 8) • basisVec (0 : Fin 3)) (r / 16) ×ˢ
      Ioo (-(r ^ 2 / 16)) (r ^ 2 / 16)) ≠ 0
  rw [Measure.prod_prod, volume_vec3Ball_eq,
    Real.volume_Ioo]
  have hlen : 0 < r ^ 2 / 8 := by positivity
  have hspace : 0 < ENNReal.ofReal (r / 16) ^ 3 *
      ENNReal.ofReal (Real.pi * 4 / 3) := by positivity
  have htime : 0 < ENNReal.ofReal (r ^ 2 / 8) := ENNReal.ofReal_pos.mpr hlen
  have hformula : r ^ 2 / 16 - -(r ^ 2 / 16) = r ^ 2 / 8 := by ring
  rw [hformula]
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ r / 16),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (r / 16) ^ 3),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ ((r / 16) ^ 3 * (Real.pi * 4 / 3)))]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

theorem shearHighSet_subset_metricBall {r δ : ℝ} (hr : 0 < r)
    (hrδ : r < δ) : shearHighSet r ⊆ Metric.ball ((0 : Vec3), (0 : ℝ)) δ := by
  intro z hz
  rcases hz with ⟨hx, ht⟩
  change vec3EuclideanNorm (z.1 - (r / 8) • basisVec 0) < r / 16 at hx
  have hc : vec3EuclideanNorm ((r / 8) • basisVec (0 : Fin 3)) = r / 8 := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (by positivity : 0 < r / 8)]
    simp [basisVec_apply, vec3EuclideanNorm]
  have htri : vec3EuclideanNorm z.1 ≤
      vec3EuclideanNorm (z.1 - (r / 8) • basisVec 0) +
        vec3EuclideanNorm ((r / 8) • basisVec 0) := by
    have h := vec3EuclideanNorm_add_le (z.1 - (r / 8) • basisVec 0)
      ((r / 8) • basisVec 0)
    have heq : (z.1 - (r / 8) • basisVec 0) +
        (r / 8) • basisVec 0 = z.1 := by abel
    rw [heq] at h
    exact h
  have hspace : vec3EuclideanNorm z.1 < δ := by
    rw [hc] at htri
    linarith only [htri, hx, hrδ, hr]
  have htime : Real.sqrt |z.2| < δ := by
    have htsq : |z.2| < r ^ 2 / 16 := by
      rcases ht with ⟨hlo, hupp⟩
      rw [abs_lt]
      constructor <;> nlinarith only [hlo, hupp]
    have hsqrt : Real.sqrt |z.2| < r / 4 :=
      (Real.sqrt_lt' (by positivity : 0 < r / 4)).mpr (by nlinarith only [htsq])
    linarith only [hsqrt, hrδ, hr]
  change z ∈ Metric.ball (show ParabolicPoint from ((0 : Vec3), (0 : ℝ))) δ
  rw [Metric.mem_ball, dist_eq_parabolicDist]
  change max (vec3EuclideanNorm (z.1 - 0))
      (Real.sqrt |z.2 - 0|) < δ
  simpa only [sub_zero] using max_lt hspace htime

theorem exists_positive_measure_high_shear_set
    {δ M : ℝ} (hδ : 0 < δ) :
    ∃ U : Set ParabolicPoint, U ⊆ Metric.ball ((0 : Vec3), (0 : ℝ)) δ ∧
      volume U ≠ 0 ∧ MeasurableSet U ∧ ∀ z ∈ U, M < shearSeries z := by
  obtain ⟨N, hscale, hlarge⟩ := exists_arbitrarily_small_high_shear_core hδ
  let r := shearScale N
  have hr : 0 < r := shearScale_pos N
  refine ⟨shearHighSet r, shearHighSet_subset_metricBall hr hscale, ?_, ?_, ?_⟩
  · exact volume_shearHighSet_ne_zero hr
  · exact (vec3Ball_measurable _ _).prod measurableSet_Ioo
  · intro z hz
    have hcore := shearHighSet_subset_core hr hz
    exact hlarge z hcore.1 hcore.2.1 (Or.inl hcore.2.2)

theorem shearVelocity_no_holder_ae_on_open_neighborhood
    (U : Set ParabolicPoint) (g : ParabolicPoint → Vec3) (γ : ℝ)
    (hU : IsOpen U) (h0 : ((0 : Vec3), (0 : ℝ)) ∈ U)
    (hEq : g =ᵐ[volume.restrict U] shearVelocity) :
    ¬ ParabolicHolderVecOn U g γ := by
  intro hHolder
  obtain ⟨B, K, hB, hK, hbound, _hmod⟩ := hHolder
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨V, hVball, hVpos, hVmeas, hVlarge⟩ :=
    exists_positive_measure_high_shear_set hδ
  have hVU : V ⊆ U := hVball.trans hball
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hEqfull : ∀ᵐ z ∂volume, z ∈ U → g z = shearVelocity z :=
    (ae_restrict_iff' hUmeas).mp hEq
  have hEqV : ∀ᵐ z ∂volume.restrict V, g z = shearVelocity z := by
    apply (ae_restrict_iff' hVmeas).2
    filter_upwards [hEqfull] with z hz hzV
    exact hz (hVU hzV)
  have hBoundV : ∀ᵐ z ∂volume.restrict V, vec3EuclideanNorm (g z) ≤ B := by
    apply (ae_restrict_iff' hVmeas).2
    exact Filter.Eventually.of_forall fun z hzV => hbound z (hVU hzV)
  have hLargeV : ∀ᵐ z ∂volume.restrict V, B + 1 < shearSeries z := by
    apply (ae_restrict_iff' hVmeas).2
    exact Filter.Eventually.of_forall fun z hzV => hVlarge z hzV
  have hFalse : ∀ᵐ z ∂volume.restrict V, False := by
    filter_upwards [hEqV, hBoundV, hLargeV] with z hzEq hzB hzlarge
    have hw : shearSeries z ≤ B := by
      calc
        shearSeries z ≤ |shearSeries z| := le_abs_self _
        _ = |g z 2| := by
          have hcoord : g z 2 = shearSeries z := by
            simpa only [shearVelocity_third] using congrFun hzEq (2 : Fin 3)
          rw [hcoord]
        _ ≤ vec3EuclideanNorm (g z) := abs_apply_le_vec3EuclideanNorm _ _
        _ ≤ B := hzB
    linarith only [hzlarge, hw]
  have hzero : volume V = 0 := by
    have hmeasure := ae_iff.mp hFalse
    simpa [Measure.restrict_apply, hVmeas] using hmeasure
  exact hVpos hzero

theorem shearVelocity_not_regular_at_origin :
    ¬ IsRegularPoint (vec3Ball 0 1) (Ioo (-1) 1) shearVelocity
      ((0 : Vec3), (0 : ℝ)) := by
  intro hregular
  rcases hregular with ⟨_, N, hNopen, hN0, _hNdomain, γ, _hγ, _hγ1,
    g, hAE, hHolder⟩
  exact shearVelocity_no_holder_ae_on_open_neighborhood
    N g γ hNopen hN0 hAE hHolder

end CKN
