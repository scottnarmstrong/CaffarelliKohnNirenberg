-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.GradientSeparation
import CKN.Setting.Examples.ShearCounterexample.SliceFinite
import CKN.Statements.SpatialGradientSq
import CKN.Foundation.Parabolic.Basic

/-! # Finite scale approximations to the shear fields. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped Topology
namespace CKN

def shearReducedBumpPartial (N : ℕ) (z : Vec 2 × ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, shearReducedBumpTerm n z

def shearReducedGradientPartial (i : Fin 2) (N : ℕ) (z : Vec 2 × ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, shearReducedGradientTerm i n z

def shearReducedForcePartial (N : ℕ) (z : Vec 2 × ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, shearReducedForceTerm n z

def shearFullScalarPartial (N : ℕ) (z : ParabolicPoint) : ℝ :=
  shearReducedBumpPartial N (shearReducedView z)

def shearFullGradientPartial (i : Fin 2) (N : ℕ) (z : ParabolicPoint) : ℝ :=
  shearReducedGradientPartial i N (shearReducedView z)

def shearFullForcePartial (N : ℕ) (z : ParabolicPoint) : ℝ :=
  shearReducedForcePartial N (shearReducedView z)

def shearCounterexampleVelocityPartial (N : ℕ) (z : ParabolicPoint) : Vec3 :=
  fun i => if i = 2 then shearFullScalarPartial N z else 0

def shearCounterexampleDuPartial (N : ℕ) (z : ParabolicPoint) : Fin 3 → Vec3 :=
  fun i => fun j => if i = 2 then
    if j = 0 then shearFullGradientPartial 0 N z else
      if j = 1 then shearFullGradientPartial 1 N z else 0 else 0

def shearCounterexampleForcePartial (N : ℕ) (z : ParabolicPoint) : Vec3 :=
  fun i => if i = 2 then shearFullForcePartial N z else 0

theorem shearReducedBumpTerm_nonneg (n : ℕ) (z : Vec 2 × ℝ) :
    0 ≤ shearReducedBumpTerm n z := by
  have hw : 0 ≤ shearWeight n := by
    unfold shearWeight
    positivity
  have hb : 0 ≤ shearBumpField (shearScale n) z := by
    unfold shearBumpField shearScaleBump
    exact mul_nonneg
      (canonicalBallCutoff_nonneg _ _ _ _)
      (timeCutoff_nonneg _ _ _ _)
  rw [shearReducedBumpTerm, smul_eq_mul]
  exact mul_nonneg hw hb

theorem shearReducedBumpPartial_le_series_of_time_nezero
    (N : ℕ) {x : Vec 2} {t : ℝ} (ht : t ≠ 0) :
    shearReducedBumpPartial N (x, t) ≤ shearReducedBumpSeries (x, t) := by
  obtain ⟨M, hM⟩ := exists_shearScale_sq_lt_abs_time ht
  have hsupport : Function.support (fun n : ℕ => shearReducedBumpTerm n (x, t)) ⊆
      Set.Iio M := by
    intro n hn
    change shearReducedBumpTerm n (x, t) ≠ 0 at hn
    by_contra hnM
    have hnM' : M ≤ n := Nat.le_of_not_gt hnM
    exact hn (shearReducedBumpTerm_zero_of_time_large (hM n hnM'))
  have hsum : Summable (fun n : ℕ => shearReducedBumpTerm n (x, t)) :=
    summable_of_hasFiniteSupport ((Set.finite_Iio M).subset hsupport)
  have hle := hsum.sum_le_tsum (Finset.range N) (fun n hn =>
    (shearReducedBumpTerm_nonneg n (x, t)))
  unfold shearReducedBumpPartial shearReducedBumpSeries
  exact hle

theorem shearReducedGradientPartial_abs_le_series (i : Fin 2) (N : ℕ)
    (z : Vec 2 × ℝ) :
    |shearReducedGradientPartial i N z| ≤ |shearReducedGradientSeries i z| := by
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact shearReducedGradientPartial_abs_le i N z

theorem shearReducedForcePartial_abs_le_series (N : ℕ) (z : Vec 2 × ℝ) :
    |shearReducedForcePartial N z| ≤ |shearReducedForceSeries z| := by
  by_cases hex : ∃ n, shearReducedForceTerm n z ≠ 0
  · rcases hex with ⟨n, hn⟩
    have hzero (m : ℕ) (hm : m ≠ n) : shearReducedForceTerm m z = 0 := by
      rcases lt_or_gt_of_ne hm with hmn | hnm
      · rcases shearReducedForceTerms_separated hmn z with hmz | hnz
        · exact hmz
        · exact (hn hnz).elim
      · rcases shearReducedForceTerms_separated hnm z with hnz | hmz
        · exact (hn hnz).elim
        · exact hmz
    have hseries : shearReducedForceSeries z = shearReducedForceTerm n z := by
      unfold shearReducedForceSeries
      exact tsum_eq_single n hzero
    rw [hseries]
    by_cases hnN : n < N
    · have hsum : (∑ m ∈ Finset.range N, shearReducedForceTerm m z) =
          shearReducedForceTerm n z :=
        Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr hnN)
          (fun m hm hmn => hzero m hmn)
      rw [shearReducedForcePartial, hsum]
    · have hsum : (∑ m ∈ Finset.range N, shearReducedForceTerm m z) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        exact hzero m (by
          intro hmn
          subst m
          exact (hnN (Finset.mem_range.mp hm)).elim)
      rw [shearReducedForcePartial, hsum]
      simp only [abs_zero]
      exact abs_nonneg _
  · have hzero (n : ℕ) : shearReducedForceTerm n z = 0 := by
      by_contra hn
      exact hex ⟨n, hn⟩
    have hs : shearReducedForceSeries z = 0 := by
      unfold shearReducedForceSeries
      calc
        ∑' n, shearReducedForceTerm n z = ∑' n, (0 : ℝ) :=
          tsum_congr (fun n => hzero n)
        _ = 0 := by simp
    rw [shearReducedForcePartial]
    rw [hs]
    simp [hzero]

theorem shearFullScalarPartial_le_ae (N : ℕ) :
    ∀ᵐ z : ParabolicPoint ∂volume,
      shearFullScalarPartial N z ≤ shearFullScalar z := by
  have htime : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    rw [show {t : ℝ | ¬ t ≠ 0} = ({0} : Set ℝ) by ext t; simp]
    exact measure_singleton (0 : ℝ)
  have hm : MeasurableSet {z : Vec3 × ℝ | z.2 ≠ 0} := by
    exact MeasurableSet.preimage ((measurableSet_singleton (0 : ℝ)).compl)
      (measurable_snd : Measurable (Prod.snd : Vec3 × ℝ → ℝ))
  have hprod : ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod (volume : Measure ℝ)),
      z.2 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae hm).2
    filter_upwards [] with x
    exact htime
  have hprod' : ∀ᵐ z : ParabolicPoint ∂volume, z.2 ≠ 0 := by
    change ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod (volume : Measure ℝ)),
      z.2 ≠ 0
    exact hprod
  clear hprod
  filter_upwards [hprod'] with z ht
  have hbound := shearReducedBumpPartial_le_series_of_time_nezero N ht
    (x := fun i : Fin 2 => z.1 i.castSucc)
  simpa [shearFullScalarPartial, shearFullScalar, shearReducedView] using hbound

theorem shearFullGradientPartial_abs_le (i : Fin 2) (N : ℕ)
    (z : ParabolicPoint) :
    |shearFullGradientPartial i N z| ≤ |shearFullGradient i z| := by
  simpa [shearFullGradientPartial, shearFullGradient, shearReducedView] using
    shearReducedGradientPartial_abs_le_series i N (shearReducedView z)

theorem shearFullForcePartial_abs_le (N : ℕ) (z : ParabolicPoint) :
    |shearFullForcePartial N z| ≤ |shearFullForceScalar z| := by
  simpa [shearFullForcePartial, shearFullForceScalar, shearReducedView] using
    shearReducedForcePartial_abs_le_series N (shearReducedView z)

theorem shearCounterexampleDuPartial_energy_le (N : ℕ) (z : ParabolicPoint) :
    spatialGradientSq (shearCounterexampleVelocityPartial N)
        (shearCounterexampleDuPartial N) z ≤
      spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z := by
  have h0 :
      (shearFullGradientPartial 0 N z) ^ 2 ≤ (shearFullGradient 0 z) ^ 2 := by
    calc
      _ = |shearFullGradientPartial 0 N z| ^ 2 := (sq_abs _).symm
      _ ≤ |shearFullGradient 0 z| ^ 2 :=
        (sq_le_sq₀ (abs_nonneg (shearFullGradientPartial 0 N z))
          (abs_nonneg (shearFullGradient 0 z))).2
          (shearFullGradientPartial_abs_le 0 N z)
      _ = _ := sq_abs _
  have h1 :
      (shearFullGradientPartial 1 N z) ^ 2 ≤ (shearFullGradient 1 z) ^ 2 := by
    calc
      _ = |shearFullGradientPartial 1 N z| ^ 2 := (sq_abs _).symm
      _ ≤ |shearFullGradient 1 z| ^ 2 :=
        (sq_le_sq₀ (abs_nonneg (shearFullGradientPartial 1 N z))
          (abs_nonneg (shearFullGradient 1 z))).2
          (shearFullGradientPartial_abs_le 1 N z)
      _ = _ := sq_abs _
  have hp : spatialGradientSq (shearCounterexampleVelocityPartial N)
      (shearCounterexampleDuPartial N) z =
        (shearFullGradientPartial 0 N z) ^ 2 +
          (shearFullGradientPartial 1 N z) ^ 2 := by
    simp [spatialGradientSq, shearCounterexampleDuPartial, Fin.sum_univ_succ]
  have hf : spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z =
        (shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2 := by
    simp [spatialGradientSq, shearCounterexampleDu, Fin.sum_univ_succ]
  rw [hp, hf]
  exact add_le_add h0 h1

theorem shearCounterexampleVelocityPartial_nonneg (N : ℕ) (z : ParabolicPoint) :
    0 ≤ shearCounterexampleVelocityPartial N z 2 := by
  unfold shearCounterexampleVelocityPartial shearFullScalarPartial
    shearReducedBumpPartial
  rw [ite_eq_left rfl]
  exact Finset.sum_nonneg (fun n _ => shearReducedBumpTerm_nonneg n _)

private theorem parabolicTime_nezero_ae :
    ∀ᵐ z : ParabolicPoint ∂volume, z.2 ≠ 0 := by
  have htime : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    rw [show {t : ℝ | ¬ t ≠ 0} = ({0} : Set ℝ) by ext t; simp]
    exact measure_singleton (0 : ℝ)
  have hm : MeasurableSet {z : Vec3 × ℝ | z.2 ≠ 0} := by
    exact MeasurableSet.preimage ((measurableSet_singleton (0 : ℝ)).compl)
      (measurable_snd : Measurable (Prod.snd : Vec3 × ℝ → ℝ))
  have hprod : ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod (volume : Measure ℝ)),
      z.2 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae hm).2
    filter_upwards [] with x
    exact htime
  change ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod (volume : Measure ℝ)),
    z.2 ≠ 0
  exact hprod

private theorem shearReducedForceTerm_zero_of_time_large_approx
    {n : ℕ} {x : Vec 2} {t : ℝ}
    (hlarge : 2 * shearScale n ^ 2 < |t|) :
    shearReducedForceTerm n (x, t) = 0 := by
  let r := shearScale n
  have hr : 0 < r := shearScale_pos n
  have hz : (x, t) ∉ shearProfileBox r := by
    intro hz
    have ht : t ∈ Ioo (-(2 * r ^ 2)) (2 * r ^ 2) := hz.2
    have habs : |t| < 2 * r ^ 2 := abs_lt.mpr ht
    exact (lt_asymm hlarge habs).elim
  have ht := shearScaleDerivative_zero_outside hr 1 (by norm_num)
    (fun _ : Fin 1 => ((0 : Vec 2), (1 : ℝ))) hz
  have h0 := shearScaleDerivative_zero_outside hr 2 (by norm_num)
    (fun _ : Fin 2 => (Pi.single 0 (1 : ℝ), (0 : ℝ))) hz
  have h1 := shearScaleDerivative_zero_outside hr 2 (by norm_num)
    (fun _ : Fin 2 => (Pi.single 1 (1 : ℝ), (0 : ℝ))) hz
  have ht' : shearTimeFirstField r (x, t) = 0 := by
    change iteratedFDeriv ℝ 1 (shearScaleBump r) (x, t)
      (fun _ : Fin 1 => ((0 : Vec 2), (1 : ℝ))) = 0
    exact ht
  have h0' : shearSpatialSecondField r 0 (x, t) = 0 := by
    change iteratedFDeriv ℝ 2 (shearScaleBump r) (x, t)
      (fun _ : Fin 2 => (Pi.single 0 (1 : ℝ), (0 : ℝ))) = 0
    exact h0
  have h1' : shearSpatialSecondField r 1 (x, t) = 0 := by
    change iteratedFDeriv ℝ 2 (shearScaleBump r) (x, t)
      (fun _ : Fin 2 => (Pi.single 1 (1 : ℝ), (0 : ℝ))) = 0
    exact h1
  simp [shearReducedForceTerm, shearReducedForceCore, r, ht', h0', h1']

private theorem sum_range_eq_of_zero_tail {f : ℕ → ℝ} {M N : ℕ}
    (hMN : M ≤ N) (hzero : ∀ n, M ≤ n → f n = 0) :
    (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range M, f n := by
  symm
  apply Finset.sum_subset (by
    intro n hn
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hn).trans_le hMN))
  intro n hn hnot
  have hnM : ¬ n < M := by
    intro h
    exact hnot (Finset.mem_range.mpr h)
  exact hzero n (Nat.le_of_not_gt hnM)

private theorem shearReducedBumpPartial_tendsto {x : Vec 2} {t : ℝ}
    (ht : t ≠ 0) :
    Tendsto (fun N => shearReducedBumpPartial N (x, t)) atTop
      (𝓝 (shearReducedBumpSeries (x, t))) := by
  obtain ⟨M, hM⟩ := exists_shearScale_sq_lt_abs_time ht
  have hzero : ∀ n, M ≤ n → shearReducedBumpTerm n (x, t) = 0 := by
    intro n hn
    exact shearReducedBumpTerm_zero_of_time_large (hM n hn)
  have hsum : shearReducedBumpSeries (x, t) =
      ∑ n ∈ Finset.range M, shearReducedBumpTerm n (x, t) := by
    unfold shearReducedBumpSeries
    exact tsum_eq_sum (fun n hn => by
      have hnM : M ≤ n := by
        have hnot : ¬ n < M := by simpa using hn
        exact Nat.le_of_not_gt hnot
      exact hzero n hnM)
  have heq : (fun N => shearReducedBumpPartial N (x, t)) =ᶠ[atTop]
      fun _ => shearReducedBumpSeries (x, t) := by
    filter_upwards [eventually_atTop.2 ⟨M, fun N hMN => hMN⟩] with N hN
    unfold shearReducedBumpPartial
    rw [sum_range_eq_of_zero_tail hN hzero, hsum]
  exact tendsto_const_nhds.congr' heq.symm

private theorem shearReducedGradientPartial_tendsto {i : Fin 2} {x : Vec 2} {t : ℝ}
    (ht : t ≠ 0) :
    Tendsto (fun N => shearReducedGradientPartial i N (x, t)) atTop
      (𝓝 (shearReducedGradientSeries i (x, t))) := by
  obtain ⟨M, hM⟩ := exists_shearScale_sq_lt_abs_time ht
  have hzero : ∀ n, M ≤ n → shearReducedGradientTerm i n (x, t) = 0 := by
    intro n hn
    exact shearReducedGradientTerm_zero_of_time_large (hM n hn)
  have hsum : shearReducedGradientSeries i (x, t) =
      ∑ n ∈ Finset.range M, shearReducedGradientTerm i n (x, t) := by
    unfold shearReducedGradientSeries
    exact tsum_eq_sum (fun n hn => by
      have hnM : M ≤ n := by
        have hnot : ¬ n < M := by simpa using hn
        exact Nat.le_of_not_gt hnot
      exact hzero n hnM)
  have heq : (fun N => shearReducedGradientPartial i N (x, t)) =ᶠ[atTop]
      fun _ => shearReducedGradientSeries i (x, t) := by
    filter_upwards [eventually_atTop.2 ⟨M, fun N hMN => hMN⟩] with N hN
    unfold shearReducedGradientPartial
    rw [sum_range_eq_of_zero_tail hN hzero, hsum]
  exact tendsto_const_nhds.congr' heq.symm

private theorem shearReducedForcePartial_tendsto {x : Vec 2} {t : ℝ}
    (ht : t ≠ 0) :
    Tendsto (fun N => shearReducedForcePartial N (x, t)) atTop
      (𝓝 (shearReducedForceSeries (x, t))) := by
  obtain ⟨M, hM⟩ := exists_shearScale_sq_lt_abs_time ht
  have hzero : ∀ n, M ≤ n → shearReducedForceTerm n (x, t) = 0 := by
    intro n hn
    exact shearReducedForceTerm_zero_of_time_large_approx (hM n hn)
  have hsum : shearReducedForceSeries (x, t) =
      ∑ n ∈ Finset.range M, shearReducedForceTerm n (x, t) := by
    unfold shearReducedForceSeries
    exact tsum_eq_sum (fun n hn => by
      have hnM : M ≤ n := by
        have hnot : ¬ n < M := by simpa using hn
        exact Nat.le_of_not_gt hnot
      exact hzero n hnM)
  have heq : (fun N => shearReducedForcePartial N (x, t)) =ᶠ[atTop]
      fun _ => shearReducedForceSeries (x, t) := by
    filter_upwards [eventually_atTop.2 ⟨M, fun N hMN => hMN⟩] with N hN
    unfold shearReducedForcePartial
    rw [sum_range_eq_of_zero_tail hN hzero, hsum]
  exact tendsto_const_nhds.congr' heq.symm

theorem shearFullScalarPartial_tendsto_ae :
    ∀ᵐ z : ParabolicPoint ∂volume,
      Tendsto (fun M => shearFullScalarPartial M z) atTop (𝓝 (shearFullScalar z)) := by
  filter_upwards [parabolicTime_nezero_ae] with z ht
  simpa [shearFullScalarPartial, shearFullScalar, shearReducedView] using
    shearReducedBumpPartial_tendsto (x := fun i : Fin 2 => z.1 i.castSucc) ht

theorem shearFullGradientPartial_tendsto_ae (i : Fin 2) :
    ∀ᵐ z : ParabolicPoint ∂volume,
      Tendsto (fun N => shearFullGradientPartial i N z) atTop
        (𝓝 (shearFullGradient i z)) := by
  filter_upwards [parabolicTime_nezero_ae] with z ht
  simpa [shearFullGradientPartial, shearFullGradient, shearReducedView] using
    shearReducedGradientPartial_tendsto (x := fun j : Fin 2 => z.1 j.castSucc) ht

theorem shearFullForcePartial_tendsto_ae :
    ∀ᵐ z : ParabolicPoint ∂volume,
      Tendsto (fun N => shearFullForcePartial N z) atTop
        (𝓝 (shearFullForceScalar z)) := by
  filter_upwards [parabolicTime_nezero_ae] with z ht
  simpa [shearFullForcePartial, shearFullForceScalar, shearReducedView] using
    shearReducedForcePartial_tendsto (x := fun j : Fin 2 => z.1 j.castSucc) ht

end CKN
