-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.ScaleSupport
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.PSeries

/-! # L2 estimates for the shear force. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

private theorem shearReducedForceCore_continuous {r : ℝ} (hr : 0 < r) :
    Continuous (shearReducedForceCore r) := by
  unfold shearReducedForceCore
  exact ((shearTimeFirstField_continuous hr).sub
    (shearSpatialSecondField_continuous hr 0)).sub
      (shearSpatialSecondField_continuous hr 1)

private theorem shearReducedForceTerm_continuous (n : ℕ) :
    Continuous (shearReducedForceTerm n) := by
  unfold shearReducedForceTerm
  change Continuous (fun z => shearWeight n * shearReducedForceCore (shearScale n) z)
  exact continuous_const.mul (shearReducedForceCore_continuous (shearScale_pos n))

private theorem shearReducedForceCore_abs_bound {r C : ℝ} (hr : 0 < r)
    (_ : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (z : Vec 2 × ℝ) :
    |shearReducedForceCore r z| ≤ 3 * C * r⁻¹ ^ 2 := by
  have ht := shearScaleBump_timeFirst_bound hr hUnit z
  have h0 := shearScaleBump_spatialSecond_bound hr hUnit 0 z
  have h1 := shearScaleBump_spatialSecond_bound hr hUnit 1 z
  have ht' : |shearTimeFirstField r z| ≤ C * r⁻¹ ^ 2 := by
    change ‖shearTimeFirstField r z‖ ≤ _ at ht
    simpa only [Real.norm_eq_abs] using ht
  have h0' : |shearSpatialSecondField r 0 z| ≤ C * r⁻¹ ^ 2 := by
    change ‖shearSpatialSecondField r 0 z‖ ≤ _ at h0
    simpa only [Real.norm_eq_abs] using h0
  have h1' : |shearSpatialSecondField r 1 z| ≤ C * r⁻¹ ^ 2 := by
    change ‖shearSpatialSecondField r 1 z‖ ≤ _ at h1
    simpa only [Real.norm_eq_abs] using h1
  unfold shearReducedForceCore
  calc
    |shearTimeFirstField r z - shearSpatialSecondField r 0 z -
        shearSpatialSecondField r 1 z| =
      |(shearTimeFirstField r z + -(shearSpatialSecondField r 0 z)) +
        -(shearSpatialSecondField r 1 z)| := by congr 1
    _ ≤ |shearTimeFirstField r z + -(shearSpatialSecondField r 0 z)| +
        |-(shearSpatialSecondField r 1 z)| := abs_add_le _ _
    _ ≤ |shearTimeFirstField r z| + |shearSpatialSecondField r 0 z| +
        |shearSpatialSecondField r 1 z| := by
      rw [abs_neg]
      have htri :
          |shearTimeFirstField r z + -(shearSpatialSecondField r 0 z)| ≤
            |shearTimeFirstField r z| + |shearSpatialSecondField r 0 z| := by
        simpa only [abs_neg] using
          (abs_add_le (shearTimeFirstField r z)
            (-(shearSpatialSecondField r 0 z)))
      exact add_le_add htri le_rfl
    _ ≤ 3 * C * r⁻¹ ^ 2 := by nlinarith only [ht', h0', h1']

private theorem shearReducedForceTerm_abs_bound {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (n : ℕ) (z : Vec 2 × ℝ) :
    |shearReducedForceTerm n z| ≤
      3 * C * shearWeight n * (shearScale n)⁻¹ ^ 2 := by
  have hw : 0 ≤ shearWeight n := by
    unfold shearWeight
    positivity
  have hr := shearScale_pos n
  have hc := shearReducedForceCore_abs_bound hr hC hUnit z
  rw [shearReducedForceTerm, smul_eq_mul]
  rw [abs_mul, abs_of_nonneg hw]
  calc
    shearWeight n * |shearReducedForceCore (shearScale n) z| ≤
      shearWeight n * (3 * C * (shearScale n)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left hc hw
    _ = 3 * C * shearWeight n * (shearScale n)⁻¹ ^ 2 := by ring

private theorem shearReducedForceTerm_zero_outside {n : ℕ} {z : Vec 2 × ℝ}
    (hz : z ∉ shearProfileBox (shearScale n)) :
    shearReducedForceTerm n z = 0 := by
  have ht := shearScaleDerivative_zero_outside (shearScale_pos n) 1
    (by norm_num) (fun _ : Fin 1 => ((0 : Vec 2), (1 : ℝ))) hz
  have h0 := shearScaleDerivative_zero_outside (shearScale_pos n) 2
    (by norm_num) (fun _ : Fin 2 => (Pi.single 0 (1 : ℝ), (0 : ℝ))) hz
  have h1 := shearScaleDerivative_zero_outside (shearScale_pos n) 2
    (by norm_num) (fun _ : Fin 2 => (Pi.single 1 (1 : ℝ), (0 : ℝ))) hz
  have ht' : shearTimeFirstField (shearScale n) z = 0 := by
    change (iteratedFDeriv ℝ 1 (shearScaleBump (shearScale n)) z
      (fun _ : Fin 1 => ((0 : Vec 2), (1 : ℝ)))) = 0
    exact ht
  have h0' : shearSpatialSecondField (shearScale n) 0 z = 0 := by
    change (iteratedFDeriv ℝ 2 (shearScaleBump (shearScale n)) z
      (fun _ : Fin 2 => (Pi.single 0 (1 : ℝ), (0 : ℝ)))) = 0
    exact h0
  have h1' : shearSpatialSecondField (shearScale n) 1 z = 0 := by
    change (iteratedFDeriv ℝ 2 (shearScaleBump (shearScale n)) z
      (fun _ : Fin 2 => (Pi.single 1 (1 : ℝ), (0 : ℝ)))) = 0
    exact h1
  simp [shearReducedForceTerm, shearReducedForceCore, ht', h0', h1']

private theorem shearReducedForceTerm_lintegral_sq_bound {C : ℝ}
    (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (n : ℕ) :
    ∫⁻ z, ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ) ∂volume ≤
      ENNReal.ofReal (576 * C ^ 2 * shearWeight n ^ 2) := by
  let r := shearScale n
  let A := 3 * C * shearWeight n * r⁻¹ ^ 2
  have hr : 0 < r := shearScale_pos n
  have hw : 0 ≤ shearWeight n := by
    unfold shearWeight
    positivity
  have hA : 0 ≤ A := by positivity
  have hS : MeasurableSet (shearProfileBox r) := by
    unfold shearProfileBox
    have hpi : MeasurableSet
        (Set.univ.pi fun _ : Fin 2 => Ioo (-(2 * r)) (2 * r)) :=
      (measurableSet_pi Set.countable_univ).2 (Or.inl (by
        intro i hi
        exact measurableSet_Ioo))
    exact hpi.prod measurableSet_Ioo
  have hdom : ∀ z,
      ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ) ≤
        (shearProfileBox r).indicator
          (fun _ : Vec 2 × ℝ => ENNReal.ofReal (A ^ 2)) z := by
    intro z
    by_cases hz : z ∈ shearProfileBox r
    · rw [Set.indicator_of_mem hz]
      rw [Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have habs := shearReducedForceTerm_abs_bound hC hUnit n z
      dsimp [A, r] at habs ⊢
      have hnonneg := abs_nonneg (shearReducedForceTerm n z)
      have hexp : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [hexp, Real.rpow_natCast]
      exact (sq_le_sq₀ hnonneg (by positivity)).2 habs
    · rw [Set.indicator_of_notMem hz, shearReducedForceTerm_zero_outside hz]
      simp
  calc
    _ ≤ ∫⁻ z, (shearProfileBox r).indicator
        (fun _ : Vec 2 × ℝ => ENNReal.ofReal (A ^ 2)) z ∂volume :=
      lintegral_mono hdom
    _ = ENNReal.ofReal (A ^ 2) * volume (shearProfileBox r) :=
      lintegral_indicator_const hS _
    _ = ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (64 * r ^ 4) := by
      rw [volume_shearProfileBox hr]
    _ = ENNReal.ofReal (A ^ 2 * (64 * r ^ 4)) := by
      rw [ENNReal.ofReal_mul (sq_nonneg A)]
    _ = ENNReal.ofReal (576 * C ^ 2 * shearWeight n ^ 2) := by
      congr 1
      dsimp [A, r]
      have hcancel : ((shearScale n)⁻¹ ^ 2) ^ 2 * shearScale n ^ 4 = 1 := by
        field_simp [ne_of_gt (shearScale_pos n)]
      calc
        (3 * C * shearWeight n * (shearScale n)⁻¹ ^ 2) ^ 2 *
            (64 * shearScale n ^ 4) =
          576 * C ^ 2 * shearWeight n ^ 2 *
            (((shearScale n)⁻¹ ^ 2) ^ 2 * shearScale n ^ 4) := by ring
        _ = 576 * C ^ 2 * shearWeight n ^ 2 := by rw [hcancel]; ring

private theorem shearReducedForceSeries_sq_eq_tsum (z : Vec 2 × ℝ) :
    ‖shearReducedForceSeries z‖ₑ ^ (2 : ℝ) =
      ∑' n, ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ) := by
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
    have hs : shearReducedForceSeries z = shearReducedForceTerm n z := by
      unfold shearReducedForceSeries
      exact tsum_eq_single n hzero
    have ht : (∑' m, ‖shearReducedForceTerm m z‖ₑ ^ (2 : ℝ)) =
        ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ) := by
      apply tsum_eq_single n
      intro m hm
      rw [hzero m hm]
      simp
    rw [hs, ht]
  · have hzero (n : ℕ) : shearReducedForceTerm n z = 0 := by
      by_contra hn
      exact hex ⟨n, hn⟩
    have hs : shearReducedForceSeries z = 0 := by
      unfold shearReducedForceSeries
      calc
        ∑' n, shearReducedForceTerm n z = ∑' n, (0 : ℝ) :=
          tsum_congr (fun n => hzero n)
        _ = 0 := by simp
    have ht : (∑' n, ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ)) = 0 := by
      calc
        ∑' n, ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ) = ∑' n, (0 : ENNReal) :=
          tsum_congr (fun n => by rw [hzero n]; simp)
        _ = 0 := by simp
    calc
      ‖shearReducedForceSeries z‖ₑ ^ (2 : ℝ) = 0 := by simp [hs]
      _ = ∑' n, ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ) := ht.symm

theorem shearReducedForceSeries_memLp :
    MemLp shearReducedForceSeries 2 volume := by
  obtain ⟨C, hC, hUnit⟩ := shearUnitBump_bound
  let htermmeas : ∀ n, AEMeasurable
      (fun z : Vec 2 × ℝ => ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ)) volume := by
    intro n
    have hcont := shearReducedForceTerm_continuous n
    have hmeas : AEMeasurable (shearReducedForceTerm n) volume := hcont.aemeasurable
    exact (hmeas.enorm).pow_const (2 : ℝ)
  have hseriesmeas : Measurable shearReducedForceSeries := by
    unfold shearReducedForceSeries
    exact Measurable.tsum (fun n => (shearReducedForceTerm_continuous n).measurable)
  have hstrong : AEStronglyMeasurable shearReducedForceSeries volume :=
    hseriesmeas.aestronglyMeasurable
  have hsum := lintegral_tsum htermmeas
  have hpoint := funext shearReducedForceSeries_sq_eq_tsum
  have hrewrite : (fun z : Vec 2 × ℝ => ‖shearReducedForceSeries z‖ₑ ^ (2 : ℝ)) =
      fun z => ∑' n, ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ) := hpoint
  have hbound : (∑' n, ∫⁻ z,
      ‖shearReducedForceTerm n z‖ₑ ^ (2 : ℝ) ∂volume) ≤
      ∑' n, ENNReal.ofReal (576 * C ^ 2 * shearWeight n ^ 2) :=
    ENNReal.tsum_le_tsum (fun n => shearReducedForceTerm_lintegral_sq_bound hC hUnit n)
  have hweights := shearWeight_sq_summable
  have hsumR : Summable (fun n : ℕ => 576 * C ^ 2 * shearWeight n ^ 2) :=
    hweights.mul_left (576 * C ^ 2)
  have htotal : (∑' n, ENNReal.ofReal (576 * C ^ 2 * shearWeight n ^ 2)) ≠ ⊤ := by
    exact hsumR.tsum_ofReal_ne_top
  have hfinite : (∫⁻ z,
      ‖shearReducedForceSeries z‖ₑ ^ (2 : ℝ) ∂volume) < ⊤ := by
    rw [hrewrite, hsum]
    exact lt_of_le_of_lt hbound htotal.lt_top
  rw [memLp_iff]
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hstrong]
  exact hfinite

end CKN
