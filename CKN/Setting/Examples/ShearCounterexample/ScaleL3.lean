-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.ScaleSeries
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! # L3 estimates for the scaled shear profile. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

private theorem shearScale_le_one_L3 (n : ℕ) : shearScale n ≤ 1 := by
  have h := shearScale_antitone (m := 0) (n := n) (by omega)
  simpa [shearScale] using h

private theorem shearScale_summable_L3 : Summable shearScale := by
  change Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n)
  exact summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (by norm_num : (1 / 4 : ℝ) < 1)

private theorem shearReducedBumpTerm_abs_bound_L3 {C : ℝ} (_ : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (n : ℕ) (z : Vec 2 × ℝ) :
    |shearReducedBumpTerm n z| ≤ shearWeight n * C := by
  have hw : 0 ≤ shearWeight n := by unfold shearWeight; positivity
  have hr := shearScale_pos n
  have hu := shearScaleBump_iteratedFDeriv_bound hr (shearScale_le_one_L3 n)
    hUnit 0 (by norm_num) z
  have hb : |shearBumpField (shearScale n) z| ≤ C := by
    simpa [shearBumpField, norm_iteratedFDeriv_zero] using hu
  rw [shearReducedBumpTerm, smul_eq_mul, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left hb hw

private theorem shearReducedBumpTerm_zero_outside_L3 {n : ℕ} {z : Vec 2 × ℝ}
    (hz : z ∉ shearProfileBox (shearScale n)) :
    shearReducedBumpTerm n z = 0 := by
  have hzero := shearScaleDerivative_zero_outside (shearScale_pos n) 0
    (by norm_num) (fun i : Fin 0 => i.elim0) hz
  have hb : shearBumpField (shearScale n) z = 0 := by
    simpa [shearBumpField, norm_iteratedFDeriv_zero] using hzero
  simp [shearReducedBumpTerm, hb]

private theorem shear_box_volume_root_bound {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) : (64 * r ^ 4) ^ (1 / 3 : ℝ) ≤ 64 * r := by
  have hmul : (64 * r ^ 4) ^ (1 / 3 : ℝ) =
      (64 : ℝ) ^ (1 / 3 : ℝ) * (r ^ 4) ^ (1 / 3 : ℝ) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have hscale : (r ^ 4) ^ (1 / 3 : ℝ) = r ^ (4 / 3 : ℝ) := by
    calc
      (r ^ 4) ^ (1 / 3 : ℝ) = (r ^ (4 : ℝ)) ^ (1 / 3 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ))
          (Real.rpow_natCast r 4).symm
      _ = r ^ ((4 : ℝ) * (1 / 3 : ℝ)) :=
        (Real.rpow_mul hr.le _ _).symm
      _ = r ^ (4 / 3 : ℝ) := by congr 1; norm_num
  have hconst : (64 : ℝ) ^ (1 / 3 : ℝ) ≤ 64 := by
    calc
      (64 : ℝ) ^ (1 / 3 : ℝ) ≤ (64 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 64 := by simp
  have hpower : r ^ (4 / 3 : ℝ) ≤ r := by
    calc
      r ^ (4 / 3 : ℝ) ≤ r ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
      _ = r := by simp
  rw [hmul, hscale]
  calc
    (64 : ℝ) ^ (1 / 3 : ℝ) * r ^ (4 / 3 : ℝ) ≤ 64 * r ^ (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hr.le _)
    _ ≤ 64 * r := mul_le_mul_of_nonneg_left hpower (by norm_num)

private theorem shearReducedBumpTerm_eLpNorm_three_bound {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (n : ℕ) :
    eLpNorm (shearReducedBumpTerm n) 3 volume ≤
      ENNReal.ofReal (64 * C * shearWeight n * shearScale n) := by
  let r := shearScale n
  let B := shearWeight n * C
  have hr := shearScale_pos n
  have hr1 := shearScale_le_one_L3 n
  have hB : 0 ≤ B := by dsimp [B, shearWeight]; positivity
  have hS : MeasurableSet (shearProfileBox r) := by
    unfold shearProfileBox
    have hpi : MeasurableSet
        (Set.univ.pi fun _ : Fin 2 => Ioo (-(2 * r)) (2 * r)) :=
      (measurableSet_pi Set.countable_univ).2 (Or.inl (by
        intro i hi
        exact measurableSet_Ioo))
    exact hpi.prod measurableSet_Ioo
  have hcont : Continuous (shearReducedBumpTerm n) := by
    unfold shearReducedBumpTerm
    change Continuous (fun z => shearWeight n * shearBumpField r z)
    exact continuous_const.mul (shearBumpField_continuous hr)
  have hdom : ∀ z,
      ‖shearReducedBumpTerm n z‖ ≤
        ‖(shearProfileBox r).indicator (fun _ : Vec 2 × ℝ => B) z‖ := by
    intro z
    by_cases hz : z ∈ shearProfileBox r
    · rw [Set.indicator_of_mem hz]
      simpa [Real.norm_eq_abs, abs_of_nonneg hB] using
        (shearReducedBumpTerm_abs_bound_L3 hC hUnit n z)
    · rw [Set.indicator_of_notMem hz, shearReducedBumpTerm_zero_outside_L3 hz]
  have hmono : eLpNorm (shearReducedBumpTerm n) 3 volume ≤
      eLpNorm ((shearProfileBox r).indicator (fun _ : Vec 2 × ℝ => B)) 3 volume :=
    eLpNorm_mono hcont.aestronglyMeasurable hdom
  calc
    eLpNorm (shearReducedBumpTerm n) 3 volume ≤
        eLpNorm ((shearProfileBox r).indicator (fun _ : Vec 2 × ℝ => B)) 3 volume := hmono
    _ = ENNReal.ofReal B * (volume (shearProfileBox r)) ^
          (1 / ((3 : ENNReal).toReal)) := by
      simpa only [Real.enorm_of_nonneg hB] using
        (eLpNorm_indicator_const (μ := volume) (p := (3 : ENNReal))
          (c := B) (s := shearProfileBox r) hS.nullMeasurableSet
          (by norm_num) (by norm_num))
    _ = ENNReal.ofReal B * (ENNReal.ofReal (64 * r ^ 4)) ^ (1 / 3 : ℝ) := by
      rw [volume_shearProfileBox hr, show (3 : ENNReal).toReal = 3 by norm_num]
    _ = ENNReal.ofReal (B * (64 * r ^ 4) ^ (1 / 3 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_pos (by positivity : 0 < 64 * r ^ 4),
        ← ENNReal.ofReal_mul hB]
    _ ≤ ENNReal.ofReal (64 * C * shearWeight n * r) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp [B, r]
      calc
        shearWeight n * C * (64 * (shearScale n) ^ 4) ^ (1 / 3 : ℝ) ≤
            shearWeight n * C * (64 * shearScale n) := by
          gcongr
          exact shear_box_volume_root_bound hr hr1
        _ = 64 * C * shearWeight n * shearScale n := by ring

private theorem shearReducedBumpTerm_memLp_three {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (n : ℕ) :
    MemLp (shearReducedBumpTerm n) 3 volume := by
  rw [memLp_iff]
  exact lt_of_le_of_lt (shearReducedBumpTerm_eLpNorm_three_bound hC hUnit n)
    ENNReal.ofReal_lt_top

private theorem shearReducedBumpTerm_eLpNorm_three_bound_simple {C : ℝ}
    (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (n : ℕ) :
    eLpNorm (shearReducedBumpTerm n) 3 volume ≤
      ENNReal.ofReal (64 * C * shearScale n) := by
  have hw : shearWeight n ≤ 1 := by
    have hn : 1 ≤ (n + 1 : ℝ) := by exact_mod_cast (Nat.le_add_left 1 n)
    have hp : 1 ≤ (n + 1 : ℝ) ^ (3 / 4 : ℝ) :=
      Real.one_le_rpow hn (by norm_num)
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
    simpa [shearWeight] using h
  calc
    eLpNorm (shearReducedBumpTerm n) 3 volume ≤
        ENNReal.ofReal (64 * C * shearWeight n * shearScale n) :=
      shearReducedBumpTerm_eLpNorm_three_bound hC hUnit n
    _ ≤ ENNReal.ofReal (64 * C * shearScale n) := by
      apply ENNReal.ofReal_le_ofReal
      have hcoef : 0 ≤ 64 * C * shearScale n :=
        mul_nonneg (mul_nonneg (by norm_num) hC) (shearScale_pos n).le
      have hweightscale : shearWeight n * shearScale n ≤ shearScale n := by
        calc
          shearWeight n * shearScale n ≤ 1 * shearScale n :=
            mul_le_mul_of_nonneg_right hw (shearScale_pos n).le
          _ = shearScale n := by ring
      calc
        64 * C * shearWeight n * shearScale n =
            (64 * C) * (shearWeight n * shearScale n) := by ring
        _ ≤ (64 * C) * shearScale n :=
          mul_le_mul_of_nonneg_left hweightscale (by positivity)
        _ = 64 * C * shearScale n := by ring

private theorem shearL3_majorant_summable {C : ℝ} (_ : 0 ≤ C) :
    Summable (fun n : ℕ => 64 * C * shearScale n) := by
  exact shearScale_summable_L3.mul_left (64 * C)

theorem shearReducedBumpSeries_memLp_three :
    MemLp shearReducedBumpSeries 3 volume := by
  obtain ⟨C, hC, hUnit⟩ := shearUnitBump_bound
  let : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩
  exact memLp_tsum_of_summable_eLpNorm_bound
    shearReducedBumpTerm (fun n => 64 * C * shearScale n)
    (shearReducedBumpTerm_memLp_three hC hUnit)
    (shearReducedBumpTerm_eLpNorm_three_bound_simple hC hUnit)
    (shearL3_majorant_summable hC)

end CKN
