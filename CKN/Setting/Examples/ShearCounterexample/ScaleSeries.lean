-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.ScaleDerivatives
import CKN.Setting.Examples.ShearCounterexample.LpTsum
import CKN.Setting.Examples.ShearCounterexample.WeightSummable
import CKN.Setting.Examples.ShearCounterexample.ShearWeightedProfile
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Lp summability of the scaled shear series. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

private theorem shearWeight_nonneg_local (n : ℕ) : 0 ≤ shearWeight n := by
  unfold shearWeight
  positivity

private theorem shearWeight_le_one_local (n : ℕ) : shearWeight n ≤ 1 := by
  have hn : 1 ≤ (n + 1 : ℝ) := by
    exact_mod_cast (Nat.le_add_left 1 n)
  have hp : 1 ≤ (n + 1 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow hn (by norm_num)
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
  simpa [shearWeight] using h

private theorem shearScale_le_one_local (n : ℕ) : shearScale n ≤ 1 := by
  have h := shearScale_antitone (m := 0) (n := n) (by omega)
  simpa [shearScale] using h

private theorem shearScale_sq_le_self_local (n : ℕ) :
    shearScale n ^ 2 ≤ shearScale n := by
  have h0 := (shearScale_pos n).le
  have h1 := shearScale_le_one_local n
  nlinarith only [h0, h1]

private theorem shearScale_summable_local : Summable shearScale := by
  change Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n)
  exact summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (by norm_num : (1 / 4 : ℝ) < 1)

private theorem shearWeightScaleSq_le {n : ℕ} {C : ℝ} (hC : 0 ≤ C) :
    shearWeight n * (8 * C * shearScale n ^ 2) ≤ 8 * C * shearScale n := by
  have hw := shearWeight_le_one_local n
  have hs := shearScale_sq_le_self_local n
  calc
    shearWeight n * (8 * C * shearScale n ^ 2) ≤
        1 * (8 * C * shearScale n ^ 2) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ 1 * (8 * C * shearScale n) := by gcongr
    _ = 8 * C * shearScale n := by ring

private theorem shearWeightScale_le {n : ℕ} {C r : ℝ} (hC : 0 ≤ C)
    (hr : 0 ≤ r) : shearWeight n * (8 * C * r) ≤ 8 * C * r := by
  have hw := shearWeight_le_one_local n
  have hcoef : 0 ≤ 8 * C * r := mul_nonneg (mul_nonneg (by norm_num) hC) hr
  calc
    shearWeight n * (8 * C * r) ≤ 1 * (8 * C * r) :=
      mul_le_mul_of_nonneg_right hw hcoef
    _ = 8 * C * r := by ring

def shearReducedBumpTerm (n : ℕ) (z : Vec 2 × ℝ) : ℝ :=
  shearWeight n • shearBumpField (shearScale n) z

def shearReducedBumpSeries (z : Vec 2 × ℝ) : ℝ :=
  ∑' n, shearReducedBumpTerm n z

def shearReducedGradientTerm (i : Fin 2) (n : ℕ) (z : Vec 2 × ℝ) : ℝ :=
  shearWeight n • shearSpatialFirstField (shearScale n) i z

def shearReducedGradientSeries (i : Fin 2) (z : Vec 2 × ℝ) : ℝ :=
  ∑' n, shearReducedGradientTerm i n z

private theorem shearReducedBumpTerm_eLpNorm_bound {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (n : ℕ) :
    eLpNorm (shearReducedBumpTerm n) 2 volume ≤
      ENNReal.ofReal (8 * C * shearScale n) := by
  have hr := shearScale_pos n
  have hr1 := shearScale_le_one_local n
  have hB := shearBumpField_eLpNorm_of_unit_bound hr hr1 hC hUnit
  change eLpNorm (shearWeight n • shearBumpField (shearScale n)) 2 volume ≤ _
  rw [eLpNorm_const_smul, Real.enorm_of_nonneg (shearWeight_nonneg_local n)]
  calc
    ENNReal.ofReal (shearWeight n) * eLpNorm (shearBumpField (shearScale n)) 2 volume ≤
        ENNReal.ofReal (shearWeight n) *
          ENNReal.ofReal (8 * C * shearScale n ^ 2) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    _ = ENNReal.ofReal (shearWeight n * (8 * C * shearScale n ^ 2)) :=
      (ENNReal.ofReal_mul (shearWeight_nonneg_local n)).symm
    _ ≤ ENNReal.ofReal (8 * C * shearScale n) :=
      ENNReal.ofReal_le_ofReal (shearWeightScaleSq_le hC)

private theorem shearReducedGradientTerm_eLpNorm_bound {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (i : Fin 2) (n : ℕ) :
    eLpNorm (shearReducedGradientTerm i n) 2 volume ≤
      ENNReal.ofReal (8 * C * shearScale n) := by
  have hr := shearScale_pos n
  have hG := shearSpatialFirstField_eLpNorm hr hC hUnit i
  change eLpNorm (shearWeight n • shearSpatialFirstField (shearScale n) i) 2 volume ≤ _
  rw [eLpNorm_const_smul, Real.enorm_of_nonneg (shearWeight_nonneg_local n)]
  calc
    ENNReal.ofReal (shearWeight n) * eLpNorm
        (shearSpatialFirstField (shearScale n) i) 2 volume ≤
        ENNReal.ofReal (shearWeight n) *
          ENNReal.ofReal (8 * C * shearScale n) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ = ENNReal.ofReal (shearWeight n * (8 * C * shearScale n)) :=
      (ENNReal.ofReal_mul (shearWeight_nonneg_local n)).symm
    _ ≤ ENNReal.ofReal (8 * C * shearScale n) :=
      ENNReal.ofReal_le_ofReal (shearWeightScale_le hC (shearScale_pos n).le)

private theorem shearScaleConstant_summable {C : ℝ} (_ : 0 ≤ C) :
    Summable (fun n : ℕ => 8 * C * shearScale n) := by
  exact (shearScale_summable_local).mul_left (8 * C)

private theorem shearReducedBumpTerm_memLp {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (n : ℕ) :
    MemLp (shearReducedBumpTerm n) 2 volume := by
  rw [memLp_iff]
  exact lt_of_le_of_lt (shearReducedBumpTerm_eLpNorm_bound hC hUnit n)
    ENNReal.ofReal_lt_top

private theorem shearReducedGradientTerm_memLp {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (i : Fin 2) (n : ℕ) :
    MemLp (shearReducedGradientTerm i n) 2 volume := by
  rw [memLp_iff]
  exact lt_of_le_of_lt (shearReducedGradientTerm_eLpNorm_bound hC hUnit i n)
    ENNReal.ofReal_lt_top

theorem shearReducedBumpSeries_memLp :
    MemLp shearReducedBumpSeries 2 volume := by
  obtain ⟨C, hC, hUnit⟩ := shearUnitBump_bound
  let : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  exact memLp_tsum_of_summable_eLpNorm_bound
    shearReducedBumpTerm (fun n => 8 * C * shearScale n)
    (shearReducedBumpTerm_memLp hC hUnit)
    (shearReducedBumpTerm_eLpNorm_bound hC hUnit)
    (shearScaleConstant_summable hC)

theorem shearReducedGradientSeries_memLp (i : Fin 2) :
    MemLp (shearReducedGradientSeries i) 2 volume := by
  obtain ⟨C, hC, hUnit⟩ := shearUnitBump_bound
  let : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  exact memLp_tsum_of_summable_eLpNorm_bound
    (shearReducedGradientTerm i) (fun n => 8 * C * shearScale n)
    (shearReducedGradientTerm_memLp hC hUnit i)
    (shearReducedGradientTerm_eLpNorm_bound hC hUnit i)
    (shearScaleConstant_summable hC)

end CKN
