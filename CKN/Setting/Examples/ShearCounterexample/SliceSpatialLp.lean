-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.SliceAE
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.PSeries

/-! # Spatial slice Lp estimates for the shear profile. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

def shearSpatialSliceBox (r : ℝ) : Set (Vec 2) :=
  Set.univ.pi fun _ : Fin 2 => Ioo (-(2 * r)) (2 * r)

private theorem shearScale_le_one_spatial (n : ℕ) : shearScale n ≤ 1 := by
  have h := shearScale_antitone (m := 0) (n := n) (by omega)
  simpa [shearScale] using h

private theorem shearWeight_nonneg_spatial (n : ℕ) : 0 ≤ shearWeight n := by
  unfold shearWeight
  positivity

theorem shearWeight_le_one_spatial (n : ℕ) : shearWeight n ≤ 1 := by
  have hn : 1 ≤ (n + 1 : ℝ) := by exact_mod_cast (Nat.le_add_left 1 n)
  have hp : 1 ≤ (n + 1 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow hn (by norm_num)
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
  simpa [shearWeight] using h


private theorem shearSpatialSliceBox_measurable (r : ℝ) :
    MeasurableSet (shearSpatialSliceBox r) := by
  unfold shearSpatialSliceBox
  exact (measurableSet_pi Set.countable_univ).2 (Or.inl (by
    intro i hi
    exact measurableSet_Ioo))

theorem volume_shearSpatialSliceBox {r : ℝ} (hr : 0 < r) :
    volume (shearSpatialSliceBox r) = ENNReal.ofReal (16 * r ^ 2) := by
  unfold shearSpatialSliceBox
  rw [volume_pi_pi]
  simp only [Real.volume_Ioo]
  simp_rw [show 2 * r - -(2 * r) = 4 * r by ring]
  rw [Fin.prod_univ_two]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * r)]
  congr 1
  ring

theorem shearReducedBumpTerm_slice_eLpNorm_bound {n : ℕ} :
    ∀ t : ℝ,
      eLpNorm (fun x : Vec 2 => shearReducedBumpTerm n (x, t)) 2 volume ≤
        ENNReal.ofReal (4 * shearUnitBump_bound.choose * shearWeight n * shearScale n) := by
  intro t
  let C := Classical.choose shearUnitBump_bound
  have hspec := Classical.choose_spec shearUnitBump_bound
  obtain ⟨hC, hunit⟩ := hspec
  let r := shearScale n
  let A := C * shearWeight n
  have hr : 0 < r := shearScale_pos n
  have hr1 : r ≤ 1 := shearScale_le_one_spatial n
  have hA : 0 ≤ A := mul_nonneg hC (shearWeight_nonneg_spatial n)
  have hcont : Continuous (fun x : Vec 2 => shearReducedBumpTerm n (x, t)) := by
    exact (shearReducedSliceTerm_contDiff n t).continuous
  have hbound : ∀ x, |shearReducedBumpTerm n (x, t)| ≤ A := by
    intro x
    have hb := shearScaleBump_iteratedFDeriv_bound hr hr1 hunit 0 (by norm_num) (x, t)
    have hb' : |shearBumpField r (x, t)| ≤ C := by
      simpa [shearBumpField, C, norm_iteratedFDeriv_zero] using hb
    rw [shearReducedBumpTerm, smul_eq_mul, abs_mul, abs_of_nonneg (shearWeight_nonneg_spatial n)]
    calc
      shearWeight n * |shearBumpField r (x, t)| ≤ shearWeight n * C :=
        mul_le_mul_of_nonneg_left hb' (shearWeight_nonneg_spatial n)
      _ = A := by ring
  have hzero : ∀ x ∉ shearSpatialSliceBox r,
      shearReducedBumpTerm n (x, t) = 0 := by
    intro x hx
    have hz : (x, t) ∉ shearProfileBox r := by
      intro h
      exact hx h.1
    have hD := shearScaleDerivative_zero_outside hr 0 (by norm_num)
      (fun j : Fin 0 => j.elim0) hz
    have hb : shearBumpField r (x, t) = 0 := by
      simpa [shearBumpField, iteratedFDeriv_zero_apply] using hD
    simp [shearReducedBumpTerm, r, hb]
  have hdom : ∀ x : Vec 2,
      ‖shearReducedBumpTerm n (x, t)‖ ≤
        ‖(shearSpatialSliceBox r).indicator (fun _ : Vec 2 => A) x‖ := by
    intro x
    by_cases hx : x ∈ shearSpatialSliceBox r
    · rw [Set.indicator_of_mem hx]
      simpa [Real.norm_eq_abs, abs_of_nonneg hA] using hbound x
    · rw [Set.indicator_of_notMem hx, hzero x hx]
  calc
    eLpNorm (fun x : Vec 2 => shearReducedBumpTerm n (x, t)) 2 volume ≤
        eLpNorm ((shearSpatialSliceBox r).indicator (fun _ : Vec 2 => A)) 2 volume := by
          exact eLpNorm_mono hcont.aestronglyMeasurable hdom
    _ = ENNReal.ofReal A * volume (shearSpatialSliceBox r) ^ (1 / 2 : ℝ) := by
      simpa [Real.enorm_of_nonneg hA] using
        (eLpNorm_indicator_const (μ := volume) (p := (2 : ENNReal))
          (c := A) (s := shearSpatialSliceBox r)
          (shearSpatialSliceBox_measurable r).nullMeasurableSet (by norm_num) (by norm_num))
    _ = ENNReal.ofReal (A * (16 * r ^ 2) ^ (1 / 2 : ℝ)) := by
      rw [volume_shearSpatialSliceBox hr,
        ENNReal.ofReal_rpow_of_pos (by positivity : 0 < 16 * r ^ 2),
        ← ENNReal.ofReal_mul hA]
    _ ≤ ENNReal.ofReal (4 * C * shearWeight n * r) := by
      apply ENNReal.ofReal_le_ofReal
      have hsqrt : (16 * r ^ 2) ^ (1 / 2 : ℝ) = 4 * r := by
        have hsqrt16 : Real.sqrt 16 = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        have hsqrr : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
        calc
          (16 * r ^ 2) ^ (1 / 2 : ℝ) = Real.sqrt (16 * r ^ 2) := by
            rw [Real.sqrt_eq_rpow]
          _ = Real.sqrt 16 * Real.sqrt (r ^ 2) :=
            Real.sqrt_mul (by norm_num : 0 ≤ (16 : ℝ)) (r ^ 2)
          _ = 4 * r := by rw [hsqrt16, hsqrr]
      rw [hsqrt]
      dsimp [A]
      calc
        C * shearWeight n * (4 * r) = 4 * C * shearWeight n * r := by ring
        _ ≤ 4 * C * shearWeight n * r := le_rfl

theorem shearSliceFiniteTermSum_eLpNorm_bound {N : ℕ} (t : ℝ) :
    eLpNorm (fun x : Vec 2 =>
      ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, t)) 2 volume ≤
      ∑ n ∈ Finset.range N,
        ENNReal.ofReal (4 * shearUnitBump_bound.choose * shearWeight n * shearScale n) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        eLpNorm (fun x : Vec 2 => shearReducedBumpTerm n (x, t)) 2 volume := by
          convert (eLpNorm_sum_le (p := (2 : ENNReal))
            (f := fun n x => shearReducedBumpTerm n (x, t))
            (s := Finset.range N) (by norm_num : 1 ≤ (2 : ENNReal))) using 1
          · congr 1
            ext x
            simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      exact shearReducedBumpTerm_slice_eLpNorm_bound (n := n) t

end CKN
