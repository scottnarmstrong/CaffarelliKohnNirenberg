-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.ScaleBounds
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Derivative estimates for the scaled shear profile. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN
private def shearSpatialTangent (i : Fin 2) : Vec 2 × ℝ := (Pi.single i (1 : ℝ), 0)
private def shearTimeTangent : Vec 2 × ℝ := (0, 1)

private theorem shearScaleBump_as_comp {r : ℝ} (hr : 0 < r) :
    shearScaleBump r = shearUnitBump ∘ shearParabolicDilation r := by
  funext z
  exact shearScaleBump_scale (ne_of_gt hr) z

private theorem shearParabolicDilation_spatialTangent {r : ℝ}
    (i : Fin 2) :
    shearParabolicDilation r (shearSpatialTangent i) =
      r⁻¹ • shearSpatialTangent i := by
  rw [shearParabolicDilation_apply]
  apply Prod.ext
  · funext j
    simp [shearSpatialTangent, div_eq_mul_inv, smul_eq_mul]
    ring
  · simp [shearSpatialTangent]

private theorem shearParabolicDilation_timeTangent {r : ℝ} :
    shearParabolicDilation r shearTimeTangent =
      (r⁻¹ ^ 2) • shearTimeTangent := by
  rw [shearParabolicDilation_apply]
  apply Prod.ext
  · ext j
    simp [shearTimeTangent]
  · simp [shearTimeTangent, div_eq_mul_inv, inv_pow, smul_eq_mul]

private theorem shearSpatialTangent_norm (i : Fin 2) :
    ‖shearSpatialTangent i‖ = 1 := by
  simp [shearSpatialTangent, Pi.norm_single]

private theorem shearTimeTangent_norm : ‖shearTimeTangent‖ = 1 := by
  simp [shearTimeTangent]

theorem shearScaleBump_spatialFirst_bound {r C : ℝ} (hr : 0 < r)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C)
    (i : Fin 2) (z : Vec 2 × ℝ) :
    ‖iteratedFDeriv ℝ 1 (shearScaleBump r) z
      (fun _ : Fin 1 => shearSpatialTangent i)‖ ≤ C * r⁻¹ := by
  rw [shearScaleBump_as_comp hr,
    ContinuousLinearMap.iteratedFDeriv_comp_right (shearParabolicDilation r)
      shearUnitBump_smooth (z) (by norm_num)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    shearParabolicDilation_spatialTangent]
  rw [ContinuousMultilinearMap.map_smul_univ]
  have hprod : ∏ _j : Fin 1, (r⁻¹ : ℝ) = r⁻¹ := by simp
  rw [hprod, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have heval : ‖iteratedFDeriv ℝ 1 shearUnitBump
      (shearParabolicDilation r z) (fun _ : Fin 1 => shearSpatialTangent i)‖ ≤ C := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ 1 shearUnitBump (shearParabolicDilation r z)‖ *
          ∏ _j : Fin 1, ‖shearSpatialTangent i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ C * 1 := by
        have hnorm : ∏ _j : Fin 1, ‖shearSpatialTangent i‖ = 1 := by
          simp [shearSpatialTangent_norm]
        rw [hnorm]
        have hu := hUnit 1 (by norm_num) (shearParabolicDilation r z)
        simpa only [norm_iteratedFDeriv_one, mul_one] using hu
      _ = C := by ring
  calc
    r⁻¹ * ‖iteratedFDeriv ℝ 1 shearUnitBump
        (shearParabolicDilation r z) (fun _ : Fin 1 => shearSpatialTangent i)‖ ≤
      r⁻¹ * C := mul_le_mul_of_nonneg_left heval (by positivity)
    _ = C * r⁻¹ := by ring

theorem shearScaleBump_spatialSecond_bound {r C : ℝ} (hr : 0 < r)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C)
    (i : Fin 2) (z : Vec 2 × ℝ) :
    ‖iteratedFDeriv ℝ 2 (shearScaleBump r) z
      (fun _ : Fin 2 => shearSpatialTangent i)‖ ≤ C * r⁻¹ ^ 2 := by
  rw [shearScaleBump_as_comp hr,
    ContinuousLinearMap.iteratedFDeriv_comp_right (shearParabolicDilation r)
      shearUnitBump_smooth (z) (by norm_num)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    shearParabolicDilation_spatialTangent]
  rw [ContinuousMultilinearMap.map_smul_univ]
  have hprod : ∏ _j : Fin 2, (r⁻¹ : ℝ) = r⁻¹ ^ 2 := by
    rw [Fin.prod_univ_two]
    ring
  rw [hprod, norm_smul, Real.norm_eq_abs,
    abs_of_pos (sq_pos_of_pos (inv_pos.mpr hr))]
  have heval : ‖iteratedFDeriv ℝ 2 shearUnitBump
      (shearParabolicDilation r z) (fun _ : Fin 2 => shearSpatialTangent i)‖ ≤ C := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ 2 shearUnitBump (shearParabolicDilation r z)‖ *
          ∏ _j : Fin 2, ‖shearSpatialTangent i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ C * 1 := by
        have hnorm : ∏ _j : Fin 2, ‖shearSpatialTangent i‖ = 1 := by
          simp [shearSpatialTangent_norm]
        rw [hnorm]
        simpa only [mul_one] using hUnit 2 (by norm_num) (shearParabolicDilation r z)
      _ = C := by ring
  calc
    r⁻¹ ^ 2 * ‖iteratedFDeriv ℝ 2 shearUnitBump
        (shearParabolicDilation r z) (fun _ : Fin 2 => shearSpatialTangent i)‖ ≤
      r⁻¹ ^ 2 * C := mul_le_mul_of_nonneg_left heval (by positivity)
    _ = C * r⁻¹ ^ 2 := by ring

theorem shearScaleBump_timeFirst_bound {r C : ℝ} (hr : 0 < r)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C)
    (z : Vec 2 × ℝ) :
    ‖iteratedFDeriv ℝ 1 (shearScaleBump r) z
      (fun _ : Fin 1 => shearTimeTangent)‖ ≤ C * r⁻¹ ^ 2 := by
  rw [shearScaleBump_as_comp hr,
    ContinuousLinearMap.iteratedFDeriv_comp_right (shearParabolicDilation r)
      shearUnitBump_smooth (z) (by norm_num)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    shearParabolicDilation_timeTangent]
  rw [ContinuousMultilinearMap.map_smul_univ]
  have hprod : ∏ _j : Fin 1, (r⁻¹ ^ 2 : ℝ) = r⁻¹ ^ 2 := by simp
  rw [hprod, norm_smul, Real.norm_eq_abs,
    abs_of_pos (sq_pos_of_pos (inv_pos.mpr hr))]
  have heval : ‖iteratedFDeriv ℝ 1 shearUnitBump
      (shearParabolicDilation r z) (fun _ : Fin 1 => shearTimeTangent)‖ ≤ C := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ 1 shearUnitBump (shearParabolicDilation r z)‖ *
          ∏ _j : Fin 1, ‖shearTimeTangent‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ C * 1 := by
        have hnorm : ∏ _j : Fin 1, ‖shearTimeTangent‖ = 1 := by
          simp [shearTimeTangent_norm]
        rw [hnorm]
        have hu := hUnit 1 (by norm_num) (shearParabolicDilation r z)
        simpa only [norm_iteratedFDeriv_one, mul_one] using hu
      _ = C := by ring
  calc
    r⁻¹ ^ 2 * ‖iteratedFDeriv ℝ 1 shearUnitBump
        (shearParabolicDilation r z) (fun _ : Fin 1 => shearTimeTangent)‖ ≤
      r⁻¹ ^ 2 * C := mul_le_mul_of_nonneg_left heval (by positivity)
    _ = C * r⁻¹ ^ 2 := by ring

end CKN

namespace CKN

theorem shearScaleBump_smooth_of_pos {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (shearScaleBump r) := by
  rw [shearScaleBump_as_comp hr]
  exact shearUnitBump_smooth.comp (shearParabolicDilation_smooth r)

def shearSpatialFirstField (r : ℝ) (i : Fin 2) (z : Vec 2 × ℝ) : ℝ :=
  iteratedFDeriv ℝ 1 (shearScaleBump r) z
    (fun _ : Fin 1 => shearSpatialTangent i)

def shearSpatialSecondField (r : ℝ) (i : Fin 2) (z : Vec 2 × ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 (shearScaleBump r) z
    (fun _ : Fin 2 => shearSpatialTangent i)

def shearTimeFirstField (r : ℝ) (z : Vec 2 × ℝ) : ℝ :=
  iteratedFDeriv ℝ 1 (shearScaleBump r) z
    (fun _ : Fin 1 => shearTimeTangent)

theorem shearSpatialFirstField_continuous {r : ℝ} (hr : 0 < r)
    (i : Fin 2) : Continuous (shearSpatialFirstField r i) := by
  unfold shearSpatialFirstField
  exact (ContDiff.continuous_iteratedFDeriv (by norm_num)
    (shearScaleBump_smooth_of_pos hr)).eval_const _

theorem shearSpatialSecondField_continuous {r : ℝ} (hr : 0 < r)
    (i : Fin 2) : Continuous (shearSpatialSecondField r i) := by
  unfold shearSpatialSecondField
  exact (ContDiff.continuous_iteratedFDeriv (by norm_num)
    (shearScaleBump_smooth_of_pos hr)).eval_const _

theorem shearTimeFirstField_continuous {r : ℝ} (hr : 0 < r) :
    Continuous (shearTimeFirstField r) := by
  unfold shearTimeFirstField
  exact (ContDiff.continuous_iteratedFDeriv (by norm_num)
    (shearScaleBump_smooth_of_pos hr)).eval_const _

theorem shearScaleDerivative_zero_outside {r : ℝ} (hr : 0 < r)
    (k : ℕ) (_ : k ≤ 2) (m : Fin k → Vec 2 × ℝ) {z : Vec 2 × ℝ}
    (hz : z ∉ shearProfileBox r) :
    (iteratedFDeriv ℝ k (shearScaleBump r) z) m = 0 := by
  have hnot : z ∉ tsupport (shearScaleBump r) := by
    intro hz'
    exact hz (shearScaleBump_support_box hr hz')
  have hzero : iteratedFDeriv ℝ k (shearScaleBump r) z = 0 := by
    by_contra hne
    have hs : z ∈ Function.support (iteratedFDeriv ℝ k (shearScaleBump r)) :=
      Function.mem_support.mpr hne
    have hit : z ∈ tsupport (iteratedFDeriv ℝ k (shearScaleBump r)) :=
      (subset_tsupport (iteratedFDeriv ℝ k (shearScaleBump r))) hs
    exact hnot ((tsupport_iteratedFDeriv_subset k) hit)
  rw [hzero]
  simp

private theorem shearProfileBox_measurable (r : ℝ) :
    MeasurableSet (shearProfileBox r) := by
  unfold shearProfileBox
  have hpi : MeasurableSet
      (Set.univ.pi fun _ : Fin 2 => Ioo (-(2 * r)) (2 * r)) :=
    (measurableSet_pi Set.countable_univ).2 (Or.inl (by
      intro i hi
      exact measurableSet_Ioo))
  exact hpi.prod measurableSet_Ioo

private theorem shear_eLpNorm_of_box_support_bound {r A : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (g : Vec 2 × ℝ → ℝ) (hg : Continuous g)
    (hz : ∀ z ∉ shearProfileBox r, g z = 0)
    (hb : ∀ z ∈ shearProfileBox r, ‖g z‖ ≤ A) :
    eLpNorm g 2 volume ≤ ENNReal.ofReal A *
      (ENNReal.ofReal (64 * r ^ 4)) ^ (1 / 2 : ℝ) := by
  let S := shearProfileBox r
  have hS : MeasurableSet S := shearProfileBox_measurable r
  have hcomp : ∀ z, ‖g z‖ ≤ ‖S.indicator (fun _ : Vec 2 × ℝ => A) z‖ := by
    intro z
    by_cases hzin : z ∈ S
    · rw [Set.indicator_of_mem hzin]
      exact (hb z hzin).trans (by simp [abs_of_nonneg hA])
    · rw [Set.indicator_of_notMem hzin, hz z hzin]
  calc
    eLpNorm g 2 volume ≤ eLpNorm (S.indicator fun _ : Vec 2 × ℝ => A) 2 volume :=
      eLpNorm_mono hg.aestronglyMeasurable hcomp
    _ = ‖A‖ₑ * volume S ^ (1 / ((2 : ENNReal).toReal)) := by
      exact eLpNorm_indicator_const hS.nullMeasurableSet (by norm_num) (by simp)
    _ = ENNReal.ofReal A * (ENNReal.ofReal (64 * r ^ 4)) ^ (1 / 2 : ℝ) := by
      rw [volume_shearProfileBox hr]
      rw [show (2 : ENNReal).toReal = 2 by norm_num]
      rw [Real.enorm_of_nonneg hA]

end CKN

namespace CKN

private theorem shearProfileBox_volume_sqrt {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal (64 * r ^ 4)) ^ (1 / 2 : ℝ) = ENNReal.ofReal (8 * r ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_pos (by positivity : 0 < 64 * r ^ 4)]
  congr 1
  rw [← Real.sqrt_eq_rpow, show 64 * r ^ 4 = (8 * r ^ 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity : 0 ≤ 8 * r ^ 2)]

theorem shear_eLpNorm_box_bound_simplified {r A : ℝ} (hr : 0 < r)
    (hA : 0 ≤ A) (g : Vec 2 × ℝ → ℝ) (hg : Continuous g)
    (hz : ∀ z ∉ shearProfileBox r, g z = 0)
    (hb : ∀ z ∈ shearProfileBox r, ‖g z‖ ≤ A) :
    eLpNorm g 2 volume ≤ ENNReal.ofReal (A * (8 * r ^ 2)) := by
  calc
    eLpNorm g 2 volume ≤ ENNReal.ofReal A *
        (ENNReal.ofReal (64 * r ^ 4)) ^ (1 / 2 : ℝ) :=
      shear_eLpNorm_of_box_support_bound hr hA g hg hz hb
    _ = ENNReal.ofReal (A * (8 * r ^ 2)) := by
      rw [shearProfileBox_volume_sqrt hr, ← ENNReal.ofReal_mul hA]

theorem shearSpatialFirstField_eLpNorm {r C : ℝ} (hr : 0 < r)
    (hC : 0 ≤ C) (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (i : Fin 2) :
    eLpNorm (shearSpatialFirstField r i) 2 volume ≤ ENNReal.ofReal (8 * C * r) := by
  have hA : 0 ≤ C * r⁻¹ := by positivity
  have hbound : ∀ z ∈ shearProfileBox r, ‖shearSpatialFirstField r i z‖ ≤ C * r⁻¹ := by
    intro z hz
    exact shearScaleBump_spatialFirst_bound hr hUnit i z
  have hzero : ∀ z ∉ shearProfileBox r, shearSpatialFirstField r i z = 0 := by
    intro z hz
    exact shearScaleDerivative_zero_outside hr 1 (by norm_num) _ hz
  have hbase := shear_eLpNorm_box_bound_simplified hr hA
    (shearSpatialFirstField r i) (shearSpatialFirstField_continuous hr i) hzero hbound
  have halg : C * r⁻¹ * (8 * r ^ 2) = 8 * C * r := by
    field_simp [ne_of_gt hr]
  rw [halg] at hbase
  exact hbase



end CKN

namespace CKN

def shearBumpField (r : ℝ) (z : Vec 2 × ℝ) : ℝ := shearScaleBump r z

theorem shearBumpField_continuous {r : ℝ} (hr : 0 < r) :
    Continuous (shearBumpField r) := by
  exact (shearScaleBump_smooth_of_pos hr).continuous

private theorem shearBumpField_zero_outside {r : ℝ} (hr : 0 < r)
    {z : Vec 2 × ℝ} (hz : z ∉ shearProfileBox r) : shearBumpField r z = 0 := by
  have h := shearScaleDerivative_zero_outside hr 0 (by norm_num)
    (fun i : Fin 0 => Fin.elim0 i) hz
  simpa only [shearBumpField, iteratedFDeriv_zero_apply] using h

private theorem shearBumpField_bound {r C : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (z : Vec 2 × ℝ) :
    ‖shearBumpField r z‖ ≤ C := by
  have h := shearScaleBump_iteratedFDeriv_bound hr hr1 hUnit 0 (by norm_num) z
  rw [norm_iteratedFDeriv_zero] at h
  norm_num at h
  exact h


end CKN

namespace CKN

theorem shearBumpField_eLpNorm_of_unit_bound {r C : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) :
    eLpNorm (shearBumpField r) 2 volume ≤ ENNReal.ofReal (8 * C * r ^ 2) := by
  have hbase := shear_eLpNorm_box_bound_simplified hr (by positivity : 0 ≤ C)
    (shearBumpField r) (shearBumpField_continuous hr)
    (fun z hz => shearBumpField_zero_outside hr hz)
    (fun z hz => shearBumpField_bound hr hr1 hUnit z)
  have halg : C * (8 * r ^ 2) = 8 * C * r ^ 2 := by ring
  rw [halg] at hbase
  exact hbase

end CKN
