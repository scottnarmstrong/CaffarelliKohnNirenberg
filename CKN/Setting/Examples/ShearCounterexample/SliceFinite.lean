-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.FullFields
import CKN.Setting.Examples.ShearCounterexample.ScaleSupport
import CKN.Foundation.Sobolev.WeakDerivative
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite-scale spatial estimates for the shear series. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped Topology
namespace CKN

private theorem shearScale_tendsto_zero_slice :
    Tendsto shearScale atTop (𝓝 (0 : ℝ)) := by
  unfold shearScale
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem exists_shearScale_sq_lt_abs_time {t : ℝ} (ht : t ≠ 0) :
    ∃ N, ∀ n, N ≤ n → 2 * shearScale n ^ 2 < |t| := by
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hsmall : ∀ᶠ n : ℕ in atTop, 2 * shearScale n ^ 2 < |t| := by
    have hpow : Tendsto (fun n : ℕ => 2 * shearScale n ^ 2) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
      simpa using hconst.mul (shearScale_tendsto_zero_slice.pow 2)
    exact hpow.eventually (Iio_mem_nhds htpos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  exact ⟨N, fun n hn => hN n hn⟩

theorem shearReducedBumpTerm_zero_of_time_large {n : ℕ} {x : Vec 2} {t : ℝ}
    (hlarge : 2 * shearScale n ^ 2 < |t|) :
    shearReducedBumpTerm n (x, t) = 0 := by
  let r := shearScale n
  have hr : 0 < r := shearScale_pos n
  have hz : (x, t) ∉ shearProfileBox r := by
    intro hz
    have ht : t ∈ Ioo (-(2 * r ^ 2)) (2 * r ^ 2) := hz.2
    have habs : |t| < 2 * r ^ 2 := abs_lt.mpr ht
    exact (lt_asymm hlarge habs).elim
  have hD := shearScaleDerivative_zero_outside hr 0 (by norm_num)
    (fun j : Fin 0 => j.elim0) hz
  have hb : shearScaleBump r (x, t) = 0 := by
    simpa [shearScaleBump, iteratedFDeriv_zero_apply] using hD
  simp [shearReducedBumpTerm, shearBumpField, r, hb]

theorem shearReducedGradientTerm_zero_of_time_large {i : Fin 2} {n : ℕ}
    {x : Vec 2} {t : ℝ} (hlarge : 2 * shearScale n ^ 2 < |t|) :
    shearReducedGradientTerm i n (x, t) = 0 := by
  let r := shearScale n
  have hr : 0 < r := shearScale_pos n
  have hz : (x, t) ∉ shearProfileBox r := by
    intro hz
    have ht : t ∈ Ioo (-(2 * r ^ 2)) (2 * r ^ 2) := hz.2
    have habs : |t| < 2 * r ^ 2 := abs_lt.mpr ht
    exact (lt_asymm hlarge habs).elim
  have hD := shearScaleDerivative_zero_outside hr 1 (by norm_num)
    (fun _ : Fin 1 => (Pi.single i (1 : ℝ), (0 : ℝ))) hz
  have hfield : shearSpatialFirstField r i (x, t) = 0 := by
    change (iteratedFDeriv ℝ 1 (shearScaleBump r) (x, t)
      (fun _ : Fin 1 => (Pi.single i 1, (0 : ℝ)))) = 0
    exact hD
  simp [shearReducedGradientTerm, r, hfield]


theorem shearReducedBumpSeries_eq_finite_of_time_nezero {t : ℝ} (ht : t ≠ 0) :
    ∃ N, ∀ x : Vec 2,
      shearReducedBumpSeries (x, t) =
        ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, t) := by
  obtain ⟨N, hN⟩ := exists_shearScale_sq_lt_abs_time ht
  refine ⟨N, fun x => ?_⟩
  unfold shearReducedBumpSeries
  apply tsum_eq_sum
  intro n hn
  have hnN : N ≤ n := by
    have hnot : ¬ n < N := by simpa using hn
    exact not_lt.mp hnot
  exact shearReducedBumpTerm_zero_of_time_large (hN n hnN)



theorem shearReducedSliceTerm_contDiff (n : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => shearReducedBumpTerm n (x, t)) := by
  unfold shearReducedBumpTerm
  have hEmbed : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (x, t)) := by fun_prop
  have h := (shearScaleBump_smooth_of_pos (shearScale_pos n)).comp hEmbed
  simpa [shearBumpField, smul_eq_mul] using h.const_smul (shearWeight n)

theorem shearReducedSliceTerm_fderiv_apply (n : ℕ) (t : ℝ)
    (i : Fin 2) (x : Vec 2) :
    fderiv ℝ (fun y : Vec 2 => shearReducedBumpTerm n (y, t)) x
        (basisVec i) = shearReducedGradientTerm i n (x, t) := by
  let r := shearScale n
  have hr : 0 < r := shearScale_pos n
  have hBumpDiff : Differentiable ℝ (shearScaleBump r) :=
    (shearScaleBump_smooth_of_pos hr).differentiable (by simp)
  have hBumpDeriv : HasFDerivAt (shearScaleBump r)
      (fderiv ℝ (shearScaleBump r) (x, t)) (x, t) :=
    hBumpDiff.differentiableAt.hasFDerivAt
  have hEmbed : HasFDerivAt (fun y : Vec 2 => (y, t))
      (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ (Vec 2))
        (0 : Vec 2 →L[ℝ] ℝ)) x :=
    (ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt.prodMk
      (hasFDerivAt_const t x)
  have hcomp := (hBumpDeriv.const_smul (shearWeight n)).comp x hEmbed
  have hcompose : (fun y : Vec 2 =>
      shearWeight n • shearScaleBump r (y, t)) =
        (fun y => (shearWeight n • shearScaleBump r) (y, t)) := rfl
  change fderiv ℝ (fun y : Vec 2 =>
    shearWeight n • shearScaleBump r (y, t)) x (basisVec i) = _
  rw [hcompose]
  change fderiv ℝ ((shearWeight n • shearScaleBump r) ∘
    (fun y : Vec 2 => (y, t))) x (basisVec i) = _
  rw [hcomp.fderiv]
  change ((shearWeight n • fderiv ℝ (shearScaleBump r) (x, t)) ∘L
    ((ContinuousLinearMap.id ℝ (Vec 2)).prod 0)) (basisVec i) = _
  have hdir : fderiv ℝ (shearScaleBump r) (x, t)
        (basisVec i, 0) =
      shearSpatialFirstField r i (x, t) := by
    change fderiv ℝ (shearScaleBump r) (x, t) (basisVec i, 0) =
      iteratedFDeriv ℝ 1 (shearScaleBump r) (x, t)
        (fun _ : Fin 1 => (Pi.single i (1 : ℝ), 0))
    simp [iteratedFDeriv_one_apply, basisVec]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply]
  rw [hdir]
  simp [shearReducedGradientTerm, shearSpatialFirstField, r, smul_eq_mul]


theorem shearFullSlice_smooth_of_time_nezero {t : ℝ} (ht : t ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => shearReducedBumpSeries (x, t)) := by
  obtain ⟨N, hN⟩ := shearReducedBumpSeries_eq_finite_of_time_nezero ht
  have hsum : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, t)) := by
    apply ContDiff.sum
    intro n hn
    exact shearReducedSliceTerm_contDiff n t
  have hEq : (fun x : Vec 2 => shearReducedBumpSeries (x, t)) =
      fun x => ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, t) := by
    funext x
    exact hN x
  rw [hEq]
  exact hsum

end CKN
