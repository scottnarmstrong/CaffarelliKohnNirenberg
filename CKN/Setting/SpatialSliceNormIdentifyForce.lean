-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SpatialSliceNorms
import CKN.Setting.SliceNormBounds
import CKN.Pressure.PkBoundsUnconditionalCore

open MeasureTheory Set
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace CKN

/-!
# Identification of the force spatial slice norm with the explicit real integral

Paper equation `eq:slice-norms` in `paper/ckn.tex`: identify the force spatial slice norm
of `CKN/Setting/SpatialSliceNorms.lean` with the explicit real integral used by the scale
quantity `lambda`.
-/

/-- The force spatial slice norm `‖f‖_{L^q(B_ρ)}` equals the explicit real integral
`(∫_{B_ρ} |f|^q)^{1/q}` for almost every time in the relevant interval. -/
theorem forceSpatialSliceNorm_eq_ofReal_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      forceSpatialSliceNorm f z.1 ρ q s =
        ENNReal.ofReal
      ((∫ y in vec3Ball z.1 ρ,
        vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)) := by
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hf_ae : AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.2.1
  have hnorm_cont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hf_norm_ae : AEStronglyMeasurable (fun w : ParabolicPoint => vec3EuclideanNorm (f w))
      (volume.restrict (spaceTimeSet Ω' J)) :=
    hnorm_cont.comp_aestronglyMeasurable hf_ae
  have hf_norm_pow_ae : AEStronglyMeasurable
      (fun w : ParabolicPoint => (vec3EuclideanNorm (f w)) ^ q)
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (Real.continuous_rpow_const hqpos.le).comp_aestronglyMeasurable hf_norm_ae
  have hf_prod : AEStronglyMeasurable f
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hf_ae
  have hf_norm_pow_prod : AEStronglyMeasurable
      (fun w : ParabolicPoint => (vec3EuclideanNorm (f w)) ^ q)
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hf_norm_pow_ae
  let B : Set Vec3 := vec3Ball z.1 ρ
  let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  have hf_norm_pow_BT_ae : AEStronglyMeasurable
      (fun w : ParabolicPoint => (vec3EuclideanNorm (f w)) ^ q)
      ((volume.restrict B).prod (volume.restrict T)) :=
    hf_norm_pow_prod.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball)
      (Measure.restrict_mono_set volume htime))
  have hf_norm_pow_BT : AEMeasurable
      (fun w : ParabolicPoint => (vec3EuclideanNorm (f w)) ^ q)
      ((volume.restrict B).prod (volume.restrict T)) :=
    hf_norm_pow_BT_ae.aemeasurable
  have hswap := pressure_prod_lintegral_swap (B := B) (T := T)
    (F := fun w : ParabolicPoint => (vec3EuclideanNorm (f w)) ^ q) hf_norm_pow_BT
  have htotal_eq : (∫⁻ s in T, ∫⁻ y in B, ENNReal.ofReal ((vec3EuclideanNorm (f (y, s))) ^ q)) =
      ∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal ((vec3EuclideanNorm (f w)) ^ q) := by
    convert hswap.symm using 1
    · rfl
  have hforce_lt_top : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) < ⊤ :=
    sws_force_integral_lt_top hsol hρ hsub
  have hforce_lt_top' : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal ((vec3EuclideanNorm (f w)) ^ q)) < ⊤ := by
    have h_eq : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) =
        (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
          ENNReal.ofReal ((vec3EuclideanNorm (f w)) ^ q)) := by
      refine lintegral_congr (fun w => ?_)
      rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg (f w)) hqpos.le]
    rw [← h_eq]
    exact hforce_lt_top
  have htotal_lt_top :
      (∫⁻ s in T, ∫⁻ y in B, ENNReal.ofReal ((vec3EuclideanNorm (f (y, s))) ^ q)) < ⊤ := by
    rw [htotal_eq]
    exact hforce_lt_top'
  have hmeas_slice_lintegral : AEMeasurable (fun s : ℝ =>
      ∫⁻ y in B, ENNReal.ofReal ((vec3EuclideanNorm (f (y, s))) ^ q))
      (volume.restrict T) := by
    -- hf_norm_pow_BT.ennreal_ofReal : AEMeasurable
    --   (fun w => ENNReal.ofReal (...))
    --   ((volume.restrict B).prod (volume.restrict T))
    -- We want AEMeasurable of fun s => ∫⁻ y in B, ... w.r.t.
    -- volume.restrict T
    -- This integrates over the LEFT factor (B), giving a
    -- function of the RIGHT factor (T = s)
    -- Use lintegral_prod_left' which integrates over the left
    -- factor, returning a function of the right factor (s).
    have h := hf_norm_pow_BT.ennreal_ofReal
    have h_lintegral := h.lintegral_prod_left'
    simpa [B] using h_lintegral
  have h_ae_finite : ∀ᵐ s ∂volume.restrict T,
      ∫⁻ y in B, ENNReal.ofReal ((vec3EuclideanNorm (f (y, s))) ^ q) < ⊤ := by
    have h_ne_top : ∀ᵐ s ∂volume.restrict T,
        ∫⁻ y in B, ENNReal.ofReal ((vec3EuclideanNorm (f (y, s))) ^ q) ≠ ⊤ := by
      filter_upwards [ae_lt_top' hmeas_slice_lintegral (ne_of_lt htotal_lt_top)] with s hs
      exact hs.ne
    filter_upwards [h_ne_top] with s hs
    exact hs.lt_top
  have hmeas_slice : ∀ᵐ s ∂volume.restrict T,
      AEStronglyMeasurable (fun y : Vec3 => (vec3EuclideanNorm (f (y, s))) ^ q)
        (volume.restrict B) := by
    exact hf_norm_pow_BT_ae.prodMk_right
  have hnonneg_slice : ∀ᵐ s ∂volume.restrict T,
      0 ≤ᵐ[volume.restrict B] fun y => (vec3EuclideanNorm (f (y, s))) ^ q := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    refine Filter.Eventually.of_forall (fun y => ?_)
    exact Real.rpow_nonneg (vec3EuclideanNorm_nonneg _) _
  filter_upwards [h_ae_finite, hmeas_slice, hnonneg_slice] with s hs_lt hmeas hnonneg
  have h_int : Integrable (fun y : Vec3 => (vec3EuclideanNorm (f (y, s))) ^ q)
      (volume.restrict B) :=
    ((lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp hs_lt.ne)
  have h_nonneg_int : 0 ≤ ∫ y in B, (vec3EuclideanNorm (f (y, s))) ^ q :=
    integral_nonneg_of_ae hnonneg
  have hmeas_norm : AEStronglyMeasurable (fun y : Vec3 => vec3EuclideanNorm (f (y, s)))
      (volume.restrict B) := by
    have h_cont : Continuous (fun x : ℝ => x ^ (q⁻¹)) :=
      Real.continuous_rpow_const (by positivity : 0 ≤ q⁻¹)
    have h_comp := h_cont.comp_aestronglyMeasurable hmeas
    refine h_comp.congr ?_
    filter_upwards with y
    have h_nonneg := vec3EuclideanNorm_nonneg (f (y, s))
    rw [Real.rpow_rpow_inv h_nonneg hqpos.ne']
  unfold forceSpatialSliceNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hqpos))
    ENNReal.ofReal_ne_top
    hmeas_norm]
  have h_enorm_eq : ∀ y, ‖vec3EuclideanNorm (f (y, s))‖ₑ =
      ENNReal.ofReal (vec3EuclideanNorm (f (y, s))) := by
    intro y
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
  have h_power_eq : ∀ y, ENNReal.ofReal (vec3EuclideanNorm (f (y, s))) ^ q =
      ENNReal.ofReal ((vec3EuclideanNorm (f (y, s))) ^ q) := by
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _) hqpos.le]
  have h_lintegral_eq : (∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (f (y, s))) ^ q) =
      (∫⁻ y in B, ENNReal.ofReal ((vec3EuclideanNorm (f (y, s))) ^ q)) := by
    refine lintegral_congr (fun y => ?_)
    rw [h_power_eq y]
  have h_toReal : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hqpos.le
  rw [h_toReal]
  calc
    (∫⁻ (x : Vec3) in B,
        ‖vec3EuclideanNorm (f (x, s))‖ₑ ^ q ∂volume) ^ (1 / q)
        = (∫⁻ (x : Vec3) in B,
          ENNReal.ofReal ((vec3EuclideanNorm (f (x, s))) ^ q) ∂volume) ^ (1 / q) := by
          congr 1
          refine lintegral_congr (fun x => ?_)
          rw [h_enorm_eq x, h_power_eq x]
    _ = (ENNReal.ofReal (∫ (x : Vec3) in B, (vec3EuclideanNorm (f (x, s))) ^ q)) ^ (1 / q) := by
          rw [← ofReal_integral_eq_lintegral_ofReal h_int hnonneg]
    _ = ENNReal.ofReal ((∫ (y : Vec3) in B, (vec3EuclideanNorm (f (y, s))) ^ q) ^ (1 / q)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg h_nonneg_int (by positivity : 0 ≤ (1 : ℝ) / q)]
    _ = ENNReal.ofReal
        ((∫ (y : Vec3) in vec3Ball z.1 ρ,
          vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q)) := by
      unfold B; rfl

end CKN
