-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.PkBoundsUnconditionalCore
import CKN.Setting.SliceNormBounds

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

set_option autoImplicit false
noncomputable section
namespace CKN

/-- Paper equation `eq:slice-norm-bounds`, force line: the `L^q(J_ρ)` time norm of the
`L^q(B_ρ)` force slice norm equals `ρ^(5/q - 3) * lambda q f z ρ`, i.e. the factor
`ρ^(5/q - 3)` times the scale quantity `lambda`. -/
theorem forceSliceTimeNorm_eq_lambda
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    eLpNorm' (fun s : ℝ =>
        (∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ))
      q (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
    ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ) := by
  let B : Set Vec3 := vec3Ball z.1 ρ
  let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  have hqpos : 0 < q := lt_trans (by norm_num : (0 : ℝ) < 5 / 2) hsol.2.2.2.1
  have hΩ : IsOpen Ω := hsol.1
  have hI : IsOpen I := hsol.2.1
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset hΩ hI hρ hsub
  have hball : B ⊆ Ω' := by
    intro y hy
    have hy' : (y, z.2) ∈ parabolicCylinder z.1 z.2 ρ := by
      rw [parabolicCylinder]
      exact ⟨hy, ⟨by nlinarith only [hρ], le_rfl⟩⟩
    exact (hcyl hy').1
  have htime : T ⊆ J := by
    intro s hs
    have hx : z.1 ∈ B := by
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hs' : (z.1, s) ∈ parabolicCylinder z.1 z.2 ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, hs⟩
    exact (hcyl hs').2
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hfglobal : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.2.1
  have hfprod : AEStronglyMeasurable f
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hfglobal
  have hfBT : AEStronglyMeasurable f
      ((volume.restrict B).prod (volume.restrict T)) :=
    hfprod.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball)
      (Measure.restrict_mono_set volume htime))
  let F : Vec3 × ℝ → ℝ := fun w => vec3EuclideanNorm (f w) ^ q
  have hnorm_cont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
    unfold vec3EuclideanNorm; fun_prop
  have hFmeas : AEStronglyMeasurable F
      ((volume.restrict B).prod (volume.restrict T)) := by
    have hnorm : AEStronglyMeasurable (fun w : Vec3 × ℝ => vec3EuclideanNorm (f w))
        ((volume.restrict B).prod (volume.restrict T)) :=
      hnorm_cont.comp_aestronglyMeasurable hfBT
    exact (Real.continuous_rpow_const hqpos.le).comp_aestronglyMeasurable hnorm
  have hFpowBT : AEMeasurable F ((volume.restrict B).prod (volume.restrict T)) :=
    hFmeas.aemeasurable
  let H : ℝ → ℝ≥0∞ := fun s => ∫⁻ y in B, ENNReal.ofReal (F (y, s))
  have hHae : AEMeasurable H (volume.restrict T) := by
    have h := hFpowBT.ennreal_ofReal.lintegral_prod_left'
      (μ := volume.restrict B) (ν := volume.restrict T)
    simpa [H, F] using h
  have hHtop : (∫⁻ s in T, H s) < ⊤ := by
    have hswap := pressure_prod_lintegral_swap (B := B) (T := T)
      (F := F) hFmeas.aemeasurable
    have hforce := sws_force_integral_lt_top hsol (z := z) hρ hsub
    have htotal : (∫⁻ s in T, H s) =
        ∫⁻ w in B ×ˢ T, ENNReal.ofReal (F w) := by
      calc
        (∫⁻ s in T, H s) = ∫⁻ s in T, ∫⁻ y in B, ENNReal.ofReal (F (y, s)) := rfl
        _ = ∫⁻ w in B ×ˢ T, ENNReal.ofReal (F w) := hswap.symm
    have hcyl_total : (∫⁻ w in B ×ˢ T, ENNReal.ofReal (F w)) =
        ∫⁻ w in parabolicCylinder z.1 z.2 ρ, ENNReal.ofReal (F w) := rfl
    have hforce_alt : (∫⁻ w in B ×ˢ T, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) < ⊤ := by
      have hforce_cyl : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) < ⊤ := hforce
      have hforce_BT : (∫⁻ w in B ×ˢ T, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) < ⊤ :=
        hforce_cyl
      exact hforce_BT
    have hforce' : (∫⁻ w in B ×ˢ T, ENNReal.ofReal (F w)) < ⊤ := by
      rw [hcyl_total, parabolicCylinder]
      calc
        (∫⁻ w in B ×ˢ T, ENNReal.ofReal (F w))
            = (∫⁻ w in B ×ˢ T, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) := by
          refine lintegral_congr (fun w => ?_)
          simp [F, ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg (f w)) hqpos.le]
        _ < ⊤ := hforce_alt
    rw [htotal]
    exact hforce'
  have hHs : ∀ᵐ s ∂volume.restrict T, H s < ⊤ := by
    have hfin : (∫⁻ s in T, H s) ≠ ∞ := ne_of_lt hHtop
    exact ae_lt_top' hHae hfin
  let G : ℝ → ℝ := fun s => (H s).toReal ^ (1 / q : ℝ)
  have hGmeas : AEStronglyMeasurable G (volume.restrict T) := by
    have hreal : AEMeasurable (fun s => (H s).toReal) (volume.restrict T) :=
      hHae.ennreal_toReal
    have hc : Continuous (fun x : ℝ => x ^ (1 / q : ℝ)) :=
      Real.continuous_rpow_const (by positivity)
    simpa [Function.comp_def, G] using
      (hc.measurable.comp_aemeasurable hreal).aestronglyMeasurable
  have hGnonneg : 0 ≤ᵐ[volume.restrict T] G :=
    Eventually.of_forall (fun s => Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hGpow : ∀ᵐ s ∂volume.restrict T,
      ‖G s‖ₑ ^ q = H s := by
    filter_upwards [hHs] with s hs
    have hmul : (1 / q) * q = (1 : ℝ) := by field_simp
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg _) hqpos.le]
    rw [← Real.rpow_mul ENNReal.toReal_nonneg, hmul, Real.rpow_one,
      ENNReal.ofReal_toReal hs.ne]
  have hlin : (∫⁻ s in T, ‖G s‖ₑ ^ q) = ∫⁻ s in T, H s := by
    apply lintegral_congr_ae
    exact hGpow
  have hconv : ∀ᵐ s ∂volume.restrict T,
      (H s).toReal = ∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q := by
    have hfm := hfBT.prodMk_right
    filter_upwards [hfm, hHs] with s hms hHs'
    have hnorm_meas : AEStronglyMeasurable (fun y : Vec3 => vec3EuclideanNorm (f (y, s)))
        (volume.restrict B) := by
      have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
        unfold vec3EuclideanNorm; fun_prop
      exact hc.comp_aestronglyMeasurable hms
    have hnormpow_meas : AEStronglyMeasurable
        (fun y : Vec3 => vec3EuclideanNorm (f (y, s)) ^ q) (volume.restrict B) :=
      (Real.continuous_rpow_const hqpos.le).comp_aestronglyMeasurable hnorm_meas
    have hnonneg : 0 ≤ᵐ[volume.restrict B] fun y =>
        vec3EuclideanNorm (f (y, s)) ^ q :=
      Eventually.of_forall (fun y => Real.rpow_nonneg (vec3EuclideanNorm_nonneg _) _)
    have hfin : (∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (f (y, s)) ^ q)) < ⊤ := by
      simpa [H, F] using hHs'
    have hint : Integrable (fun y : Vec3 => vec3EuclideanNorm (f (y, s)) ^ q)
        (volume.restrict B) :=
      (lintegral_ofReal_ne_top_iff_integrable hnormpow_meas hnonneg).mp
        (ne_of_lt hfin)
    have hconv' := ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall (fun y => Real.rpow_nonneg (vec3EuclideanNorm_nonneg _) q))
    -- hconv' : ENNReal.ofReal (∫ y in B, ...) = ∫⁻ y in B, ENNReal.ofReal (...)
    -- We need (H s).toReal = ∫ y in B, ...
    -- H s = ∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (f (y, s)) ^ q)
    -- So (H s).toReal = (∫⁻ y in B, ENNReal.ofReal (...)).toReal
    -- And hconv' gives ENNReal.ofReal (∫ ...) = ∫⁻ ...
    -- Taking toReal of both sides of hconv' gives ∫ ... = (∫⁻ ...).toReal
    have hpos_int : 0 ≤ ∫ y in B, vec3EuclideanNorm (f (y, s)) ^ q :=
      integral_nonneg_of_ae hnonneg
    apply_fun ENNReal.toReal at hconv'
    simpa [H, F, ENNReal.toReal_ofReal hpos_int] using hconv'.symm
  have hG_ae_eq : (fun s : ℝ =>
      (∫ y in vec3Ball z.1 ρ,
        vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)) =ᵐ[volume.restrict T] G := by
    filter_upwards [hconv] with s hs
    dsimp [G]
    rw [hs]
  have hA : 0 ≤ ρ ^ (5 / q - 3) * lambda q f z ρ := by
    exact mul_nonneg (Real.rpow_nonneg hρ.le _) (by unfold lambda; positivity)
  have hforce_eq := sws_lintegral_vec3EuclideanNorm_pow_eq_ofReal_lambda_pow
    hsol (z := z) hρ hsub
  have hcyl_meas : AEMeasurable (fun w : ParabolicPoint =>
      ENNReal.ofReal (vec3EuclideanNorm (f w) ^ q))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    have hFcyl_meas : AEStronglyMeasurable (fun w : ParabolicPoint =>
        ENNReal.ofReal (F w))
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
      have h := (hFmeas.aemeasurable.ennreal_ofReal).aestronglyMeasurable
      rw [Measure.prod_restrict B T, ← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ] at h
      exact h
    simpa [F] using hFcyl_meas.aemeasurable
  calc
    eLpNorm' (fun s : ℝ =>
        (∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ))
      q (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) = eLpNorm' G q (volume.restrict T) := by
      rw [eLpNorm'_congr_ae hG_ae_eq]
    _ = (∫⁻ s in T, ‖G s‖ₑ ^ q) ^ (1 / q : ℝ) := by
      rw [eLpNorm'_eq_lintegral_enorm]
    _ = (∫⁻ s in T, H s) ^ (1 / q : ℝ) := by rw [hlin]
    _ = (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (f w) ^ q)) ^ (1 / q : ℝ) := by
      rw [lintegral_parabolicCylinder hcyl_meas]
    _ = (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ^ (1 / q : ℝ) := by
      refine congrArg (fun t => t ^ (1 / q : ℝ)) (lintegral_congr ?_)
      intro w
      rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg (f w)) hqpos.le]
    _ = (ENNReal.ofReal ((ρ ^ (5 / q - 3) * lambda q f z ρ) ^ q)) ^ (1 / q : ℝ) := by
      rw [hforce_eq]
    _ = ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hA hqpos.le, ← ENNReal.rpow_mul]
      have hqmul : q * (1 / q : ℝ) = (1 : ℝ) := by field_simp
      rw [hqmul, ENNReal.rpow_one]

end CKN
