-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.SliceSpatialUniform
import CKN.Setting.Examples.ShearCounterexample.AmbientLp
import CKN.Statements.LocalBox
import CKN.Statements.SpaceTimeSet
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.EssSup

/-! # Spatial slice energy estimates for the shear profile. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
open scoped ENNReal
namespace CKN

def shearPassiveSpatialSlab : Set Vec3 := {x | x 2 ∈ Icc (-1 : ℝ) 1}

private theorem shearSpatialCoordinateEquiv_slab_preimage :
    shearSpatialCoordinateEquiv ⁻¹' (Icc (-1 : ℝ) 1 ×ˢ (Set.univ : Set Vec2)) =
      shearPassiveSpatialSlab := by
  ext x
  simp [shearPassiveSpatialSlab, shearSpatialCoordinateEquiv]

private theorem shearSpatialCoordinateEquiv_apply (x : Vec3) :
    shearSpatialCoordinateEquiv x = (x 2, fun i : Fin 2 => x i.castSucc) := by
  change (x 2, fun i : Fin 2 => x ((2 : Fin 3).succAbove i)) = _
  congr 2
  funext i
  change x ((Fin.last 2).succAbove i) = _
  rw [Fin.succAbove_last]

private theorem shearSpatialCoordinateEquiv_measurePreserving_on_slab :
    MeasurePreserving shearSpatialCoordinateEquiv
      (volume.restrict shearPassiveSpatialSlab)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume : Measure Vec2)) := by
  have hs : MeasurableSet (Icc (-1 : ℝ) 1 ×ˢ (Set.univ : Set Vec2)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hsp : MeasurePreserving shearSpatialCoordinateEquiv volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have hmp := hsp.restrict_preimage hs
  rw [Measure.volume_eq_prod, shearSpatialCoordinateEquiv_slab_preimage,
    ← Measure.prod_restrict, Measure.restrict_univ] at hmp
  exact hmp

private theorem shearCounterexampleVelocity_slice_norm_eq (x : Vec3) (t : ℝ) :
    ‖shearCounterexampleVelocity (x, t)‖ₑ =
      ‖shearReducedBumpSeries ((fun i : Fin 2 => x i.castSucc), t)‖ₑ := by
  have hform : shearCounterexampleVelocity (x, t) =
      shearFullScalar ((x, t) : ParabolicPoint) • basisVec (2 : Fin 3) := by
    ext i
    by_cases hi : i = 2
    · subst i
      simp [shearCounterexampleVelocity, shearFullScalar, basisVec_apply]
    · simp [shearCounterexampleVelocity, basisVec_apply, hi]
  have hb : ‖basisVec (2 : Fin 3)‖ₑ = 1 := by
    rw [← enorm_norm]
    simp [basisVec, Pi.norm_single]
  rw [hform, enorm_smul, hb, mul_one]
  simp [shearFullScalar, shearReducedView]

theorem shearVelocity_sliceEnergy_le_of_localBox {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) {t : ℝ} (ht : t ≠ 0) :
    ∫⁻ x in Ω', ‖shearCounterexampleVelocity (x, t)‖ₑ ^ (2 : ℝ) ∂volume ≤
      ENNReal.ofReal (2 * (16 / 3 * shearUnitBump_bound.choose) ^ 2) := by
  have hsubset : Ω' ⊆ shearPassiveSpatialSlab := by
    intro x hx
    have hxcl : x ∈ closure Ω' := subset_closure hx
    have hxball : x ∈ vec3Ball 0 1 := hbox.2.2.1 hxcl
    have hn : vec3EuclideanNorm x < 1 := by simpa [vec3Ball] using hxball
    have hcoord : |x 2| < 1 := (abs_apply_le_vec3EuclideanNorm x 2).trans_lt hn
    change x 2 ∈ Icc (-1 : ℝ) 1
    rcases abs_lt.mp hcoord with ⟨hl, hu⟩
    exact ⟨le_of_lt hl, le_of_lt hu⟩
  calc
    _ ≤ ∫⁻ x in shearPassiveSpatialSlab,
        ‖shearCounterexampleVelocity (x, t)‖ₑ ^ (2 : ℝ) ∂volume :=
      lintegral_mono_set hsubset
    _ = ∫⁻ y : ℝ × Vec2 in (Icc (-1 : ℝ) 1 ×ˢ Set.univ),
        ‖shearReducedBumpSeries (y.2, t)‖ₑ ^ (2 : ℝ) ∂volume := by
      have hEq : (fun x : Vec3 => ‖shearCounterexampleVelocity (x, t)‖ₑ ^ (2 : ℝ)) =
          fun y : Vec3 =>
            (‖shearReducedBumpSeries ((fun i : Fin 2 => y i.castSucc), t)‖ₑ ^ (2 : ℝ)) := by
        funext x
        exact congrArg (fun a : ℝ≥0∞ => a ^ (2 : ℝ)) (shearCounterexampleVelocity_slice_norm_eq x t)
      rw [hEq]
      have hmap : Measurable (fun y : ℝ × Vec2 => (y.2, t)) :=
        measurable_snd.prodMk measurable_const
      have hprofile : Measurable (fun y : ℝ × Vec2 =>
          shearReducedBumpSeries (y.2, t)) := shearReducedBumpSeries_measurable.comp hmap
      have hf : Measurable (fun y : ℝ × Vec2 =>
          ‖shearReducedBumpSeries (y.2, t)‖ₑ ^ (2 : ℝ)) :=
        ENNReal.continuous_rpow_const.measurable.comp hprofile.enorm
      have hmp := shearSpatialCoordinateEquiv_measurePreserving_on_slab
      have hp := hmp.lintegral_comp hf
      have hcomp : (fun x : Vec3 =>
          ‖shearReducedBumpSeries ((fun i : Fin 2 => x i.castSucc), t)‖ₑ ^ (2 : ℝ)) =
          fun x => ‖shearReducedBumpSeries ((shearSpatialCoordinateEquiv x).2, t)‖ₑ ^ (2 : ℝ) := by
        funext x
        congr 3
        rw [shearSpatialCoordinateEquiv_apply]
      rw [hcomp]
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
      exact hp
    _ = (∫⁻ s : ℝ, (1 : ℝ≥0∞) ∂volume.restrict (Icc (-1 : ℝ) 1)) *
        ∫⁻ y : Vec2, ‖shearReducedBumpSeries (y, t)‖ₑ ^ (2 : ℝ) ∂volume := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
      calc
        ∫⁻ y : ℝ × Vec2, ‖shearReducedBumpSeries (y.2, t)‖ₑ ^ (2 : ℝ) ∂
            (volume.restrict (Icc (-1 : ℝ) 1)).prod volume =
          ∫⁻ y : ℝ × Vec2, (1 : ℝ≥0∞) *
            ‖shearReducedBumpSeries (y.2, t)‖ₑ ^ (2 : ℝ) ∂
            (volume.restrict (Icc (-1 : ℝ) 1)).prod volume := by simp
        _ = (∫⁻ s : ℝ, (1 : ℝ≥0∞) ∂volume.restrict (Icc (-1 : ℝ) 1)) *
            ∫⁻ y : Vec2, ‖shearReducedBumpSeries (y, t)‖ₑ ^ (2 : ℝ) ∂volume := by
          have hslice : Measurable (fun y : Vec2 => shearReducedBumpSeries (y, t)) :=
            shearReducedBumpSeries_measurable.comp (measurable_id.prodMk measurable_const)
          exact lintegral_prod_mul (μ := volume.restrict (Icc (-1 : ℝ) 1))
            (ν := volume) (f := fun _ : ℝ => (1 : ℝ≥0∞))
            (g := fun y : Vec2 => ‖shearReducedBumpSeries (y, t)‖ₑ ^ (2 : ℝ))
            aemeasurable_const
            (ENNReal.continuous_rpow_const.measurable.comp hslice.enorm).aemeasurable
    _ = ENNReal.ofReal 2 * ∫⁻ y : Vec2,
        ‖shearReducedBumpSeries (y, t)‖ₑ ^ (2 : ℝ) ∂volume := by
      congr 1
      rw [lintegral_const]
      rw [show (volume.restrict (Icc (-1 : ℝ) 1)) Set.univ = volume (Icc (-1 : ℝ) 1) by
        simp]
      rw [Real.volume_Icc]
      norm_num
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal
        ((16 / 3 * shearUnitBump_bound.choose) ^ 2) := by
      gcongr
      exact shearReducedBumpSeries_slice_integral_bound ht
    _ = ENNReal.ofReal (2 * (16 / 3 * shearUnitBump_bound.choose) ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]

theorem shearVelocity_sliceEnergy_essSup_finite {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    essSup (fun s => ∫⁻ x in Ω',
      ‖shearCounterexampleVelocity (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) < ⊤ := by
  let K : ℝ≥0∞ := ENNReal.ofReal (2 * (16 / 3 * shearUnitBump_bound.choose) ^ 2)
  have hbound : (fun s => ∫⁻ x in Ω',
      ‖shearCounterexampleVelocity (x, s)‖ₑ ^ (2 : ℝ)) ≤ᵐ[volume.restrict J] fun _ => K := by
    filter_upwards [ae_restrict_of_ae (MeasureTheory.Measure.ae_ne volume 0)] with s hs
    exact shearVelocity_sliceEnergy_le_of_localBox hbox hs
  have hsup := essSup_le_of_ae_le K hbound
  exact lt_of_le_of_lt hsup (ENNReal.ofReal_lt_top)

end CKN
