-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.ShearCoordinates
import CKN.Statements.LocalBox
import CKN.Statements.SpaceTimeSet
import CKN.Foundation.Parabolic.Vec3Norm
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Measure.Restrict

/-! # Lp bounds for the passive coordinate of the shear. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

def shearPassiveSlab : Set ParabolicPoint :=
  {z | z.1 2 ∈ Icc (-1 : ℝ) 1}

private theorem shearCoordinateSlab_preimage :
    shearCoordinateEquiv ⁻¹' (Icc (-1 : ℝ) 1 ×ˢ (Set.univ : Set (Vec2 × ℝ))) =
      shearPassiveSlab := by
  ext z
  simp [shearPassiveSlab, shearCoordinateEquiv_apply]

private theorem shearCoordinateEquiv_measurePreserving_on_slab :
    MeasurePreserving shearCoordinateEquiv
      (volume.restrict shearPassiveSlab)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume : Measure (Vec2 × ℝ))) := by
  have hs : MeasurableSet
      (Icc (-1 : ℝ) 1 ×ˢ (Set.univ : Set (Vec2 × ℝ))) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hmp := shearCoordinateEquiv_measurePreserving.restrict_preimage hs
  rw [Measure.volume_eq_prod, shearCoordinateSlab_preimage,
    ← Measure.prod_restrict, Measure.restrict_univ] at hmp
  exact hmp

theorem shearFullProfile_memLp_of_reduced {p : ENNReal}
    {g : Vec2 × ℝ → ℝ} (hg : MemLp g p volume) :
    MemLp (fun z : ParabolicPoint => g (shearCoordinateEquiv z).2) p
      (volume.restrict shearPassiveSlab) := by
  have hprod : MemLp (fun y : ℝ × (Vec2 × ℝ) => g y.2) p
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume : Measure (Vec2 × ℝ))) := by
    exact hg.comp_snd (volume.restrict (Icc (-1 : ℝ) 1))
  exact hprod.comp_measurePreserving shearCoordinateEquiv_measurePreserving_on_slab

theorem spaceTimeSet_subset_shearPassiveSlab_of_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    spaceTimeSet Ω' J ⊆ shearPassiveSlab := by
  intro z hz
  rcases hz with ⟨hx, ht⟩
  have hxcl : z.1 ∈ closure Ω' := subset_closure hx
  have hxball : z.1 ∈ vec3Ball 0 1 := hbox.2.2.1 hxcl
  have hn : vec3EuclideanNorm z.1 < 1 := by
    simpa [vec3Ball] using hxball
  have hcoord : |z.1 2| < 1 :=
    (abs_apply_le_vec3EuclideanNorm z.1 2).trans_lt hn
  change z.1 2 ∈ Icc (-1 : ℝ) 1
  rcases abs_lt.mp hcoord with ⟨hl, hu⟩
  exact ⟨le_of_lt hl, le_of_lt hu⟩

theorem shearFullProfile_memLp_of_reduced_on_localBox {p : ENNReal}
    {g : Vec2 × ℝ → ℝ} (hg : MemLp g p volume)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    MemLp (fun z : ParabolicPoint => g (shearCoordinateEquiv z).2) p
      (volume.restrict (spaceTimeSet Ω' J)) := by
  apply MemLp.mono_measure
    (Measure.restrict_mono (spaceTimeSet_subset_shearPassiveSlab_of_localBox hbox)
      (le_refl volume))
  exact shearFullProfile_memLp_of_reduced hg

end CKN
