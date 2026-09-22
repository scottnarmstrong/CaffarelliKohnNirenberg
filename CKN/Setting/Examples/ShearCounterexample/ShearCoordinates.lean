-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

/-! # Measure-preserving coordinates separating the passive shear variable. -/
set_option autoImplicit false
open MeasureTheory
open CKN.Foundation.Parabolic
namespace CKN
abbrev Vec2 := Fin 2 → ℝ
open CKN.Foundation.Parabolic
def shearSpatialCoordinateEquiv : Vec3 ≃ᵐ ℝ × Vec2 :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
def shearCoordinateEquiv : ParabolicPoint ≃ᵐ ℝ × (Vec2 × ℝ) :=
  (shearSpatialCoordinateEquiv.prodCongr (MeasurableEquiv.refl ℝ)).trans
    MeasurableEquiv.prodAssoc
theorem shearCoordinateEquiv_measurePreserving :
    MeasurePreserving shearCoordinateEquiv volume volume := by
  have hsp : MeasurePreserving shearSpatialCoordinateEquiv volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have hid : MeasurePreserving (id : ℝ → ℝ) volume volume := MeasureTheory.MeasurePreserving.id volume
  have hp0 := hsp.prod hid
  have hp : MeasurePreserving
      (shearSpatialCoordinateEquiv.prodCongr (MeasurableEquiv.refl ℝ)) volume volume := by
    change MeasurePreserving (Prod.map shearSpatialCoordinateEquiv id) volume volume
    simpa only [Measure.volume_eq_prod] using hp0
  have ha : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((ℝ × Vec2) × ℝ) ≃ᵐ (ℝ × (Vec2 × ℝ)))
      volume volume := MeasureTheory.volume_preserving_prodAssoc
  exact ha.comp hp
theorem shearCoordinateEquiv_apply (z : ParabolicPoint) :
    shearCoordinateEquiv z =
      (z.1 2, ((fun i : Fin 2 => z.1 i.castSucc), z.2)) := by
  change (z.1 2, ((fun i : Fin 2 => z.1 ((2 : Fin 3).succAbove i)), z.2)) = _
  congr 2
  funext i
  change z.1 ((Fin.last 2).succAbove i) = z.1 i.castSucc
  rw [Fin.succAbove_last]
end CKN
