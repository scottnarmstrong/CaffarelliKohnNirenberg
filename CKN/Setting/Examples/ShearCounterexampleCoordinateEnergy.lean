-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.


import CKN.Setting.Examples.ShearCounterexample.ShearCoordinates
import CKN.Setting.Examples.ShearCounterexample.AmbientLp
import CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! # A passive-coordinate estimate for the rough shear energy. -/


set_option autoImplicit false
noncomputable section

open CKN.Foundation.Parabolic Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace CKN

/-- A reduced nonnegative density gains the length of the passive shear coordinate when it is
integrated over a centered parabolic cylinder. -/
theorem shear_lintegral_cylinder_le_reduced {r : ℝ}
    (hr : 0 < r) (g : Vec2 × ℝ → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        g (shearCoordinateEquiv z).2 ≤
      ENNReal.ofReal (2 * r) * ∫⁻ y, g y := by
  let S : Set (ℝ × (Vec2 × ℝ)) := Icc (-r) r ×ˢ Set.univ
  have hS : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  have hpre : shearCoordinateEquiv ⁻¹' S =
      {z : ParabolicPoint | z.1 2 ∈ Icc (-r) r} := by
    ext z
    simp [S, shearCoordinateEquiv_apply]
  have hsub : parabolicCylinder (0 : Vec3) 0 r ⊆ shearCoordinateEquiv ⁻¹' S := by
    intro z hz
    rw [hpre]
    have hx := hz.1
    have hnorm : vec3EuclideanNorm z.1 < r := by
      simpa [vec3Ball] using hx
    have hcoord : |z.1 2| < r :=
      (abs_apply_le_vec3EuclideanNorm z.1 2).trans_lt hnorm
    exact ⟨le_of_lt (abs_lt.mp hcoord).1, le_of_lt (abs_lt.mp hcoord).2⟩
  have hmp := shearCoordinateEquiv_measurePreserving.restrict_preimage hS
  calc
    ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        g (shearCoordinateEquiv z).2 ≤
        ∫⁻ z in shearCoordinateEquiv ⁻¹' S,
          g (shearCoordinateEquiv z).2 := lintegral_mono_set hsub
    _ = ∫⁻ y in S, g y.2 := by
      exact MeasurePreserving.lintegral_comp hmp
        (f := fun y : ℝ × (Vec2 × ℝ) => g y.2)
        (hg.comp measurable_snd)
    _ = (∫⁻ s : ℝ in Icc (-r) r, (1 : ℝ≥0∞)) * ∫⁻ y : Vec2 × ℝ, g y := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
      simpa only [one_mul] using
        (lintegral_prod_mul (μ := volume.restrict (Icc (-r) r))
          (ν := volume) (f := fun _ : ℝ => (1 : ℝ≥0∞))
          (g := fun y : Vec2 × ℝ => g y)
          aemeasurable_const hg.aemeasurable)
    _ = ENNReal.ofReal (2 * r) * ∫⁻ y, g y := by
      congr 1
      rw [lintegral_const]
      rw [show (volume.restrict (Icc (-r) r)) Set.univ = volume (Icc (-r) r) by simp]
      rw [Real.volume_Icc]
      rw [show r - -r = 2 * r by ring]
      rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      have hr0 : 0 ≤ r := hr.le
      norm_num [hr0]

end CKN
