-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.LocalZeroMeanPairing
import CKN.Foundation.Harmonic.RadialBumpDensities
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.PeakFunction
import CKN.Foundation.Harmonic.SolidBallMeanValueOriginCore

open MeasureTheory Set Filter
open scoped Topology ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

/-!
# Solid-ball mean value property

The arbitrary-center formula follows from the origin-centered identity by translation.
-/

namespace CKN.Foundation.Harmonic

/-- The solid-ball mean value property for a harmonic function on an open set.
This is clause (i) of the interior estimate in `paper/ckn.tex`, label `ext:harmonic`. -/
theorem harmonic_solidBall_mean_value
    (U : Set Vec3) (hU : IsOpen U) (f : Vec3 → ℝ)
    (hf : ContDiffOn ℝ 2 f U)
    (hHarm : ∀ y ∈ U, CKN.spatialLaplacian f y = 0)
    (x : Vec3) (s : ℝ) (hs : 0 < s)
    (hball : closure (euclideanBall x s) ⊆ U) :
    f x = (volume (euclideanBall x s)).toReal⁻¹ *
      ∫ y in euclideanBall x s, f y := by
  let T : Vec3 → Vec3 := fun y => x + y
  let f₀ : Vec3 → ℝ := fun y => f (x + y)
  let U₀ : Set Vec3 := T ⁻¹' U
  have hTcont : ContDiff ℝ (⊤ : ℕ∞) T := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => x + y)
    exact contDiff_const.add contDiff_id
  have hTcont₂ : ContDiff ℝ 2 T := hTcont.of_le (by norm_num)
  have hf₀ : ContDiffOn ℝ 2 f₀ U₀ := by
    change ContDiffOn ℝ 2 (f ∘ T) U₀
    apply hf.comp hTcont₂.contDiffOn
    intro y hy
    exact hy
  have hU₀ : IsOpen U₀ := hU.preimage (continuous_const_add x)
  have hHarm₀ : ∀ y ∈ U₀, CKN.spatialLaplacian f₀ y = 0 := by
    intro y hy
    change CKN.spatialLaplacian (fun z => f (x + z)) y = 0
    rw [spatialLaplacian_comp_add_left]
    exact hHarm (x + y) hy
  have hBallTranslate : euclideanBall x s = T '' euclideanBall (0 : Vec3) s := by
    ext y
    constructor
    · intro hy
      refine ⟨y - x, ?_, ?_⟩
      · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
        have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hy
        simpa [sub_zero] using hy'
      · change x + (y - x) = y
        abel
    · rintro ⟨z, hz, rfl⟩
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
      have hz' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hz
      have hcancel : T z - x = z := by dsimp [T]; abel
      rw [hcancel]
      simpa [sub_zero] using hz'
  have hClosureTranslate : T '' closure (euclideanBall (0 : Vec3) s) =
      closure (euclideanBall x s) := by
    rw [hBallTranslate]
    exact (Homeomorph.addLeft x).image_closure (euclideanBall (0 : Vec3) s)
  have hBall₀U₀ : closure (euclideanBall (0 : Vec3) s) ⊆ U₀ := by
    intro y hy
    change x + y ∈ U
    apply hball
    rw [← hClosureTranslate]
    exact ⟨y, hy, rfl⟩
  have hmean₀ := harmonic_solidBall_mean_value_at_origin
    hU₀ hf₀ hHarm₀ hs hBall₀U₀
  have hpreimage : T ⁻¹' euclideanBall x s = euclideanBall (0 : Vec3) s := by
    ext y
    change x + y ∈ euclideanBall x s ↔ y ∈ euclideanBall (0 : Vec3) s
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hs,
      mem_euclideanBall_iff_vecEuclideanNorm_lt hs]
    simp
  have hvol : volume (euclideanBall x s) = volume (euclideanBall (0 : Vec3) s) := by
    have hmp := measurePreserving_add_left volume x
    calc
      volume (euclideanBall x s) = volume (T ⁻¹' euclideanBall x s) := by
        symm
        exact hmp.measure_preimage
          (measurableSet_euclideanBall x s).nullMeasurableSet
      _ = volume (euclideanBall (0 : Vec3) s) := by rw [hpreimage]
  have hB₀meas : MeasurableSet (euclideanBall (0 : Vec3) s) :=
    measurableSet_euclideanBall 0 s
  have hBxmeas : MeasurableSet (euclideanBall x s) := measurableSet_euclideanBall x s
  have hmem (y : Vec3) : y ∈ euclideanBall (0 : Vec3) s ↔
      T y ∈ euclideanBall x s := by
    rw [← hpreimage]
    rfl
  let g : Vec3 → ℝ := (euclideanBall x s).indicator f
  have hleft : ∫ y in euclideanBall (0 : Vec3) s, f₀ y = ∫ y, g (T y) := by
    calc
      ∫ y in euclideanBall (0 : Vec3) s, f₀ y =
          ∫ y, (euclideanBall (0 : Vec3) s).indicator f₀ y := by
        rw [← integral_indicator hB₀meas]
      _ = ∫ y, g (T y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ euclideanBall (0 : Vec3) s
        · have hTy : T y ∈ euclideanBall x s := (hmem y).mp hy
          simp [g, f₀, T, Set.indicator, hy, hTy]
        · have hTy : T y ∉ euclideanBall x s := fun h => hy ((hmem y).mpr h)
          simp [g, f₀, T, Set.indicator, hy, hTy]
  have hmiddle : ∫ y, g (T y) = ∫ y, g y := by
    exact (measurePreserving_add_left volume x).integral_comp
      (MeasurableEquiv.addLeft x).measurableEmbedding g
  have hright : ∫ y, g y = ∫ y in euclideanBall x s, f y := by
    dsimp [g]
    rw [integral_indicator hBxmeas]
  have htranslated : ∫ y in euclideanBall (0 : Vec3) s, f₀ y =
      ∫ y in euclideanBall x s, f y := hleft.trans (hmiddle.trans hright)
  have hmean₀' : f x = (volume (euclideanBall (0 : Vec3) s)).toReal⁻¹ *
      ∫ y in euclideanBall (0 : Vec3) s, f₀ y := by
    simpa [f₀] using hmean₀
  rw [htranslated, ← hvol] at hmean₀'
  exact hmean₀'

end CKN.Foundation.Harmonic
