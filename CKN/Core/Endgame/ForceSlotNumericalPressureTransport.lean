-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumericalPressureScaling
import CKN.Core.Endgame.ForceSlotNumericalNormalization
import CKN.Core.Endgame.LocalBoxRestriction
import CKN.Setting.Finiteness

/-!
# Pressure transport to the full localization collar

The selected normalized pressure gradient transports to the symmetric
physical collar. Its weak identity is required only where it is supplied
by the normalized pressure estimate.
-/

open MeasureTheory Set
open scoped Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The centre of the inverse affine parabolic transformation. -/
def forceSlotInverseCenter (a : ℝ) (b : ParabolicPoint) : ParabolicPoint :=
  (-a⁻¹ • b.1, -(a⁻¹ ^ 2) * b.2)

/-- The inverse dilation undoes the original affine transformation. -/
theorem force_slot_inverse_scaling (a : ℝ) (ha : a ≠ 0) (b w : ParabolicPoint) :
    scalingParabolic a⁻¹ (forceSlotInverseCenter a b) (scalingParabolic a b w) = w := by
  apply Prod.ext
  · change -a⁻¹ • b.1 + a⁻¹ • (b.1 + a • w.1) = w.1
    simp [smul_add, smul_smul, ha]
  · change -(a⁻¹ ^ 2) * b.2 + a⁻¹ ^ 2 * (b.2 + a ^ 2 * w.2) = w.2
    field_simp
    ring

/-- The original dilation undoes the inverse affine transformation. -/
theorem force_slot_scaling_inverse (a : ℝ) (ha : a ≠ 0) (b w : ParabolicPoint) :
    scalingParabolic a b (scalingParabolic a⁻¹ (forceSlotInverseCenter a b) w) = w := by
  apply Prod.ext
  · change b.1 + a • (-a⁻¹ • b.1 + a⁻¹ • w.1) = w.1
    simp [smul_add, smul_smul, ha]
  · change b.2 + a ^ 2 * (-(a⁻¹ ^ 2) * b.2 + a⁻¹ ^ 2 * w.2) = w.2
    field_simp
    ring

/-- A selected normalized gradient yields integrability and the weak pairing
on the entire physical collar, with its exact amplitude identity retained. -/
theorem force_slot_pressure_transport (a : ℝ) (ha : 0 < a) (z : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (p : ParabolicPoint → ℝ) (Dn : ParabolicPoint → Vec3)
    (hInt : ∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
      U ⊆ vec3Ball 0 (19 / 32) → ∀ i,
      Integrable (fun w => Dn w i) (volume.restrict (spaceTimeSet U J)))
    (hweak : ∀ i (ψ : Vec3 × ℝ → ℝ),
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport ψ ⊆ vec3Ball 0 (19 / 32) ×ˢ I →
      (∫ w : ParabolicPoint,
        rescalePressure (32 * a) (z.1, z.2 + 16 * a ^ 2) p w * spatialPartial ψ i w) =
          -(∫ w : ParabolicPoint, Dn w i * ψ w)) :
    ∃ Dp : ParabolicPoint → Vec3,
      (∀ w i, (32 * a) ^ 3 * Dp (scalingParabolic (32 * a)
        (z.1, z.2 + 16 * a ^ 2) w) i = Dn w i) ∧
      (∀ i, Integrable (fun w => Dp w i)
        (volume.restrict (Metric.ball z (4 * a)))) ∧
      (∀ i (ψ : Vec3 × ℝ → ℝ),
        ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
        tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z (4 * a) →
        (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
          -(∫ w : ParabolicPoint, Dp w i * ψ w)) := by
  let μ := 32 * a
  let b : ParabolicPoint := (z.1, z.2 + 16 * a ^ 2)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  let T := scalingParabolic μ b
  let S := scalingParabolic μ⁻¹ (forceSlotInverseCenter μ b)
  have hST (w) : S (T w) = w := force_slot_inverse_scaling μ hμ.ne' b w
  have hTS (w) : T (S w) = w := force_slot_scaling_inverse μ hμ.ne' b w
  have hSQ : ∀ w ∈ Metric.ball z (4 * a),
      S w ∈ parabolicCylinder (0 : Vec3) 0 (19 / 32) := by
    intro w hw
    obtain ⟨v, hv, heq⟩ := force_slot_collar_subset_normalized_pressure a ha z hw
    change T v = w at heq
    rw [← heq, hST]
    exact hv
  let Dp : ParabolicPoint → Vec3 := fun w i => μ⁻¹ ^ 2 * μ⁻¹ * Dn (S w) i
  refine ⟨Dp, ?_, ?_, ?_⟩
  · intro w i
    change μ ^ 3 * (μ⁻¹ ^ 2 * μ⁻¹ * Dn (S (T w)) i) = Dn w i
    rw [hST]
    field_simp
  · obtain ⟨U, J, hbox, hQbox⟩ := exists_localBox_of_closure_subset hΩ hI
      (by norm_num : (0 : ℝ) < 1) hdom
    have hb := localBox_inter_spatial_open hbox (isOpen_vec3Ball (0 : Vec3) (19 / 32))
    have hi := hInt _ J hb inter_subset_right
    have hJ : MeasurableSet J := hbox.2.2.2.1.measurableSet
    have ht := force_slot_pressure_integrable_scaling μ⁻¹ (μ⁻¹ ^ 2)
      (inv_pos.mpr hμ) (forceSlotInverseCenter μ b) hb.1.measurableSet hJ Dn hi
    intro i
    apply (ht i).mono_measure
    apply Measure.restrict_mono_set
    intro w hw
    have hq := hSQ w hw
    have hj := hQbox (parabolicCylinder_mono (by norm_num) (by norm_num) hq)
    exact ⟨⟨hj.1, hq.1⟩, hj.2⟩
  · intro i ψ hψ hs
    have hs' : tsupport ψ ⊆ (fun w : Vec3 × ℝ =>
        ((forceSlotInverseCenter μ b).1 + μ⁻¹ • w.1,
          (forceSlotInverseCenter μ b).2 + μ⁻¹ ^ 2 * w.2)) ⁻¹'
          (vec3Ball 0 (19 / 32) ×ˢ I) := by
      intro w hw
      have hq := hSQ (parabolicHomeomorph.symm w) (hs hw)
      exact ⟨hq.1, (hdom (subset_closure
        (parabolicCylinder_mono (by norm_num) (by norm_num) hq))).2⟩
    have ht := force_slot_weak_pressure_gradient_scaling μ⁻¹ (μ⁻¹ ^ 2)
      (inv_pos.mpr hμ) (forceSlotInverseCenter μ b) _
      (rescalePressure μ b p) Dn hweak i ψ hψ hs'
    have hp (w : ParabolicPoint) : μ⁻¹ ^ 2 * rescalePressure μ b p (S w) = p w := by
      change μ⁻¹ ^ 2 * (μ ^ 2 * p (T (S w))) = p w
      rw [hTS]
      field_simp
    change (∫ w : ParabolicPoint,
      (μ⁻¹ ^ 2 * rescalePressure μ b p (S w)) * spatialPartial ψ i w) =
      -(∫ w : ParabolicPoint, Dp w i * ψ w) at ht
    simpa only [hp] using ht

end CKN.Core.Endgame
