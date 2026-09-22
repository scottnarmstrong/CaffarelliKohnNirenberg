-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.InteriorGradientProducerScaling

/-! # A selected pressure gradient transported back from a dilated solution

A parabolic dilation about the space-time origin turns a suitable solution
into another suitable solution whose pressure is the dilated pressure.  A
selected weak spatial gradient of the dilated pressure on an interior ball
therefore determines a selected weak spatial gradient of the original
pressure on the correspondingly smaller interior ball.

The transported field keeps all four of the clauses in which a selected
pressure gradient is consumed: almost-everywhere measurability on the
interior product carrier, integrability on every local box inside that
carrier, the space-time weak pairing against compactly supported smooth test
functions, and a Morrey bound on the interior cylinder.  The Morrey bound
picks up the explicit finite dilation factor recorded in the statement.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Endgame

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

/-- The backward transport of a selected weak pressure gradient along a
parabolic dilation about the space-time origin.  The dilated pressure is
`rescalePressure μ originPoint p`, its selected gradient is carried by the
ball of radius `R₁'`, and the conclusion is carried by the ball of radius
`R₁`, which the dilation maps inside it. -/
theorem interior_gradient_transport
    {Ω : Set Vec3} {I : Set ℝ} {μ R₁ R₁' θ : ℝ} {KP : ℝ≥0∞}
    (hμ : 0 < μ) (hR₁ : 0 < R₁) (hR : R₁ ≤ μ * R₁')
    (hImeas : MeasurableSet I)
    (p : ParabolicPoint → ℝ) (Dn : ParabolicPoint → Vec3)
    (hAE : ∀ i, AEMeasurable (fun w => Dn w i)
      (volume.restrict (vec3Ball (0 : Vec3) R₁' ×ˢ rescaledTime μ (0 : ℝ) I)))
    (hInt : ∀ (U : Set Vec3) (J : Set ℝ),
      localBox (rescaledSpace μ (0 : Vec3) Ω) (rescaledTime μ (0 : ℝ) I) U J →
      U ⊆ vec3Ball (0 : Vec3) R₁' → ∀ i : Fin 3,
      Integrable (fun w => Dn w i) (volume.restrict (spaceTimeSet U J)))
    (hweak : ∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport ψ ⊆ vec3Ball (0 : Vec3) R₁' ×ˢ rescaledTime μ (0 : ℝ) I →
      (∫ w : ParabolicPoint,
        rescalePressure μ originPoint p w * spatialPartial ψ i w) =
        -(∫ w : ParabolicPoint, Dn w i * ψ w))
    (hN : ∀ i : Fin 3, morreyNorm (6 / 5 : ℝ) θ
      ((parabolicCylinder (0 : Vec3) 0 R₁').indicator (fun w => Dn w i)) ≤ KP) :
    ∃ Dp : ParabolicPoint → Vec3,
      (∀ i, AEMeasurable (fun z => Dp z i)
        (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I))) ∧
      (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
        U ⊆ vec3Ball (0 : Vec3) R₁ → ∀ i : Fin 3,
        Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) ∧
      (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
        tsupport ψ ⊆ vec3Ball (0 : Vec3) R₁ ×ˢ I →
        (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
          -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
      (∀ i : Fin 3, morreyNorm (6 / 5 : ℝ) θ
        ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i)) ≤
        ENNReal.ofReal |μ⁻¹ ^ 2 * μ⁻¹| *
          (ENNReal.ofReal μ⁻¹ ^ (-5 / θ : ℝ) * KP)) := by
  classical
  have hμinv : (0 : ℝ) < μ⁻¹ := inv_pos.mpr hμ
  have hR₁' : (0 : ℝ) < R₁' := by
    rcases lt_or_ge 0 R₁' with h | h
    · exact h
    · exact absurd hR (by
        have hle : μ * R₁' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ.le h
        exact not_le.mpr (lt_of_le_of_lt hle hR₁))
  have hinvR : μ⁻¹ * R₁ ≤ R₁' := by
    rw [inv_mul_le_iff₀ hμ]
    linarith only [hR]
  have hTS : ∀ w, scalingParabolic μ originPoint
      (scalingParabolic μ⁻¹ originPoint w) = w := by
    intro w
    have h := force_slot_scaling_inverse μ hμ.ne' originPoint w
    rwa [forceSlotInverseCenter_origin] at h
  have hI' : MeasurableSet (rescaledTime μ (0 : ℝ) I) := by
    refine hImeas.preimage ?_
    exact (measurable_const_add _).comp (measurable_const_mul (μ ^ 2))
  refine ⟨fun w i => μ⁻¹ ^ 2 * μ⁻¹ * Dn (scalingParabolic μ⁻¹ originPoint w) i,
    ?_, ?_, ?_, ?_⟩
  · intro i
    have hset1 : rescaledSpace μ⁻¹ (0 : Vec3) (vec3Ball (0 : Vec3) R₁') =
        vec3Ball (0 : Vec3) (μ * R₁') := by
      rw [rescaledSpace_origin_ball hμinv, inv_inv]
    have hset2 : rescaledTime μ⁻¹ (0 : ℝ) (rescaledTime μ (0 : ℝ) I) = I :=
      rescaledTime_origin_inv hμ I
    have hmap := map_scalingParabolic_restrict (μ := μ⁻¹) hμinv originPoint
      (isOpen_vec3Ball (0 : Vec3) R₁').measurableSet hI'
    simp only [originPoint_fst, originPoint_snd, hset1, hset2, inv_inv] at hmap
    rw [show spaceTimeSet (vec3Ball (0 : Vec3) R₁') (rescaledTime μ (0 : ℝ) I) =
      vec3Ball (0 : Vec3) R₁' ×ˢ rescaledTime μ (0 : ℝ) I from rfl] at hmap
    have hs := (hAE i).smul_measure (ENNReal.ofReal (μ ^ 5))
    rw [← hmap] at hs
    have hcomp := hs.comp_measurable (originScaling_measurable μ⁻¹)
    have hmono : volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I) ≤
        volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) (μ * R₁')) I) :=
      Measure.restrict_mono (Set.prod_mono (vec3Ball_mono hR) Subset.rfl) le_rfl
    exact AEMeasurable.const_mul (hcomp.mono_measure hmono) (μ⁻¹ ^ 2 * μ⁻¹)
  · intro U J hbox hsub i
    have hbox0 : localBox (rescaledSpace μ⁻¹ (0 : Vec3) (rescaledSpace μ (0 : Vec3) Ω))
        (rescaledTime μ⁻¹ (0 : ℝ) (rescaledTime μ (0 : ℝ) I)) U J := by
      rw [rescaledSpace_origin_inv hμ, rescaledTime_origin_inv hμ]
      exact hbox
    have hbox' := localBox_forward (μ := μ⁻¹) hμinv originPoint hbox0
    simp only [originPoint_fst, originPoint_snd] at hbox'
    have hsub' : scalingSpace μ⁻¹ (0 : Vec3) '' U ⊆ vec3Ball (0 : Vec3) R₁' := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : vec3EuclideanNorm (y - 0) < R₁ := hsub hy
      rw [sub_zero] at hy'
      show vec3EuclideanNorm (scalingSpace μ⁻¹ (0 : Vec3) y - 0) < R₁'
      rw [sub_zero]
      show vec3EuclideanNorm ((0 : Vec3) + μ⁻¹ • y) < R₁'
      rw [zero_add, vec3EuclideanNorm_smul, abs_of_pos hμinv]
      have hlt : μ⁻¹ * vec3EuclideanNorm y < μ⁻¹ * R₁ :=
        mul_lt_mul_of_pos_left hy' hμinv
      linarith only [hlt, hinvR]
    have hDnInt := hInt _ _ hbox' hsub'
    have hUmeas : MeasurableSet (scalingSpace μ⁻¹ (0 : Vec3) '' U) :=
      hbox'.1.measurableSet
    have hJmeas : MeasurableSet (scalingTime μ⁻¹ (0 : ℝ) '' J) :=
      hbox'.2.2.2.1.measurableSet
    have htrans := force_slot_pressure_integrable_scaling μ⁻¹ (μ⁻¹ ^ 2) hμinv
      originPoint hUmeas hJmeas Dn hDnInt i
    have hU : rescaledSpace μ⁻¹ (0 : Vec3) (scalingSpace μ⁻¹ (0 : Vec3) '' U) = U :=
      (scalingSpace_origin_injective hμinv.ne').preimage_image U
    have hJ : rescaledTime μ⁻¹ (0 : ℝ) (scalingTime μ⁻¹ (0 : ℝ) '' J) = J :=
      (scalingTime_origin_injective hμinv.ne').preimage_image J
    simp only [originPoint_fst, originPoint_snd, hU, hJ] at htrans
    exact htrans
  · intro i ψ hψ hsupp
    have hsupp' : tsupport ψ ⊆ (fun w : Vec3 × ℝ =>
        (originPoint.1 + μ⁻¹ • w.1, originPoint.2 + μ⁻¹ ^ 2 * w.2)) ⁻¹'
          (vec3Ball (0 : Vec3) R₁' ×ˢ rescaledTime μ (0 : ℝ) I) := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := hsupp hw
      constructor
      · have hw1' : vec3EuclideanNorm (w.1 - 0) < R₁ := hw1
        rw [sub_zero] at hw1'
        show vec3EuclideanNorm (originPoint.1 + μ⁻¹ • w.1 - 0) < R₁'
        rw [originPoint_fst, zero_add, sub_zero, vec3EuclideanNorm_smul,
          abs_of_pos hμinv]
        have hlt : μ⁻¹ * vec3EuclideanNorm w.1 < μ⁻¹ * R₁ :=
          mul_lt_mul_of_pos_left hw1' hμinv
        linarith only [hlt, hinvR]
      · show originPoint.2 + μ⁻¹ ^ 2 * w.2 ∈ rescaledTime μ (0 : ℝ) I
        rw [originPoint_snd, zero_add]
        show (0 : ℝ) + μ ^ 2 * (μ⁻¹ ^ 2 * w.2) ∈ I
        rw [zero_add, ← mul_assoc, show μ ^ 2 * μ⁻¹ ^ 2 = 1 by field_simp, one_mul]
        exact hw2
    have h := force_slot_weak_pressure_gradient_scaling μ⁻¹ (μ⁻¹ ^ 2) hμinv
      originPoint _ (rescalePressure μ originPoint p) Dn hweak i ψ hψ hsupp'
    have hp : ∀ w : ParabolicPoint,
        μ⁻¹ ^ 2 * rescalePressure μ originPoint p
          (scalingParabolic μ⁻¹ originPoint w) = p w := by
      intro w
      show μ⁻¹ ^ 2 * (μ ^ 2 *
        p (scalingParabolic μ originPoint (scalingParabolic μ⁻¹ originPoint w))) = p w
      rw [hTS, ← mul_assoc, show μ⁻¹ ^ 2 * μ ^ 2 = 1 by field_simp, one_mul]
    simpa only [hp] using h
  · intro i
    refine force_slot_subcarrier_scaling_le μ⁻¹ (μ⁻¹ ^ 2 * μ⁻¹) (6 / 5 : ℝ) θ KP
      hμinv (by norm_num) originPoint _ _ (fun w => Dn w i) ?_ (hN i)
    rw [originScaling_cylinder hμinv]
    exact parabolicCylinder_mono (by positivity) hinvR

end CKN.Core.Step4
