-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.ScalingInvarianceS3S4

/-!
# Faithful local-energy scaling

This file proves the local-energy change-of-variables display used in the proof
of parabolic scaling invariance.

## Main result

- `s4_rescale_integrals_iff`: all six local-energy quantities scale by
  `μ⁻¹`, and the original and rescaled local energy inequalities are equivalent.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology Pointwise
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

set_option autoImplicit false

noncomputable section

namespace CKN

private def s4ScalingHomeomorph (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    ParabolicPoint ≃ₜ ParabolicPoint :=
  (parabolicHomeomorph.trans (Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft z₀.1))
    ((Homeomorph.smulOfNeZero (μ ^ 2) (sq_pos_of_pos hμ).ne').trans
      (Homeomorph.addLeft z₀.2)))).trans parabolicHomeomorph.symm

private theorem s4ScalingHomeomorph_apply (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) :
    ⇑(s4ScalingHomeomorph μ hμ z₀) = scalingParabolic μ z₀ := by
  funext z
  simp [s4ScalingHomeomorph, scalingParabolic, parabolicHomeomorph_apply,
    parabolicTranslate, parabolicScale]
  rfl

private theorem integral_comp_scaling_s4 (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (F : ParabolicPoint → ℝ) :
    ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I),
      F (scalingParabolic μ z₀ z) =
      (ENNReal.ofReal (μ⁻¹ ^ 5)).toReal * ∫ z in spaceTimeSet Ω I, F z := by
  have hmap := map_scalingParabolic_restrict hμ z₀ hΩ hI
  have hmap' : Measure.map (s4ScalingHomeomorph μ hμ z₀)
      (volume.restrict
        (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) =
      ENNReal.ofReal (μ⁻¹ ^ 5) • volume.restrict (spaceTimeSet Ω I) := by
    simpa only [s4ScalingHomeomorph_apply] using hmap
  have hchange := (s4ScalingHomeomorph μ hμ z₀).measurableEmbedding.integral_map
    (μ := volume.restrict
      (spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I))) F
  rw [hmap'] at hchange
  rw [integral_smul_measure] at hchange
  simpa [s4ScalingHomeomorph_apply, Function.comp_def, smul_eq_mul] using hchange.symm

private theorem integral_s4_scaled (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    {F G : ParabolicPoint → ℝ}
    (hpoint : ∀ z, G z = μ ^ 4 * F (scalingParabolic μ z₀ z)) :
    ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I), G z =
      μ⁻¹ * ∫ z in spaceTimeSet Ω I, F z := by
  calc
    ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I), G z =
        ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I),
          μ ^ 4 * F (scalingParabolic μ z₀ z) := by
            apply integral_congr_ae
            exact Eventually.of_forall hpoint
    _ = μ ^ 4 * ∫ z in spaceTimeSet (rescaledSpace μ z₀.1 Ω)
        (rescaledTime μ z₀.2 I), F (scalingParabolic μ z₀ z) := by
          rw [integral_const_mul]
    _ = μ ^ 4 * ((ENNReal.ofReal (μ⁻¹ ^ 5)).toReal *
        ∫ z in spaceTimeSet Ω I, F z) := by
          rw [integral_comp_scaling_s4 μ hμ z₀ hΩ hI F]
    _ = μ⁻¹ * ∫ z in spaceTimeSet Ω I, F z := by
          rw [ENNReal.toReal_ofReal (le_of_lt (pow_pos (inv_pos.mpr hμ) 5))]
          have hcoeff : μ ^ 4 * (μ⁻¹ ^ 5) = μ⁻¹ := by
            field_simp [hμ.ne']
          rw [← mul_assoc, hcoeff]

/-- The local-energy integrals transform with the paper's factor `μ⁻¹`, and
the local energy inequality is equivalent before and after parabolic rescaling. -/
theorem s4_rescale_integrals_iff {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I) (z₀ : ParabolicPoint)
    {μ : ℝ} (hμ : 0 < μ) (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I)) :
    let ψhat : Vec3 × ℝ → ℝ := fun w => ψ (μ⁻¹ • (w.1 - z₀.1),
      (w.2 - z₀.2) / μ ^ 2)
    let Oμ : Set ParabolicPoint :=
      spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I)
    let uμ := rescaleVelocity μ z₀ u
    let pμ := rescalePressure μ z₀ p
    let fμ := rescaleForce μ z₀ f
    ((∫ z in Oμ, spatialGradientSq uμ (rescaleGradient μ z₀ Du) z * ψ z) =
        μ⁻¹ * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψhat z) ∧
    ((∫ z in Oμ, (vec3EuclideanNorm (uμ z)) ^ 2 *
        (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)) =
      μ⁻¹ * ∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (u z)) ^ 2 *
        (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)) ∧
    ((∫ z in Oμ, (vec3EuclideanNorm (uμ z)) ^ 2 *
        ∑ i, uμ z i * spatialPartial ψ i z) =
      μ⁻¹ * ∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (u z)) ^ 2 *
        ∑ i, u z i * spatialPartial ψhat i z) ∧
    ((∫ z in Oμ, pμ z * ∑ i, uμ z i * spatialPartial ψ i z) =
      μ⁻¹ * ∫ z in spaceTimeSet Ω I, p z * ∑ i, u z i * spatialPartial ψhat i z) ∧
    ((∫ z in Oμ, (∑ i, fμ z i * uμ z i) * ψ z) =
      μ⁻¹ * ∫ z in spaceTimeSet Ω I, (∑ i, f z i * u z i) * ψhat z) ∧
    ((2 * ∫ z in Oμ, spatialGradientSq uμ (rescaleGradient μ z₀ Du) z * ψ z ≤
        ∫ z in Oμ, (vec3EuclideanNorm (uμ z)) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
          + ((vec3EuclideanNorm (uμ z)) ^ 2 + 2 * pμ z) *
            ∑ i, uμ z i * spatialPartial ψ i z
          + 2 * (∑ i, fμ z i * uμ z i) * ψ z) ↔
      (2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψhat z ≤
        ∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (u z)) ^ 2 *
          (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)
          + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψhat i z
          + 2 * (∑ i, f z i * u z i) * ψhat z)) := by
  intro ψhat Oμ uμ pμ fμ
  have hψhat_comp : ψhat = ψ ∘ (fun w : Vec3 × ℝ =>
      (μ⁻¹ • (w.1 - z₀.1), (μ ^ 2)⁻¹ * (w.2 - z₀.2))) := by
    funext w
    apply congrArg ψ
    apply Prod.ext
    · rfl
    · dsimp [ψhat]
      field_simp [hμ.ne']
  have heval : ∀ z, ψhat (scalingParabolic μ z₀ z) = ψ z := by
    intro z
    simp [ψhat, scalingParabolic, parabolicTranslate, parabolicScale, hμ.ne']
    rfl
  have hsp : ∀ i z,
      spatialPartial ψhat i (scalingParabolic μ z₀ z) =
        μ⁻¹ * spatialPartial ψ i z := by
    intro i z
    rw [hψhat_comp]
    exact spatialPartial_pullback μ hμ z₀ hψ.1 i z
  have ht : ∀ z,
      timePartial ψhat (scalingParabolic μ z₀ z) =
        (μ ^ 2)⁻¹ * timePartial ψ z := by
    intro z
    rw [hψhat_comp]
    exact timePartial_pullback μ hμ z₀ hψ.1 z
  have hss : ∀ i j z,
      spatialSecondPartial ψhat i j (scalingParabolic μ z₀ z) =
        (μ ^ 2)⁻¹ * spatialSecondPartial ψ i j z := by
    intro i j z
    rw [hψhat_comp]
    exact spatialSecondPartial_pullback μ hμ z₀ hψ.1 i j z
  have hsp' : ∀ i z,
      spatialPartial ψ i z =
        μ * spatialPartial ψhat i (scalingParabolic μ z₀ z) := by
    intro i z
    rw [hsp i z]
    field_simp [hμ.ne']
  have ht' : ∀ z,
      timePartial ψ z =
        μ ^ 2 * timePartial ψhat (scalingParabolic μ z₀ z) := by
    intro z
    rw [ht z]
    field_simp [pow_ne_zero 2 hμ.ne']
  have hss' : ∀ i j z,
      spatialSecondPartial ψ i j z =
        μ ^ 2 * spatialSecondPartial ψhat i j (scalingParabolic μ z₀ z) := by
    intro i j z
    rw [hss i j z]
    field_simp [pow_ne_zero 2 hμ.ne']
  have hnorm : ∀ z,
      vec3EuclideanNorm (uμ z) =
        μ * vec3EuclideanNorm (u (scalingParabolic μ z₀ z)) := by
    intro z
    change vec3EuclideanNorm (μ • u (scalingParabolic μ z₀ z)) = _
    rw [vec3EuclideanNorm_smul, abs_of_pos hμ]
  have hvel : ∀ i z, uμ z i = μ * u (scalingParabolic μ z₀ z) i := by
    intro i z
    simp [uμ, rescaleVelocity, scalingParabolic, parabolicTranslate, parabolicScale,
      Pi.smul_apply, smul_eq_mul]
  have hpres : ∀ z, pμ z = μ ^ 2 * p (scalingParabolic μ z₀ z) := by
    intro z
    simp [pμ, rescalePressure, scalingParabolic, parabolicTranslate, parabolicScale]
  have hforce : ∀ i z,
      fμ z i = μ ^ 3 * f (scalingParabolic μ z₀ z) i := by
    intro i z
    simp [fμ, rescaleForce, scalingParabolic, parabolicTranslate, parabolicScale,
      Pi.smul_apply, smul_eq_mul]
  have hgrad : ∀ z,
      spatialGradientSq uμ (rescaleGradient μ z₀ Du) z =
        μ ^ 4 * spatialGradientSq u Du
          (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)) := by
    intro z
    simp only [spatialGradientSq, rescaleGradient, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsecondSum : ∀ z,
      (∑ i, spatialSecondPartial ψ i i z) =
        μ ^ 2 * ∑ i, spatialSecondPartial ψhat i i (scalingParabolic μ z₀ z) := by
    intro z
    calc
      (∑ i, spatialSecondPartial ψ i i z) =
          ∑ i, μ ^ 2 * spatialSecondPartial ψhat i i (scalingParabolic μ z₀ z) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hss' i i z
      _ = _ := by rw [Finset.mul_sum]
  have htimeLap : ∀ z,
      timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z =
        μ ^ 2 * (timePartial ψhat (scalingParabolic μ z₀ z) +
          ∑ i, spatialSecondPartial ψhat i i (scalingParabolic μ z₀ z)) := by
    intro z
    rw [ht' z, hsecondSum z]
    ring
  have hconvSum : ∀ z,
      (∑ i, uμ z i * spatialPartial ψ i z) =
        μ ^ 2 * ∑ i, u (scalingParabolic μ z₀ z) i *
          spatialPartial ψhat i (scalingParabolic μ z₀ z) := by
    intro z
    calc
      (∑ i, uμ z i * spatialPartial ψ i z) =
          ∑ i, μ ^ 2 * (u (scalingParabolic μ z₀ z) i *
            spatialPartial ψhat i (scalingParabolic μ z₀ z)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hvel i z, hsp' i z]
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hforceSum : ∀ z,
      (∑ i, fμ z i * uμ z i) =
        μ ^ 4 * ∑ i, f (scalingParabolic μ z₀ z) i *
          u (scalingParabolic μ z₀ z) i := by
    intro z
    calc
      (∑ i, fμ z i * uμ z i) =
          ∑ i, μ ^ 4 * (f (scalingParabolic μ z₀ z) i *
            u (scalingParabolic μ z₀ z) i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hforce i z, hvel i z]
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hDpoint : ∀ z,
      spatialGradientSq uμ (rescaleGradient μ z₀ Du) z * ψ z =
        μ ^ 4 * (spatialGradientSq u Du (scalingParabolic μ z₀ z) *
          ψhat (scalingParabolic μ z₀ z)) := by
    intro z
    rw [hgrad z]
    have hT : parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z) =
        scalingParabolic μ z₀ z := by
      rfl
    rw [hT, heval z]
    ring
  have hEpoint : ∀ z,
      (vec3EuclideanNorm (uμ z)) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) =
        μ ^ 4 * ((vec3EuclideanNorm (u (scalingParabolic μ z₀ z))) ^ 2 *
          (timePartial ψhat (scalingParabolic μ z₀ z) +
            ∑ i, spatialSecondPartial ψhat i i (scalingParabolic μ z₀ z))) := by
    intro z
    rw [hnorm z, htimeLap z]
    ring
  have hCpoint : ∀ z,
      (vec3EuclideanNorm (uμ z)) ^ 2 *
          (∑ i, uμ z i * spatialPartial ψ i z) =
        μ ^ 4 * ((vec3EuclideanNorm (u (scalingParabolic μ z₀ z))) ^ 2 *
          (∑ i, u (scalingParabolic μ z₀ z) i *
            spatialPartial ψhat i (scalingParabolic μ z₀ z))) := by
    intro z
    rw [hnorm z, hconvSum z]
    ring
  have hPpoint : ∀ z,
      pμ z * (∑ i, uμ z i * spatialPartial ψ i z) =
        μ ^ 4 * (p (scalingParabolic μ z₀ z) *
          (∑ i, u (scalingParabolic μ z₀ z) i *
            spatialPartial ψhat i (scalingParabolic μ z₀ z))) := by
    intro z
    rw [hpres z, hconvSum z]
    ring
  have hFpoint : ∀ z,
      (∑ i, fμ z i * uμ z i) * ψ z =
        μ ^ 4 * ((∑ i, f (scalingParabolic μ z₀ z) i *
          u (scalingParabolic μ z₀ z) i) * ψhat (scalingParabolic μ z₀ z)) := by
    intro z
    rw [hforceSum z, heval z]
    ring
  have hRpoint : ∀ z,
      (vec3EuclideanNorm (uμ z)) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
        + ((vec3EuclideanNorm (uμ z)) ^ 2 + 2 * pμ z) *
            ∑ i, uμ z i * spatialPartial ψ i z
        + 2 * (∑ i, fμ z i * uμ z i) * ψ z =
      μ ^ 4 * ((vec3EuclideanNorm (u (scalingParabolic μ z₀ z))) ^ 2 *
          (timePartial ψhat (scalingParabolic μ z₀ z) +
            ∑ i, spatialSecondPartial ψhat i i (scalingParabolic μ z₀ z))
        + ((vec3EuclideanNorm (u (scalingParabolic μ z₀ z))) ^ 2 +
            2 * p (scalingParabolic μ z₀ z)) *
          ∑ i, u (scalingParabolic μ z₀ z) i *
            spatialPartial ψhat i (scalingParabolic μ z₀ z)
        + 2 * (∑ i, f (scalingParabolic μ z₀ z) i *
          u (scalingParabolic μ z₀ z) i) * ψhat (scalingParabolic μ z₀ z)) := by
    intro z
    rw [hnorm z, htimeLap z, hconvSum z, hpres z, hforceSum z, heval z]
    ring
  have hDint :
      ∫ z in Oμ, spatialGradientSq uμ (rescaleGradient μ z₀ Du) z * ψ z =
        μ⁻¹ * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψhat z :=
    integral_s4_scaled μ hμ z₀ hΩ hI hDpoint
  have hEint :
      ∫ z in Oμ, (vec3EuclideanNorm (uμ z)) ^ 2 *
        (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) =
        μ⁻¹ * ∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (u z)) ^ 2 *
          (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z) :=
    integral_s4_scaled μ hμ z₀ hΩ hI hEpoint
  have hCint :
      ∫ z in Oμ, (vec3EuclideanNorm (uμ z)) ^ 2 *
        (∑ i, uμ z i * spatialPartial ψ i z) =
        μ⁻¹ * ∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (u z)) ^ 2 *
          (∑ i, u z i * spatialPartial ψhat i z) :=
    integral_s4_scaled μ hμ z₀ hΩ hI hCpoint
  have hPint :
      ∫ z in Oμ, pμ z * (∑ i, uμ z i * spatialPartial ψ i z) =
        μ⁻¹ * ∫ z in spaceTimeSet Ω I, p z *
          (∑ i, u z i * spatialPartial ψhat i z) :=
    integral_s4_scaled μ hμ z₀ hΩ hI hPpoint
  have hFint :
      ∫ z in Oμ, (∑ i, fμ z i * uμ z i) * ψ z =
        μ⁻¹ * ∫ z in spaceTimeSet Ω I, (∑ i, f z i * u z i) * ψhat z :=
    integral_s4_scaled μ hμ z₀ hΩ hI hFpoint
  have hRint :
      ∫ z in Oμ,
        (vec3EuclideanNorm (uμ z)) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
          + ((vec3EuclideanNorm (uμ z)) ^ 2 + 2 * pμ z) *
              ∑ i, uμ z i * spatialPartial ψ i z
          + 2 * (∑ i, fμ z i * uμ z i) * ψ z =
        μ⁻¹ * ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψhat i z
            + 2 * (∑ i, f z i * u z i) * ψhat z :=
    integral_s4_scaled μ hμ z₀ hΩ hI hRpoint
  refine ⟨hDint, hEint, hCint, hPint, hFint, ?_⟩
  constructor
  · intro h
    rw [hDint, hRint] at h
    have h' : μ⁻¹ * (2 *
        ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψhat z) ≤
        μ⁻¹ * ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψhat i z
            + 2 * (∑ i, f z i * u z i) * ψhat z := by
      calc
        _ = 2 * (μ⁻¹ *
            ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψhat z) := by ring
        _ ≤ _ := h
    have h'' :
        (2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψhat z) * μ⁻¹ ≤
        (∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψhat i z
            + 2 * (∑ i, f z i * u z i) * ψhat z) * μ⁻¹ := by
      calc
        _ = μ⁻¹ * (2 *
            ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψhat z) := by ring
        _ ≤ μ⁻¹ * ∫ z in spaceTimeSet Ω I,
            (vec3EuclideanNorm (u z)) ^ 2 *
                (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)
              + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                  ∑ i, u z i * spatialPartial ψhat i z
              + 2 * (∑ i, f z i * u z i) * ψhat z := h'
        _ = _ := by rw [mul_comm]
    exact (mul_le_mul_iff_left₀ (inv_pos.mpr hμ)).mp h''
  · intro h
    have h' := (mul_le_mul_iff_left₀ (inv_pos.mpr hμ)).mpr h
    have h'' : 2 * (μ⁻¹ *
        ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψhat z) ≤
        μ⁻¹ * ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψhat i z
            + 2 * (∑ i, f z i * u z i) * ψhat z := by
      calc
        _ = (2 *
            ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψhat z) * μ⁻¹ := by ring
        _ ≤ _ := h'
        _ = μ⁻¹ *
            ∫ z in spaceTimeSet Ω I,
              (vec3EuclideanNorm (u z)) ^ 2 *
                  (timePartial ψhat z + ∑ i, spatialSecondPartial ψhat i i z)
                + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                    ∑ i, u z i * spatialPartial ψhat i z
                + 2 * (∑ i, f z i * u z i) * ψhat z := by ring
    rw [hDint, hRint]
    exact h''

end CKN

end
