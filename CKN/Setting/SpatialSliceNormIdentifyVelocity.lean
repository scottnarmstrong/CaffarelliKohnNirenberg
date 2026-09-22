-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SpatialSliceNorms
import CKN.Setting.SliceNormBounds
import CKN.Pressure.PkBoundsUnconditionalCore

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Identify the velocity spatial slice `eLpNorm` with the explicit real integral
used by the scale quantity `alpha`.  For almost every time `s` in the
parabolic cylinder, the `L²` norm of the velocity on the spatial ball
equals the `ENNReal.ofReal` of the real power integral. -/
theorem velocitySpatialSliceNorm_eq_ofReal_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      velocitySpatialSliceNorm u z.1 ρ s =
        ENNReal.ofReal
          ((∫ y in vec3Ball z.1 ρ,
            vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) := by
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hslices := slice_memLp_ae_of_sws hsol hbox
  have hslices' := ae_restrict_of_ae_restrict_of_subset htime hslices
  filter_upwards [hslices'] with s hs
  rcases hs with ⟨hu_memLp, _⟩
  have hu_meas : AEStronglyMeasurable (fun x : Vec3 => u (x, s))
      (volume.restrict (vec3Ball z.1 ρ)) :=
    hu_memLp.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hball)
  have hnorm_meas : AEStronglyMeasurable
      (fun y : Vec3 => vec3EuclideanNorm (u (y, s)))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have hcont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact hcont.comp_aestronglyMeasurable hu_meas
  have hu_sq_int : Integrable (fun x : Vec3 => (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have hmem := hu_memLp.mono_measure (Measure.restrict_mono_set volume hball)
    have hintegrable_sq := (memLp_two_iff_integrable_sq_norm hu_meas).mp hmem
    -- hintegrable_sq : Integrable (fun x => ‖u (x, s)‖ ^ 2) (volume.restrict ...)
    -- The norm on Vec3 is the sup norm; vec3EuclideanNorm is the Euclidean norm.
    -- They are equivalent: ‖v‖ ≤ vec3EuclideanNorm v ≤ √3 * ‖v‖.
    -- So integrability transfers by comparison.
    have h_bound : ∀ x : Vec3, (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ) ≤
        3 * (‖u (x, s)‖ ^ 2) := by
      intro x
      have hle : vec3EuclideanNorm (u (x, s)) ≤ Real.sqrt 3 * ‖u (x, s)‖ :=
        vec3EuclideanNorm_le_sqrt_three_mul_norm (u (x, s))
      have h_nonneg_norm : 0 ≤ ‖u (x, s)‖ := norm_nonneg _
      have h_nonneg_eucl : 0 ≤ vec3EuclideanNorm (u (x, s)) := vec3EuclideanNorm_nonneg _
      calc
        (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ) = (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ) := by
          norm_num [Real.rpow_natCast]
        _ ≤ (Real.sqrt 3 * ‖u (x, s)‖) ^ (2 : ℝ) :=
          Real.rpow_le_rpow h_nonneg_eucl hle (by norm_num : (0 : ℝ) ≤ 2)
        _ = (Real.sqrt 3) ^ (2 : ℝ) * (‖u (x, s)‖ ^ (2 : ℝ)) := by
          rw [Real.mul_rpow (Real.sqrt_nonneg _) h_nonneg_norm]
        _ = (3 : ℝ) * (‖u (x, s)‖ ^ (2 : ℝ)) := by
          have hsq : (Real.sqrt 3) ^ (2 : ℝ) = (3 : ℝ) := by norm_num
          rw [hsq]
        _ = (3 : ℝ) * (‖u (x, s)‖ ^ (2 : ℕ)) := by norm_num [Real.rpow_natCast]
    -- Now use integrability of ‖u‖^2 and the bound to get integrability of vec3EuclideanNorm^2
    have hmeas : AEStronglyMeasurable (fun x : Vec3 => (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ))
        (volume.restrict (vec3Ball z.1 ρ)) := by
      have hcont : Continuous (fun (v : Vec3) => (vec3EuclideanNorm v) ^ (2 : ℕ)) := by
        unfold vec3EuclideanNorm
        fun_prop
      exact hcont.comp_aestronglyMeasurable hu_meas
    have h_nonneg_target : 0 ≤ᵐ[volume.restrict (vec3Ball z.1 ρ)]
        fun x : Vec3 => (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ) :=
      Filter.Eventually.of_forall (fun x => pow_nonneg (vec3EuclideanNorm_nonneg _) _)
    refine Integrable.mono_nonneg (hintegrable_sq.const_mul 3) hmeas h_nonneg_target ?_
    filter_upwards [] with x
    exact h_bound x
  have h_nonneg : 0 ≤ᵐ[volume.restrict (vec3Ball z.1 ρ)]
      fun y => (vec3EuclideanNorm (u (y, s))) ^ (2 : ℕ) :=
    Filter.Eventually.of_forall (fun y => pow_nonneg (vec3EuclideanNorm_nonneg _) _)
  have hconv := ofReal_integral_eq_lintegral_ofReal hu_sq_int h_nonneg
  unfold velocitySpatialSliceNorm
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top hnorm_meas]
  have h_toReal_two : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h_toReal_two]
  rw [show (1 / (2 : ℝ)) = ((1 : ℝ) / 2) by norm_num]
  have h_enorm_eq : ∀ y : Vec3, ‖vec3EuclideanNorm (u (y, s))‖ₑ =
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) := by
    intro y
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
  simp_rw [h_enorm_eq]
  have h_ofReal_pow : ∀ y : Vec3, (ENNReal.ofReal (vec3EuclideanNorm (u (y, s)))) ^ (2 : ℝ) =
      ENNReal.ofReal ((vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) := by
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [h_ofReal_pow]
  have h_pow_eq : ∀ y : Vec3, (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) =
      (vec3EuclideanNorm (u (y, s))) ^ (2 : ℕ) := by
    intro y
    norm_num [Real.rpow_natCast]
  simp_rw [h_pow_eq]
  rw [← hconv]
  rw [ENNReal.ofReal_rpow_of_nonneg]
  · exact integral_nonneg_of_ae h_nonneg
  · norm_num

end CKN
