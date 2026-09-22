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

/-- Identify the velocity-gradient spatial slice `eLpNorm` with the explicit real integral
of `spatialGradientSq` used by the scale quantity `beta`. For almost every time `s` in the
parabolic cylinder, the `L²` norm of the velocity gradient on the spatial ball
equals the `ENNReal.ofReal` of the real power integral. -/
theorem gradientSpatialSliceNorm_eq_ofReal_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      gradientSpatialSliceNorm Du z.1 ρ s =
        ENNReal.ofReal ((∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s)) ^ (1 / 2 : ℝ)) := by
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hslices := slice_memLp_ae_of_sws hsol hbox
  have hslices' := ae_restrict_of_ae_restrict_of_subset htime hslices
  filter_upwards [hslices'] with s hs
  rcases hs with ⟨_, hDu_memLp⟩
  have hDu_meas : AEStronglyMeasurable (fun x : Vec3 => Du (x, s))
      (volume.restrict (vec3Ball z.1 ρ)) :=
    hDu_memLp.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hball)
  have h_grad_meas : AEStronglyMeasurable
      (fun y : Vec3 => Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have hcont : Continuous (fun v : Fin 3 → Vec3 => ∑ i, ∑ j, (v i j) ^ (2 : ℕ)) := by
      fun_prop
    have hm := hcont.comp_aestronglyMeasurable hDu_meas
    have hm_sq : AEStronglyMeasurable (fun x : Vec3 => spatialGradientSq u Du (x, s))
        (volume.restrict (vec3Ball z.1 ρ)) := by
      simpa [spatialGradientSq, Function.comp_def] using hm
    have h_nonneg : 0 ≤ᵐ[volume.restrict (vec3Ball z.1 ρ)]
        fun x : Vec3 => spatialGradientSq u Du (x, s) :=
      Filter.Eventually.of_forall (fun x => by
        unfold spatialGradientSq; positivity)
    have h_sqrt_cont : Continuous (fun t : ℝ => Real.sqrt t) :=
      Real.continuous_sqrt
    have h_sqrt_meas : AEStronglyMeasurable (fun x : Vec3 =>
        Real.sqrt (spatialGradientSq u Du (x, s)))
        (volume.restrict (vec3Ball z.1 ρ)) :=
      h_sqrt_cont.comp_aestronglyMeasurable hm_sq
    have h_eq : (fun y : Vec3 => Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2)) =
        (fun y : Vec3 => Real.sqrt (spatialGradientSq u Du (y, s))) := by
      ext y
      congr 1
      unfold spatialGradientSq vec3EuclideanNorm
      simp_rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pow_two_nonneg _))]
    simpa [h_eq] using h_sqrt_meas
  have hDu_sq_int : Integrable (fun x : Vec3 => (‖Du (x, s)‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have hmem := hDu_memLp.mono_measure (Measure.restrict_mono_set volume hball)
    exact (memLp_two_iff_integrable_sq_norm hDu_meas).mp hmem
  have h_sq_bound : ∀ x : Vec3, spatialGradientSq u Du (x, s) ≤ 9 * ((‖Du (x, s)‖ : ℝ) ^ 2) := by
    intro x
    have h := pressure_spatialGradientSq_le u Du (x, s)
    simpa [sq] using h
  have h_nonneg_sq : 0 ≤ᵐ[volume.restrict (vec3Ball z.1 ρ)]
      fun x : Vec3 => spatialGradientSq u Du (x, s) :=
    Filter.Eventually.of_forall (fun x => by
      unfold spatialGradientSq
      positivity)
  have hmeas_sq : AEStronglyMeasurable (fun x : Vec3 => spatialGradientSq u Du (x, s))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have hcont : Continuous (fun v : Fin 3 → Vec3 => ∑ i, ∑ j, (v i j) ^ (2 : ℕ)) := by
      fun_prop
    have hm := hcont.comp_aestronglyMeasurable hDu_meas
    simpa [spatialGradientSq, Function.comp_def] using hm
  have h_bound_int : Integrable (fun x : Vec3 => 9 * ((‖Du (x, s)‖ : ℝ) ^ 2))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have := hDu_sq_int.const_mul 9
    simpa [sq] using this
  have h_sq_int : Integrable (fun x : Vec3 => spatialGradientSq u Du (x, s))
      (volume.restrict (vec3Ball z.1 ρ)) :=
    h_bound_int.mono_nonneg hmeas_sq h_nonneg_sq (by
      filter_upwards [] with x
      exact h_sq_bound x)
  have hconv := ofReal_integral_eq_lintegral_ofReal h_sq_int h_nonneg_sq
  have h_nonneg_int : 0 ≤ ∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s) :=
    integral_nonneg_of_ae h_nonneg_sq
  unfold gradientSpatialSliceNorm
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top h_grad_meas]
  have h_toReal_two : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h_toReal_two]
  have h_enorm_eq : ∀ y : Vec3,
      ‖Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2)‖ₑ =
      ENNReal.ofReal (Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2)) := by
    intro y
    rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
  simp_rw [h_enorm_eq]
  have h_ofReal_pow : ∀ y : Vec3,
      (ENNReal.ofReal
        (Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2))) ^ (2 : ℝ) =
      ENNReal.ofReal ((Real.sqrt
        (∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2)) ^ (2 : ℝ)) := by
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [h_ofReal_pow]
  have h_sqrt_sq_eq : ∀ y : Vec3,
      (Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2)) ^ (2 : ℝ) =
      spatialGradientSq u Du (y, s) := by
    intro y
    have h_nonneg_inner : 0 ≤ ∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2 := by
      refine Finset.sum_nonneg (fun i _ => ?_)
      apply pow_two_nonneg
    have h_sum_eq : ∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2 =
        spatialGradientSq u Du (y, s) := by
      unfold spatialGradientSq vec3EuclideanNorm
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => pow_two_nonneg _))]
    calc
      (Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2)) ^ (2 : ℝ) =
          (Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2)) ^ (2 : ℕ) := by
        norm_num [Real.rpow_natCast]
      _ = ∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2 := by
        rw [Real.sq_sqrt h_nonneg_inner]
      _ = spatialGradientSq u Du (y, s) := h_sum_eq
  simp_rw [h_sqrt_sq_eq]
  rw [← hconv]
  rw [ENNReal.ofReal_rpow_of_nonneg h_nonneg_int (by norm_num : (0 : ℝ) ≤ 1 / 2)]

end CKN
