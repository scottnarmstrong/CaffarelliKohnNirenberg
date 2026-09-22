-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.PkBoundsUnconditionalCore
import CKN.Setting.SliceNormBounds

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

set_option autoImplicit false
noncomputable section
namespace CKN

/-!
# Velocity slice-time essential supremum equality

This module formalizes the velocity line of `eq:slice-norm-bounds` of
`paper/ckn.tex` as an equality: the essential supremum of the time-slice energy
of `u` over the cylinder equals `ρ^(1/2) * α(z,ρ)`, because `α` is defined by
that essential supremum.
-/

/-- Paper equation `eq:slice-norm-bounds`, velocity line: the essential supremum
of the time-slice energy of `u` over the cylinder is exactly `ρ^(1/2) * α(z,ρ)`. -/
theorem velocitySliceTimeEssSup_eq_alpha
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    essSup (fun s : ℝ => ENNReal.ofReal
        ((∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
    ENNReal.ofReal (Real.sqrt ρ * alpha u z ρ) := by
  have hess_eq_raw : timeSliceEnergyEssSup z.1 z.2 ρ (fun w => vec3EuclideanNorm (u w)) =
      ENNReal.ofReal (ρ * alpha u z ρ ^ 2) :=
    sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq hsol z hρ hsub
  -- α is nonnegative because it is a power of a nonnegative quantity
  have hα_nonneg : 0 ≤ alpha u z ρ := by
    unfold alpha
    refine Real.rpow_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg) _
  have h_rho_mul_nonneg : 0 ≤ ρ * alpha u z ρ ^ 2 :=
    mul_nonneg hρ.le (sq_nonneg _)
  have h_rho_mul_nonneg : 0 ≤ ρ * alpha u z ρ ^ 2 :=
    mul_nonneg hρ.le (sq_nonneg _)
  have hpos : 0 < (1 / 2 : ℝ) := by norm_num
  -- The order isomorphism x ↦ x^(1/2) commutes with essSup
  let iso := ENNReal.orderIsoRpow (1 / 2 : ℝ) hpos
  have h_comm : iso (essSup (timeSliceBallEnergy z.1 ρ · (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))) =
      essSup (fun s : ℝ => iso (timeSliceBallEnergy z.1 ρ s
        (fun w => vec3EuclideanNorm (u w))))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
    refine iso.essSup_apply _ _ ?_ ?_ ?_ ?_
    all_goals { isBoundedDefault }
  -- On the left side, we have the essSup of timeSliceBallEnergy = ENNReal.ofReal (ρ * α²)
  have hess_eq : essSup (timeSliceBallEnergy z.1 ρ · (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
      ENNReal.ofReal (ρ * alpha u z ρ ^ 2) := by
    dsimp [timeSliceEnergyEssSup] at hess_eq_raw
    exact hess_eq_raw
  have h_left : iso (essSup (timeSliceBallEnergy z.1 ρ · (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))) =
      ENNReal.ofReal (Real.sqrt ρ * alpha u z ρ) := by
    rw [hess_eq]
    have h_sq : alpha u z ρ ^ 2 = (alpha u z ρ) ^ (2 : ℝ) := by
      norm_num [Real.rpow_natCast]
    calc
      iso (ENNReal.ofReal (ρ * alpha u z ρ ^ 2)) =
          (ENNReal.ofReal (ρ * alpha u z ρ ^ 2)) ^ (1 / 2 : ℝ) := rfl
      _ = ENNReal.ofReal ((ρ * alpha u z ρ ^ 2) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg h_rho_mul_nonneg (by norm_num)
      _ = ENNReal.ofReal ((ρ * (alpha u z ρ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by rw [h_sq]
      _ = ENNReal.ofReal (Real.sqrt ρ * alpha u z ρ) := by
        rw [Real.mul_rpow hρ.le (Real.rpow_nonneg hα_nonneg 2),
          Real.sqrt_eq_rpow, ← Real.rpow_mul hα_nonneg]
        norm_num
  -- On the right side, for a.e. s, the integrand equals iso(timeSliceBallEnergy ...)
  have h_ae_eq : (fun s : ℝ => ENNReal.ofReal
      ((∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)))
      =ᵐ[volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)]
      (fun s : ℝ => iso (timeSliceBallEnergy z.1 ρ s
        (fun w => vec3EuclideanNorm (u w)))) := by
    have hbox := pressure_box_geometry hsol hρ hsub
    obtain ⟨Ω', J, hbox', hball, htime⟩ := hbox
    have hslices := slice_memLp_ae_of_sws hsol hbox'
    have hslices' := ae_restrict_of_ae_restrict_of_subset htime hslices
    filter_upwards [hslices'] with s hs
    have huB : MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict (vec3Ball z.1 ρ)) :=
      hs.1.mono_measure (Measure.restrict_mono_set volume hball)
    have hu_int : Integrable
        (fun x : Vec3 => vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ))
        (volume.restrict (vec3Ball z.1 ρ)) := by
      have huNorm := huB.integrable_norm_rpow (by norm_num) (by norm_num)
      have hmeas : AEStronglyMeasurable (fun x : Vec3 => u (x, s))
          (volume.restrict (vec3Ball z.1 ρ)) := huB.aestronglyMeasurable
      have hnormmeas : AEStronglyMeasurable
          (fun x : Vec3 => vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ))
          (volume.restrict (vec3Ball z.1 ρ)) := by
        have hcont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
          unfold vec3EuclideanNorm; fun_prop
        have hnormmeas' : AEStronglyMeasurable
            (fun x : Vec3 => vec3EuclideanNorm (u (x, s)))
            (volume.restrict (vec3Ball z.1 ρ)) :=
          hcont.comp_aestronglyMeasurable hmeas
        exact (hnormmeas'.pow 2)
      have hbound : ∀ᵐ x ∂volume.restrict (vec3Ball z.1 ρ),
          ‖vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ)‖ ≤
          3 * ‖u (x, s)‖ ^ ENNReal.toReal 2 := by
        filter_upwards [] with x
        have hle : vec3EuclideanNorm (u (x, s)) ≤ Real.sqrt 3 * ‖u (x, s)‖ := by
          have hsq : vec3EuclideanNorm (u (x, s)) ^ 2 ≤ (Real.sqrt 3 * ‖u (x, s)‖) ^ 2 := by
            unfold vec3EuclideanNorm
            rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
              mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
            calc
              _ ≤ ∑ _i : Fin 3, ‖u (x, s)‖ ^ 2 := by
                apply Finset.sum_le_sum
                intro i _hi
                rw [← sq_abs]
                exact pow_le_pow_left₀ (norm_nonneg (u (x, s) i))
                  (norm_le_pi_norm (u (x, s)) i) 2
              _ = 3 * ‖u (x, s)‖ ^ 2 := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          exact (sq_le_sq₀ (vec3EuclideanNorm_nonneg _) (by positivity)).mp hsq
        have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
          rw [Real.sq_sqrt]; norm_num
        calc
          ‖vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ)‖ = |vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ)| :=
            rfl
          _ = (vec3EuclideanNorm (u (x, s))) ^ 2 :=
            abs_of_nonneg (pow_nonneg (vec3EuclideanNorm_nonneg _) _)
          _ ≤ (Real.sqrt 3 * ‖u (x, s)‖) ^ 2 :=
            (sq_le_sq₀ (vec3EuclideanNorm_nonneg _) (by positivity)).mpr hle
          _ = 3 * ‖u (x, s)‖ ^ 2 := by rw [mul_pow, hsqrt]
          _ = 3 * ‖u (x, s)‖ ^ ENNReal.toReal 2 := by norm_num
      exact (huNorm.const_mul (3 : ℝ)).mono' hnormmeas hbound
    have hconv := ofReal_integral_eq_lintegral_ofReal hu_int
      (Eventually.of_forall (fun x => pow_nonneg (vec3EuclideanNorm_nonneg _) _))
    have hE : timeSliceBallEnergy z.1 ρ s (fun w => vec3EuclideanNorm (u w)) =
        ENNReal.ofReal (∫ y in vec3Ball z.1 ρ,
          vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) := by
      dsimp [timeSliceBallEnergy]
      rw [hconv]
      refine lintegral_congr (fun y => ?_)
      rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _),
        ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg (u (y, s))) 2]
      norm_num [Real.rpow_natCast]
    rw [hE]
    have hint_nonneg : 0 ≤ ∫ (y : Vec3) in vec3Ball z.1 ρ,
      vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ) :=
      integral_nonneg (fun y => pow_nonneg (vec3EuclideanNorm_nonneg _) _)
    rw [← ENNReal.ofReal_rpow_of_nonneg hint_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    simp [iso, ENNReal.orderIsoRpow]
  -- Combine everything
  have h_essSup_eq : essSup (fun s : ℝ => ENNReal.ofReal
      ((∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
      essSup (fun s : ℝ => iso (timeSliceBallEnergy z.1 ρ s
        (fun w => vec3EuclideanNorm (u w))))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) :=
    essSup_congr_ae h_ae_eq
  calc
    essSup (fun s : ℝ => ENNReal.ofReal
      ((∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))
        = essSup (fun s : ℝ => iso (timeSliceBallEnergy z.1 ρ s
            (fun w => vec3EuclideanNorm (u w))))
            (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := h_essSup_eq
    _ = iso (essSup (timeSliceBallEnergy z.1 ρ · (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))) := by rw [h_comm]
    _ = ENNReal.ofReal (Real.sqrt ρ * alpha u z ρ) := h_left

end CKN
