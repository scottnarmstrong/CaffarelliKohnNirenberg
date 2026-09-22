-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumericalScaling
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Numerical energy bounds for normalized fields

The pressure-gradient estimates take an integral bound on the unit cylinder.
These estimates retain the amplitude and Jacobian of the parabolic change
of variables and use the original scalar Lp bounds.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- A finite scalar Lp bound controls its power integral with the same
explicit numerical constant raised to that power. -/
theorem force_slot_power_integral_le_of_eLpNorm
    (P : ℝ) (K : ℝ≥0∞) (hP : 0 < P)
    {B : Set ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict B))
    (hN : eLpNorm f (ENNReal.ofReal P) (volume.restrict B) ≤ K) :
    (∫⁻ w in B, ENNReal.ofReal |f w| ^ P) ≤ K ^ P := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hP).ne'
    ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hP.le] at hN
  have h := ENNReal.rpow_le_rpow hN hP.le
  rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hP] at h
  simpa only [Real.enorm_eq_ofReal_abs] using h

/-- The normalized cylinder power integral is bounded by the original Lp
norm, with both scaling factors explicit. -/
theorem force_slot_rescaled_power_integral_le
    (a c P : ℝ) (K : ℝ≥0∞) (ha : 0 < a) (hP : 0 < P)
    (z₀ z : ParabolicPoint) (r : ℝ)
    {B : Set ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hQB : parabolicCylinder (scalingParabolic a z₀ z).1
      (scalingParabolic a z₀ z).2 (a * r) ⊆ B)
    (hf : AEStronglyMeasurable f (volume.restrict B))
    (hN : eLpNorm f (ENNReal.ofReal P) (volume.restrict B) ≤ K) :
    cylinderPowerIntegral P (fun w => c * f (scalingParabolic a z₀ w)) z r ≤
      ENNReal.ofReal |c| ^ P * (ENNReal.ofReal (a⁻¹ ^ 5) * K ^ P) := by
  have hconst : cylinderPowerIntegral P (fun w => c * f (scalingParabolic a z₀ w)) z r =
      ENNReal.ofReal |c| ^ P *
        cylinderPowerIntegral P (fun w => f (scalingParabolic a z₀ w)) z r := by
    unfold cylinderPowerIntegral
    simp_rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg c),
      ENNReal.mul_rpow_of_nonneg _ _ hP.le]
    exact lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top)
  rw [hconst, force_slot_power_integral_scaling ha]
  apply mul_le_mul_of_nonneg_left _ bot_le
  apply mul_le_mul_of_nonneg_left _ bot_le
  exact (lintegral_mono_set hQB).trans
    (force_slot_power_integral_le_of_eLpNorm P K hP hf hN)

/-- Lowering the velocity integrability exponent retains the volume factor
needed in the normalized energy estimate. -/
theorem force_slot_velocity_cube_norm_le (U : ℝ≥0∞)
    {B : Set ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict B))
    (hN : eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict B) ≤ U) :
    eLpNorm f (ENNReal.ofReal (3 : ℝ)) (volume.restrict B) ≤
      U * volume B ^ (1 / 30 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := ENNReal.ofReal (3 : ℝ)) (q := ENNReal.ofReal (10 / 3 : ℝ)) (by norm_num) hf
  norm_num at h
  simpa using h.trans (mul_le_mul_of_nonneg_right hN bot_le)

/-- The explicit normalized energy from the three original scalar norms. -/
def forceSlotNormalizedEnergyBound (a q : ℝ) (U P F : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (a⁻¹ ^ 5) *
    ((ENNReal.ofReal |a| * U) ^ (3 : ℝ) +
      (ENNReal.ofReal |a ^ 2| * P) ^ (3 / 2 : ℝ) +
      (ENNReal.ofReal |a ^ 3| * F) ^ q)

/-- Finite original norm bounds give a finite normalized energy bound. -/
theorem forceSlotNormalizedEnergyBound_lt_top (a q : ℝ) (hq : 0 ≤ q)
    {U P F : ℝ≥0∞} (hU : U < ⊤) (hP : P < ⊤) (hF : F < ⊤) :
    forceSlotNormalizedEnergyBound a q U P F < ⊤ := by
  have hb (c t : ℝ) (ht : 0 ≤ t) {K : ℝ≥0∞} (hK : K < ⊤) :
      (ENNReal.ofReal |c| * K) ^ t < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg ht (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK).ne
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
      ⟨hb a 3 (by norm_num) hU, hb (a ^ 2) (3 / 2) (by norm_num) hP⟩,
      hb (a ^ 3) q hq hF⟩)

private theorem amplitude_integral_le (c t : ℝ) (ht : 0 < t) (K : ℝ≥0∞)
    {B : Set ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict B))
    (hN : eLpNorm f (ENNReal.ofReal t) (volume.restrict B) ≤ K) :
    (∫⁻ w in B, ENNReal.ofReal |c * f w| ^ t) ≤ (ENNReal.ofReal |c| * K) ^ t := by
  apply force_slot_power_integral_le_of_eLpNorm t _ ht (hf.const_mul c)
  have h := eLpNorm_const_smul_le (c := c) (f := f)
    (p := ENNReal.ofReal t) (μ := volume.restrict B)
  change eLpNorm (fun w => c * f w) (ENNReal.ofReal t) (volume.restrict B) ≤
    ‖c‖ₑ * eLpNorm f (ENNReal.ofReal t) (volume.restrict B) at h
  simpa only [Real.enorm_eq_ofReal_abs] using
    h.trans (mul_le_mul_of_nonneg_left hN bot_le)

/-- The three normalized energy terms are bounded together by the explicit
Jacobian-weighted expression in their original Lp norms. -/
theorem force_slot_normalized_energy_le
    (a q : ℝ) (U P F : ℝ≥0∞) (ha : 0 < a) (hq : 0 < q)
    (z₀ : ParabolicPoint) {B : Set ParabolicPoint}
    (hQB : parabolicCylinder
      (scalingParabolic a z₀ ((0, 0) : ParabolicPoint)).1
      (scalingParabolic a z₀ ((0, 0) : ParabolicPoint)).2 (a * 1) ⊆ B)
    {u p f : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict B))
    (hp : AEStronglyMeasurable p (volume.restrict B))
    (hf : AEStronglyMeasurable f (volume.restrict B))
    (hU : eLpNorm u (ENNReal.ofReal (3 : ℝ)) (volume.restrict B) ≤ U)
    (hP : eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B) ≤ P)
    (hF : eLpNorm f (ENNReal.ofReal q) (volume.restrict B) ≤ F) :
    (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal |a * u (scalingParabolic a z₀ w)| ^ (3 : ℝ) +
        ENNReal.ofReal |a ^ 2 * p (scalingParabolic a z₀ w)| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal |a ^ 3 * f (scalingParabolic a z₀ w)| ^ q) ≤
      forceSlotNormalizedEnergyBound a q U P F := by
  rw [force_slot_lintegral_scaling ha z₀ ((0, 0) : ParabolicPoint) 1
    (fun w => ENNReal.ofReal |a * u w| ^ (3 : ℝ) +
      ENNReal.ofReal |a ^ 2 * p w| ^ (3 / 2 : ℝ) +
      ENNReal.ofReal |a ^ 3 * f w| ^ q)]
  unfold forceSlotNormalizedEnergyBound
  apply mul_le_mul_of_nonneg_left _ bot_le
  apply (lintegral_mono_set hQB).trans
  have hA : AEMeasurable (fun w => ENNReal.ofReal |a * u w| ^ (3 : ℝ))
      (volume.restrict B) := by
    simpa only [Real.norm_eq_abs] using
      ((hu.aemeasurable.const_mul a).norm.ennreal_ofReal).pow_const (3 : ℝ)
  have hB : AEMeasurable (fun w => ENNReal.ofReal |a ^ 2 * p w| ^ (3 / 2 : ℝ))
      (volume.restrict B) := by
    simpa only [Real.norm_eq_abs] using
      ((hp.aemeasurable.const_mul (a ^ 2)).norm.ennreal_ofReal).pow_const (3 / 2 : ℝ)
  have hAB : AEMeasurable (fun w => ENNReal.ofReal |a * u w| ^ (3 : ℝ) +
      ENNReal.ofReal |a ^ 2 * p w| ^ (3 / 2 : ℝ)) (volume.restrict B) := hA.add hB
  rw [lintegral_add_left' hAB, lintegral_add_left' hA]
  exact add_le_add (add_le_add (amplitude_integral_le a 3 (by norm_num) U hu hU)
    (amplitude_integral_le (a ^ 2) (3 / 2) (by norm_num) P hp hP))
    (amplitude_integral_le (a ^ 3) q hq F hf hF)

end CKN.Core.Endgame
