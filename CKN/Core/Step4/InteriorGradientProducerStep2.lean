-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.InteriorGradientProducer
import CKN.Core.Endgame.BootstrapPressureConsumer
import CKN.Core.Step3.GradientSlotDuhamel

/-! # The interior first round started from the smaller Step 2 carrier

The velocity improvement and the second pressure estimate are available from
the Morrey data on the cylinder of radius `11/16`.  The causality step has
those data only on the cylinder of radius `5/8`.

Dilating by `10/11` about the space-time origin turns a solution with data on
`Q_{5/8}` into a solution with data on `Q_{11/16}`, so the established velocity
improvement applies to it; pulling its conclusion back gives the improved
velocity exponent on `Q_{25/44}`, and hence on the smaller cylinder `Q_{9/16}`.
The second pressure estimate then runs on the pair `(9/16, 17/32)`.

The result is the first-round package the causality localization consumes: an
improved velocity bound and a pressure-gradient bound, both with constants
fixed from the force exponent and the two data bounds alone, before every
domain, time interval and solution.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Endgame CKN.Core.Step3

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

/-- The past carrier of the causality step is the backward cylinder of radius
`5/8` about the space-time origin. -/
theorem pastCarrier_eq_parabolicCylinder :
    vec3Ball (0 : Vec3) (5 / 8) ×ˢ Ioc (-(25 / 64 : ℝ)) 0 =
      parabolicCylinder (0 : Vec3) 0 (5 / 8) := by
  rw [parabolicCylinder]
  norm_num

/-- The velocity improvement started from the data on the cylinder of radius
`5/8`.  Its conclusion is carried by every cylinder of radius at most `25/44`,
the dilated image of the established conclusion radius `5/8`. -/
theorem exists_uniform_bootstrap_on_interior_collar
    (q ε R : ℝ) (KUinitial KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hε : 0 ≤ ε) (hR : 0 ≤ R) (hRle : R ≤ 25 / 44)
    (hKUinitial : KUinitial < ⊤) (hKD : KD < ⊤) :
    ∃ KU : ℝ≥0∞, KU < ⊤ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 (25 / 3)
          ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
            (fun z => u z i)) ≤ KUinitial) →
        (∀ i j, morreyNorm 2 (25 / 8)
          ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
            (fun z => Du z i j)) ≤ KD) →
        (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε →
        ∀ i, morreyNorm 3 25
          ((parabolicCylinder (0 : Vec3) 0 R).indicator
            (fun z => u z i)) ≤ KU := by
  classical
  have hμ : (0 : ℝ) < 10 / 11 := by norm_num
  have hμ1 : (10 : ℝ) / 11 ≤ 1 := by norm_num
  set KUi' : ℝ≥0∞ := ENNReal.ofReal |(10 : ℝ) / 11| *
    (ENNReal.ofReal ((10 : ℝ) / 11) ^ (-5 / (25 / 3 : ℝ) : ℝ) * KUinitial) with hKUi'
  set KD' : ℝ≥0∞ := ENNReal.ofReal |((10 : ℝ) / 11) ^ 2| *
    (ENNReal.ofReal ((10 : ℝ) / 11) ^ (-5 / (25 / 8 : ℝ) : ℝ) * KD) with hKD'
  have hKUi'top : KUi' < ⊤ :=
    force_slot_scaling_bound_lt_top (10 / 11) (10 / 11) (25 / 3) hμ hKUinitial
  have hKD'top : KD' < ⊤ :=
    force_slot_scaling_bound_lt_top (10 / 11) ((10 / 11) ^ 2) (25 / 8) hμ hKD
  have hε' : (0 : ℝ) ≤ ((10 : ℝ) / 11)⁻¹ ^ 2 * ε := by positivity
  obtain ⟨KP, hKP, hpress⟩ := exists_pressure_gradient_morrey_bound_on_fixed_collar
    q (25 / 3) (11 / 16) (43 / 64) (((10 : ℝ) / 11)⁻¹ ^ 2 * ε) KUi' KD' hq
    (by norm_num) (by norm_num) (Or.inl ⟨rfl, rfl, rfl⟩) (by norm_num)
    (by norm_num) (by norm_num) hε' hKUi'top hKD'top
  have hmin : min (((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹) q = 25 / 11 := by
    rw [show ((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹ = 25 / 11 by norm_num]
    exact min_eq_left (by linarith only [hq])
  obtain ⟨KU, hKU, hboot⟩ := exists_uniform_bootstrap_of_initial_pressure
    q (((10 : ℝ) / 11)⁻¹ ^ 2 * ε) KUi' KD' hq hKUi'top hKD'top
    (by
      refine ⟨KP, hKP, ?_⟩
      intro Ω I u f Du p hsol hdom hsmall hU hD
      obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hpress hsol hdom hU hD hsmall
      exact ⟨Dp, hAE, hInt, hweak, fun i => by simpa only [hmin] using hN i⟩)
    (fun _ _ _ _ _ _ _ hsol _ _ _ hφ hbox hsupp hInt hweak =>
      localized_gradient_slot_duhamel_of_sws hsol hφ hbox hsupp hInt hweak)
  refine ⟨ENNReal.ofReal ((10 : ℝ) / 11) ^ (5 / (25 : ℝ) : ℝ) *
    (ENNReal.ofReal |((10 : ℝ) / 11)⁻¹| * KU), ?_, ?_⟩
  · refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKU)
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr hμ).ne' ENNReal.ofReal_ne_top)
  · intro Ω I u f Du p hsol hdom hU hD hsmall i
    have hsol' := isSuitableWeakSolutionIntegrable_rescale hsol originPoint hμ
    have hdom' := interior_rescaled_domain hμ hμ1 hdom
    have hU' : ∀ j, morreyNorm 3 (25 / 3)
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
          (fun z => rescaleVelocity (10 / 11) originPoint u z j)) ≤ KUi' := by
      intro j
      exact rescaled_indicator_morrey_le (c := (10 : ℝ) / 11) (P := 3)
        (τ := (25 / 3 : ℝ)) (R := (5 / 8 : ℝ)) (R' := (11 / 16 : ℝ)) hμ
        (by norm_num) (by norm_num) (by norm_num) (fun z => u z j) (hU j)
    have hD' : ∀ j k, morreyNorm 2 (25 / 8)
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
          (fun z => rescaleGradient (10 / 11) originPoint Du z j k)) ≤ KD' := by
      intro j k
      exact rescaled_indicator_morrey_le (c := ((10 : ℝ) / 11) ^ 2) (P := 2)
        (τ := (25 / 8 : ℝ)) (R := (5 / 8 : ℝ)) (R' := (11 / 16 : ℝ)) hμ
        (by norm_num) (by norm_num) (by norm_num) (fun z => Du z j k) (hD j k)
    have hsmall' := rescaled_unit_data_le (u := u) (f := f) (p := p) hμ hμ1 hq hsmall
    have hconc := hboot _ _ (rescaleVelocity (10 / 11) originPoint u)
      (rescaleForce (10 / 11) originPoint f) (rescaleGradient (10 / 11) originPoint Du)
      (rescalePressure (10 / 11) originPoint p) hsol' hdom' hU' hD' hsmall' i
    refine force_slot_subcarrier_unscaling_le (10 / 11) (10 / 11) 3 25 KU hμ
      (by norm_num) (by norm_num) originPoint _ _ (fun z => u z i) ?_ hconc
    exact originScaling_cylinder_preimage_subset hμ hR (by linarith only [hRle])

/-- **The interior first round from the Step 2 data on the smaller carrier.**
From the force exponent, the cubic data bound and the common Morrey bound of
the Step 2 conclusions on the backward cylinder of radius `5/8`, two finite
constants are fixed before every domain, time interval and solution: an
improved velocity Morrey bound on the cylinder of radius `9/16`, and a Morrey
bound for a selected weak spatial pressure gradient on the cylinder of radius
`17/32`, carrying all of the clauses in which such a gradient is consumed. -/
theorem exists_interior_first_round_of_step2_data
    (q ε K : ℝ) (hq : 5 / 2 < q) (hε : 0 ≤ ε) :
    ∃ KU KP : ℝ≥0∞, KU < ⊤ ∧ KP < ⊤ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
        (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε →
        (∀ i, morreyBallNorm 3 stepTau₂
          ((vec3Ball (0 : Vec3) (5 / 8) ×ˢ Ioc (-(25 / 64 : ℝ)) 0).indicator
            (fun z => u z i)) ≤ ENNReal.ofReal K) →
        (∀ i j, morreyBallNorm 2 stepTau₃
          ((vec3Ball (0 : Vec3) (5 / 8) ×ˢ Ioc (-(25 / 64 : ℝ)) 0).indicator
            (fun z => Du z i j)) ≤ ENNReal.ofReal K) →
        (∀ i, morreyNorm 3 25
          ((parabolicCylinder (0 : Vec3) 0 (9 / 16)).indicator
            (fun z => u z i)) ≤ KU) ∧
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball (0 : Vec3) (17 / 32) ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball (0 : Vec3) (17 / 32) → ∀ i : Fin 3,
            Integrable (fun z => Dp z i)
              (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball (0 : Vec3) (17 / 32) ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
            ((parabolicCylinder (0 : Vec3) 0 (17 / 32)).indicator
              (fun z => Dp z i)) ≤ KP) := by
  classical
  obtain ⟨KU, hKU, hboot⟩ := exists_uniform_bootstrap_on_interior_collar q ε (9 / 16)
    (ENNReal.ofReal K) (ENNReal.ofReal K) hq hε (by norm_num) (by norm_num)
    ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  obtain ⟨KP, hKP, hpress⟩ := exists_pressure_gradient_morrey_bound_on_past_collar
    q 25 (9 / 16) (17 / 32) ε KU (ENNReal.ofReal K) hq (Or.inr ⟨rfl, rfl, rfl⟩)
    hε hKU ENNReal.ofReal_lt_top
  refine ⟨KU, KP, hKU, hKP, ?_⟩
  intro Ω I u Du p f hsol hdom hsmall hUball hDball
  rw [pastCarrier_eq_parabolicCylinder] at hUball hDball
  have hU : ∀ i, morreyNorm 3 (25 / 3)
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
        (fun z => u z i)) ≤ ENNReal.ofReal K := fun i =>
    (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans (hUball i)
  have hD : ∀ i j, morreyNorm 2 (25 / 8)
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
        (fun z => Du z i j)) ≤ ENNReal.ofReal K := fun i j =>
    (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans (hDball i j)
  have hsub : parabolicCylinder (0 : Vec3) 0 (9 / 16) ⊆
      parabolicCylinder (0 : Vec3) 0 (5 / 8) :=
    parabolicCylinder_mono (by norm_num) (by norm_num)
  have hDsmall : ∀ i j, morreyNorm 2 (25 / 8)
      ((parabolicCylinder (0 : Vec3) 0 (9 / 16)).indicator
        (fun z => Du z i j)) ≤ ENNReal.ofReal K := fun i j =>
    (morreyNorm_indicator_mono_set (by norm_num : (0 : ℝ) ≤ 2) hsub
      (fun z => Du z i j)).trans (hD i j)
  have hUbig := hboot Ω I u f Du p hsol hdom hU hD hsmall
  refine ⟨hUbig, ?_⟩
  obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hpress hsol hdom hUbig hDsmall hsmall
  refine ⟨Dp, hAE, hInt, hweak, fun i => ?_⟩
  have hexp : min (((1 / (25 : ℝ)) + 8 / 25)⁻¹) q = min q (25 / 9 : ℝ) := by
    rw [show ((1 / (25 : ℝ)) + 8 / 25)⁻¹ = 25 / 9 by norm_num, min_comm]
  simpa only [hexp] using hN i

end CKN.Core.Step4
