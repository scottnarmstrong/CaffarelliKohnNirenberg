-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.BootstrapPressureConsumer
import CKN.Core.Step4.PressureGradientOneSidedCell

/-!
# Uniform bootstrap and the final selected pressure gradient

The initial and final calls use precisely the one-sided pressure-gradient
interface. The heat representation is supplied as the standard localized
representation identity. All Morrey bounds are chosen before the solution fields.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The exact one-sided pressure-gradient estimate gives both the improved
velocity bound and its corresponding explicit final pressure bound. -/
theorem force_slot_unit_bootstrap_of_GA_and_representation
    (hGA : oneSidedPressureGradientQuantitative)
    (q C_CZ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hC : 0 ≤ C_CZ) (hε : 0 ≤ ε)
    (hKU : KU < ⊤) (hKD : KD < ⊤)
    (hL : ∀ (Ω : Set Vec3) (I : Set ℝ)
      (u f Dp : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ), IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ (φ : Vec3 × ℝ → ℝ) (U : Set Vec3) (J : Set ℝ),
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      localBox Ω I U J → tsupport φ ⊆ U ×ˢ J →
      (∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) →
      (∀ (i : Fin 3) (ψ : Vec3 × ℝ → ℝ),
        ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ → tsupport ψ ⊆ U ×ˢ J →
        (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
          -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
      localizedVelocity φ u =ᵐ[volume] (fun z i => heatPotential
        (fun w => localizedGradientSourceG φ u Du f Dp w i)
        (fun j w => localizedGradientSourceH φ u j w i) z)) :
    ∃ KU25 : ℝ≥0∞, KU25 < ⊤ ∧
      oneSidedPressureGradientKP q 25 C_CZ (5 / 8) (19 / 32) ε KU25 KD < ⊤ ∧
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∀ i, morreyNorm 3 (25 / 3)
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun w => u w i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8)
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun w => Du w i j)) ≤ KD) →
      (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε →
      (∀ i, morreyNorm 3 25
        ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun w => u w i)) ≤ KU25) ∧
      ∃ Dp : ParabolicPoint → Vec3,
        (∀ i, AEMeasurable (fun w => Dp w i)
          (volume.restrict (vec3Ball 0 (19 / 32) ×ˢ I))) ∧
        (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
          U ⊆ vec3Ball 0 (19 / 32) → ∀ i,
          Integrable (fun w => Dp w i) (volume.restrict (spaceTimeSet U J))) ∧
        (∀ i (ψ : Vec3 × ℝ → ℝ),
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ vec3Ball 0 (19 / 32) ×ˢ I →
          (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
            -(∫ w : ParabolicPoint, Dp w i * ψ w)) ∧
        (∀ i, morreyNorm (6 / 5) (min q (25 / 9))
          ((parabolicCylinder (0 : Vec3) 0 (19 / 32)).indicator (fun w => Dp w i)) ≤
            oneSidedPressureGradientKP q 25 C_CZ (5 / 8) (19 / 32) ε KU25 KD) := by
  obtain ⟨KI, hKI, hInitial⟩ := initial_pressure_gradient_of_quantitative hGA q C_CZ ε
    KU KD hq hC hε hKU hKD
  obtain ⟨KU25, hKU25, hboot⟩ := exists_uniform_bootstrap_of_initial_pressure
    q ε KU KD hq hKU hKD ⟨KI, hKI, by
      intro Ω I u f Du p hsol hdom hsmall hU hD
      exact hInitial hsol hdom hU hD hsmall⟩
    hL
  obtain ⟨hKP, hFinal⟩ := hGA q 25 C_CZ (5 / 8) (19 / 32) ε KU25 KD
    hq (by norm_num) (by norm_num) hC (by norm_num) (by norm_num) (by norm_num)
    hε hKU25 hKD
  refine ⟨KU25, hKU25, hKP, ?_⟩
  intro Ω I u f Du p hsol hdom hU hD hsmall
  have hImproved := hboot Ω I u f Du p hsol hdom hU hD hsmall
  have hDsmall (i j : Fin 3) : morreyNorm 2 (25 / 8)
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun w => Du w i j)) ≤ KD := by
    apply le_trans (morreyNorm_mono (by norm_num) ?_) (hD i j)
    intro w
    by_cases hw : w ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8)
    · rw [indicator_of_mem hw, indicator_of_mem
        (parabolicCylinder_mono (by norm_num) (by norm_num) hw)]
    · rw [indicator_of_notMem hw, abs_zero]
      exact abs_nonneg _
  obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hFinal hsol hdom hImproved hDsmall hsmall
  refine ⟨hImproved, Dp, hAE, hInt, hweak, ?_⟩
  intro i
  simpa only [show ((1 / (25 : ℝ) + 8 / 25)⁻¹) = 25 / 9 by norm_num, min_comm] using hN i

end CKN.Core.Endgame
