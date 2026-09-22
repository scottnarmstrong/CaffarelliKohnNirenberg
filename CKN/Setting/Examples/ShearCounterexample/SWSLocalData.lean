-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.SliceEnergy
import CKN.Setting.Examples.ShearCounterexample.VectorLocal
import CKN.Statements.SuitableWeakSolutionIntegrable
import CKN.Statements.SpaceTimeTestFunction
import CKN.Statements.SpatialPartial
import CKN.Statements.TimePartial
import CKN.Statements.SpatialSecondPartial
import CKN.Statements.SpatialGradientSq
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Local suitable-solution data for the rough shear fields. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace CKN

def IsSuitableWeakSolutionAtExponent (Ω : Set Vec3) (I : Set ℝ) (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) : Prop :=
  IsOpen Ω ∧ IsOpen I ∧ OrdConnected I ∧
    (∀ Ω' J, localBox Ω I Ω' J → localVecLp (spaceTimeSet Ω' J) q f) ∧
    (∀ Ω' J, localBox Ω I Ω' J →
      AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω' J)) ∧
      essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) < ⊤ ∧
      (∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet Ω' J)) ∧
      MemLp f (ENNReal.ofReal q) (volume.restrict (spaceTimeSet Ω' J)) ∧
      ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i)) ∧
    (∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z) (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z = 0) ∧
    (∀ φ : Vec3 × ℝ → Vec3, φ ∈ spaceTimeTestFunction (V := Vec3) Ω I →
      IntegrableOn (fun z =>
          (-(∑ i, u z i * timePartial (fun w => φ w i) z))
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f z i * φ z i) (tsupport φ) volume ∧
      ∫ z in spaceTimeSet Ω I,
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, f z i * φ z i = 0) ∧
    (∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      (∀ z, 0 ≤ ψ z) →
      IntegrableOn (fun z => spatialGradientSq u Du z * ψ z) (tsupport ψ) volume ∧
      IntegrableOn (fun z =>
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) * ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z) (tsupport ψ) volume ∧
      2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) * ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z)

theorem shearCounterexample_localData_atBox {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    localVecLp (spaceTimeSet Ω' J) 2 shearCounterexampleForce ∧
      AEStronglyMeasurable shearCounterexampleVelocity (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable shearCounterexampleDu (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable shearCounterexamplePressure (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable shearCounterexampleForce (volume.restrict (spaceTimeSet Ω' J)) ∧
      essSup (fun s => ∫⁻ x in Ω',
        ‖shearCounterexampleVelocity (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) < ⊤ ∧
      (∫⁻ z in spaceTimeSet Ω' J,
        ‖shearCounterexampleVelocity z‖ₑ ^ (2 : ℝ) +
          ‖shearCounterexampleDu z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      MemLp shearCounterexamplePressure (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) ∧
      MemLp shearCounterexampleForce 2 (volume.restrict (spaceTimeSet Ω' J)) ∧
      ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => shearCounterexampleVelocity (x, s) i)
          (fun x => shearCounterexampleDu (x, s) i) := by
  have hvel := shearCounterexampleVelocity_memLp_on_localBox hbox
  have hdu := shearCounterexampleDu_memLp_on_localBox hbox
  have hEnergyInt : Integrable
      (fun z => ‖shearCounterexampleVelocity z‖ₑ ^ (2 : ℝ) +
        ‖shearCounterexampleDu z‖ₑ ^ (2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
    exact (hvel.integrable_enorm_rpow (by norm_num) (by norm_num)).add
      (hdu.integrable_enorm_rpow (by norm_num) (by norm_num))
  have hEnergy := hEnergyInt.hasFiniteIntegral
  refine ⟨shearCounterexampleForce_localVecLp_on_localBox hbox,
    shearCounterexampleVelocity_measurable.aestronglyMeasurable,
    shearCounterexampleDu_measurable.aestronglyMeasurable,
    (aestronglyMeasurable_const : AEStronglyMeasurable
      (fun _ : ParabolicPoint => (0 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J))),
    shearCounterexampleForce_measurable.aestronglyMeasurable,
    shearVelocity_sliceEnergy_essSup_finite hbox, ?_,
    shearCounterexamplePressure_memLp_on_localBox,
    shearCounterexampleForce_memLp_on_localBox hbox,
    shearCounterexampleSlice_hasWeakGradient_ae hbox.1⟩
  change ∫⁻ z, ‖(fun z =>
      ‖shearCounterexampleVelocity z‖ₑ ^ (2 : ℝ) +
        ‖shearCounterexampleDu z‖ₑ ^ (2 : ℝ)) z‖ₑ ∂
      (volume.restrict (spaceTimeSet Ω' J)) < ⊤ at hEnergy
  simpa only [MeasureTheory.HasFiniteIntegral, enorm_eq_self] using hEnergy

end CKN
