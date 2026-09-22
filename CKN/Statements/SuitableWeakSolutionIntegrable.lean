-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Statements.SpaceTimeSet
import CKN.Statements.SpaceTimeTestFunction
import CKN.Statements.LocalLp
import CKN.Statements.LocalVecLp
import CKN.Statements.LocalBox
import CKN.Statements.SpatialPartial
import CKN.Statements.TimePartial
import CKN.Statements.SpatialSecondPartial
import CKN.Statements.SpatialGradientSq
import CKN.Foundation.Sobolev.WeakDerivative
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN

/-- The suitable weak-solution class from `def:sws`, with explicit measurability,
finite energies, support integrability, and interval time domains. The a.e.
uniqueness of the weak gradient is `CKN.HasWeakPartialDerivOn.ae_eq` from
`CKN/Foundation/Sobolev/WeakDerivative.lean`. -/
def IsSuitableWeakSolutionIntegrable (Ω : Set Vec3) (I : Set ℝ) (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) : Prop :=
  IsOpen Ω ∧ IsOpen I ∧ OrdConnected I ∧ 5 / 2 < q ∧
    (∀ Ω' J, localBox Ω I Ω' J → localVecLp (spaceTimeSet Ω' J) q f) ∧
    (∀ Ω' J, localBox Ω I Ω' J →
      AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω' J)) ∧
      essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
          (volume.restrict J) < ⊤ ∧
      (∫⁻ z in spaceTimeSet Ω' J,
          ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (spaceTimeSet Ω' J)) ∧
      MemLp f (ENNReal.ofReal q)
          (volume.restrict (spaceTimeSet Ω' J)) ∧
      ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i)) ∧
    (∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z)
          (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I,
        ∑ i, u z i * spatialPartial ψ i z = 0) ∧
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
      IntegrableOn (fun z => spatialGradientSq u Du z * ψ z)
          (tsupport ψ) volume ∧
      IntegrableOn (fun z =>
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z)
          (tsupport ψ) volume ∧
      2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z)

end CKN
