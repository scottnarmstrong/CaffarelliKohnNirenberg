-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Examples.ShearCounterexample.FiniteApproxCalculus
import CKN.Setting.Examples.ShearCounterexample.FactorIBP
import CKN.Statements.SpatialSecondPartial

/-! # Finite-scale momentum identities for the shear fields. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory CKN.Foundation.Parabolic Finset
namespace CKN




theorem shearScalarSquared_spatialPartial_zero (N : ℕ) (z : ParabolicPoint) :
    spatialPartial (show ParabolicPoint → ℝ from
      fun w => (shearFullScalarPartial N w) ^ 2) 2 z = 0 := by
  have hmul := spatialPartial_mul
    (g := shearFullScalarPartial N) (h := shearFullScalarPartial N)
    (shearFullScalarPartial_contDiff N) (shearFullScalarPartial_contDiff N) 2 z
  have hzero := shearFullScalarPartial_gradient_zero N z
  simpa [pow_two, hzero] using hmul


theorem shearFiniteMomentumResidual_simplify (N : ℕ)
    (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) :
    (-(∑ i : Fin 3,
        shearCounterexampleVelocityPartial N z i *
          timePartial (fun w => φ w i) z)
      - ∑ i : Fin 3, ∑ j : Fin 3,
          shearCounterexampleVelocityPartial N z i *
            shearCounterexampleVelocityPartial N z j * spatialPartial (fun w => φ w i) j z
      + ∑ i : Fin 3, ∑ j : Fin 3,
          shearCounterexampleDuPartial N z i j * spatialPartial (fun w => φ w i) j z
      - ∑ i : Fin 3,
          shearCounterexampleForcePartial N z i * φ z i) =
    -(shearFullScalarPartial N z * timePartial (fun w => φ w 2) z)
      - (shearFullScalarPartial N z) ^ 2 * spatialPartial (fun w => φ w 2) 2 z
      + ∑ j : Fin 3,
          shearCounterexampleDuPartial N z 2 j * spatialPartial (fun w => φ w 2) j z
      - shearFullForcePartial N z * φ z 2 := by
  simp [shearCounterexampleVelocityPartial, shearCounterexampleDuPartial,
    shearCounterexampleForcePartial, Fin.sum_univ_succ, pow_two]

end CKN
