-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Examples.ShearCounterexample.FiniteHeatIdentity
import CKN.Setting.Examples.ShearCounterexample.TestSupport
import CKN.Foundation.Parabolic.Topology

/-! # Calculus identities for finite shear approximations. -/

set_option autoImplicit false
open CKN.Foundation.Parabolic Finset
namespace CKN

theorem shearReducedForceTerm_continuous_finite (n : ℕ) :
    Continuous (shearReducedForceTerm n) := by
  unfold shearReducedForceTerm shearReducedForceCore
  change Continuous (fun z => shearWeight n *
    (shearTimeFirstField (shearScale n) z -
      shearSpatialSecondField (shearScale n) 0 z -
      shearSpatialSecondField (shearScale n) 1 z))
  exact continuous_const.mul
    (((shearTimeFirstField_continuous (shearScale_pos n)).sub
      (shearSpatialSecondField_continuous (shearScale_pos n) 0)).sub
      (shearSpatialSecondField_continuous (shearScale_pos n) 1))

theorem shearReducedForcePartial_continuous_finite (N : ℕ) :
    Continuous (shearReducedForcePartial N) := by
  unfold shearReducedForcePartial
  apply continuous_finsetSum
  intro n hn
  exact shearReducedForceTerm_continuous_finite n

theorem shearFullForcePartial_continuous (N : ℕ) :
    Continuous (shearFullForcePartial N) := by
  let Q : Vec3 × ℝ → Vec2 × ℝ := fun z => ((fun i : Fin 2 => z.1 i.castSucc), z.2)
  have hQ : Continuous Q := by
    dsimp [Q]
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      exact (continuous_apply (i.castSucc)).comp continuous_fst
    · exact continuous_snd
  have hF : Continuous (shearReducedForcePartial N ∘ Q) :=
    (shearReducedForcePartial_continuous_finite N).comp hQ
  have heq : shearFullForcePartial N =
      (shearReducedForcePartial N ∘ Q) ∘ parabolicHomeomorph := by
    funext z
    rfl
  rw [heq]
  exact hF.comp parabolicHomeomorph.continuous

theorem shearFullScalarPartial_gradient_zero (N : ℕ) (z : ParabolicPoint) :
    spatialPartial (show ParabolicPoint → ℝ from shearFullScalarPartial N) 2 z = 0 := by
  simpa using shearFullScalarPartial_spatialPartial N z 2

theorem shearCounterexampleDuPartial_energy_eq (N : ℕ) (z : ParabolicPoint) :
    spatialGradientSq (shearCounterexampleVelocityPartial N)
      (shearCounterexampleDuPartial N) z =
      (shearFullGradientPartial 0 N z) ^ 2 +
        (shearFullGradientPartial 1 N z) ^ 2 := by
  simp [spatialGradientSq, shearCounterexampleDuPartial, Fin.sum_univ_succ]

theorem shearCounterexampleVelocityPartial_norm_sq (N : ℕ) (z : ParabolicPoint) :
    (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 =
      (shearFullScalarPartial N z) ^ 2 := by
  simp [vec3EuclideanNorm, shearCounterexampleVelocityPartial,
    shearFullScalarPartial]
  exact Real.sq_sqrt (sq_nonneg (shearFullScalarPartial N z))

end CKN
