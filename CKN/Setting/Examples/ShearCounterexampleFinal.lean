-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.


import CKN.Setting.Examples.ShearCounterexample
import CKN.Setting.Examples.ShearCounterexampleEnergyDecay

/-! # The critical shear counterexample to the exponent-two regularity criterion. -/


set_option autoImplicit false
noncomputable section

open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CKN

theorem shear_counterexample_forceL2 :
    ∃ (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolutionAtExponent (vec3Ball 0 1) (Ioo (-1) 1) 2 u Du p f ∧
      (∀ z, p z = 0) ∧ (∀ z, u z 0 = 0 ∧ u z 1 = 0) ∧
      Filter.limsup (fun r : ℝ => (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder (0 : Vec3) 0 r, ENNReal.ofReal (spatialGradientSq u Du w))
        (𝓝[>] (0 : ℝ)) = 0 ∧
      ¬ IsRegularPoint (vec3Ball 0 1) (Ioo (-1) 1) u ((0 : Vec3), (0 : ℝ)) := by
  refine ⟨shearCounterexampleVelocity, shearCounterexampleDu,
    shearCounterexamplePressure, shearCounterexampleForce,
    shearCounterexample_suitableAtExponent, ?_, ?_, ?_, ?_⟩
  · intro z
    rfl
  · intro z
    simp [shearCounterexampleVelocity]
  · exact shear_counterexample_energy_limsup_zero
  · have hU : shearCounterexampleVelocity = shearVelocity := by
      funext z
      exact shearCounterexampleVelocity_eq_shearVelocity z
    rw [hU]
    exact shearVelocity_not_regular_at_origin

end CKN
