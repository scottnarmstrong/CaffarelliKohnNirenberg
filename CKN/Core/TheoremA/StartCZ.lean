-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.TheoremA.StartCaccioppoliBridge
import CKN.Pressure.OscillationLin34

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-! The start wrapper consumes the integrated Lin 3.4 display and obtains the
gamma-form Caccioppoli display from the established solution-level producer. -/

/-- Theorem A start with the integrated Lin 3.4 estimate as its only named
analytic input. -/
theorem thmA_start_of_CZ
    (q C₁₃ C₂₇ C₂₈ : ℝ)
    (hq : 5 / 2 < q) (hC₁₃ : 0 ≤ C₁₃)
    (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hLin34 : ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
        r ≤ ρ / 2 →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        pressureD p z r ≤ lin34ForceConstant C₁₃ *
          ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
            (r / ρ) * pressureD p z ρ +
            (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
      (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
      ∀ z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0,
        theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ / 4) ≤
            iterationEta C₂₇ ∧
          lambda q f z (iterationKappa C₂₇ / 4) ≤
            iterationLambda₀ C₂₇ C₂₈ := by
  have hC₃₂ : 0 ≤ lin34ForceConstant C₁₃ := by
    dsimp [lin34ForceConstant]
    exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (by norm_num)
      (Real.rpow_nonneg hC₁₃ _))
  exact thmA_start_of_caccioppoli_and_lin34 q C₂₇ C₂₈
    (lin34ForceConstant C₁₃) hq hC₂₇ hC₂₈ hC₃₂ hLin34

end CKN
