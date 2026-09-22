-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.StartCaccioppoli
import CKN.Core.TheoremA.Start

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-!
This bridge records the part of the Start assembly that is now unconditional.
The remaining pressure display is deliberately an explicit solution-level
input here; the pressure file owns its CZ-to-Lin34 replacement.
-/

theorem thmA_start_of_caccioppoli_and_lin34
    (q C₂₇ C₂₈ C₃₂ : ℝ)
    (hq : 5 / 2 < q) (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hC₃₂ : 0 ≤ C₃₂)
    (hLin34 : ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
        r ≤ ρ / 2 →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        pressureD p z r ≤ C₃₂ *
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
  have hC₂₅ : 0 ≤ Core.Endgame.startGammaConstant := by
    unfold Core.Endgame.startGammaConstant
    positivity
  have hC₂₆ : 0 ≤ caccioppoliC₂₆ q := by
    unfold caccioppoliC₂₆
    positivity
  obtain ⟨ε₀, hε₀, hstart⟩ := thmA_start_of_inputs q
    Core.Endgame.startGammaConstant (caccioppoliC₂₆ q) C₂₇ C₂₈ C₃₂
    hq hC₂₇ hC₂₈ hC₂₅ hC₂₆ hC₃₂
  refine ⟨ε₀, hε₀, ?_⟩
  intro Ω I u Du p f hsol hQ₁ hthmA
  exact hstart hsol hQ₁ hthmA
    (Core.Endgame.caccioppoli_gamma_display_fixed hsol) (hLin34 hsol)

end CKN
