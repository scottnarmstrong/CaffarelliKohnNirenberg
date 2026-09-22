-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatFarAssembly
import CKN.Core.HeatPotential.GeneralSymbolHeatConclusionAssembly

/-!
# The Campanato bound for the general-symbol heat potential

`step:heat-conclusion` of `paper/ckn.tex`.  The near estimate, the finite
near/far splitting of the potential and the far-shell oscillation are
combined into a single representative of the potential: one function, locally
integrable, almost everywhere equal to the potential, of class `L^P` on every
closed ball, whose pair oscillation on the ball of radius `r` is at most
`r ^ γ` times the Morrey size of the source.

Only one representative appears: the near estimate and the splitting are read
off the same function, the triangle inequality separates the near block from
the shell series and Jensen's inequality restores the `P`-th root, and the
shell series is summed as a geometric series of ratio `2 ^ (γ - 1)`.  The
far-shell input is the theorem of the preceding module, so no hypothesis is
added here beyond those of the source.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat

/-- **`step:heat-conclusion`.**  One constant, fixed after the symbols and the
exponents and before the source, and one representative of the general-symbol
heat potential, which is locally integrable, of class `L^P` on every closed
ball, and whose pair oscillation on the ball of radius `r` is at most
`r ^ γ` times the Morrey size of the source. -/
theorem heatConclusion
    {K : ℕ} {γ θ₀ θ₁ P : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (σ : Fin K → Vec3 → ℂ) (hσ : ∀ k, SmoothOffOrigin (σ k))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ},
        AEMeasurable F volume → (∀ k, AEMeasurable (G k) volume) →
        morreyNorm P θ₀ F < ∞ → (∀ k, morreyNorm P θ₁ (G k) < ∞) →
        HasCompactSupport F → (∀ k, HasCompactSupport (G k)) →
        ∃ hbar : ParabolicPoint → ℂ,
          LocallyIntegrable hbar volume ∧
          hbar =ᵐ[volume] multiplierHeatPotential σ F G ∧
          (∀ z : ParabolicPoint, ∀ R : ℝ, 0 < R →
            MemLp hbar (ENNReal.ofReal P)
              (volume.restrict (Metric.closedBall z R))) ∧
          ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r →
            multiplierHeatPairOscillation hbar z r P ≤
              C * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G :=
  heatConclusion_of_heatFar hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ σ hσ hhom
    (heatFar hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ σ hσ hhom)

end CKN.Core.HeatPotential
