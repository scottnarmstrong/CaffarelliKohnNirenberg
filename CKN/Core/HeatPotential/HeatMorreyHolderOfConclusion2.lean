-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatHolderOfConclusion
import CKN.Core.HeatPotential.HeatLinftyOfHolder
import CKN.Foundation.Euclidean.DegreeOneSymbol

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem heatMorreyHolder_of_heatHolder_conclusion
    {K : ℕ} {γ θ₀ θ₁ P : ℝ}
    (hγ : 0 < γ) (_ : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (_ : P ≤ θ₀) (_ : P ≤ θ₁)
    (σ : Fin K → Vec3 → ℂ)
    (_ : ∀ k, SmoothOffOrigin (σ k))
    (_ : ∀ k, IsDegreeOneHomogeneous (σ k))
    (hheatHolder :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ},
          AEMeasurable F volume → (∀ k, AEMeasurable (G k) volume) →
          morreyNorm P θ₀ F < ∞ → (∀ k, morreyNorm P θ₁ (G k) < ∞) →
          HasCompactSupport F → (∀ k, HasCompactSupport (G k)) →
          ∃ hbar : ParabolicPoint → ℂ,
            LocallyIntegrable hbar volume ∧
            hbar =ᵐ[volume] multiplierHeatPotential σ F G ∧
            (∀ z w, ‖hbar z - hbar w‖ ≤
              C * multiplierHeatSourceSize P θ₀ θ₁ F G *
                parabolicDist z w ^ γ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ},
        AEMeasurable F volume → (∀ k, AEMeasurable (G k) volume) →
        morreyNorm P θ₀ F < ∞ → (∀ k, morreyNorm P θ₁ (G k) < ∞) →
        HasCompactSupport F → (∀ k, HasCompactSupport (G k)) →
        ∃ hbar : ParabolicPoint → ℂ,
          LocallyIntegrable hbar volume ∧
          hbar =ᵐ[volume] multiplierHeatPotential σ F G ∧
          (∀ z w, ‖hbar z - hbar w‖ ≤
            C * multiplierHeatSourceSize P θ₀ θ₁ F G *
              parabolicDist z w ^ γ) ∧
          (∀ z : ParabolicPoint, ∀ R : ℝ, 0 < R →
            ∀ w ∈ Metric.ball z R,
              ‖hbar w‖ ≤
                (2 : ℝ) ^ γ * max 1 (parabolicCampanatoHolderConstant γ P) *
                  C * multiplierHeatSourceSize P θ₀ θ₁ F G * R ^ γ +
                (⨍ v in Metric.ball z R, ‖hbar v‖ ^ P) ^ (1 / P)) := by
  rcases hheatHolder with ⟨C, hC, happly⟩
  have hθ₀eq : θ₀ = 5 / (2 - γ) := by
    apply inv_injective
    simpa only [one_div, inv_div] using hθ₀
  have hθ₁eq : θ₁ = 5 / (1 - γ) := by
    apply inv_injective
    simpa only [one_div, inv_div] using hθ₁
  refine ⟨C, hC, ?_⟩
  intro F G hFm hGm hFn hGn hFs hGs
  rcases happly hFm hGm hFn hGn hFs hGs with
    ⟨hbar, hbarLoc, hbarEq, hbarHolder⟩
  have hbarHolderCanonical : ∀ z w, ‖hbar z - hbar w‖ ≤
      C * multiplierHeatSourceSize P (5 / (2 - γ)) (5 / (1 - γ)) F G *
        parabolicDist z w ^ γ := by
    simpa only [hθ₀eq, hθ₁eq] using hbarHolder
  have hbarLinfty := heatLinfty_of_holder_representative hγ hP σ C hC hbar
    hbarLoc hbarEq hbarHolderCanonical
  refine ⟨hbar, hbarLoc, hbarEq, hbarHolder, ?_⟩
  simpa only [hθ₀eq, hθ₁eq] using hbarLinfty.2.2

end CKN.Core.HeatPotential
