-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatLinfty
import CKN.Core.HeatPotential.HeatMorreyHolderOfConclusion2

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem heatMorreyHolder
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
          (∀ z w, ‖hbar z - hbar w‖ ≤
            C * multiplierHeatSourceSize P θ₀ θ₁ F G *
              parabolicDist z w ^ γ) ∧
          (∀ z : ParabolicPoint, ∀ R : ℝ, 0 < R →
            ∀ w ∈ Metric.ball z R,
              ‖hbar w‖ ≤
                (2 : ℝ) ^ γ * max 1 (parabolicCampanatoHolderConstant γ P) *
                  C * multiplierHeatSourceSize P θ₀ θ₁ F G * R ^ γ +
                (⨍ v in Metric.ball z R,
                  ‖hbar v‖ ^ P) ^ (1 / P)) := by
  exact heatMorreyHolder_of_heatHolder_conclusion hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁
    σ hσ hhom (heatHolder hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ σ hσ hhom)

end CKN.Core.HeatPotential
