-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatConclusionAssembly
import CKN.Core.HeatPotential.HeatHolderOfConclusion

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem heatHolder
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
              parabolicDist z w ^ γ) := by
  rcases heatConclusion hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ σ hσ hhom with
    ⟨C, hC, happly⟩
  have hcamp : 0 ≤ parabolicCampanatoHolderConstant γ P := by
    have h := heat_holder_campanato_coefficient_nonneg
      (α := γ) (p := P) (K := 1) hγ (by positivity)
    simpa using h
  let C' : ℝ := 2 * parabolicCampanatoHolderConstant γ P * C
  have hC' : 0 ≤ C' := by
    dsimp [C']
    exact mul_nonneg (mul_nonneg (by positivity) hcamp) hC
  refine ⟨C', hC', ?_⟩
  intro F G hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp
  rcases happly hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp with
    ⟨hbar, hbarLoc, hbarEq, hbarMem, hbarOsc⟩
  have hresult := heatHolder_of_conclusion_data hγ hγ1 hP σ hC hbarLoc hbarEq
    hbarMem hbarOsc
  simpa [C'] using hresult

end CKN.Core.HeatPotential
