-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatHolder
import CKN.Core.HeatPotential.HeatLinftyOfHolder

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem heatLinfty
    (γ P : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) (hP : 1 ≤ P)
    (hPθ₀ : P ≤ 5 / (2 - γ)) (K : ℕ) (σ : Fin K → Vec3 → ℂ)
    (hσ : ∀ k, SmoothOffOrigin (σ k))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : ParabolicPoint → ℝ) (G : Fin K → ParabolicPoint → ℝ),
        AEMeasurable F volume → (∀ k, AEMeasurable (G k) volume) →
        HasCompactSupport F → (∀ k, HasCompactSupport (G k)) →
        morreyNorm P (5 / (2 - γ)) F < ∞ →
        (∀ k, morreyNorm P (5 / (1 - γ)) (G k) < ∞) →
        ∃ hbar : ParabolicPoint → ℂ,
          LocallyIntegrable hbar volume ∧
          hbar =ᵐ[volume] multiplierHeatPotential σ F G ∧
          ∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
            ∀ w ∈ Metric.ball z R,
              ‖hbar w‖ ≤
                (2 : ℝ) ^ γ * max 1 (parabolicCampanatoHolderConstant γ P) *
                  C * multiplierHeatSourceSize P (5 / (2 - γ))
                    (5 / (1 - γ)) F G * R ^ γ +
                  (⨍ v in Metric.ball z R,
                    ‖hbar v‖ ^ P) ^ (1 / P) := by
  have hden₀ : 0 < 2 - γ := by linarith only [hγ1]
  have hden₁ : 0 < 1 - γ := by linarith only [hγ1]
  have hPθ₁ : P ≤ 5 / (1 - γ) := by
    apply hPθ₀.trans
    apply (div_le_div_iff₀ hden₀ hden₁).2
    nlinarith only [hγ]
  have hθ₀ : 1 / (5 / (2 - γ)) = (2 - γ) / 5 := by
    field_simp [ne_of_gt hden₀]
  have hθ₁ : 1 / (5 / (1 - γ)) = (1 - γ) / 5 := by
    field_simp [ne_of_gt hden₁]
  rcases heatHolder hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ σ hσ hhom with
    ⟨C, hC, happly⟩
  refine ⟨C, hC, ?_⟩
  intro F G hFmeas hGmeas hFsupp hGsupp hFmorrey hGmorrey
  rcases happly hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp with
    ⟨hbar, hbarLoc, hbarEq, hbarHolder⟩
  exact ⟨hbar, heatLinfty_of_holder_representative hγ hP σ C hC hbar
    hbarLoc hbarEq hbarHolder⟩

end CKN.Core.HeatPotential
