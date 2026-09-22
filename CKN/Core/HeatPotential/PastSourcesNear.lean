-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.Causality
import CKN.Core.HeatPotential.GeneralSymbolHeatNearProof

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

/-- The near estimate applies to sources restricted to nonpositive times, with
its analytic constant chosen before the sources and evaluation cylinder. -/
theorem heatNear_of_past_source_data
    {K : ℕ} {γ θ₀ θ₁ P : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀)
    (σ : Fin K → Vec3 → ℂ) (hσ : ∀ k, SmoothOffOrigin (σ k))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ},
        AEMeasurable F volume → (∀ k, AEMeasurable (G k) volume) →
        morreyNorm P θ₀ F < ∞ →
        (∀ k, morreyNorm P θ₁ (G k) < ∞) →
        HasCompactSupport F → (∀ k, HasCompactSupport (G k)) →
        ∀ {z : ParabolicPoint} {r : ℝ}, 0 < r →
        ∃ hnear : ParabolicPoint → ℂ,
          LocallyIntegrable hnear volume ∧
          hnear =ᵐ[volume]
            multiplierHeatPotentialNear σ
              ({v : ParabolicPoint | v.2 ≤ (0 : ℝ)}.indicator F)
              (fun k =>
                {v : ParabolicPoint | v.2 ≤ (0 : ℝ)}.indicator (G k)) z r ∧
          MemLp hnear (ENNReal.ofReal P)
            (volume.restrict (Metric.closedBall z r)) ∧
          multiplierHeatPairOscillation hnear z r P ≤
            C * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁
              ({v : ParabolicPoint | v.2 ≤ (0 : ℝ)}.indicator F)
              (fun k =>
                {v : ParabolicPoint | v.2 ≤ (0 : ℝ)}.indicator (G k)) := by
  obtain ⟨C, hC, hnear⟩ :=
    heatNear hγ hγ1 hθ₀ hθ₁ hP hPθ₀ σ hσ hhom
  refine ⟨C, hC, ?_⟩
  intro F G hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp z r hr
  let past : Set ParabolicPoint := {v | v.2 ≤ (0 : ℝ)}
  have hPnonneg : 0 ≤ P := le_trans (by norm_num) hP
  have hFpast := CKN.Core.Endgame.time_truncation_source_data
    (P := P) (θ := θ₀) (T := 0) hPnonneg hFmeas hFmorrey hFsupp
  have hGpast : ∀ k,
      AEMeasurable (past.indicator (G k)) volume ∧
        morreyNorm P θ₁ (past.indicator (G k)) < ∞ ∧
        HasCompactSupport (past.indicator (G k)) := by
    intro k
    exact CKN.Core.Endgame.time_truncation_source_data
      (P := P) (θ := θ₁) (T := 0) hPnonneg
        (hGmeas k) (hGmorrey k) (hGsupp k)
  simpa [past] using
    (hnear (F := past.indicator F) (G := fun k => past.indicator (G k))
      hFpast.1 (fun k => (hGpast k).1) hFpast.2.1
      (fun k => (hGpast k).2.1) hFpast.2.2
      (fun k => (hGpast k).2.2) hr)

end CKN.Core.HeatPotential
