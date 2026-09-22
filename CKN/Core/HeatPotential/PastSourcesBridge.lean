-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.PastSourcesNear
import CKN.Core.HeatPotential.GeneralSymbolCharacterizationFinal

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

/-- Componentwise finite-Morrey sources have the kernel integrability and
slice-form clauses used after past-time truncation. -/
theorem past_source_kernel_clauses_of_morrey_data
    {K : ℕ} {P θ₀ θ₁ : ℝ}
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (σ : Fin K → Vec3 → ℂ) (hσ : ∀ k, SmoothOffOrigin (σ k))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k))
    {F : ParabolicPoint → Vec3} {G : Fin K → ParabolicPoint → Vec3}
    (hFmeas : ∀ i, AEMeasurable (fun z => F z i) volume)
    (hGmeas : ∀ k i, AEMeasurable (fun z => G k z i) volume)
    (hFmorrey : ∀ i, morreyNorm P θ₀ (fun z => F z i) < ∞)
    (hGmorrey : ∀ k i, morreyNorm P θ₁ (fun z => G k z i) < ∞)
    (hFsupp : ∀ i, HasCompactSupport (fun z => F z i))
    (hGsupp : ∀ k i, HasCompactSupport (fun z => G k z i)) :
    (∀ i, ∀ᵐ w ∂volume,
      Integrable (fun v =>
        (heatKernelPlus (pointSub w v) : ℂ) * (F v i : ℂ)) volume ∧
        ∀ k, Integrable (fun v =>
          spatialMultiplierHeatKernel (σ k) (pointSub w v).1
            (pointSub w v).2 * (G k v i : ℂ)) volume) ∧
      (∀ i, ∀ᵐ w ∂volume,
        multiplierHeatPotential σ (fun y => F y i)
            (fun k y => G k y i) w =
          (∫ s : ℝ, spatialHeatConv (w.2 - s)
            (fun y : Vec3 => (F (y, s) i : ℂ)) w.1) +
          ∑ k, ∫ s : ℝ, spatialMultiplierApply (σ k)
            (spatialHeatConv (w.2 - s)
              (fun y : Vec3 => (G k (y, s) i : ℂ))) w.1) := by
  have hσ' : ∀ k, ∀ n : ℕ,
      ContDiffOn ℝ (n : ℕ∞) (σ k) ({0}ᶜ : Set Vec3) := by
    intro k n
    exact hσ k n
  constructor
  · intro i
    obtain ⟨_, _, _, hInt, _, _⟩ := heatPotentialCharacterization
      hP hPθ₀ hPθ₁ σ hσ' hhom (hFmeas i) (fun k => hGmeas k i)
      (hFmorrey i) (fun k => hGmorrey k i) (hFsupp i)
      (fun k => hGsupp k i)
    exact hInt
  · intro i
    exact multiplierHeatPotential_slice_form_ae_of_morrey
      hP hPθ₀ hPθ₁ hσ' hhom (hFmeas i) (fun k => hGmeas k i)
      (hFmorrey i) (fun k => hGmorrey k i) (hFsupp i)
      (fun k => hGsupp k i)

end CKN.Core.HeatPotential
