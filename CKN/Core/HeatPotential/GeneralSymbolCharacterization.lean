-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbol
import CKN.Core.HeatPotential.MultiplierPotentialBridge
import CKN.Core.HeatPotential.SubordinatedBase

open scoped BigOperators ENNReal

open MeasureTheory Set

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

/-! The source assumptions of `prop:heat-morrey-hoelder` first give ordinary
integrability of every source.  This is the part of the characterization that
does not use the fourth multiplier-kernel clause. -/

theorem multiplierHeatPotential_sources_integrable
    {K : ℕ} {P θ₀ θ₁ : ℝ}
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    (hF : AEMeasurable F volume) (hG : ∀ k, AEMeasurable (G k) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ k, morreyNorm P θ₁ (G k) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ k, HasCompactSupport (G k)) :
    Integrable F volume ∧ ∀ k, Integrable (G k) volume := by
  refine ⟨heatPotential_source_integrable_of_compact_support
      hP hPθ₀ hF hNF hSupportF, ?_⟩
  intro k
  exact heatPotential_source_integrable_of_compact_support
    hP hPθ₁ (hG k) (hNG k) (hSupportG k)

/-! The product-Fubini side condition for the slice-wise multiplier bridge is
also a consequence of the source Morrey data. -/

theorem multiplierHeatPotential_source_slice_integrable
    {K : ℕ} {P θ₀ θ₁ : ℝ}
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    (hF : AEMeasurable F volume) (hG : ∀ k, AEMeasurable (G k) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ k, morreyNorm P θ₁ (G k) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ k, HasCompactSupport (G k)) :
    ∀ k, ∀ᵐ s : ℝ, Integrable
      (fun y : Vec3 => ((G k (y, s) : ℝ) : ℂ)) volume := by
  have hsrc := multiplierHeatPotential_sources_integrable
    hP hPθ₀ hPθ₁ hF hG hNF hNG hSupportF hSupportG
  intro k
  have hreal : Integrable (G k) ((volume : Measure Vec3).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hsrc.2 k
  have hprod : Integrable (fun v : Vec3 × ℝ =>
      ((G k v : ℝ) : ℂ)) ((volume : Measure Vec3).prod volume) := hreal.ofReal
  exact hprod.prod_left_ae

/-! Once the pointwise kernel pairings are available, CE's bridge gives the
exact source-object identification required by `eq:heat-potential`.  The
remaining theorem-level work is to obtain these pairings from clause 4 of
`eq:heat-kernel-bounds`; that clause is deliberately not inserted as a node
hypothesis here. -/

theorem multiplierHeatPotential_slice_form_of_pairings
    {K : ℕ} {σ : Fin K → Vec3 → ℂ}
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    (hσ : ∀ k, ∀ n : ℕ,
      ContDiffOn ℝ (n : ℕ∞) (σ k) ({0}ᶜ : Set Vec3))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k))
    (hGslice : ∀ k, ∀ᵐ s : ℝ, Integrable
      (fun y : Vec3 => ((G k (y, s) : ℝ) : ℂ)) volume)
    (w : ParabolicPoint)
    (hFpair : Integrable (fun v : ParabolicPoint =>
      (heatKernelPlus (pointSub w v) : ℂ) * ((F v : ℝ) : ℂ)) volume)
    (hGpair : ∀ k, Integrable (fun v : ParabolicPoint =>
      spatialMultiplierHeatKernel (σ k) (pointSub w v).1 (pointSub w v).2 *
        ((G k v : ℝ) : ℂ)) volume) :
    multiplierHeatPotential σ F G w =
      (∫ s : ℝ, spatialHeatConv (w.2 - s)
        (fun y : Vec3 => ((F (y, s) : ℝ) : ℂ)) w.1) +
        ∑ k, ∫ s : ℝ, spatialMultiplierApply (σ k)
          (spatialHeatConv (w.2 - s)
            (fun y : Vec3 => ((G k (y, s) : ℝ) : ℂ))) w.1 := by
  rw [show multiplierHeatPotential σ F G w =
      causalMultiplierPotential σ
        (fun v : Vec3 × ℝ => ((F v : ℝ) : ℂ))
        (fun k v => ((G k v : ℝ) : ℂ)) w from rfl]
  exact causalMultiplierPotential_eq_slice_form
    (fun k => (hσ k 1).continuousOn) hhom hGslice w hFpair hGpair

/- The exact remaining export needed to turn the side-data reduction into the
node theorem is the SPEC-1 clause-4 statement:

theorem locallyIntegrable_spatialMultiplierHeatKernel {σ : Vec3 → ℂ}
    (hcont : ContinuousOn σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    LocallyIntegrable
      (fun z : Vec3 × ℝ => spatialMultiplierHeatKernel σ z.1 z.2) volume

No replacement premise is introduced here. -/

end CKN.Core.HeatPotential
