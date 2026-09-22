-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatHolderBridge

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem heatHolder_of_conclusion_data
    {K : ℕ} {γ θ₀ θ₁ P : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hP : 1 ≤ P)
    (σ : Fin K → Vec3 → ℂ)
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    {C : ℝ} {hbar : ParabolicPoint → ℂ}
    (hC : 0 ≤ C)
    (hbarLoc : LocallyIntegrable hbar volume)
    (hbarEq : hbar =ᵐ[volume] multiplierHeatPotential σ F G)
    (hbarMem : ∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
      MemLp hbar (ENNReal.ofReal P)
        (volume.restrict
          (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R)))
    (hbarOsc : ∀ (z : ParabolicPoint) (r : ℝ), 0 < r →
      multiplierHeatPairOscillation hbar z r P ≤
        C * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G) :
    ∃ g : ParabolicPoint → ℂ,
      LocallyIntegrable g volume ∧
      g =ᵐ[volume] multiplierHeatPotential σ F G ∧
      (∀ z w, ‖g z - g w‖ ≤
        (2 * parabolicCampanatoHolderConstant γ P * C) *
          multiplierHeatSourceSize P θ₀ θ₁ F G * parabolicDist z w ^ γ) := by
  have hsize : 0 ≤ multiplierHeatSourceSize P θ₀ θ₁ F G := by
    unfold multiplierHeatSourceSize
    positivity
  have hK : 0 ≤ C * multiplierHeatSourceSize P θ₀ θ₁ F G :=
    mul_nonneg hC hsize
  rcases heat_conclusion_component_campanato_bridge hP hbarMem hbarOsc with
    ⟨⟨hReLoc, hReData, hReCamp⟩, ⟨hImLoc, hImData, hImCamp⟩⟩
  have hcommon : ∀ᵐ z ∂volume,
      hbar z = (hbar z).re + Complex.I * (hbar z).im := by
    filter_upwards [] with z
    apply Complex.ext <;> simp
  rcases heat_holder_complex_components_of_campanato_common
      hγ hγ1 hP hK hReLoc hReData hReCamp hImLoc hImData hImCamp hcommon with
    ⟨gRe, gIm, hgRe, hgIm, hReHolder, hImHolder, hbarRecomb⟩
  let g : ParabolicPoint → ℂ := fun z =>
    (gRe z : ℂ) + Complex.I * (gIm z : ℂ)
  have hbarEqG : hbar =ᵐ[volume] g := by
    simpa only [g] using hbarRecomb
  have hgLoc : LocallyIntegrable g volume := hbarLoc.congr hbarEqG
  refine ⟨g, hgLoc, hbarEqG.symm.trans hbarEq, ?_⟩
  intro z w
  have hbound := heat_holder_complex_components_bound hReHolder hImHolder z w
  calc
    ‖g z - g w‖ ≤
        2 * (parabolicCampanatoHolderConstant γ P *
          (C * multiplierHeatSourceSize P θ₀ θ₁ F G)) *
          parabolicDist z w ^ γ := by
      simpa only [g] using hbound
    _ = (2 * parabolicCampanatoHolderConstant γ P * C) *
          multiplierHeatSourceSize P θ₀ θ₁ F G * parabolicDist z w ^ γ := by
      ring

theorem heatHolder_of_heatConclusion_conclusion
    {K : ℕ} {γ θ₀ θ₁ P : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hP : 1 ≤ P)
    (σ : Fin K → Vec3 → ℂ)
    (hconclusion :
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
                C * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ},
        AEMeasurable F volume → (∀ k, AEMeasurable (G k) volume) →
        morreyNorm P θ₀ F < ∞ → (∀ k, morreyNorm P θ₁ (G k) < ∞) →
        HasCompactSupport F → (∀ k, HasCompactSupport (G k)) →
        ∃ g : ParabolicPoint → ℂ,
          LocallyIntegrable g volume ∧
          g =ᵐ[volume] multiplierHeatPotential σ F G ∧
          (∀ z w, ‖g z - g w‖ ≤
            C * multiplierHeatSourceSize P θ₀ θ₁ F G *
              parabolicDist z w ^ γ) := by
  rcases hconclusion with ⟨C, hC, happly⟩
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
