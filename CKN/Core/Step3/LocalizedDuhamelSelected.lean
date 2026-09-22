-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step3.LocalizedDuhamelProducer

open MeasureTheory Set
open scoped BigOperators ENNReal
open CKN CKN.Core.HeatPotential CKN.Core.Step3 CKN.Core.Step4
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Step3

/-!
# The localized causal Duhamel representation with a selected pressure gradient

The pressure-gradient field is selected from suitability rather than supplied
as an additional datum. Its local integrability and tested weak-gradient
identity are included with the representation.
-/

/-- The localized velocity has the causal gradient-slot Duhamel representation
with the weak pressure gradient selected internally from suitability. -/
theorem localized_duhamel_from_leibniz_of_sws
    :
  ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
    ∀ {φ : Vec3 × ℝ → ℝ},
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      ∀ {Ω' : Set Vec3} {J : Set ℝ},
        localBox Ω I Ω' J →
        tsupport φ ⊆ Ω' ×ˢ J →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i : Fin 3, Integrable (fun z => Dp z i)
            (volume.restrict (spaceTimeSet Ω' J))) ∧
          (∀ i : Fin 3, ∀ χ : Vec3 × ℝ → ℝ,
            χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport χ ⊆ Ω' ×ˢ J →
            (∫ z : ParabolicPoint, p z * spatialPartial χ i z) =
              -(∫ z : ParabolicPoint, Dp z i * χ z)) ∧
          localizedVelocity φ u =ᵐ[volume]
            (fun z i => heatPotential
              (fun w => localizedGradientSourceG φ u Du f Dp w i)
              (fun j w => localizedGradientSourceH φ u j w i) z) := by
  intro Ω I q u Du p f hsol φ hφ Ω' J hbox hφbox
  exact localized_duhamel_of_sws hsol hφ hbox hφbox

end CKN.Core.Step3
