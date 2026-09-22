-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step3.LocalizedDuhamelSelected
import CKN.Core.Step3.LocalizedEquationDuhamel
import CKN.Core.Step3.GradientSlotDuhamelTested

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat CKN.Core.HeatPotential
open CKN.Core.Step4

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Step3

/-! The localized equation display with the pressure gradient selected from the
    suitable weak solution. -/

theorem localized_equation_display_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) :
    ∃ Dp : ParabolicPoint → Vec3,
      (∀ i : Fin 3, Integrable (fun z => Dp z i)
        (volume.restrict (spaceTimeSet Ω' J))) ∧
      (∀ i : Fin 3, ∀ χ : Vec3 × ℝ → ℝ,
        χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
        tsupport χ ⊆ Ω' ×ˢ J →
        (∫ z : ParabolicPoint, p z * spatialPartial χ i z) =
          -(∫ z : ParabolicPoint, Dp z i * χ z)) ∧
      (∀ ψ : Vec3 × ℝ → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
        let v : ParabolicPoint → Vec3 :=
          localizedVelocity (show ParabolicPoint → ℝ from φ) u
        let g : ParabolicPoint → Vec3 := localizedEquationG φ u Du f
        let h : Fin 3 → ParabolicPoint → Vec3 := localizedEquationH φ u
        ∀ i : Fin 3,
          (∫ z : ParabolicPoint, v z i *
            (-(timePartial ψ z) - ∑ j, spatialSecondPartial ψ j j z)) =
            (∫ z : ParabolicPoint,
              (g z i - φ z * Dp z i) * ψ z) -
              ∑ j, ∫ z : ParabolicPoint,
                h j z i * spatialPartial ψ j z) := by
  obtain ⟨Dp, hDpInt, hDpweak, -⟩ :=
    localized_duhamel_from_leibniz_of_sws hsol hφ hbox hφbox
  refine ⟨Dp, hDpInt, hDpweak, ?_⟩
  intro ψ hψ
  dsimp
  intro i
  have hdiv := localized_divergence_scalar_tested_of_sws
    hsol hφ hbox hφbox i hψ
  have hgrad := gradientSlot_tested_transfer_of_sws
    hsol hφ hbox hφbox hDpInt hDpweak hψ i
  calc
    (∫ z : ParabolicPoint,
        localizedVelocity (show ParabolicPoint → ℝ from φ) u z i *
          (-(timePartial ψ z) - ∑ j, spatialSecondPartial ψ j j z)) =
        (∫ z : ParabolicPoint,
          localizedDivergenceG φ u Du p f z i * ψ z) +
          ∑ j, ∫ z : ParabolicPoint,
            localizedDivergenceH φ u p j z i * spatialPartial ψ j z := hdiv
    _ = (∫ z : ParabolicPoint,
          localizedGradientSourceG φ u Du f Dp z i * ψ z) +
          ∑ j, ∫ z : ParabolicPoint,
            (-localizedGradientSourceH φ u j z i) * spatialPartial ψ j z := hgrad
    _ = (∫ z : ParabolicPoint,
          (localizedEquationG φ u Du f z i - φ z * Dp z i) * ψ z) -
          ∑ j, ∫ z : ParabolicPoint,
            localizedEquationH φ u j z i * spatialPartial ψ j z := by
      simp only [localizedGradientSourceG, localizedGradientSourceH, neg_mul,
        integral_neg, Finset.sum_neg_distrib, sub_eq_add_neg]

end CKN.Core.Step3
