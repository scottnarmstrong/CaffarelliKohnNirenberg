-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.RouteAAssembly
import CKN.Core.Step4.PressureGradientMorreyBridge
import CKN.Core.Step4.PressureGradientOneSided
import CKN.Core.Step4.SliceSelectedGradient
import CKN.Core.Step3.LocalizedEquationBasics
import CKN.Core.Endgame.Localization
import CKN.Foundation.Parabolic.BallDisplays

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-! The symmetric carrier for `G`.  The slice producer is deliberately kept at
the exact inner-ball interface consumed by `exists_spacetime_weak_gradient_of_slices`.
This is the space-time form of the paper's display (3.5). -/

def symmetricPressureGradientSliceProducer : Prop :=
  ∀ q : ℝ, 5 / 2 < q →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
      Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
      morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u →
      (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
        (Metric.ball z₀ R) (fun z => Du z i)) →
      ∃ K : Fin 3 → ℝ → ℝ≥0∞,
        ∀ᵐ t ∂(volume.restrict (Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2))),
          ∀ i : Fin 3, ∃ g : Vec3 → ℝ,
            LocallyIntegrableOn g (vec3Ball z₀.1 R) volume ∧
            HasWeakPartialDerivOn (vec3Ball z₀.1 R) i
              (fun x => p (x, t)) g ∧
            eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
              (volume.restrict (vec3Ball z₀.1 (R / 2))) ≤ K i t

end CKN.Core.Step4
