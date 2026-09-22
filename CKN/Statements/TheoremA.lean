-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Main.TheoremA
import CKN.Main.TheoremAPaper
import CKN.Statements.SpaceTimeSet
import CKN.Statements.SuitableWeakSolutionIntegrable
import CKN.Statements.SuitableWeakSolution
import CKN.Statements.RegularPoint
import CKN.Statements.ParabolicHolderVecNormLE

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Theorem A, paper label `thm:A`; the Hölder-representative convention of docs/DESIGN_NOTES.md retains the open-cylinder regular-point conclusion and the quantitative Hölder representative. -/
theorem epsilonRegularityL3 (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolution Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z :=
by exact CKN.Main.epsilonRegularityL3Paper q hq

end CKN
