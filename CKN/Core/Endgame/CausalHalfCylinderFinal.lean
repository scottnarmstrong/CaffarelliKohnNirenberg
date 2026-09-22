-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.CausalHalfCylinderAssembly
import CKN.Core.HeatPotential.PastSourcesStep2

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Endgame

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

/-- The Step 2 source construction gives the one-sided half-cylinder conclusion. -/
theorem thmA_halfCylinder_of_step2
    (q : ℝ) (hq : 5 / 2 < q) (ε₀ K : ℝ) (hε₀ : 0 ≤ ε₀) (hK : 0 ≤ K) :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        let Q₂s : Set ParabolicPoint :=
          vec3Ball 0 (5 / 8) ×ˢ Ioc (-(25 / 64 : ℝ)) 0
        (∀ i : Fin 3,
          morreyBallNorm 3 stepTau₂ (Q₂s.indicator (fun z => u z i)) ≤
            ENNReal.ofReal K) →
        (∀ i j : Fin 3,
          morreyBallNorm 2 stepTau₃ (Q₂s.indicator (fun z => Du z i j)) ≤
            ENNReal.ofReal K) →
        morreyBallNorm (3 / 2) stepTauP (Q₂s.indicator p) ≤ ENNReal.ofReal K →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w (stepGamma₀ q) C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  exact causal_halfCylinder_of_past_source_producer q hq ε₀ K hε₀ hK
    (exists_past_heat_sources_of_step2 q hq ε₀ K hε₀ hK)

end CKN.Core.Endgame
