-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.TheoremA.ScaleIterationFaithful

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-! The fixed-radius and fixed-coefficient form of `eq:thmA-morrey`. -/

theorem thmA_morrey_absolute :
    ∃ r₅ M : ℝ, 0 < r₅ ∧ 0 ≤ M ∧
      ∀ (q : ℝ), 5 / 2 < q → ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
          {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
          {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
          (∫⁻ z in parabolicCylinder 0 0 1,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
          ∀ z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0,
            ∀ r : ℝ, 0 < r → r ≤ r₅ →
              max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ (2 : ℕ)) ≤
                M * r ^ (2 / 5 : ℝ) := by
  obtain ⟨C₂₇, hC₂₇, hdecay⟩ := thmA_uniform_morrey_decay
  let r₅ : ℝ := iterationKappa C₂₇ / 4
  let M : ℝ :=
    iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) *
      iterationEta C₂₇ * (iterationKappa C₂₇ / 4) ^ (-iterationEpsilon)
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hη : 0 < iterationEta C₂₇ := iterationEta_pos hC₂₇
  have hκ₄ : 0 < iterationKappa C₂₇ / 4 := div_pos hκ (by norm_num)
  have hr₅ : 0 < r₅ := by
    dsimp [r₅]
    positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨r₅, M, hr₅, hM, ?_⟩
  intro q hq
  obtain ⟨ε₀, hε₀, hqdecay⟩ := hdecay q hq
  refine ⟨ε₀, hε₀, ?_⟩
  intro Ω I u Du p f hsol hQ₁ hsmall z hz r hr hrr
  have hz' : z ∈ parabolicCylinder (0 : Vec3) (0 : ℝ) (3 / 4) := by
    change z.1 ∈ vec3Ball (0 : Vec3) (3 / 4) ∧
      z.2 ∈ Ioc (0 - (3 / 4 : ℝ) ^ 2) 0
    rcases hz with ⟨hzx, hzt⟩
    refine ⟨hzx, ?_⟩
    rcases hzt with ⟨hzlow, hzup⟩
    refine ⟨?_, hzup⟩
    norm_num at hzlow ⊢
    exact hzlow
  have h := hqdecay hsol hQ₁ hsmall z hz' r hr (by
    simpa [r₅] using hrr)
  simpa [M, iterationEpsilon] using h

end CKN
