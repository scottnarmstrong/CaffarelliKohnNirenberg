-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.TheoremA.ScaleIterationFaithful
import CKN.Core.Endgame.OneSidedGradient

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

set_option autoImplicit false
noncomputable section
namespace CKN

/-- The three initial Morrey bounds on the backward cylinder of radius `5/8`
are finite absolute constants; only the positive smallness threshold depends
on the force exponent. -/
theorem theoremA_initial_morrey_absolute :
∃ K₂ K₃ Kp : ℝ≥0∞, K₂ ≠ ∞ ∧ K₃ ≠ ∞ ∧ Kp ≠ ∞ ∧
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
      (∀ i : Fin 3,
        morreyNorm 3 (25 / 3 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
            (fun z => u z i)) ≤ K₂) ∧
      (∀ i j : Fin 3,
        morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
            (fun z => Du z i j)) ≤ K₃) ∧
      morreyNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator p) ≤ Kp := by
  obtain ⟨C, hC, hdecay⟩ := thmA_uniform_morrey_decay
  let r₀ := iterationKappa C / 4
  let M := iterationKappa C ^ (-4 / 3 - iterationEpsilon) *
    iterationEta C * r₀ ^ (-iterationEpsilon)
  have hr₀ : 0 < r₀ := div_pos (iterationKappa_pos hC) (by norm_num)
  have hrquarter : r₀ ≤ 1 / 4 := by
    dsimp only [r₀]
    linarith only [iterationKappa_le_half C]
  have hM : 0 ≤ M := by
    dsimp only [M]
    have hκ := (iterationKappa_pos hC).le
    have hη := (iterationEta_pos hC).le
    positivity
  obtain ⟨N, hgradient⟩ := oneSided_gradient_morrey_of_decay M r₀ hM hr₀ hrquarter
  refine ⟨oneSidedVelocityMorreyBound M r₀ 1,
    oneSidedGradientMorreyBound M r₀ N, oneSidedPressureMorreyBound M r₀ 1,
    (oneSidedVelocityMorreyBound_lt_top M r₀ 1).ne,
    (oneSidedGradientMorreyBound_lt_top M r₀ N).ne,
    (oneSidedPressureMorreyBound_lt_top M r₀ 1).ne, ?_⟩
  intro q hq
  obtain ⟨ε, hε, hdec⟩ := hdecay q hq
  refine ⟨min ε 1, lt_min hε (by norm_num), ?_⟩
  intro Ω I u Du p f hsol hQ hsmall
  have hsmallε := hsmall.trans (ENNReal.ofReal_le_ofReal (min_le_left ε 1))
  have hsmallOne := hsmall.trans (ENNReal.ofReal_le_ofReal (min_le_right ε 1))
  have hd : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
          M * r ^ (2 / 5 : ℝ) := by
    simpa only [M, r₀, iterationEpsilon] using hdec hsol hQ hsmallε
  exact ⟨fun i => oneSided_velocity_morrey_of_decay M r₀ 1 hM hr₀ hrquarter
      hsol hQ hsmallOne hd i,
    hgradient hsol hQ hd,
    oneSided_pressure_morrey_of_decay M r₀ 1 hM hr₀ hrquarter
      hsol hQ hsmallOne hd⟩

end CKN
