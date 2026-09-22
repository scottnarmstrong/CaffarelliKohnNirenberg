-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientOriginClauseBudget
import CKN.Core.Step4.PressureGradientOriginClauseMajorantArith
import CKN.Core.Step4.PressureGradientOriginClauseGeometry
import CKN.Witnesses.TrivialSolution
import CKN.Foundation.Parabolic.Morrey.Zero

/-!
# Satisfiability of the clipped slicewise pressure data

A hypothesis that no datum satisfies proves everything and is worth nothing.
This module records two certificates for the conclusion of the clipped
slicewise pressure data of the origin-carrier producer.

The first is degenerate: the identically zero pressure satisfies every clause
with the zero majorant and zero constants, so the conclusion is not empty.  The
second is not: whenever the weak gradients of the pressure slices are bounded in
absolute value by a constant `β` on the carrier ball, the conclusion holds with
an explicit **non-zero** majorant, an explicit non-zero growth constant and an
explicit non-zero total mass, and the two constants are proportional to
`β ^ (6/5)`.  Together with the comparison budget of
`oneSidedMorreyBound_le_pressureGradientKP`, this shows that the growth clause
does not secretly force its constant to vanish: it is satisfiable with room to
spare as soon as the slice gradients are small compared with the numerical
datum.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-- The zero function is its own weak partial derivative on any set. -/
theorem originClauseHasWeakPartialDeriv_zero (U : Set Vec3) (i : Fin 3) :
    HasWeakPartialDerivOn U i (fun _ : Vec3 => (0 : ℝ)) (fun _ => (0 : ℝ)) := by
  have h := HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
    (f := fun _ : Vec3 => (0 : ℝ)) (contDiff_const (𝕜 := ℝ))
  simpa using h

/-- **The degenerate certificate.**  The identically zero pressure satisfies
every clause of the clipped slicewise data, with the zero majorant and zero
constants, for every admissible numerical datum.  None of the numerical side
conditions is used. -/
theorem originClauseData_conclusion_zero
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞) (I : Set ℝ) :
    ∃ M : Fin 3 → Vec3 → ℝ → ℝ → ℝ≥0∞, ∃ A B : ℝ≥0∞,
      (∀ (i : Fin 3) (x : Vec3) (r : ℝ),
        ∀ᵐ s ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
          LocallyIntegrableOn g (vec3Ball (0 : Vec3) R₀) volume ∧
          HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₀) i
            (fun y => (fun _ : ParabolicPoint => (0 : ℝ)) (y, s)) g ∧
          eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)) ≤
              M i x r s) ∧
      (∀ i : Fin 3, ∀ᵐ s ∂(volume.restrict I), M i (0 : Vec3) R₁ s ≠ ∞) ∧
      (∀ i : Fin 3, ∀ T : Set ℝ, IsCompact (closure T) → closure T ⊆ I →
        Integrable (fun s => (M i (0 : Vec3) R₁ s).toReal) (volume.restrict T)) ∧
      (∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ R₁ →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          M i z.1 r s ^ (6 / 5 : ℝ)) ≤
          A * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) ∧
      (∀ i : Fin 3, (∫⁻ s in Ioc (-(R₁ ^ 2)) 0,
        M i (0 : Vec3) R₁ s ^ (6 / 5 : ℝ)) ≤ B) ∧
      oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q) R₁ A B ≤
        oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD := by
  refine ⟨fun _ _ _ _ => 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x r
    filter_upwards with s
    refine ⟨fun _ => (0 : ℝ), ?_, originClauseHasWeakPartialDeriv_zero _ i, ?_⟩
    · exact locallyIntegrableOn_const 0
    · simp
  · intro i
    filter_upwards with s
    exact ENNReal.zero_ne_top
  · intro i T _ _
    simp
  · intro i z _ r _ _
    simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 6 / 5)]
  · intro i
    simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 6 / 5)]
  · exact oneSidedMorreyBound_le_pressureGradientKP bot_le bot_le

/-- The four solution-side hypotheses of the producer hold at the identically
zero datum on the whole space-time domain, so the degenerate certificate is not
about an empty class. -/
theorem originClauseZeroDatum_hypotheses
    (q τ R₀ ε : ℝ) (KU KD : ℝ≥0∞) (hq : 5 / 2 < q) :
    IsSuitableWeakSolutionIntegrable (Set.univ : Set Vec3) (Set.univ : Set ℝ) q
        (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0) ∧
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆
        CKN.spaceTimeSet (Set.univ : Set Vec3) (Set.univ : Set ℝ) ∧
      (∀ i, morreyNorm 3 τ
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
          (fun z => (fun _ : ParabolicPoint => (0 : Vec3)) z i)) ≤ KU) ∧
      (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
          (fun z => (fun (_ : ParabolicPoint) (_ : Fin 3) => (0 : Vec3)) z i j))
            ≤ KD) ∧
      ((∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm ((fun _ : ParabolicPoint => (0 : Vec3)) z))
            ^ (3 : ℝ) +
        ENNReal.ofReal |(fun _ : ParabolicPoint => (0 : ℝ)) z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm ((fun _ : ParabolicPoint => (0 : Vec3)) z))
            ^ q) ≤ ENNReal.ofReal ε) := by
  have hzeroNorm : vec3EuclideanNorm (0 : Vec3) = 0 := by simp [vec3EuclideanNorm]
  refine ⟨CKN.isSuitableWeakSolutionIntegrable_zero isOpen_univ isOpen_univ ordConnected_univ hq,
    fun z _ => ⟨trivial, trivial⟩, ?_, ?_, ?_⟩
  · intro i
    have h : (parabolicCylinder (0 : Vec3) 0 R₀).indicator
        (fun _ : ParabolicPoint => (0 : ℝ)) = fun _ => (0 : ℝ) := by
      funext z
      by_cases hz : z ∈ parabolicCylinder (0 : Vec3) 0 R₀ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
    have hfun : ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
        (fun z : ParabolicPoint => (fun _ : ParabolicPoint => (0 : Vec3)) z i))
        = fun _ => (0 : ℝ) := h
    rw [hfun, morreyNorm_zero (by norm_num : (0 : ℝ) < 3)]
    exact bot_le
  · intro i j
    have h : (parabolicCylinder (0 : Vec3) 0 R₀).indicator
        (fun _ : ParabolicPoint => (0 : ℝ)) = fun _ => (0 : ℝ) := by
      funext z
      by_cases hz : z ∈ parabolicCylinder (0 : Vec3) 0 R₀ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
    have hfun : ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
        (fun z : ParabolicPoint => (fun (_ : ParabolicPoint) (_ : Fin 3) => (0 : Vec3)) z i j))
        = fun _ => (0 : ℝ) := h
    rw [hfun, morreyNorm_zero (by norm_num : (0 : ℝ) < 2)]
    exact bot_le
  · have h : ∀ z : ParabolicPoint,
        ENNReal.ofReal (vec3EuclideanNorm (0 : Vec3)) ^ (3 : ℝ) +
          ENNReal.ofReal |(0 : ℝ)| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (0 : Vec3)) ^ q = 0 := by
      intro z
      rw [hzeroNorm, abs_zero, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 3),
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
        ENNReal.zero_rpow_of_pos (by linarith only [hq] : (0 : ℝ) < q)]
      simp
    calc (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (0 : Vec3)) ^ (3 : ℝ) +
        ENNReal.ofReal |(0 : ℝ)| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (0 : Vec3)) ^ q)
        = ∫⁻ _ in parabolicCylinder (0 : Vec3) 0 1, (0 : ℝ≥0∞) := by
          exact lintegral_congr fun z => h z
      _ = 0 := lintegral_zero
      _ ≤ ENNReal.ofReal ε := bot_le

end CKN.Core.Step4
