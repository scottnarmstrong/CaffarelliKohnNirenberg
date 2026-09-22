-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Covering.TheoremCReduction
import CKN.Foundation.Parabolic.BallsVsCylindersFaithful

/-!
# The defect inequalities at a singular point

`CKN/Covering/TheoremCReduction.lean` runs the contrapositive of the gradient
criterion inside the proof of `singularSet_null_of_gradient_criterion` and
exposes neither of the two displays that the source step records.  This file
states them: at a singular point the normalised gradient `limsup` is at least
`ε₁²`, and consequently every punctured scale range contains a radius whose
cylinder sits inside the domain and carries more than half of the critical
gradient mass.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The defect displays `eq:defect` and `eq:defect-r` in the proof of `thm:C`, from the ε-regularity
criterion in contrapositive form at a singular point. -/
theorem defect_of_singular_point
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hB : ∀ z₀ ∈ spaceTimeSet Ω I,
      Filter.limsup (fun r : ℝ =>
          (ENNReal.ofReal r)⁻¹ *
            ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
              ENNReal.ofReal (spatialGradientSq u Du w))
        (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
      IsRegularPoint Ω I u z₀)
    {z : ParabolicPoint} (hz : z ∈ SingularSet Ω I u) :
    ENNReal.ofReal (ε₁ ^ (2 : ℕ)) ≤
        Filter.limsup (fun r : ℝ =>
            (ENNReal.ofReal r)⁻¹ *
              ∫⁻ w in parabolicCylinder z.1 z.2 r,
                ENNReal.ofReal (spatialGradientSq u Du w))
          (𝓝[>] (0 : ℝ)) ∧
      ∀ τ : ℝ, 0 < τ → ∃ r : ℝ, 0 < r ∧ r < τ ∧
        parabolicCylinder z.1 z.2 r ⊆ spaceTimeSet Ω I ∧
        ENNReal.ofReal (ε₁ ^ (2 : ℕ) * r / 2) <
          ∫⁻ w in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal (spatialGradientSq u Du w) := by
  set X : ℝ → ℝ≥0∞ := fun r =>
    ∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (spatialGradientSq u Du w) with hX
  set L : ℝ → ℝ≥0∞ := fun r => (ENNReal.ofReal r)⁻¹ * X r with hL
  have hmain : ENNReal.ofReal (ε₁ ^ (2 : ℕ)) ≤ Filter.limsup L (𝓝[>] (0 : ℝ)) := by
    by_contra hlt
    exact hz.2 (hB z hz.1 (lt_of_not_ge hlt))
  refine ⟨hmain, ?_⟩
  -- a radius range on which every cylinder stays inside the domain
  have hopen : IsOpen (spaceTimeSet Ω I) :=
    isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hopen z hz.1
  intro τ hτ
  set m : ℝ := min τ r₀ with hm
  have hmpos : 0 < m := lt_min hτ hr₀
  have hhalf : ENNReal.ofReal (ε₁ ^ (2 : ℕ) / 2) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) := by
    refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr ?_
    have : 0 < ε₁ ^ (2 : ℕ) := by positivity
    linarith only [this]
  have hIoo : Ioo (0 : ℝ) m ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT hmpos
  have hsup : Filter.limsup L (𝓝[>] (0 : ℝ)) ≤ ⨆ r ∈ Ioo (0 : ℝ) m, L r := by
    rw [Filter.limsup_eq_iInf_iSup]
    exact iInf₂_le _ hIoo
  have hlt : ENNReal.ofReal (ε₁ ^ (2 : ℕ) / 2) < ⨆ r ∈ Ioo (0 : ℝ) m, L r :=
    lt_of_lt_of_le (hhalf.trans_le hmain) hsup
  obtain ⟨r, hr⟩ := lt_iSup_iff.mp hlt
  obtain ⟨hrmem, hrlt⟩ := lt_iSup_iff.mp hr
  have hrpos : 0 < r := hrmem.1
  have hrm : r < m := hrmem.2
  refine ⟨r, hrpos, lt_of_lt_of_le hrm (min_le_left _ _), ?_, ?_⟩
  · refine (parabolicCylinder_subset_metricBall_same_center hrpos).trans ?_
    refine hball.trans' ?_
    exact Metric.ball_subset_ball (le_of_lt (lt_of_lt_of_le hrm (min_le_right _ _)))
  · have hne : ENNReal.ofReal r ≠ 0 := by
      simpa using (ENNReal.ofReal_pos.mpr hrpos).ne'
    have htop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmul : ENNReal.ofReal (ε₁ ^ (2 : ℕ) / 2) * ENNReal.ofReal r <
        L r * ENNReal.ofReal r :=
      ENNReal.mul_lt_mul_left hne htop hrlt
    have hcancel : L r * ENNReal.ofReal r = X r := by
      rw [hL]
      rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hne htop, one_mul]
    have hleft : ENNReal.ofReal (ε₁ ^ (2 : ℕ) / 2) * ENNReal.ofReal r =
        ENNReal.ofReal (ε₁ ^ (2 : ℕ) * r / 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [hleft, hcancel] at hmul
    exact hmul

end CKN
