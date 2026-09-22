-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.UniformCutoffFamilyScaled
import CKN.Core.Endgame.CompactBall
import CKN.Core.Endgame.QuantitativeEndgame

/-!
# A cutoff family with one derivative constant for every centre and radius

The quantitative form of `thm:endgame` needs localization cutoffs whose first
spatial derivative obeys a bound fixed *before* the domain, the centre and the
solution.  The construction of `CKN.Core.Endgame.endgameCutoff` supplies them:
one fixed profile, translated to the centre and rescaled parabolically by the
radius, so that the chain rule turns the profile's derivative bounds into the
factors `a ^ (-1)` and `a ^ (-2)`.

## Main results

* `exists_uniform_parabolic_cutoff_family`: one constant `C₁₀`, quantified
  before the centre and the radius, such that every parabolic ball carries a
  smooth compactly supported cutoff which equals one on the ball, is supported
  in the doubled ball, and obeys `|∂_j φ| ≤ C₁₀ / a`, `|∂_t φ| ≤ C₁₀ / a ^ 2`
  and `|∂_i ∂_j φ| ≤ C₁₀ / a ^ 2`.
* `exists_endgame_cutoff_family`: the same family read at the endgame radius
  `endgameLocalRadius r₂ r₃`, in the exact shape of the cutoff hypothesis of
  the quantitative endgame consumer.
-/

open Set Metric
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Endgame

/-- One numerical constant serves every space-time centre and every parabolic
radius: each parabolic ball carries a smooth compactly supported cutoff that is
one on the ball, vanishes outside the doubled ball, and whose first spatial
derivative, time derivative and second spatial derivatives obey the parabolic
scaling bounds `C₁₀ / a`, `C₁₀ / a ^ 2` and `C₁₀ / a ^ 2`.  The constant is
fixed before the centre, the radius, the domain and any solution. -/
theorem exists_uniform_parabolic_cutoff_family :
    ∃ C₁₀ : ℝ, 0 < C₁₀ ∧
      ∀ (z : ParabolicPoint) (a : ℝ), 0 < a →
        ∃ φ : Vec3 × ℝ → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ ∧
          HasCompactSupport φ ∧
          (∀ w ∈ Metric.ball z a, φ w = 1) ∧
          tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z (2 * a) ∧
          (∀ (j : Fin 3) (w : Vec3 × ℝ), |spatialPartial φ j w| ≤ C₁₀ / a) ∧
          (∀ w : Vec3 × ℝ, |timePartial φ w| ≤ C₁₀ / a ^ 2) ∧
          (∀ (i j : Fin 3) (w : Vec3 × ℝ),
            |spatialSecondPartial φ i j w| ≤ C₁₀ / a ^ 2) := by
  refine ⟨uniformCutoffConstant, uniformCutoffConstant_pos, ?_⟩
  intro z a ha
  exact ⟨endgameCutoff z ha, endgameCutoff_smooth z ha,
    endgameCutoff_hasCompactSupport z ha,
    fun _ hw => endgameCutoff_eq_one ha hw,
    endgameCutoff_tsupport_subset z ha,
    endgameCutoff_abs_spatialPartial_le z ha,
    endgameCutoff_abs_timePartial_le z ha,
    endgameCutoff_abs_spatialSecondPartial_le z ha⟩

/-- The cutoff family of the quantitative endgame: at the radii `r₂` and `r₃`
of `thm:endgame` there is one derivative constant `C₁₀`, fixed before the
domain, the centre and the solution, such that every centre `z` in the closed
ball of radius `r₃` carries an admissible localization cutoff which equals one
on the parabolic ball of radius `endgameLocalRadius r₂ r₃`, is supported inside
the doubled ball, and has `|∂_j φ| ≤ C₁₀` everywhere. -/
theorem exists_endgame_cutoff_family (r₂ r₃ : ℝ) (hr₃ : 0 < r₃)
    (hrr : r₃ < r₂ / 4) :
    ∃ C₁₀ : ℝ, 0 ≤ C₁₀ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (z₀ z : ParabolicPoint),
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
        z ∈ Metric.closedBall z₀ r₃ →
        ∃ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
          localBox Ω I Ω' J ∧
          tsupport φ ⊆ Ω' ×ˢ J ∧
          (∀ w ∈ Metric.ball z (endgameLocalRadius r₂ r₃), φ w = 1) ∧
          tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
            Metric.ball z (2 * endgameLocalRadius r₂ r₃) ∧
          (∀ j w, |spatialPartial φ j w| ≤ C₁₀) := by
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  refine ⟨uniformCutoffConstant / endgameLocalRadius r₂ r₃,
    div_nonneg uniformCutoffConstant_nonneg ha.le, ?_⟩
  intro Ω I z₀ z hdom hz
  have hsub : Metric.ball z (2 * endgameLocalRadius r₂ r₃) ⊆
      Metric.ball z₀ (r₂ / 4) := by
    refine parabolic_ball_subset_ball_of_center_mem_closedBall hz ?_
    unfold endgameLocalRadius
    linarith only [hrr]
  have hts : tsupport (endgameCutoff z ha) ⊆
      parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (r₂ / 4) :=
    (endgameCutoff_tsupport_subset z ha).trans (preimage_mono hsub)
  refine ⟨endgameCutoff z ha, vec3Ball z₀.1 r₂,
    Ioo (z₀.2 - r₂ ^ 2) (z₀.2 + r₂ ^ 2), ⟨endgameCutoff_smooth z ha,
      endgameCutoff_hasCompactSupport z ha, ?_⟩,
    localBox_of_parabolic_ball hr₂ hdom,
    hts.trans (parabolicBall_preimage_subset_box hr₂),
    fun _ hw => endgameCutoff_eq_one ha hw,
    endgameCutoff_tsupport_subset z ha,
    endgameCutoff_abs_spatialPartial_le z ha⟩
  intro w hw
  exact hdom (Metric.ball_subset_ball (by linarith only [hr₂]) (hts hw))

/-- The cutoff family of the quantitative endgame in its coefficient form: any
constant `C₁₀` at least the explicit `endgameCutoffCoefficientBound` of the
endgame radius bounds simultaneously the cutoff, its time derivative, its first
spatial derivatives and its spatial Laplacian, for every domain, every centre
`z₀` and every `z` in the closed ball of radius `r₃`.  The bound is fixed
before the domain, the centre and any solution.  This is the cutoff input of
the quantitative endgame consumer. -/
theorem endgame_cutoff_family_coefficients {r₂ r₃ C₁₀ : ℝ} (hr₃ : 0 < r₃)
    (hrr : r₃ < r₂ / 4)
    (hC : endgameCutoffCoefficientBound (endgameLocalRadius r₂ r₃) ≤ C₁₀) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (z₀ z : ParabolicPoint),
      Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
      z ∈ Metric.closedBall z₀ r₃ →
      ∃ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
        φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
        localBox Ω I Ω' J ∧
        tsupport φ ⊆ Ω' ×ˢ J ∧
        (∀ w ∈ Metric.ball z (endgameLocalRadius r₂ r₃), φ w = 1) ∧
        tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
          Metric.ball z (2 * endgameLocalRadius r₂ r₃) ∧
        (∀ w : Vec3 × ℝ, |φ w| ≤ C₁₀ ∧
          |timePartial φ w| ≤ C₁₀ ∧
          (∀ j, |spatialPartial φ j w| ≤ C₁₀) ∧
          |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C₁₀) := by
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  intro Ω I z₀ z hdom hz
  have hsub : Metric.ball z (2 * endgameLocalRadius r₂ r₃) ⊆
      Metric.ball z₀ (r₂ / 4) := by
    refine parabolic_ball_subset_ball_of_center_mem_closedBall hz ?_
    unfold endgameLocalRadius
    linarith only [hrr]
  have hts : tsupport (endgameCutoff z ha) ⊆
      parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (r₂ / 4) :=
    (endgameCutoff_tsupport_subset z ha).trans (preimage_mono hsub)
  have hcoeff : ∀ w : Vec3 × ℝ, |endgameCutoff z ha w| ≤ C₁₀ ∧
      |timePartial (endgameCutoff z ha) w| ≤ C₁₀ ∧
      (∀ j, |spatialPartial (endgameCutoff z ha) j w| ≤ C₁₀) ∧
      |spatialLaplacian (fun x => endgameCutoff z ha (x, w.2)) w.1| ≤ C₁₀ := by
    intro w
    obtain ⟨h0, ht, hs, hl⟩ := endgameCutoff_coefficient_bounds z ha w
    exact ⟨h0.trans hC, ht.trans hC, fun j => (hs j).trans hC, hl.trans hC⟩
  refine ⟨endgameCutoff z ha, vec3Ball z₀.1 r₂,
    Ioo (z₀.2 - r₂ ^ 2) (z₀.2 + r₂ ^ 2), ⟨endgameCutoff_smooth z ha,
      endgameCutoff_hasCompactSupport z ha, ?_⟩,
    localBox_of_parabolic_ball hr₂ hdom,
    hts.trans (parabolicBall_preimage_subset_box hr₂),
    fun _ hw => endgameCutoff_eq_one ha hw,
    endgameCutoff_tsupport_subset z ha, hcoeff⟩
  intro w hw
  exact hdom (Metric.ball_subset_ball (by linarith only [hr₂]) (hts hw))

/-- The existential form of `endgame_cutoff_family_coefficients`: one constant,
quantified before the domain, the centre and the solution, bounds all four
coefficients of the localized heat equation attached to the cutoff. -/
theorem exists_endgame_cutoff_family_coefficients (r₂ r₃ : ℝ) (hr₃ : 0 < r₃)
    (hrr : r₃ < r₂ / 4) :
    ∃ C₁₀ : ℝ, 0 ≤ C₁₀ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (z₀ z : ParabolicPoint),
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
        z ∈ Metric.closedBall z₀ r₃ →
        ∃ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
          localBox Ω I Ω' J ∧
          tsupport φ ⊆ Ω' ×ˢ J ∧
          (∀ w ∈ Metric.ball z (endgameLocalRadius r₂ r₃), φ w = 1) ∧
          tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
            Metric.ball z (2 * endgameLocalRadius r₂ r₃) ∧
          (∀ w : Vec3 × ℝ, |φ w| ≤ C₁₀ ∧
            |timePartial φ w| ≤ C₁₀ ∧
            (∀ j, |spatialPartial φ j w| ≤ C₁₀) ∧
            |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C₁₀) := by
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  exact ⟨endgameCutoffCoefficientBound (endgameLocalRadius r₂ r₃),
    endgameCutoffCoefficientBound_nonneg ha,
    endgame_cutoff_family_coefficients hr₃ hrr le_rfl⟩

end CKN.Core.Endgame
