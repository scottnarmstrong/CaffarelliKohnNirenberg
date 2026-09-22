-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.InterpolationBall

/-!
# The two–six interpolation display on a ball

`paper/ckn.tex` records, for `2 ≤ q ≤ 6`, the interpolation exponent
`θ = 3(1/2 − 1/q)` and the estimate

`‖v‖_{L^q(B)}^q ≤ ‖v‖_{L²(B)}^{q(1−θ)} ‖v‖_{L⁶(B)}^{qθ}`.

This module states that display publicly on every Euclidean ball, with the
exponent written out, for any almost-everywhere strongly measurable function.
-/

open MeasureTheory Set

open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace CKN

private lemma interp_theta_pos {q : ℝ} (hq : 2 < q) :
    0 < 3 * (1 / 2 - 1 / q) := by
  have hq0 : (0 : ℝ) < q := by linarith only [hq]
  have h : (1 : ℝ) / q < 1 / 2 := by
    rw [div_lt_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)]
    linarith only [hq]
  linarith only [h]

private lemma interp_theta_lt_one {q : ℝ} (hq2 : 2 < q) (hq : q < 6) :
    3 * (1 / 2 - 1 / q) < 1 := by
  have hq0 : (0 : ℝ) < q := by linarith only [hq2]
  have h : (1 : ℝ) / 6 < 1 / q := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 6) hq0]
    linarith only [hq]
  linarith only [h]

/-- The two–six interpolation inequality for the `eLpNorm` seminorms of a single
measure, at the exponent `θ = 3(1/2 − 1/q)` with `2 < q < 6`. -/
private theorem eLpNorm_interpolate_two_six_public
    {μ : Measure (Vec 3)} {g : Vec 3 → ℝ} {q : ℝ}
    (hq2 : 2 < q) (hq6 : q < 6) (hg : AEStronglyMeasurable g μ) :
    eLpNorm g (ENNReal.ofReal q) μ ≤
      eLpNorm g 2 μ ^ (1 - 3 * (1 / 2 - 1 / q)) *
        eLpNorm g 6 μ ^ (3 * (1 / 2 - 1 / q)) := by
  obtain ⟨θ, hθdef⟩ : ∃ t : ℝ, t = 3 * (1 / 2 - 1 / q) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; exact interp_theta_pos hq2
  have hθ1 : θ < 1 := by rw [hθdef]; exact interp_theta_lt_one hq2 hq6
  have hq : (0 : ℝ) < q := by linarith only [hq2]
  have hne : (1 : ℝ) - θ ≠ 0 := ne_of_gt (sub_pos.mpr hθ1)
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  obtain ⟨P, hPdef⟩ : ∃ t : ℝ, t = 2 / (1 - θ) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ t : ℝ, t = 6 / θ := ⟨_, rfl⟩
  have hP : 0 < P := by
    rw [hPdef]; exact div_pos (by norm_num) (sub_pos.mpr hθ1)
  have hS : 0 < S := by rw [hSdef]; exact div_pos (by norm_num) hθ0
  have hrecip : P⁻¹ + S⁻¹ = q⁻¹ := by
    rw [hPdef, hSdef, inv_div, inv_div, hθdef]
    field_simp
    ring
  have hHT : ENNReal.HolderTriple (ENNReal.ofReal P) (ENNReal.ofReal S)
      (ENNReal.ofReal q) := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos hP, ← ENNReal.ofReal_inv_of_pos hS,
      ← ENNReal.ofReal_inv_of_pos hq,
      ← ENNReal.ofReal_add (le_of_lt (inv_pos.mpr hP))
        (le_of_lt (inv_pos.mpr hS)), hrecip]
  have hw : AEStronglyMeasurable (fun x => ‖g x‖ ^ (1 - θ)) μ := by
    simpa [Function.comp_def] using
      ((Real.continuous_rpow_const (q := 1 - θ)
        (by linarith only [hθ1])).aemeasurable.comp_aemeasurable
        hg.aemeasurable.norm).aestronglyMeasurable
  have hy : AEStronglyMeasurable (fun x => ‖g x‖ ^ θ) μ := by
    simpa [Function.comp_def] using
      ((Real.continuous_rpow_const (q := θ)
        (by linarith only [hθ0])).aemeasurable.comp_aemeasurable
        hg.aemeasurable.norm).aestronglyMeasurable
  have hholder :
      eLpNorm (fun x => ‖g x‖ ^ (1 - θ) * ‖g x‖ ^ θ) (ENNReal.ofReal q) μ ≤
        eLpNorm (fun x => ‖g x‖ ^ (1 - θ)) (ENNReal.ofReal P) μ *
          eLpNorm (fun x => ‖g x‖ ^ θ) (ENNReal.ofReal S) μ := by
    simpa [ENNReal.smul_def, one_mul] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (μ := μ) (p := ENNReal.ofReal P) (q := ENNReal.ofReal S)
        (r := ENNReal.ofReal q)
        (fun a b : ℝ => a * b) 1 continuous_mul hw hy
        (Filter.Eventually.of_forall (fun x => by
          simp [Real.norm_eq_abs, one_mul])))
  have hprod : (fun x => ‖g x‖ ^ (1 - θ) * ‖g x‖ ^ θ) = fun x => ‖g x‖ := by
    funext x
    by_cases hzero : ‖g x‖ = 0
    · rw [hzero, Real.zero_rpow (by linarith only [hθ1]),
        Real.zero_rpow (by linarith only [hθ0]), zero_mul]
    · rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero))]
      norm_num
  have hwp : eLpNorm (fun x => ‖g x‖ ^ (1 - θ)) (ENNReal.ofReal P) μ =
      eLpNorm g 2 μ ^ (1 - θ) := by
    have hraw := eLpNorm_norm_rpow g hg (q := 1 - θ)
      (by linarith only [hθ1]) (p := ENNReal.ofReal P)
    have hPexp : ENNReal.ofReal P * ENNReal.ofReal (1 - θ) = 2 := by
      rw [← ENNReal.ofReal_mul hP.le, hPdef, div_mul_cancel₀ _ hne]
      simp
    rw [hPexp] at hraw
    simpa using hraw
  have hys : eLpNorm (fun x => ‖g x‖ ^ θ) (ENNReal.ofReal S) μ =
      eLpNorm g 6 μ ^ θ := by
    have hraw := eLpNorm_norm_rpow g hg (q := θ) hθ0 (p := ENNReal.ofReal S)
    have hSexp : ENNReal.ofReal S * ENNReal.ofReal θ = 6 := by
      rw [← ENNReal.ofReal_mul hS.le, hSdef, div_mul_cancel₀ _ hθne]
      simp
    rw [hSexp] at hraw
    simpa using hraw
  rw [hprod, hwp, hys, eLpNorm_norm g hg] at hholder
  rw [← hθdef]
  exact hholder

set_option linter.unusedVariables false in
/-- **`eq:interp-step1`.**  For `2 ≤ q ≤ 6` the `L^q` seminorm on a Euclidean
ball interpolates between the `L²` and the `L⁶` seminorms with the exponent
`θ = 3(1/2 − 1/q)` of `paper/ckn.tex`. -/
theorem lpNormOn_interpolate_two_six_ball
    {q : ℝ} (hq2 : 2 ≤ q) (hq6 : q ≤ 6) {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    (v : Vec 3 → ℝ)
    (hv : AEStronglyMeasurable v (volume.restrict (euclideanBall x₀ r))) :
    lpNormOn (ENNReal.ofReal q) (euclideanBall x₀ r) v ^ q ≤
      lpNormOn 2 (euclideanBall x₀ r) v ^ (q * (1 - 3 * (1 / 2 - 1 / q))) *
        lpNormOn 6 (euclideanBall x₀ r) v ^ (q * (3 * (1 / 2 - 1 / q))) := by
  rcases eq_or_lt_of_le hq2 with hq2' | hq2'
  · subst hq2'
    norm_num [lpNormOn]
  rcases eq_or_lt_of_le hq6 with hq6' | hq6'
  · subst hq6'
    norm_num [lpNormOn]
  have hq0 : (0 : ℝ) < q := by linarith only [hq2']
  have hbase := eLpNorm_interpolate_two_six_public (μ :=
    volume.restrict (euclideanBall x₀ r)) hq2' hq6' hv
  have hstep := ENNReal.rpow_le_rpow hbase hq0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, mul_comm (1 - 3 * (1 / 2 - 1 / q)) q,
    mul_comm (3 * (1 / 2 - 1 / q)) q] at hstep
  exact hstep

end CKN
