-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Cutoff.Profile
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A fixed smooth temporal profile with an explicit derivative bound

This file builds a single fixed smooth one-dimensional temporal profile that
equals `1` on the interval `[-1, 1]` and vanishes outside the open interval
`(-2, 2)`, together with an explicit bound on its first derivative. It is
assembled from two copies of the repository's canonical smooth transition
profile `CKN.smoothTransitionProfile`, one increasing and one decreasing, so
that the resulting profile is symmetric about the origin and its support
collar has width one on each side.

## Main definitions

* `CKN.Core.Endgame.uniformTimeProfile`: the fixed temporal profile.

## Main results

* `uniformTimeProfile_smooth`: the profile is smooth to every order.
* `uniformTimeProfile_eq_one`: the profile equals `1` on `[-1, 1]`.
* `uniformTimeProfile_eq_zero`: the profile vanishes outside `(-2, 2)`.
* `uniformTimeProfile_abs_deriv_le`: the first derivative is bounded by `16`.
-/

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The fixed smooth temporal profile, obtained as the product of an increasing
and a decreasing copy of the canonical transition profile. It equals `1` on
`[-1, 1]` and vanishes outside `(-2, 2)`. -/
def uniformTimeProfile (s : ℝ) : ℝ :=
  smoothTransitionProfile (s + 2) * smoothTransitionProfile (2 - s)

/-- The absolute value of a value of the canonical transition profile is at
most one. -/
private theorem smoothTransitionProfile_abs_le_one (t : ℝ) :
    |smoothTransitionProfile t| ≤ 1 := by
  rw [abs_of_nonneg (smoothTransitionProfile.nonneg t)]
  exact smoothTransitionProfile.le_one t

/-- The fixed temporal profile is smooth to every order. -/
theorem uniformTimeProfile_smooth : ContDiff ℝ (⊤ : ℕ∞) uniformTimeProfile :=
  (smoothTransitionProfile.smooth.comp
      (contDiff_id.add contDiff_const)).mul
    (smoothTransitionProfile.smooth.comp
      (contDiff_const.sub contDiff_id))

/-- The fixed temporal profile is nonnegative. -/
theorem uniformTimeProfile_nonneg (s : ℝ) : 0 ≤ uniformTimeProfile s := by
  unfold uniformTimeProfile
  exact mul_nonneg (smoothTransitionProfile.nonneg _)
    (smoothTransitionProfile.nonneg _)

/-- The fixed temporal profile is at most one. -/
theorem uniformTimeProfile_le_one (s : ℝ) : uniformTimeProfile s ≤ 1 := by
  unfold uniformTimeProfile
  calc
    smoothTransitionProfile (s + 2) * smoothTransitionProfile (2 - s)
        ≤ 1 * 1 :=
      mul_le_mul (smoothTransitionProfile.le_one _)
        (smoothTransitionProfile.le_one _)
        (smoothTransitionProfile.nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The fixed temporal profile takes values in `[-1, 1]`. -/
theorem uniformTimeProfile_abs_le_one (s : ℝ) :
    |uniformTimeProfile s| ≤ 1 := by
  rw [abs_of_nonneg (uniformTimeProfile_nonneg s)]
  exact uniformTimeProfile_le_one s

/-- The fixed temporal profile equals `1` on the interval `[-1, 1]`. -/
theorem uniformTimeProfile_eq_one {s : ℝ} (hs : |s| ≤ 1) :
    uniformTimeProfile s = 1 := by
  have hs₁ : -1 ≤ s := (abs_le.mp hs).1
  have hs₂ : s ≤ 1 := (abs_le.mp hs).2
  unfold uniformTimeProfile
  rw [smoothTransitionProfile.one_of_one_le (show 1 ≤ s + 2 by linarith only [hs₁]),
    smoothTransitionProfile.one_of_one_le (show 1 ≤ 2 - s by linarith only [hs₂])]
  norm_num

/-- The fixed temporal profile vanishes outside the open interval `(-2, 2)`. -/
theorem uniformTimeProfile_eq_zero {s : ℝ} (hs : 2 ≤ |s|) :
    uniformTimeProfile s = 0 := by
  unfold uniformTimeProfile
  by_cases hs' : 0 ≤ s
  · have hsabs : |s| = s := abs_of_nonneg hs'
    rw [hsabs] at hs
    rw [smoothTransitionProfile.zero_of_nonpos
      (show 2 - s ≤ 0 by linarith only [hs])]
    exact mul_zero _
  · have hslt : s < 0 := not_le.mp hs'
    have hsabs : |s| = -s := abs_of_neg hslt
    rw [hsabs] at hs
    rw [smoothTransitionProfile.zero_of_nonpos
      (show s + 2 ≤ 0 by linarith only [hs])]
    exact zero_mul _

/-- The first derivative of the fixed temporal profile is bounded by `16`. -/
theorem uniformTimeProfile_abs_deriv_le (s : ℝ) :
    |deriv uniformTimeProfile s| ≤ 16 := by
  have hL :
      HasDerivAt (fun x : ℝ => smoothTransitionProfile (x + 2))
        (deriv smoothTransitionProfile (s + 2)) s := by
    have h :=
      (smoothTransitionProfile.smooth.differentiable (by simp)
        (s + 2)).hasDerivAt.comp s ((hasDerivAt_id s).add_const 2)
    simpa [Function.comp_def] using h
  have hR :
      HasDerivAt (fun x : ℝ => smoothTransitionProfile (2 - x))
        (-deriv smoothTransitionProfile (2 - s)) s := by
    have h :=
      (smoothTransitionProfile.smooth.differentiable (by simp)
        (2 - s)).hasDerivAt.comp s
        ((hasDerivAt_const s 2).sub (hasDerivAt_id s))
    simpa [Function.comp_def] using h
  have hA :
      |deriv smoothTransitionProfile (s + 2)| ≤ 8 :=
    smoothTransitionProfile.abs_deriv_le_eight _
  have hB :
      |smoothTransitionProfile (2 - s)| ≤ 1 :=
    smoothTransitionProfile_abs_le_one _
  have hC :
      |smoothTransitionProfile (s + 2)| ≤ 1 :=
    smoothTransitionProfile_abs_le_one _
  have hD :
      |deriv smoothTransitionProfile (2 - s)| ≤ 8 :=
    smoothTransitionProfile.abs_deriv_le_eight _
  have hAB :
      |deriv smoothTransitionProfile (s + 2)| *
          |smoothTransitionProfile (2 - s)| ≤ 8 * 1 :=
    mul_le_mul hA hB (abs_nonneg _) (by norm_num)
  have hCD :
      |smoothTransitionProfile (s + 2)| *
          |deriv smoothTransitionProfile (2 - s)| ≤ 1 * 8 :=
    mul_le_mul hC hD (abs_nonneg _) (by norm_num)
  have hd :
      deriv uniformTimeProfile s =
        deriv smoothTransitionProfile (s + 2) * smoothTransitionProfile (2 - s) +
          smoothTransitionProfile (s + 2) *
            (-deriv smoothTransitionProfile (2 - s)) := by
    rw [show uniformTimeProfile =
        (fun x : ℝ => smoothTransitionProfile (x + 2)) *
          (fun x : ℝ => smoothTransitionProfile (2 - x)) from rfl]
    exact (hL.mul hR).deriv
  rw [hd]
  calc
    |deriv smoothTransitionProfile (s + 2) *
          smoothTransitionProfile (2 - s) +
        smoothTransitionProfile (s + 2) *
          (-deriv smoothTransitionProfile (2 - s))| ≤
        |deriv smoothTransitionProfile (s + 2) *
            smoothTransitionProfile (2 - s)| +
          |smoothTransitionProfile (s + 2) *
            (-deriv smoothTransitionProfile (2 - s))| :=
      abs_add_le _ _
    _ =
        |deriv smoothTransitionProfile (s + 2)| *
            |smoothTransitionProfile (2 - s)| +
          |smoothTransitionProfile (s + 2)| *
            |deriv smoothTransitionProfile (2 - s)| := by
      rw [abs_mul, abs_mul, abs_neg]
    _ ≤ 8 * 1 + 1 * 8 := by linarith only [hAB, hCD]
    _ = 16 := by norm_num

end CKN.Core.Endgame
