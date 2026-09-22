-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.Localization
import CKN.Foundation.Sobolev.Cutoff.Ball
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Geometry of parabolic balls in space-time coordinates

The parabolic metric on space-time is the maximum of the Euclidean distance of
the spatial coordinates and the square root of the time difference.  This module
translates membership in a parabolic metric ball into the two explicit
coordinate bounds, relates the two Euclidean norm names available on `Vec3`,
and records that the product box with radius `r` in space and time half-width
`r ^ 2` contains the preimage of the parabolic ball of the much smaller radius
`r / 4`.

The results are stated for the ambient `Vec3` and the parabolic metric used
throughout the localization arguments.
-/

open Set Metric
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The parabolic Euclidean norm on `Vec3` agrees with the general Euclidean
norm for coordinate vectors.  Both are the square root of the sum of squares of
the coordinates, differing only in how the square is spelled. -/
theorem vec3EuclideanNorm_eq_vecNorm (v : Vec3) :
    vec3EuclideanNorm v = vecEuclideanNorm v := by
  simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- Membership in a parabolic ball follows from the two explicit coordinate
bounds: the spatial distance is below `r` and the absolute time difference is
below `r ^ 2`. -/
theorem mem_parabolicBall_of_bounds {z w : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hs : vec3EuclideanNorm (w.1 - z.1) < r) (ht : |w.2 - z.2| < r ^ 2) :
    w ∈ Metric.ball z r := by
  rw [Metric.mem_ball, dist_eq_parabolicDist]
  change max (vec3EuclideanNorm (w.1 - z.1)) (Real.sqrt |w.2 - z.2|) < r
  exact max_lt hs ((Real.sqrt_lt' hr).mpr ht)

/-- The spatial coordinate of a point of a parabolic ball is within the ball
radius of the centre in the parabolic Euclidean norm. -/
theorem vec3EuclideanNorm_lt_of_mem_parabolicBall {z w : ParabolicPoint} {r : ℝ}
    (hw : w ∈ Metric.ball z r) : vec3EuclideanNorm (w.1 - z.1) < r := by
  rw [Metric.mem_ball, dist_eq_parabolicDist] at hw
  change max (vec3EuclideanNorm (w.1 - z.1)) (Real.sqrt |w.2 - z.2|) < r at hw
  exact (max_lt_iff.mp hw).1

/-- The time coordinate of a point of a parabolic ball differs from the centre
time by less than the square of the ball radius. -/
theorem abs_time_sub_lt_of_mem_parabolicBall {z w : ParabolicPoint} {r : ℝ}
    (hw : w ∈ Metric.ball z r) : |w.2 - z.2| < r ^ 2 := by
  rw [Metric.mem_ball, dist_eq_parabolicDist] at hw
  change max (vec3EuclideanNorm (w.1 - z.1)) (Real.sqrt |w.2 - z.2|) < r at hw
  have hsqrt : Real.sqrt |w.2 - z.2| < r := (max_lt_iff.mp hw).2
  have hr : 0 < r := lt_of_le_of_lt (Real.sqrt_nonneg _) hsqrt
  exact (Real.sqrt_lt' hr).mp hsqrt

/-- The product box with spatial radius `r` and time half-width `r ^ 2`
contains the preimage of the parabolic ball of radius `r / 4`. -/
theorem parabolicBall_preimage_subset_box {z₀ : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (r / 4) ⊆
      vec3Ball z₀.1 r ×ˢ Set.Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2) := by
  intro w hw
  have hb := hw
  change dist (parabolicHomeomorph.symm w) z₀ < r / 4 at hb
  rw [dist_eq_parabolicDist] at hb
  change max (vec3EuclideanNorm (w.1 - z₀.1)) (Real.sqrt |w.2 - z₀.2|) < r / 4 at hb
  have hspace := (max_lt_iff.mp hb).1
  have htime := (Real.sqrt_lt (abs_nonneg _) (by positivity : 0 ≤ r / 4)).mp
    (max_lt_iff.mp hb).2
  refine ⟨?_, ?_⟩
  · change vec3EuclideanNorm (w.1 - z₀.1) < r
    linarith only [hspace, hr]
  · have habs : |w.2 - z₀.2| < r ^ 2 :=
      htime.trans (by nlinarith only [sq_pos_of_pos hr])
    have ht := abs_lt.mp habs
    constructor <;> linarith only [ht.1, ht.2]

end CKN.Core.Endgame
