-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.UniformCutoffFamilyGeometry
import CKN.Core.Endgame.UniformCutoffFamilySeparated
import CKN.Core.Endgame.UniformCutoffFamilyTimeProfile
import CKN.Foundation.Harmonic.InteriorEstimatesBasic
import CKN.Pressure.PkBoundsCylinder

/-!
# The translated and parabolically rescaled cutoff family

A single fixed profile, the product of the repository's convolution ball
cutoff in space and the fixed temporal profile of
`CKN.Core.Endgame.uniformTimeProfile`, is translated to a space-time centre
`z` and rescaled parabolically by a radius `a`: the spatial variable is
measured in units of `a` and the time variable in units of `a ^ 2`.

The resulting `endgameCutoff z ha` equals one on the parabolic ball of radius
`a` about `z`, has topological support inside the parabolic ball of radius
`2 * a` about `z`, and obeys the derivative bounds

`|∂_j φ| ≤ C / a`,  `|∂_t φ| ≤ C / a ^ 2`,  `|∂_i ∂_j φ| ≤ C / a ^ 2`

with the one numerical constant `uniformCutoffConstant`, which does not depend
on the centre `z`, on the radius `a`, or on any solution. The `a ^ (-1)` and
`a ^ (-2)` factors come from the chain rule for the rescaling map, which is
carried out inside the fixed ball cutoff of `CKN.mollifiedBallCutoff` in space
and in `endgameTimeCutoff_abs_deriv_le` in time.
-/

open Set Metric
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Endgame

/-- Twice a positive radius is positive; this names the spatial scale of the
cutoff family. -/
theorem two_mul_radius_pos {a : ℝ} (ha : 0 < a) : (0 : ℝ) < 2 * a := by
  linarith only [ha]

/-! ## The two factors -/

/-- The temporal factor of the cutoff family: the fixed temporal profile read
in units of `a ^ 2` about the time `z.2`. -/
def endgameTimeCutoff (z : ParabolicPoint) (a : ℝ) : ℝ → ℝ :=
  fun t => uniformTimeProfile ((t - z.2) / a ^ 2)

/-- The spatial factor of the cutoff family: the repository's convolution ball
cutoff at centre `z.1` and radius `2 * a`. -/
def endgameSpaceCutoff (z : ParabolicPoint) {a : ℝ} (ha : 0 < a) : Vec3 → ℝ :=
  mollifiedBallCutoff z.1 (two_mul_radius_pos ha)

/-- The cutoff of the quantitative endgame at space-time centre `z` and
parabolic radius `a`. -/
def endgameCutoff (z : ParabolicPoint) {a : ℝ} (ha : 0 < a) : Vec3 × ℝ → ℝ :=
  fun w => endgameSpaceCutoff z ha w.1 * endgameTimeCutoff z a w.2

/-! ## The temporal factor -/

/-- The temporal factor is smooth to every order. -/
theorem endgameTimeCutoff_smooth (z : ParabolicPoint) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (endgameTimeCutoff z a) :=
  uniformTimeProfile_smooth.comp ((contDiff_id.sub contDiff_const).div_const _)

/-- The temporal factor never exceeds one in absolute value. -/
theorem endgameTimeCutoff_abs_le_one (z : ParabolicPoint) (a t : ℝ) :
    |endgameTimeCutoff z a t| ≤ 1 :=
  uniformTimeProfile_abs_le_one _

/-- The temporal factor equals one on the time interval of half-width
`a ^ 2` about `z.2`. -/
theorem endgameTimeCutoff_eq_one {z : ParabolicPoint} {a t : ℝ} (ha : 0 < a)
    (ht : |t - z.2| < a ^ 2) : endgameTimeCutoff z a t = 1 := by
  have hpos : (0 : ℝ) < a ^ 2 := by positivity
  refine uniformTimeProfile_eq_one ?_
  rw [abs_div, abs_of_pos hpos, div_le_one hpos]
  linarith only [ht]

/-- The temporal factor vanishes outside the time interval of half-width
`2 * a ^ 2` about `z.2`. -/
theorem endgameTimeCutoff_eq_zero {z : ParabolicPoint} {a t : ℝ} (ha : 0 < a)
    (ht : 2 * a ^ 2 ≤ |t - z.2|) : endgameTimeCutoff z a t = 0 := by
  have hpos : (0 : ℝ) < a ^ 2 := by positivity
  refine uniformTimeProfile_eq_zero ?_
  rw [abs_div, abs_of_pos hpos, le_div_iff₀ hpos]
  linarith only [ht]

/-- The chain rule for the temporal rescaling: the derivative of the temporal
factor is the profile derivative divided by `a ^ 2`. -/
theorem endgameTimeCutoff_hasDerivAt (z : ParabolicPoint) (a t : ℝ) :
    HasDerivAt (endgameTimeCutoff z a)
      (deriv uniformTimeProfile ((t - z.2) / a ^ 2) * (1 / a ^ 2)) t := by
  have harg : HasDerivAt (fun s : ℝ => (s - z.2) / a ^ 2) (1 / a ^ 2) t := by
    simpa using ((hasDerivAt_id t).sub_const z.2).div_const (a ^ 2)
  have hprofile :=
    (uniformTimeProfile_smooth.differentiable (by simp)
      ((t - z.2) / a ^ 2)).hasDerivAt
  exact hprofile.comp t harg

/-- The temporal derivative bound: it carries the factor `a ^ (-2)` of the
parabolic rescaling. -/
theorem endgameTimeCutoff_abs_deriv_le {z : ParabolicPoint} {a : ℝ} (ha : 0 < a)
    (t : ℝ) : |deriv (endgameTimeCutoff z a) t| ≤ 16 / a ^ 2 := by
  have hpos : (0 : ℝ) < a ^ 2 := by positivity
  rw [(endgameTimeCutoff_hasDerivAt z a t).deriv, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / a ^ 2)]
  have hprofile := uniformTimeProfile_abs_deriv_le ((t - z.2) / a ^ 2)
  calc
    |deriv uniformTimeProfile ((t - z.2) / a ^ 2)| * (1 / a ^ 2) ≤
        16 * (1 / a ^ 2) := by
      exact mul_le_mul_of_nonneg_right hprofile (by positivity)
    _ = 16 / a ^ 2 := by ring

/-- The topological support of the temporal factor lies in the closed time
interval of half-width `2 * a ^ 2` about `z.2`. -/
theorem endgameTimeCutoff_tsupport_subset {z : ParabolicPoint} {a : ℝ}
    (ha : 0 < a) :
    tsupport (endgameTimeCutoff z a) ⊆
      Icc (z.2 - 2 * a ^ 2) (z.2 + 2 * a ^ 2) := by
  refine closure_minimal ?_ isClosed_Icc
  intro t ht
  rw [mem_Icc]
  by_contra hcon
  refine ht (endgameTimeCutoff_eq_zero ha ?_)
  rw [le_abs]
  rcases not_and_or.mp hcon with h | h
  · exact Or.inr (by linarith only [not_le.mp h])
  · exact Or.inl (by linarith only [not_le.mp h])

/-! ## The spatial factor -/

/-- The spatial factor is smooth to every order. -/
theorem endgameSpaceCutoff_smooth (z : ParabolicPoint) {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ (⊤ : ℕ∞) (endgameSpaceCutoff z ha) :=
  mollifiedBallCutoff_smooth z.1 (two_mul_radius_pos ha)

/-- The spatial factor never exceeds one in absolute value. -/
theorem endgameSpaceCutoff_abs_le_one (z : ParabolicPoint) {a : ℝ} (ha : 0 < a)
    (x : Vec3) : |endgameSpaceCutoff z ha x| ≤ 1 := by
  have hnn : 0 ≤ endgameSpaceCutoff z ha x :=
    mollifiedBallCutoff_nonneg z.1 (two_mul_radius_pos ha) x
  have hle : endgameSpaceCutoff z ha x ≤ 1 :=
    mollifiedBallCutoff_le_one z.1 (two_mul_radius_pos ha) x
  rw [abs_of_nonneg hnn]
  exact hle

/-- The spatial factor equals one on the Euclidean ball of radius `a`. -/
theorem endgameSpaceCutoff_eq_one {z : ParabolicPoint} {a : ℝ} (ha : 0 < a)
    {x : Vec3} (hx : vec3EuclideanNorm (x - z.1) < a) :
    endgameSpaceCutoff z ha x = 1 := by
  refine mollifiedBallCutoff_eq_one_on_inner z.1 (two_mul_radius_pos ha) ?_
  refine (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by positivity : (0 : ℝ) < 13 * (2 * a) / 20)).2 ?_
  rw [← vec3EuclideanNorm_eq_vecNorm]
  linarith only [hx, ha]

/-- The topological support of the spatial factor lies in the Euclidean ball of
radius `3 * a / 2`. -/
theorem endgameSpaceCutoff_tsupport_subset (z : ParabolicPoint) {a : ℝ}
    (ha : 0 < a) :
    tsupport (endgameSpaceCutoff z ha) ⊆ euclideanBall z.1 (3 * a / 2) := by
  have h := mollifiedBallCutoff_tsupport_subset_outer z.1 (two_mul_radius_pos ha)
  have hrad : 3 * (2 * a) / 4 = 3 * a / 2 := by ring
  rw [hrad] at h
  exact h

/-- The first spatial derivative bound of the spatial factor, at the scale
`2 * a`. -/
theorem endgameSpaceCutoff_abs_spatialDeriv_le (z : ParabolicPoint) {a : ℝ}
    (ha : 0 < a) (j : Fin 3) (x : Vec3) :
    |spatialDeriv (endgameSpaceCutoff z ha) j x| ≤
      cutoffGradientConstant / (2 * a) :=
  pressure_cutoff_spatialDeriv_bound z.1 (two_mul_radius_pos ha) x j

/-- The second spatial derivative bound of the spatial factor, at the scale
`2 * a`. -/
theorem endgameSpaceCutoff_abs_mixedSecond_le (z : ParabolicPoint) {a : ℝ}
    (ha : 0 < a) (i j : Fin 3) (x : Vec3) :
    |mixedSecond (endgameSpaceCutoff z ha) i j x| ≤
      cutoffSecondDerivativeConstant / (2 * a) ^ 2 :=
  pressure_cutoff_mixedSecond_bound z.1 (two_mul_radius_pos ha) x i j

/-! ## The unit-scale constants are nonnegative -/

/-- The single numerical constant of the cutoff family: it depends on nothing
but the fixed profile, and in particular not on the centre, the radius, or any
solution. -/
def uniformCutoffConstant : ℝ :=
  max (max cutoffGradientConstant cutoffSecondDerivativeConstant) 16

/-- The constant of the cutoff family is positive. -/
theorem uniformCutoffConstant_pos : 0 < uniformCutoffConstant :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

/-- The constant of the cutoff family is nonnegative. -/
theorem uniformCutoffConstant_nonneg : 0 ≤ uniformCutoffConstant :=
  uniformCutoffConstant_pos.le

private theorem gradient_constant_le : cutoffGradientConstant ≤ uniformCutoffConstant :=
  le_trans (le_max_left _ _) (le_max_left _ _)

private theorem second_constant_le :
    cutoffSecondDerivativeConstant ≤ uniformCutoffConstant :=
  le_trans (le_max_right _ _) (le_max_left _ _)

private theorem sixteen_le : (16 : ℝ) ≤ uniformCutoffConstant :=
  le_max_right _ _

/-! ## The rescaled cutoff -/

/-- The cutoff is smooth to every order. -/
theorem endgameCutoff_smooth (z : ParabolicPoint) {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ (⊤ : ℕ∞) (endgameCutoff z ha) :=
  contDiff_separatedProduct (endgameSpaceCutoff_smooth z ha)
    (endgameTimeCutoff_smooth z a)

/-- The topological support of the cutoff lies in the product of the spatial
ball of radius `3 * a / 2` and the time interval of half-width `2 * a ^ 2`. -/
theorem endgameCutoff_tsupport_prod (z : ParabolicPoint) {a : ℝ} (ha : 0 < a) :
    tsupport (endgameCutoff z ha) ⊆
      euclideanBall z.1 (3 * a / 2) ×ˢ Icc (z.2 - 2 * a ^ 2) (z.2 + 2 * a ^ 2) :=
  (tsupport_separatedProduct_subset _ _).trans
    (Set.prod_mono (endgameSpaceCutoff_tsupport_subset z ha)
      (endgameTimeCutoff_tsupport_subset ha))

/-- The cutoff has compact support. -/
theorem endgameCutoff_hasCompactSupport (z : ParabolicPoint) {a : ℝ}
    (ha : 0 < a) : HasCompactSupport (endgameCutoff z ha) := by
  refine HasCompactSupport.intro
    ((isCompact_euclideanClosedBall z.1 (R := 3 * a / 2) (by positivity)).prod
      (isCompact_Icc (a := z.2 - 2 * a ^ 2) (b := z.2 + 2 * a ^ 2))) ?_
  intro w hw
  by_contra hne
  have hmem := endgameCutoff_tsupport_prod z ha (subset_tsupport _ hne)
  refine hw ⟨?_, hmem.2⟩
  refine (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
    (by positivity : (0 : ℝ) ≤ 3 * a / 2)).2 ?_
  exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by positivity : (0 : ℝ) < 3 * a / 2)).1 hmem.1).le

/-- The cutoff equals one on the parabolic ball of radius `a` about `z`. -/
theorem endgameCutoff_eq_one {z : ParabolicPoint} {a : ℝ} (ha : 0 < a)
    {w : ParabolicPoint} (hw : w ∈ Metric.ball z a) :
    endgameCutoff z ha w = 1 := by
  have hspace := vec3EuclideanNorm_lt_of_mem_parabolicBall hw
  have htime := abs_time_sub_lt_of_mem_parabolicBall hw
  show endgameSpaceCutoff z ha w.1 * endgameTimeCutoff z a w.2 = 1
  rw [endgameSpaceCutoff_eq_one ha hspace, endgameTimeCutoff_eq_one ha htime,
    mul_one]

/-- The topological support of the cutoff lies in the parabolic ball of radius
`2 * a` about `z`. -/
theorem endgameCutoff_tsupport_subset (z : ParabolicPoint) {a : ℝ} (ha : 0 < a) :
    tsupport (endgameCutoff z ha) ⊆
      parabolicHomeomorph.symm ⁻¹' Metric.ball z (2 * a) := by
  intro w hw
  obtain ⟨hx, ht⟩ := endgameCutoff_tsupport_prod z ha hw
  have hspace : vec3EuclideanNorm (w.1 - z.1) < 2 * a := by
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : (0 : ℝ) < 3 * a / 2)).1 hx
    rw [← vec3EuclideanNorm_eq_vecNorm] at hx'
    linarith only [hx', ha]
  have htime : |w.2 - z.2| < (2 * a) ^ 2 := by
    rw [mem_Icc] at ht
    have habs : |w.2 - z.2| ≤ 2 * a ^ 2 :=
      abs_le.2 ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
    have hsq : (0 : ℝ) < a ^ 2 := by positivity
    have hexp : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
    rw [hexp]
    linarith only [habs, hsq]
  exact mem_parabolicBall_of_bounds (z := z)
    (w := parabolicHomeomorph.symm w) (two_mul_radius_pos ha) hspace htime

/-! ## The derivative bounds of the rescaled cutoff -/

/-- The first spatial derivative of the cutoff carries the factor `a ^ (-1)` of
the parabolic rescaling. -/
theorem endgameCutoff_abs_spatialPartial_le (z : ParabolicPoint) {a : ℝ}
    (ha : 0 < a) (j : Fin 3) (w : Vec3 × ℝ) :
    |spatialPartial (endgameCutoff z ha) j w| ≤ uniformCutoffConstant / a := by
  have hsplit : spatialPartial (endgameCutoff z ha) j w =
      spatialDeriv (endgameSpaceCutoff z ha) j w.1 * endgameTimeCutoff z a w.2 :=
    spatialPartial_separatedProduct _ (endgameSpaceCutoff_smooth z ha) j w
  have h1 := endgameSpaceCutoff_abs_spatialDeriv_le z ha j w.1
  have h2 := endgameTimeCutoff_abs_le_one z a w.2
  have hnn : 0 ≤ cutoffGradientConstant / (2 * a) := le_trans (abs_nonneg _) h1
  have hstep : |spatialPartial (endgameCutoff z ha) j w| ≤
      cutoffGradientConstant / (2 * a) := by
    rw [hsplit, abs_mul]
    calc
      |spatialDeriv (endgameSpaceCutoff z ha) j w.1| *
          |endgameTimeCutoff z a w.2| ≤
          cutoffGradientConstant / (2 * a) * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) hnn
      _ = cutoffGradientConstant / (2 * a) := mul_one _
  refine hstep.trans ?_
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a), div_mul_eq_mul_div,
    le_div_iff₀ ha]
  linarith only
    [mul_nonneg (sub_nonneg.mpr gradient_constant_le) ha.le,
      mul_nonneg uniformCutoffConstant_nonneg ha.le]

/-- The time derivative of the cutoff carries the factor `a ^ (-2)` of the
parabolic rescaling. -/
theorem endgameCutoff_abs_timePartial_le (z : ParabolicPoint) {a : ℝ}
    (ha : 0 < a) (w : Vec3 × ℝ) :
    |timePartial (endgameCutoff z ha) w| ≤ uniformCutoffConstant / a ^ 2 := by
  have hsplit : timePartial (endgameCutoff z ha) w =
      endgameSpaceCutoff z ha w.1 * deriv (endgameTimeCutoff z a) w.2 :=
    timePartial_separatedProduct _ (endgameTimeCutoff_smooth z a) w
  have h1 := endgameSpaceCutoff_abs_le_one z ha w.1
  have h2 := endgameTimeCutoff_abs_deriv_le (z := z) ha w.2
  have hnn : (0 : ℝ) ≤ 16 / a ^ 2 := by positivity
  have hstep : |timePartial (endgameCutoff z ha) w| ≤ 16 / a ^ 2 := by
    rw [hsplit, abs_mul]
    calc
      |endgameSpaceCutoff z ha w.1| * |deriv (endgameTimeCutoff z a) w.2| ≤
          1 * (16 / a ^ 2) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 16 / a ^ 2 := one_mul _
  refine hstep.trans ?_
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < a ^ 2), div_mul_eq_mul_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < a ^ 2)]
  linarith only [mul_nonneg (sub_nonneg.mpr sixteen_le) (sq_nonneg a)]

/-- The second spatial derivative of the cutoff carries the factor `a ^ (-2)` of
the parabolic rescaling. -/
theorem endgameCutoff_abs_spatialSecondPartial_le (z : ParabolicPoint) {a : ℝ}
    (ha : 0 < a) (i j : Fin 3) (w : Vec3 × ℝ) :
    |spatialSecondPartial (endgameCutoff z ha) i j w| ≤
      uniformCutoffConstant / a ^ 2 := by
  have hsplit : spatialSecondPartial (endgameCutoff z ha) i j w =
      mixedSecond (endgameSpaceCutoff z ha) j i w.1 * endgameTimeCutoff z a w.2 :=
    spatialSecondPartial_separatedProduct _ (endgameSpaceCutoff_smooth z ha) i j w
  have h1 := endgameSpaceCutoff_abs_mixedSecond_le z ha j i w.1
  have h2 := endgameTimeCutoff_abs_le_one z a w.2
  have hnn : 0 ≤ cutoffSecondDerivativeConstant / (2 * a) ^ 2 :=
    le_trans (abs_nonneg _) h1
  have hstep : |spatialSecondPartial (endgameCutoff z ha) i j w| ≤
      cutoffSecondDerivativeConstant / (2 * a) ^ 2 := by
    rw [hsplit, abs_mul]
    calc
      |mixedSecond (endgameSpaceCutoff z ha) j i w.1| *
          |endgameTimeCutoff z a w.2| ≤
          cutoffSecondDerivativeConstant / (2 * a) ^ 2 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) hnn
      _ = cutoffSecondDerivativeConstant / (2 * a) ^ 2 := mul_one _
  refine hstep.trans ?_
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 * a) ^ 2), div_mul_eq_mul_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < a ^ 2)]
  linarith only
    [mul_nonneg (sub_nonneg.mpr second_constant_le) (sq_nonneg a),
      mul_nonneg uniformCutoffConstant_nonneg (sq_nonneg a)]

/-- The cutoff never exceeds one in absolute value. -/
theorem endgameCutoff_abs_le_one (z : ParabolicPoint) {a : ℝ} (ha : 0 < a)
    (w : Vec3 × ℝ) : |endgameCutoff z ha w| ≤ 1 := by
  have h1 := endgameSpaceCutoff_abs_le_one z ha w.1
  have h2 := endgameTimeCutoff_abs_le_one z a w.2
  show |endgameSpaceCutoff z ha w.1 * endgameTimeCutoff z a w.2| ≤ 1
  rw [abs_mul]
  calc
    |endgameSpaceCutoff z ha w.1| * |endgameTimeCutoff z a w.2| ≤ 1 * 1 :=
      mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The spatial Laplacian of the cutoff is the sum of its three second spatial
derivatives, so it carries the same factor `a ^ (-2)`. -/
theorem endgameCutoff_abs_spatialLaplacian_le (z : ParabolicPoint) {a : ℝ}
    (ha : 0 < a) (w : Vec3 × ℝ) :
    |spatialLaplacian (fun x => endgameCutoff z ha (x, w.2)) w.1| ≤
      3 * (uniformCutoffConstant / a ^ 2) := by
  have hsum : spatialLaplacian (fun x => endgameCutoff z ha (x, w.2)) w.1 =
      ∑ i : Fin 3, spatialSecondPartial (endgameCutoff z ha) i i w := rfl
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ i : Fin 3, |spatialSecondPartial (endgameCutoff z ha) i i w| ≤
        ∑ _i : Fin 3, uniformCutoffConstant / a ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        endgameCutoff_abs_spatialSecondPartial_le z ha i i w
    _ = 3 * (uniformCutoffConstant / a ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num

/-- The common numerical bound for the cutoff value, its time derivative, its
first spatial derivatives and its spatial Laplacian at radius `a`. -/
def endgameCutoffCoefficientBound (a : ℝ) : ℝ :=
  1 + uniformCutoffConstant / a + 3 * (uniformCutoffConstant / a ^ 2)

/-- The common coefficient bound is nonnegative. -/
theorem endgameCutoffCoefficientBound_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ endgameCutoffCoefficientBound a := by
  have h1 : 0 ≤ uniformCutoffConstant / a :=
    div_nonneg uniformCutoffConstant_nonneg ha.le
  have h2 : 0 ≤ uniformCutoffConstant / a ^ 2 :=
    div_nonneg uniformCutoffConstant_nonneg (by positivity)
  rw [endgameCutoffCoefficientBound]
  linarith only [h1, h2]

/-- All four coefficients of the localized heat equation attached to the cutoff
obey the single bound `endgameCutoffCoefficientBound a`. -/
theorem endgameCutoff_coefficient_bounds (z : ParabolicPoint) {a : ℝ}
    (ha : 0 < a) (w : Vec3 × ℝ) :
    |endgameCutoff z ha w| ≤ endgameCutoffCoefficientBound a ∧
      |timePartial (endgameCutoff z ha) w| ≤ endgameCutoffCoefficientBound a ∧
      (∀ j, |spatialPartial (endgameCutoff z ha) j w| ≤
        endgameCutoffCoefficientBound a) ∧
      |spatialLaplacian (fun x => endgameCutoff z ha (x, w.2)) w.1| ≤
        endgameCutoffCoefficientBound a := by
  have h1 : 0 ≤ uniformCutoffConstant / a :=
    div_nonneg uniformCutoffConstant_nonneg ha.le
  have h2 : 0 ≤ uniformCutoffConstant / a ^ 2 :=
    div_nonneg uniformCutoffConstant_nonneg (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := endgameCutoff_abs_le_one z ha w
    rw [endgameCutoffCoefficientBound]
    linarith only [h, h1, h2]
  · have h := endgameCutoff_abs_timePartial_le z ha w
    rw [endgameCutoffCoefficientBound]
    linarith only [h, h1, h2]
  · intro j
    have h := endgameCutoff_abs_spatialPartial_le z ha j w
    rw [endgameCutoffCoefficientBound]
    linarith only [h, h1, h2]
  · have h := endgameCutoff_abs_spatialLaplacian_le z ha w
    rw [endgameCutoffCoefficientBound]
    linarith only [h, h1, h2]

end CKN.Core.Endgame
