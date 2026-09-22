-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatFarAssemblyGeometry
import CKN.Core.HeatPotential.FarShell
import CKN.Foundation.Sobolev.Ambient.Basis
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Kernel oscillation across a far shell

Two observation points `w, w'` of the ball of radius `r` around `z` are
compared against a point `v` of the far shell of inner radius `R = 2 ^ j r`,
`j ≥ 6`.  Both causal kernels used by the general-symbol heat potential are
estimated here.

* The **causal heat kernel** `heatPotentialKernel` has a two-step oscillation
  bound valid at every shell point, including those whose time lies between
  the two observation times: the earlier kernel then vanishes, and the later
  one is compared with its own value at the interface time instead.  The
  bound is proportional to the parabolic distance of the two observation
  points.
* The **multiplier heat kernel** `spatialMultiplierHeatKernel σ` is estimated
  only on the part of the shell that lies strictly below both observation
  times, where the mean value theorem applies in space at frozen time and
  then in time at frozen space without meeting the causal interface.  Its
  size is estimated on the whole shell.

Both estimates use the separation `farShellAssembly_gauge_lower`, so the
gauge is at least `R / 2` throughout and the kernel orders four, five and six
turn into powers of `R`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat

/-- A square root bound transported to the square. -/
private lemma farShellAssembly_sq_of_sqrt_le {x y : ℝ} (hx : 0 ≤ x)
    (h : Real.sqrt x ≤ y) : x ≤ y ^ 2 := by
  have hsq : x = (Real.sqrt x) ^ 2 := (Real.sq_sqrt hx).symm
  rw [hsq]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- A negative integer power of a halved radius. -/
private lemma farShellAssembly_half_rpow {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (R / 2) ^ (-(n : ℝ)) = 2 ^ n / R ^ n := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_pow]
  field_simp

/-- Three nonnegative reals are dominated by twice the square root of the sum
of their squares. -/
private lemma farShellAssembly_sum_three_le (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, a i ≤ 2 * Real.sqrt (∑ i, a i ^ 2) := by
  have hS : (0 : ℝ) ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs2 : (Real.sqrt (∑ i, a i ^ 2)) ^ 2 = ∑ i, a i ^ 2 := Real.sq_sqrt hS
  have hsum : (0 : ℝ) ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  have hsq : (∑ i, a i) ^ 2 ≤ (2 * Real.sqrt (∑ i, a i ^ 2)) ^ 2 := by
    rw [mul_pow, hs2, Fin.sum_univ_three, Fin.sum_univ_three]
    nlinarith only [sq_nonneg (a 0 - a 1), sq_nonneg (a 1 - a 2),
      sq_nonneg (a 0 - a 2)]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hsum, Real.sqrt_sq (by positivity)] at h

/-- The operator norm of a linear map on `Vec3` is at most the sum of the
norms of its values on the coordinate directions. -/
private lemma farShellAssembly_opNorm_le_sum (L : Vec3 →L[ℝ] ℂ) :
    ‖L‖ ≤ ∑ i : Fin 3, ‖L (basisVec i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro u
  have hu : L u = ∑ i : Fin 3, u i • L (basisVec i) := by
    conv_lhs => rw [← sum_smul_basisVec u]
    rw [map_sum]
    simp only [map_smul]
  rw [hu]
  calc ‖∑ i : Fin 3, u i • L (basisVec i)‖
      ≤ ∑ i : Fin 3, ‖u i • L (basisVec i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, |u i| * ‖L (basisVec i)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i : Fin 3, ‖u‖ * ‖L (basisVec i)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right
          (by simpa using norm_le_pi_norm u i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖L (basisVec i)‖) * ‖u‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- **Oscillation of the causal heat kernel across a far shell.**  The
difference of the causal heat kernel at two observation points of the ball of
radius `r` is at most `parabolicDist w w'` times `(2 ^ j r) ^ (-4)`, uniformly
over the far shell.  No positivity of the observation times is required: the
interface is crossed by restarting the time comparison at the source time. -/
theorem farShellAssembly_scalar_kernel_diff {z v w w' : ParabolicPoint} {r : ℝ}
    {j : ℕ} (hr : 0 < r) (hj : 6 ≤ j) (hv : v ∈ multiplierHeatShellSet z r j)
    (hw : w ∈ Metric.ball z r) (hw' : w' ∈ Metric.ball z r) (hww' : w.2 ≤ w'.2) :
    |heatPotentialKernel w v - heatPotentialKernel w' v| ≤
      32000000 / ((2 : ℝ) ^ j * r) ^ 4 * parabolicDist w w' := by
  set R : ℝ := (2 : ℝ) ^ j * r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hR64 : 64 * r ≤ R := by rw [hRdef]; exact farShellAssembly_radius_ge hr hj
  have hApos : (0 : ℝ) < R / 2 := by positivity
  have hwc : w ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
    Metric.ball_subset_closedBall hw
  have hw'c : w' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
    Metric.ball_subset_closedBall hw'
  have hw's : vec3EuclideanNorm (w'.1 - z.1) ≤ r := by
    have h := Metric.mem_closedBall.mp hw'c
    rw [dist_eq_parabolicDist] at h
    exact (le_max_left _ _).trans h
  have hD0 : (0 : ℝ) ≤ parabolicDist w w' := by
    rw [← dist_eq_parabolicDist]; exact dist_nonneg
  have hDs : vec3EuclideanNorm (w.1 - w'.1) ≤ parabolicDist w w' := le_max_left _ _
  have hDt : |w.2 - w'.2| ≤ parabolicDist w w' ^ 2 :=
    farShellAssembly_sq_of_sqrt_le (abs_nonneg _) (le_max_right _ _)
  have hDball : parabolicDist w w' ≤ 2 * r := by
    have h1 : dist w z < r := Metric.mem_ball.mp hw
    have h2 : dist w' z < r := Metric.mem_ball.mp hw'
    have htri : dist w w' ≤ dist w z + dist z w' := dist_triangle w z w'
    rw [dist_comm z w'] at htri
    rw [← dist_eq_parabolicDist]
    linarith only [htri, h1, h2]
  -- Separation of the shell from every causally relevant observation point.
  have hsep : ∀ q : ParabolicPoint,
      q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r →
      0 ≤ q.2 - v.2 → R / 2 ≤ rhoTwo (q.1 - v.1) (q.2 - v.2) := by
    intro q hq hqv
    have hg := farShellAssembly_gauge_lower hr hj hv hq hqv
    rw [← hRdef] at hg
    refine hg.trans ?_
    rw [rhoTwo]
    exact max_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg _))
  -- Spatial step, at the earlier observation time.
  have hspace : |heatPotentialKernel w v -
      heatPotentialKernel ((w'.1, w.2) : ParabolicPoint) v| ≤
      900000 / (R / 2) ^ 4 * vec3EuclideanNorm (w.1 - w'.1) := by
    by_cases ht : 0 < w.2 - v.2
    · refine heatPotential_spatial_kernel_difference_abs_le hApos ht ?_
      intro y hy
      have hyc : ((y, w.2) : ParabolicPoint) ∈
          @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
        parabolic_ball_segment_mem hwc hw'c hy rfl
      exact hsep ((y, w.2) : ParabolicPoint) hyc ht.le
    · have h1 : w.2 - v.2 ≤ 0 := le_of_not_gt ht
      have hz1 : heatPotentialKernel w v = 0 := by
        simp only [heatPotentialKernel, pointSub]
        exact heatKernelPlus_eq_zero_of_nonpos h1
      have hz2 : heatPotentialKernel ((w'.1, w.2) : ParabolicPoint) v = 0 := by
        simp only [heatPotentialKernel, pointSub]
        exact heatKernelPlus_eq_zero_of_nonpos h1
      rw [hz1, hz2, sub_zero, abs_zero]
      exact mul_nonneg (by positivity) (vec3EuclideanNorm_nonneg _)
  -- Time step, at the later observation point.
  have htimesep : ∀ s : ℝ, w.2 ≤ s → s ≤ w'.2 → 0 ≤ s - v.2 →
      R / 2 ≤ rhoTwo (w'.1 - v.1) (s - v.2) := by
    intro s hs1 hs2 hsv
    have hqc := parabolic_ball_time_segment_mem hr.le hwc hw'c hw's
      (Set.mem_Icc.mpr ⟨hs1, hs2⟩)
    exact hsep ((w'.1, s) : ParabolicPoint) hqc hsv
  have htime : |heatPotentialKernel ((w'.1, w.2) : ParabolicPoint) v -
      heatPotentialKernel w' v| ≤
      10000000 / (R / 2) ^ 5 * |w.2 - w'.2| := by
    by_cases ht : v.2 ≤ w.2
    · refine heatPotential_time_kernel_difference_abs_le (p := w) (p' := w')
        hApos hww' (by linarith only [ht]) ?_
      intro s hs
      exact htimesep s hs.1 hs.2 (by linarith only [hs.1, ht])
    · have hvw : w.2 < v.2 := lt_of_not_ge ht
      by_cases ht' : w'.2 ≤ v.2
      · have hz1 : heatPotentialKernel ((w'.1, w.2) : ParabolicPoint) v = 0 := by
          simp only [heatPotentialKernel, pointSub]
          exact heatKernelPlus_eq_zero_of_nonpos (by linarith only [hvw])
        have hz2 : heatPotentialKernel w' v = 0 := by
          simp only [heatPotentialKernel, pointSub]
          exact heatKernelPlus_eq_zero_of_nonpos (by linarith only [ht'])
        rw [hz1, hz2, sub_zero, abs_zero]
        positivity
      · have hvw' : v.2 < w'.2 := lt_of_not_ge ht'
        have hrestart := heatPotential_time_kernel_difference_abs_le
          (p := ((w'.1, v.2) : ParabolicPoint)) (p' := w') (v := v) hApos
          hvw'.le (by simp) ?_
        · have hz1 : heatPotentialKernel ((w'.1, w.2) : ParabolicPoint) v =
              heatPotentialKernel ((w'.1, v.2) : ParabolicPoint) v := by
            simp only [heatPotentialKernel, pointSub]
            rw [heatKernelPlus_eq_zero_of_nonpos (by linarith only [hvw]),
              heatKernelPlus_eq_zero_of_nonpos (le_of_eq (sub_self v.2))]
          rw [hz1]
          refine hrestart.trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [abs_of_nonpos (by linarith only [hvw']),
            abs_of_nonpos (by linarith only [hww'])]
          linarith only [hvw]
        · intro s hs
          exact htimesep s (by linarith only [hs.1, hvw]) hs.2
            (by linarith only [hs.1])
  -- Combine the two steps and convert the powers of `R / 2`.
  have hcomb := (abs_sub_le (heatPotentialKernel w v)
    (heatPotentialKernel ((w'.1, w.2) : ParabolicPoint) v)
    (heatPotentialKernel w' v)).trans (add_le_add hspace htime)
  refine hcomb.trans ?_
  have hstep1 : 900000 / (R / 2) ^ 4 * vec3EuclideanNorm (w.1 - w'.1) ≤
      900000 / (R / 2) ^ 4 * parabolicDist w w' :=
    mul_le_mul_of_nonneg_left hDs (by positivity)
  have hstep2 : 10000000 / (R / 2) ^ 5 * |w.2 - w'.2| ≤
      625000 / (R / 2) ^ 4 * parabolicDist w w' := by
    refine (mul_le_mul_of_nonneg_left hDt (by positivity)).trans ?_
    have hkey : 10000000 * parabolicDist w w' ≤ 625000 * (R / 2) := by
      linarith only [hDball, hR64, hD0]
    have hnn : (0 : ℝ) ≤ parabolicDist w w' / (R / 2) ^ 5 := by positivity
    calc 10000000 / (R / 2) ^ 5 * parabolicDist w w' ^ 2
        = (10000000 * parabolicDist w w') *
            (parabolicDist w w' / (R / 2) ^ 5) := by ring
      _ ≤ (625000 * (R / 2)) * (parabolicDist w w' / (R / 2) ^ 5) :=
          mul_le_mul_of_nonneg_right hkey hnn
      _ = 625000 / (R / 2) ^ 4 * parabolicDist w w' := by
          field_simp
  refine (add_le_add hstep1 hstep2).trans ?_
  have hfold : 900000 / (R / 2) ^ 4 * parabolicDist w w' +
      625000 / (R / 2) ^ 4 * parabolicDist w w' =
      1525000 / (R / 2) ^ 4 * parabolicDist w w' := by ring
  rw [hfold]
  refine mul_le_mul_of_nonneg_right ?_ hD0
  have h4 : (0 : ℝ) < R ^ 4 := by positivity
  rw [div_pow, div_div_eq_mul_div]
  gcongr
  norm_num

/-- **Size and oscillation of a multiplier heat kernel across a far shell.**
One constant, fixed after the symbol and before all shell data, bounds the
kernel uniformly on the far shell by `(2 ^ j r) ^ (-4)` and its oscillation
between two observation points of the ball of radius `r` by
`parabolicDist w w'` times `(2 ^ j r) ^ (-5)`, on the part of the shell that
lies strictly below both observation times. -/
theorem farShellAssembly_exists_multiplier_kernel_bounds (σ : Vec3 → ℂ)
    (hσ : SmoothOffOrigin σ) (hhom : IsDegreeOneHomogeneous σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ {z v q : ParabolicPoint} {r : ℝ} {j : ℕ}, 0 < r → 6 ≤ j →
        v ∈ multiplierHeatShellSet z r j →
        q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r →
        ‖spatialMultiplierHeatKernel σ (q.1 - v.1) (q.2 - v.2)‖ ≤
          C / ((2 : ℝ) ^ j * r) ^ 4) ∧
      (∀ {z v w w' : ParabolicPoint} {r : ℝ} {j : ℕ}, 0 < r → 6 ≤ j →
        v ∈ multiplierHeatShellSet z r j →
        w ∈ Metric.ball z r → w' ∈ Metric.ball z r → w.2 ≤ w'.2 → v.2 < w.2 →
        ‖spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) -
            spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2)‖ ≤
          C / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w') := by
  obtain ⟨CK, hCK, hKB⟩ := exists_spatialMultiplierHeatKernel_crossZero_bounds σ
    (contDiffOn_infty.mpr hσ) hhom
  obtain ⟨CD, hCD, hDB⟩ :=
    exists_spatialMultiplierHeatKernel_bounds_of_degreeOne σ
      (contDiffOn_infty.mpr hσ) hhom
  refine ⟨128 * CK, by positivity, ?_, ?_⟩
  · intro z v q r j hr hj hv hq
    have hRpos : (0 : ℝ) < (2 : ℝ) ^ j * r := by positivity
    by_cases ht : 0 < q.2 - v.2
    · have hg := farShellAssembly_gauge_lower hr hj hv hq ht.le
      have habs : |q.2 - v.2| = q.2 - v.2 := abs_of_nonneg ht.le
      have hm : (2 : ℝ) ^ j * r / 2 ≤
          max (vec3EuclideanNorm (q.1 - v.1)) (Real.sqrt |q.2 - v.2|) := by
        rw [habs]; exact hg
      have hpow : (max (vec3EuclideanNorm (q.1 - v.1))
          (Real.sqrt |q.2 - v.2|)) ^ (-4 : ℝ) ≤
          ((2 : ℝ) ^ j * r / 2) ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hm (by norm_num)
      have hval : ((2 : ℝ) ^ j * r / 2) ^ (-4 : ℝ) =
          16 / ((2 : ℝ) ^ j * r) ^ 4 := by
        rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
          farShellAssembly_half_rpow hRpos]
        norm_num
      calc ‖spatialMultiplierHeatKernel σ (q.1 - v.1) (q.2 - v.2)‖
          ≤ CK * (max (vec3EuclideanNorm (q.1 - v.1))
              (Real.sqrt |q.2 - v.2|)) ^ (-4 : ℝ) :=
            (hKB (q.1 - v.1) (q.2 - v.2)).1
        _ ≤ CK * (((2 : ℝ) ^ j * r / 2) ^ (-4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow hCK
        _ = CK * (16 / ((2 : ℝ) ^ j * r) ^ 4) := by rw [hval]
        _ = 16 * CK / ((2 : ℝ) ^ j * r) ^ 4 := by ring
        _ ≤ 128 * CK / ((2 : ℝ) ^ j * r) ^ 4 := by
            gcongr
            norm_num
    · rw [spatialMultiplierHeatKernel_of_nonpos σ _ (le_of_not_gt ht), norm_zero]
      positivity
  · intro z v w w' r j hr hj hv hw hw' hww' hvw
    have hRpos : (0 : ℝ) < (2 : ℝ) ^ j * r := by positivity
    have hR64 : 64 * r ≤ (2 : ℝ) ^ j * r := farShellAssembly_radius_ge hr hj
    have hApos : (0 : ℝ) < (2 : ℝ) ^ j * r / 2 := by positivity
    have ht0 : 0 < w.2 - v.2 := by linarith only [hvw]
    have hwc : w ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
      Metric.ball_subset_closedBall hw
    have hw'c : w' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
      Metric.ball_subset_closedBall hw'
    have hw's : vec3EuclideanNorm (w'.1 - z.1) ≤ r := by
      have h := Metric.mem_closedBall.mp hw'c
      rw [dist_eq_parabolicDist] at h
      exact (le_max_left _ _).trans h
    have hD0 : (0 : ℝ) ≤ parabolicDist w w' := by
      rw [← dist_eq_parabolicDist]; exact dist_nonneg
    have hDs : vec3EuclideanNorm (w.1 - w'.1) ≤ parabolicDist w w' :=
      le_max_left _ _
    have hDt : |w.2 - w'.2| ≤ parabolicDist w w' ^ 2 :=
      farShellAssembly_sq_of_sqrt_le (abs_nonneg _) (le_max_right _ _)
    have hDball : parabolicDist w w' ≤ 2 * r := by
      have h1 : dist w z < r := Metric.mem_ball.mp hw
      have h2 : dist w' z < r := Metric.mem_ball.mp hw'
      have htri : dist w w' ≤ dist w z + dist z w' := dist_triangle w z w'
      rw [dist_comm z w'] at htri
      rw [← dist_eq_parabolicDist]
      linarith only [htri, h1, h2]
    -- Spatial step at the earlier observation time.
    have hspace : ‖spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) -
        spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2)‖ ≤
        2 * CK * (((2 : ℝ) ^ j * r / 2) ^ (-5 : ℝ)) *
          vec3EuclideanNorm (w.1 - w'.1) := by
      have hdiffAt : ∀ y : Vec3, y ∈ segment ℝ w.1 w'.1 →
          DifferentiableAt ℝ
            (fun u : Vec3 => spatialMultiplierHeatKernel σ (u - v.1) (w.2 - v.2)) y := by
        intro y _
        have hinner : HasFDerivAt (fun u : Vec3 => u - v.1)
            (ContinuousLinearMap.id ℝ Vec3) y := by
          simpa using (hasFDerivAt_id (𝕜 := ℝ) y).sub_const v.1
        have houter := ((hDB (y - v.1) (w.2 - v.2) ht0).1).hasFDerivAt
        exact (houter.comp y hinner).differentiableAt
      have hfd : ∀ y : Vec3,
          fderiv ℝ (fun u : Vec3 =>
              spatialMultiplierHeatKernel σ (u - v.1) (w.2 - v.2)) y =
            fderiv ℝ (fun x : Vec3 =>
              spatialMultiplierHeatKernel σ x (w.2 - v.2)) (y - v.1) := by
        intro y
        have hinner : HasFDerivAt (fun u : Vec3 => u - v.1)
            (ContinuousLinearMap.id ℝ Vec3) y := by
          simpa using (hasFDerivAt_id (𝕜 := ℝ) y).sub_const v.1
        have houter := ((hDB (y - v.1) (w.2 - v.2) ht0).1).hasFDerivAt
        have hcomp := houter.comp y hinner
        rw [ContinuousLinearMap.comp_id] at hcomp
        exact hcomp.fderiv
      have hbound : ∀ y : Vec3, y ∈ segment ℝ w.1 w'.1 →
          ‖fderiv ℝ (fun u : Vec3 =>
              spatialMultiplierHeatKernel σ (u - v.1) (w.2 - v.2)) y‖ ≤
            2 * CK * (((2 : ℝ) ^ j * r / 2) ^ (-5 : ℝ)) := by
        intro y hy
        have hyc : ((y, w.2) : ParabolicPoint) ∈
            @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
          parabolic_ball_segment_mem hwc hw'c hy rfl
        have hg := farShellAssembly_gauge_lower hr hj hv hyc ht0.le
        have habs : |w.2 - v.2| = w.2 - v.2 := abs_of_nonneg ht0.le
        have hm : (2 : ℝ) ^ j * r / 2 ≤
            max (vec3EuclideanNorm (y - v.1)) (Real.sqrt |w.2 - v.2|) := by
          rw [habs]; exact hg
        have hpow : (max (vec3EuclideanNorm (y - v.1))
            (Real.sqrt |w.2 - v.2|)) ^ (-5 : ℝ) ≤
            ((2 : ℝ) ^ j * r / 2) ^ (-5 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hApos hm (by norm_num)
        rw [hfd y]
        refine (farShellAssembly_opNorm_le_sum _).trans ?_
        refine (farShellAssembly_sum_three_le _ (fun i => norm_nonneg _)).trans ?_
        have hgrad := (hKB (y - v.1) (w.2 - v.2)).2.1
        calc 2 * Real.sqrt (∑ i : Fin 3,
              ‖(fderiv ℝ (fun x : Vec3 =>
                spatialMultiplierHeatKernel σ x (w.2 - v.2)) (y - v.1))
                  (basisVec i)‖ ^ 2)
            ≤ 2 * (CK * (max (vec3EuclideanNorm (y - v.1))
                (Real.sqrt |w.2 - v.2|)) ^ (-5 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hgrad (by norm_num)
          _ ≤ 2 * (CK * (((2 : ℝ) ^ j * r / 2) ^ (-5 : ℝ))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hpow hCK) (by norm_num)
          _ = 2 * CK * (((2 : ℝ) ^ j * r / 2) ^ (-5 : ℝ)) := by ring
      have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
        (f := fun u : Vec3 => spatialMultiplierHeatKernel σ (u - v.1) (w.2 - v.2))
        (s := segment ℝ w.1 w'.1) hdiffAt hbound (convex_segment w.1 w'.1)
        (left_mem_segment ℝ w.1 w'.1) (right_mem_segment ℝ w.1 w'.1)
      rw [← norm_neg]
      have hneg : -(spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) -
          spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2)) =
          spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2) -
          spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) := by ring
      rw [hneg]
      refine hmvt.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine le_trans (vec3_norm_le_euclidean_norm _) ?_
      rw [← vec3EuclideanNorm_neg (w'.1 - w.1), neg_sub]
    -- Time step at the later observation point.
    have htime : ‖spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2) -
        spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2)‖ ≤
        CK * (((2 : ℝ) ^ j * r / 2) ^ (-6 : ℝ)) * |w.2 - w'.2| := by
      have hpos : ∀ s : ℝ, s ∈ Set.Icc w.2 w'.2 → 0 < s - v.2 := by
        intro s hs
        linarith only [hs.1, ht0]
      have hdiffAt : ∀ s : ℝ, s ∈ Set.Icc w.2 w'.2 →
          DifferentiableAt ℝ (fun u : ℝ =>
            spatialMultiplierHeatKernel σ (w'.1 - v.1) (u - v.2)) s := by
        intro s hs
        have hd := ((hKB (w'.1 - v.1) (s - v.2)).2.2
          (ne_of_gt (hpos s hs))).1
        exact (HasDerivAt.comp_sub_const s v.2 hd.hasDerivAt).differentiableAt
      have hbound : ∀ s : ℝ, s ∈ Set.Icc w.2 w'.2 →
          ‖deriv (fun u : ℝ =>
            spatialMultiplierHeatKernel σ (w'.1 - v.1) (u - v.2)) s‖ ≤
            CK * (((2 : ℝ) ^ j * r / 2) ^ (-6 : ℝ)) := by
        intro s hs
        have hd := ((hKB (w'.1 - v.1) (s - v.2)).2.2
          (ne_of_gt (hpos s hs))).1
        have hderiv : deriv (fun u : ℝ =>
            spatialMultiplierHeatKernel σ (w'.1 - v.1) (u - v.2)) s =
            deriv (fun u : ℝ =>
              spatialMultiplierHeatKernel σ (w'.1 - v.1) u) (s - v.2) :=
          (HasDerivAt.comp_sub_const s v.2 hd.hasDerivAt).deriv
        rw [hderiv]
        have hqc := parabolic_ball_time_segment_mem hr.le hwc hw'c hw's hs
        have hg := farShellAssembly_gauge_lower hr hj hv hqc (hpos s hs).le
        have habs : |s - v.2| = s - v.2 := abs_of_nonneg (hpos s hs).le
        have hm : (2 : ℝ) ^ j * r / 2 ≤
            max (vec3EuclideanNorm (w'.1 - v.1)) (Real.sqrt |s - v.2|) := by
          rw [habs]; exact hg
        have hpow : (max (vec3EuclideanNorm (w'.1 - v.1))
            (Real.sqrt |s - v.2|)) ^ (-6 : ℝ) ≤
            ((2 : ℝ) ^ j * r / 2) ^ (-6 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hApos hm (by norm_num)
        exact ((hKB (w'.1 - v.1) (s - v.2)).2.2
          (ne_of_gt (hpos s hs))).2.trans
          (mul_le_mul_of_nonneg_left hpow hCK)
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
        (f := fun u : ℝ => spatialMultiplierHeatKernel σ (w'.1 - v.1) (u - v.2))
        (s := Set.Icc w.2 w'.2) hdiffAt hbound (convex_Icc w.2 w'.2)
        (Set.left_mem_Icc.mpr hww') (Set.right_mem_Icc.mpr hww')
      rw [← norm_neg]
      have hneg : -(spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2) -
          spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2)) =
          spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2) -
          spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2) := by ring
      rw [hneg]
      refine hmvt.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [Real.norm_eq_abs, abs_sub_comm]
    -- Combine.
    have htri : ‖spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) -
        spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2)‖ ≤
        ‖spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) -
          spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2)‖ +
        ‖spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2) -
          spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2)‖ := by
      have h := norm_add_le
        (spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) -
          spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2))
        (spatialMultiplierHeatKernel σ (w'.1 - v.1) (w.2 - v.2) -
          spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2))
      rwa [sub_add_sub_cancel] at h
    refine (htri.trans (add_le_add hspace htime)).trans ?_
    have h5 : ((2 : ℝ) ^ j * r / 2) ^ (-5 : ℝ) = 32 / ((2 : ℝ) ^ j * r) ^ 5 := by
      rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num,
        farShellAssembly_half_rpow hRpos]
      norm_num
    have h6 : ((2 : ℝ) ^ j * r / 2) ^ (-6 : ℝ) = 64 / ((2 : ℝ) ^ j * r) ^ 6 := by
      rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num,
        farShellAssembly_half_rpow hRpos]
      norm_num
    rw [h5, h6]
    have hstep1 : 2 * CK * (32 / ((2 : ℝ) ^ j * r) ^ 5) *
        vec3EuclideanNorm (w.1 - w'.1) ≤
        64 * CK / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w' := by
      refine le_trans (mul_le_mul_of_nonneg_left hDs (by positivity)) ?_
      refine mul_le_mul_of_nonneg_right (le_of_eq ?_) hD0
      field_simp
      ring
    have hstep2 : CK * (64 / ((2 : ℝ) ^ j * r) ^ 6) * |w.2 - w'.2| ≤
        2 * CK / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w' := by
      refine le_trans (mul_le_mul_of_nonneg_left hDt (by positivity)) ?_
      have hkey : 64 * CK * parabolicDist w w' ≤
          2 * CK * ((2 : ℝ) ^ j * r) := by
        have hDR : 32 * parabolicDist w w' ≤ (2 : ℝ) ^ j * r := by
          linarith only [hDball, hR64]
        nlinarith only [hDR, hCK, hD0]
      have hnn : (0 : ℝ) ≤ parabolicDist w w' / ((2 : ℝ) ^ j * r) ^ 6 := by
        positivity
      calc CK * (64 / ((2 : ℝ) ^ j * r) ^ 6) * parabolicDist w w' ^ 2
          = (64 * CK * parabolicDist w w') *
              (parabolicDist w w' / ((2 : ℝ) ^ j * r) ^ 6) := by ring
        _ ≤ (2 * CK * ((2 : ℝ) ^ j * r)) *
              (parabolicDist w w' / ((2 : ℝ) ^ j * r) ^ 6) :=
            mul_le_mul_of_nonneg_right hkey hnn
        _ = 2 * CK / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w' := by
            field_simp
    refine (add_le_add hstep1 hstep2).trans ?_
    have hfold : 64 * CK / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w' +
        2 * CK / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w' =
        66 * CK / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w' := by ring
    rw [hfold]
    refine mul_le_mul_of_nonneg_right ?_ hD0
    gcongr
    norm_num

end CKN.Core.HeatPotential
