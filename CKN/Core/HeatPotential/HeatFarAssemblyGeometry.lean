-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatFarStripBound
import CKN.Core.HeatPotential.GeneralSymbolHeatKernelSplitData
import CKN.Foundation.Parabolic.BallDisplays

/-!
# Geometry of a far shell and the mass of its source

Fix a base point `z`, a radius `r > 0` and a shell index `j ≥ 6`, and write
`R = 2 ^ j r` for the inner radius of the shell
`multiplierHeatShellSet z r j`.  Two facts about that shell are used by every
far estimate.

* **Separation.**  An observation point `q` in the closed ball of radius `r`
  around `z` is separated from every shell point `v` whose time lies below
  `q.2`: the parabolic gauge
  `max ‖q.1 - v.1‖ √(q.2 - v.2)` is at least `R / 2`.  The shell is at
  parabolic distance at least `R` from `z` while `q` is at distance at most
  `r ≤ R / 64`, so the excess `R - r` survives in whichever of the two
  coordinates carries the shell separation.  When the shell separates in time
  and the shell point lies *after* `z`, no such `q` exists at all, which is
  why the causal restriction `q.2 ≥ v.2` is part of the statement.

* **Mass.**  The shell sits inside a parabolic cylinder of radius `4 R`, so
  the Morrey seminorm of the source controls its absolute mass by
  `R ^ (5 - 5/θ)` and the source is integrable there.

Both statements fix their constants before the source and before the shell
data.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat

/-- A square root bound transported to the square. -/
private lemma farShellAssembly_geometry_sq_of_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (h : Real.sqrt x ≤ y) :
    x ≤ y ^ 2 := by
  have hsq : x = (Real.sqrt x) ^ 2 := (Real.sq_sqrt hx).symm
  rw [hsq]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- The inner radius of a far shell is at least `64 r`. -/
theorem farShellAssembly_radius_ge {r : ℝ} (hr : 0 < r) {j : ℕ} (hj : 6 ≤ j) :
    64 * r ≤ (2 : ℝ) ^ j * r := by
  rw [show (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) by norm_num]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hr.le

/-- **Parabolic separation on a far shell.**  An observation point in the
closed ball of radius `r` around `z` sees every causally relevant point of the
shell `multiplierHeatShellSet z r j` at parabolic gauge at least
`(2 ^ j r) / 2`. -/
theorem farShellAssembly_gauge_lower {z v q : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hj : 6 ≤ j) (hv : v ∈ multiplierHeatShellSet z r j)
    (hq : q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hqv : 0 ≤ q.2 - v.2) :
    (2 : ℝ) ^ j * r / 2 ≤
      max (vec3EuclideanNorm (q.1 - v.1)) (Real.sqrt (q.2 - v.2)) := by
  set R : ℝ := (2 : ℝ) ^ j * r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hR64 : 64 * r ≤ R := farShellAssembly_radius_ge hr hj
  obtain ⟨-, hvout⟩ := hv
  have hvz : R ≤ dist v z := by
    by_contra hcon
    exact hvout (Metric.mem_ball.mpr (not_le.mp hcon))
  rw [dist_eq_parabolicDist] at hvz
  have hvz' : R ≤ max (vec3EuclideanNorm (v.1 - z.1)) (Real.sqrt |v.2 - z.2|) := hvz
  have hqz : dist q z ≤ r := Metric.mem_closedBall.mp hq
  rw [dist_eq_parabolicDist] at hqz
  have hqs : vec3EuclideanNorm (q.1 - z.1) ≤ r := (le_max_left _ _).trans hqz
  have hqt : Real.sqrt |q.2 - z.2| ≤ r := (le_max_right _ _).trans hqz
  have hqt2 : |q.2 - z.2| ≤ r ^ 2 := farShellAssembly_geometry_sq_of_sqrt_le (abs_nonneg _) hqt
  have hrsq : r ^ 2 ≤ R ^ 2 / 4096 := by
    have h1 : 0 ≤ r := hr.le
    nlinarith only [hR64, h1, hRpos]
  rcases le_max_iff.mp hvz' with hcase | hcase
  · refine le_trans ?_ (le_max_left _ _)
    have htri : vec3EuclideanNorm (v.1 - z.1) ≤
        vec3EuclideanNorm (q.1 - v.1) + vec3EuclideanNorm (q.1 - z.1) := by
      have hsplit : v.1 - z.1 = -(q.1 - v.1) + (q.1 - z.1) := by abel
      rw [hsplit]
      exact (vec3EuclideanNorm_add_le _ _).trans_eq
        (by rw [vec3EuclideanNorm_neg])
    linarith only [hcase, htri, hqs, hR64, hr]
  · refine le_trans ?_ (le_max_right _ _)
    have hsq : R ^ 2 ≤ |v.2 - z.2| := by
      have hpow : R ^ 2 ≤ (Real.sqrt |v.2 - z.2|) ^ 2 :=
        pow_le_pow_left₀ hRpos.le hcase 2
      rwa [Real.sq_sqrt (abs_nonneg _)] at hpow
    have hR2pos : (0 : ℝ) < R ^ 2 := pow_pos hRpos 2
    have hquarter : R ^ 2 / 4 ≤ q.2 - v.2 := by
      rcases le_or_gt v.2 z.2 with hvt | hvt
      · have habs : |v.2 - z.2| = z.2 - v.2 := by
          rw [abs_of_nonpos (by linarith only [hvt])]; ring
        have hlow : -(r ^ 2) ≤ q.2 - z.2 := (abs_le.mp hqt2).1
        rw [habs] at hsq
        linarith only [hsq, hlow, hrsq, hR2pos]
      · have habs : |v.2 - z.2| = v.2 - z.2 := by
          rw [abs_of_nonneg (by linarith only [hvt])]
        have hhigh : q.2 - z.2 ≤ r ^ 2 := (abs_le.mp hqt2).2
        rw [habs] at hsq
        exact absurd hqv (by
          have : q.2 - v.2 ≤ r ^ 2 - R ^ 2 := by linarith only [hsq, hhigh]
          have hneg : r ^ 2 - R ^ 2 < 0 := by
            linarith only [hrsq, hR2pos]
          exact not_le.mpr (by linarith only [this, hneg]))
    have hhalf : R / 2 = Real.sqrt ((R / 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    rw [hhalf]
    refine Real.sqrt_le_sqrt ?_
    have : (R / 2) ^ 2 = R ^ 2 / 4 := by ring
    linarith only [hquarter, this.le, this.ge]

/-- The far shell sits inside the parabolic ball of radius `2 ^ (j+1) r`. -/
theorem farShellAssembly_shell_subset_ball (z : ParabolicPoint) (r : ℝ) (j : ℕ) :
    multiplierHeatShellSet z r j ⊆ Metric.ball z (2 * ((2 : ℝ) ^ j * r)) := by
  intro v hv
  have h := hv.1
  rwa [show (2 : ℝ) ^ (j + 1) * r = 2 * ((2 : ℝ) ^ j * r) by rw [pow_succ]; ring] at h

/-- The far shell is a measurable set. -/
theorem farShellAssembly_measurableSet_shell (z : ParabolicPoint) (r : ℝ) (j : ℕ) :
    MeasurableSet (multiplierHeatShellSet z r j) :=
  Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet

/-- **Source mass on a far shell.**  One constant, fixed before the source and
before the shell data, bounds the absolute mass of a finite-Morrey source on
the shell of inner radius `2 ^ j r` by `(2 ^ j r) ^ (5 - 5/θ)` times its
Morrey seminorm, and the source is integrable there. -/
theorem farShellAssembly_exists_shell_mass_bound {P θ : ℝ} (hP : 1 ≤ P)
    (hPθ : P ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {G : ParabolicPoint → ℝ}, AEMeasurable G volume → morreyNorm P θ G < ∞ →
        ∀ (z : ParabolicPoint) (r : ℝ) (j : ℕ), 0 < r →
          IntegrableOn G (multiplierHeatShellSet z r j) volume ∧
          (∫ v in multiplierHeatShellSet z r j, |G v|) ≤
            C * ((2 : ℝ) ^ j * r) ^ (5 - 5 / θ) *
              (morreyNorm P θ G).toReal := by
  obtain ⟨C, hC, hB⟩ := exists_stripAbsIntegral_bound hP hPθ
  have hθpos : (0 : ℝ) < θ := lt_of_lt_of_le zero_lt_one (hP.trans hPθ)
  refine ⟨1024 * C, by positivity, ?_⟩
  intro G hG hGM z r j hr
  set R : ℝ := (2 : ℝ) ^ j * r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hincl : multiplierHeatShellSet z r j ⊆
      parabolicStrip z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R) := by
    rw [parabolicStrip_self]
    intro v hv
    have hball := farShellAssembly_shell_subset_ball z r j hv
    have hcyl := metricBall_subset_parabolicCylinder_doubled z
      (r := 2 * R) (by positivity) hball
    rwa [show 2 * (2 * R) = 4 * R by ring] at hcyl
  obtain ⟨hint, hbd⟩ := hB hG hGM z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R)
    (by positivity) le_rfl
  refine ⟨hint.mono_set hincl, ?_⟩
  have habs : IntegrableOn (fun v => |G v|)
      (parabolicStrip z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R)) volume := hint.abs
  have hmono : (∫ v in multiplierHeatShellSet z r j, |G v|) ≤
      ∫ v in parabolicStrip z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R), |G v| := by
    refine setIntegral_mono_set habs ?_ (Filter.Eventually.of_forall hincl)
    exact Filter.Eventually.of_forall fun v => abs_nonneg _
  refine hmono.trans (hbd.trans ?_)
  have hMnn : (0 : ℝ) ≤ (morreyNorm P θ G).toReal := ENNReal.toReal_nonneg
  refine mul_le_mul_of_nonneg_right ?_ hMnn
  have h4 : (4 * R) ^ (2 - 5 / θ : ℝ) ≤ 16 * R ^ (2 - 5 / θ : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hRpos.le]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hRpos.le _)
    have hle : (4 : ℝ) ^ (2 - 5 / θ : ℝ) ≤ (4 : ℝ) ^ (2 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (0 : ℝ) ≤ 5 / θ := by positivity
      linarith only [this]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hle
    norm_num at hle
    exact hle
  have hcube : (4 * R) ^ 3 = 64 * R ^ 3 := by ring
  have hsplit : R ^ 3 * R ^ (2 - 5 / θ : ℝ) = R ^ (5 - 5 / θ : ℝ) := by
    rw [show (R : ℝ) ^ 3 = R ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast],
      ← Real.rpow_add hRpos]
    congr 1
    push_cast
    ring
  have hrnn : (0 : ℝ) ≤ R ^ (2 - 5 / θ : ℝ) := Real.rpow_nonneg hRpos.le _
  calc C * (4 * R) ^ 3 * (4 * R) ^ (2 - 5 / θ : ℝ)
      = (C * (64 * R ^ 3)) * (4 * R) ^ (2 - 5 / θ : ℝ) := by rw [hcube]
    _ ≤ (C * (64 * R ^ 3)) * (16 * R ^ (2 - 5 / θ : ℝ)) := by
        refine mul_le_mul_of_nonneg_left h4 ?_
        have : (0 : ℝ) ≤ R ^ 3 := by positivity
        positivity
    _ = 1024 * C * (R ^ 3 * R ^ (2 - 5 / θ : ℝ)) := by ring
    _ = 1024 * C * R ^ (5 - 5 / θ : ℝ) := by rw [hsplit]

end CKN.Core.HeatPotential
