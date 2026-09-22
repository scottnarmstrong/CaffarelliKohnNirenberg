-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

/-! # Radius-gauge contents for cylinders and parabolic balls

Countable covers are indexed by subsets of the natural numbers, so empty and
finite covers are allowed, including at dimension zero. Costs are powers of
radii, not diameters. The finite-scale cylinder-to-ball comparison preserves
the radii; the reverse comparison doubles them and shifts the top time forward.
The positive-scale limits give the source's Hausdorff radius gauges in every
nonnegative dimension.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

noncomputable section
namespace CKN.Foundation.Parabolic

/-- Radius content for a specified family of covering sets, allowing every
empty, finite or countable family with positive radii at most the scale. -/
def radiusCoverContent (shape : ParabolicPoint → ℝ → Set ParabolicPoint)
    (α δ : ℝ) (E : Set ParabolicPoint) : ℝ≥0∞ :=
  ⨅ (T : Set ℕ) (z : T → ParabolicPoint) (r : T → ℝ)
    (_ : ∀ i, 0 < r i ∧ r i ≤ δ) (_ : E ⊆ ⋃ i, shape (z i) (r i)),
      ∑' i, ENNReal.ofReal (r i) ^ α

/-- Finite-scale spherical content with parabolic ball radii as gauge. -/
def parabolicBallRadiusContent (α δ : ℝ) (E : Set ParabolicPoint) : ℝ≥0∞ :=
  radiusCoverContent (fun z r => Metric.ball z r) α δ E

/-- Finite-scale content with backward cylinder radii as gauge. -/
def parabolicCylinderRadiusContent (α δ : ℝ) (E : Set ParabolicPoint) : ℝ≥0∞ :=
  radiusCoverContent (fun z r => parabolicCylinder z.1 z.2 r) α δ E

private theorem radiusCoverContent_le
    (shape : ParabolicPoint → ℝ → Set ParabolicPoint) (α δ : ℝ) (E : Set ParabolicPoint)
    (T : Set ℕ) (z : T → ParabolicPoint) (r : T → ℝ)
    (hr : ∀ i, 0 < r i ∧ r i ≤ δ) (hcover : E ⊆ ⋃ i, shape (z i) (r i)) :
    radiusCoverContent shape α δ E ≤ ∑' i, ENNReal.ofReal (r i) ^ α := by
  exact iInf_le_of_le T (iInf_le_of_le z (iInf_le_of_le r
    (iInf_le_of_le hr (iInf_le _ hcover))))

private theorem ball_subset_forward_cylinder (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    Metric.ball z r ⊆ parabolicCylinder z.1 (z.2 + r ^ 2) (2 * r) := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_parabolicDist] at hw
  obtain ⟨hx, ht⟩ := max_lt_iff.mp hw
  have ht' := (Real.sqrt_lt' hr).mp ht
  obtain ⟨hlo, hhi⟩ := abs_lt.mp ht'
  refine ⟨hx.trans (by linarith only [hr]), ?_, ?_⟩
  · nlinarith only [hlo, sq_pos_of_pos hr]
  · linarith only [hhi]

/-- Cylinders are covered by parabolic balls with unchanged radii, giving the
sharp constant-one comparison at each scale and every dimension. -/
theorem parabolicBallRadiusContent_le_cylinder (α δ : ℝ) (E : Set ParabolicPoint) :
    parabolicBallRadiusContent α δ E ≤ parabolicCylinderRadiusContent α δ E := by
  unfold parabolicCylinderRadiusContent radiusCoverContent
  refine le_iInf fun T => le_iInf fun z => le_iInf fun r =>
    le_iInf fun hr => le_iInf fun hc => ?_
  apply radiusCoverContent_le _ α δ E T (fun i => ((z i).1, (z i).2 - (r i)^2/2)) r hr
  intro w hw
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hc hw)
  exact mem_iUnion.mpr ⟨i, parabolicCylinder_subset_metricBall (hr i).1 hi⟩

/-- A parabolic ball fits in the cylinder of twice its radius with top time
shifted forward by the square of its original radius. -/
theorem parabolicCylinderRadiusContent_two_mul_le (α δ : ℝ) (hα : 0 ≤ α)
    (E : Set ParabolicPoint) :
    parabolicCylinderRadiusContent α (2 * δ) E ≤
      (2 : ℝ≥0∞) ^ α * parabolicBallRadiusContent α δ E := by
  unfold parabolicBallRadiusContent radiusCoverContent
  simp_rw [ENNReal.mul_iInf_of_ne (by positivity : (2 : ℝ≥0∞) ^ α ≠ 0)
    (by finiteness : (2 : ℝ≥0∞) ^ α ≠ ⊤)]
  refine le_iInf fun T => le_iInf fun z => le_iInf fun r =>
    le_iInf fun hr => le_iInf fun hc => ?_
  have hb := radiusCoverContent_le (fun z r => parabolicCylinder z.1 z.2 r)
    α (2 * δ) E T (fun i => ((z i).1, (z i).2 + (r i)^2)) (fun i => 2 * r i)
    (fun i => ⟨mul_pos (by norm_num) (hr i).1,
      mul_le_mul_of_nonneg_left (hr i).2 (by norm_num)⟩) (by
      intro w hw
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hc hw)
      exact mem_iUnion.mpr ⟨i, ball_subset_forward_cylinder (z i) (hr i).1 hi⟩)
  calc
    _ ≤ ∑' i : T, ENNReal.ofReal (2 * r i) ^ α := hb
    _ = ∑' i : T, (2 : ℝ≥0∞) ^ α * ENNReal.ofReal (r i) ^ α := by
      congr 1
      funext i
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ hα]
      norm_num
    _ = _ := ENNReal.tsum_mul_left

/-- The two finite-scale comparisons between radius-gauge contents, with the
same scale in the sharp direction and doubled scale in the reverse direction. -/
theorem parabolic_radius_content_comparison (α : ℝ) (hα : 0 ≤ α)
    (δ : ℝ) (E : Set ParabolicPoint) :
    parabolicBallRadiusContent α δ E ≤ parabolicCylinderRadiusContent α δ E ∧
      parabolicCylinderRadiusContent α (2 * δ) E ≤
        (2 : ℝ≥0∞) ^ α * parabolicBallRadiusContent α δ E := by
  exact ⟨parabolicBallRadiusContent_le_cylinder α δ E,
    parabolicCylinderRadiusContent_two_mul_le α δ hα E⟩

/-- The Hausdorff radius gauge obtained from parabolic-ball covers in
`def:parabolic-hausdorff`, with the scale tending to zero. -/
def parabolicBallRadiusHausdorffContent (α : ℝ) (E : Set ParabolicPoint) :
    ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), parabolicBallRadiusContent α δ E

/-- The Hausdorff radius gauge obtained by replacing parabolic-ball covers
with backward-cylinder covers. -/
def parabolicCylinderRadiusHausdorffContent (α : ℝ) (E : Set ParabolicPoint) :
    ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), parabolicCylinderRadiusContent α δ E

/-- The parabolic-ball and backward-cylinder radius gauges obey the source
comparison in every nonnegative dimension, and therefore have the same null
sets. The first inequality retains constant one. -/
theorem parabolic_radius_hausdorff_content_comparison (α : ℝ) (hα : 0 ≤ α)
    (E : Set ParabolicPoint) :
    parabolicBallRadiusHausdorffContent α E ≤
        parabolicCylinderRadiusHausdorffContent α E ∧
      parabolicCylinderRadiusHausdorffContent α E ≤
        (2 : ℝ≥0∞) ^ α * parabolicBallRadiusHausdorffContent α E ∧
      (parabolicBallRadiusHausdorffContent α E = 0 ↔
        parabolicCylinderRadiusHausdorffContent α E = 0) := by
  have hball : parabolicBallRadiusHausdorffContent α E ≤
      parabolicCylinderRadiusHausdorffContent α E := by
    unfold parabolicBallRadiusHausdorffContent parabolicCylinderRadiusHausdorffContent
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact le_iSup_of_le δ (le_iSup_of_le hδ
      (parabolicBallRadiusContent_le_cylinder α δ E))
  have hcylinder : parabolicCylinderRadiusHausdorffContent α E ≤
      (2 : ℝ≥0∞) ^ α * parabolicBallRadiusHausdorffContent α E := by
    unfold parabolicCylinderRadiusHausdorffContent parabolicBallRadiusHausdorffContent
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    have hhalf : 0 < δ / 2 := by positivity
    have hscale := parabolicCylinderRadiusContent_two_mul_le α (δ / 2) hα E
    have hscale' : parabolicCylinderRadiusContent α δ E ≤
        (2 : ℝ≥0∞) ^ α * parabolicBallRadiusContent α (δ / 2) E := by
      rw [show 2 * (δ / 2) = δ by ring] at hscale
      exact hscale
    calc
      parabolicCylinderRadiusContent α δ E ≤
          (2 : ℝ≥0∞) ^ α * parabolicBallRadiusContent α (δ / 2) E := hscale'
      _ ≤ (2 : ℝ≥0∞) ^ α *
          (⨆ (ε : ℝ) (_ : 0 < ε), parabolicBallRadiusContent α ε E) := by
        exact mul_le_mul_of_nonneg_left
          (le_iSup_of_le (δ / 2) (le_iSup_of_le hhalf le_rfl)) (by positivity)
  refine ⟨hball, hcylinder, ?_⟩
  constructor
  · intro hzero
    apply le_antisymm _ bot_le
    simpa [hzero] using hcylinder
  · intro hzero
    apply le_antisymm _ bot_le
    simpa [hzero] using hball

end CKN.Foundation.Parabolic
