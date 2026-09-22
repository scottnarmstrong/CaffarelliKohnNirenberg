-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Covering.SumRadiiDefectBalls
import CKN.Covering.CylinderRadiusContent
import CKN.Foundation.Parabolic.Covering
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# The fixed-scale covering estimate `eq:P1-delta`

Paper display `eq:P1-delta`, in the measure-estimate step of the proof of `thm:C`.
For `S ⊆ V` with `V` open, a scale `δ > 0` and `0 < ε`, suppose every `z ∈ S` has a
radius `r < δ` whose parabolic ball lies in `V` and whose backward cylinder carries a
defect of size `(ε / 2) * r`:

`(ε / 2) * r < ∫_{Cyl_r(z)} g`.

Then the radius-gauge content of `S` at the enlarged scale `5 * δ` is bounded by the
mass of `g` over `V`:

`parabolicBallRadiusContent 1 (5 * δ) S ≤ (10 / ε) * ∫_V g`.

The proof is a Vitali selection of pairwise disjoint balls at shrinking scales, followed
by the established sum-of-radii estimate `CKN.sum_radii_le_of_disjoint_defect_balls` for the
defect radii.  The auxiliary `radiusCoverContent_le_of_countable` reindexes a countable
covering family by a subset of `ℕ`, which is the index shape required by
`radiusCoverContent`.

Both results below live in the namespace `CKN.Foundation.Parabolic`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Reindexing bound for `radiusCoverContent`: a countable covering family of sets
`shape (c i) (ρ i)` with radii bounded by `δ` controls the radius-gauge content, and the
sum of the radius powers is the `tsum` over the original countable index type.  This is
the shape required by `radiusCoverContent`, whose covers are indexed by subsets of `ℕ`. -/
theorem radiusCoverContent_le_of_countable
    (shape : ParabolicPoint → ℝ → Set ParabolicPoint) (α δ : ℝ) (E : Set ParabolicPoint)
    {ι : Type*} [Countable ι] (c : ι → ParabolicPoint) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i ∧ ρ i ≤ δ) (hcover : E ⊆ ⋃ i, shape (c i) (ρ i)) :
    radiusCoverContent shape α δ E ≤ ∑' i, ENNReal.ofReal (ρ i) ^ α := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  let T : Set ℕ := Set.range f
  let e : ι ≃ T := Equiv.ofInjective f hf
  let z' : T → ParabolicPoint := fun n => c (e.symm n)
  let r' : T → ℝ := fun n => ρ (e.symm n)
  have hρ' : ∀ n : T, 0 < r' n ∧ r' n ≤ δ := fun n => hρ (e.symm n)
  have hcover' : E ⊆ ⋃ n : T, shape (z' n) (r' n) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    refine mem_iUnion.mpr ⟨e i, ?_⟩
    have hei : e.symm (e i) = i := e.symm_apply_apply i
    show x ∈ shape (c (e.symm (e i))) (ρ (e.symm (e i)))
    rw [hei]
    exact hi
  have hle : radiusCoverContent shape α δ E ≤ ∑' n : T, ENNReal.ofReal (r' n) ^ α :=
    iInf_le_of_le T (iInf_le_of_le z' (iInf_le_of_le r'
      (iInf_le_of_le hρ' (iInf_le _ hcover'))))
  exact hle.trans (le_of_eq (Equiv.tsum_eq e.symm fun i => ENNReal.ofReal (ρ i) ^ α))

/-- `eq:P1-delta`, in the proof of `thm:C`: if every
`z ∈ S` has a ball of radius `r < δ` inside `V` whose backward cylinder carries the defect
`(ε / 2) * r < ∫_{Cyl_r(z)} g`, then the radius-gauge content of `S` at the enlarged scale
`5 * δ` obeys `parabolicBallRadiusContent 1 (5 * δ) S ≤ (10 / ε) * ∫_V g`.

The paper's hypotheses that `V` is open, that `S ⊆ V` and that `δ > 0` are recorded but
not consumed by the covering argument, exactly as in
`parabolicHausdorffMeasure_one_le_integral_of_small_cylinders`. -/
theorem parabolicBallRadiusContent_one_le_integral_of_defect_radii
    {g : ParabolicPoint → ℝ≥0∞} {V S : Set ParabolicPoint} {ε : ℝ≥0} {δ : ℝ}
    (_ : IsOpen V) (_ : S ⊆ V) (hε : 0 < ε) (_ : 0 < δ)
    (hdefect : ∀ z ∈ S, ∃ r : ℝ, 0 < r ∧ r < δ ∧ Metric.ball z r ⊆ V ∧
      (ε : ℝ≥0∞) / 2 * ENNReal.ofReal r < ∫⁻ y in parabolicCylinder z.1 z.2 r, g y) :
    parabolicBallRadiusContent 1 (5 * δ) S ≤ (10 : ℝ≥0∞) / (ε : ℝ≥0∞) * ∫⁻ y in V, g y := by
  let radius : S → ℝ := fun z => Classical.choose (hdefect z z.property)
  have radius_spec (z : S) :
      0 < radius z ∧ radius z < δ ∧ Metric.ball (z : ParabolicPoint) (radius z) ⊆ V ∧
        (ε : ℝ≥0∞) / 2 * ENNReal.ofReal (radius z) <
          ∫⁻ y in parabolicCylinder z.1.1 z.1.2 (radius z), g y :=
    Classical.choose_spec (hdefect z z.property)
  let ball : S → Set ParabolicPoint := fun z => Metric.ball (z : ParabolicPoint) (radius z)
  have ball_nonempty (z : S) : (ball z).Nonempty :=
    ⟨z.1, Metric.mem_ball_self (radius_spec z).1⟩
  obtain ⟨u, _hu, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun z : S => ball z) Set.univ radius 2 (by norm_num)
      (fun a _ => (radius_spec a).1.le) δ (fun a _ => (radius_spec a).2.1.le)
      (fun a _ => ball_nonempty a)
  let index : Type := {z : S // z ∈ u}
  set_option linter.style.haveILetI false in
  haveI : Countable index := by
    dsimp [index]
    refine hdisj.countable_of_isOpen ?_ ?_
    · intro z _
      show IsOpen (Metric.ball (z : ParabolicPoint) (radius z))
      exact Metric.isOpen_ball
    · intro z _
      exact ball_nonempty z
  have hcover : S ⊆ ⋃ i : index, Metric.ball (i.1 : ParabolicPoint) (5 * radius i.1) := by
    intro x hx
    obtain ⟨b, hb, hbne, hbrad⟩ := hcov ⟨x, hx⟩ trivial
    have hdist : dist x (b : ParabolicPoint) < radius ⟨x, hx⟩ + radius b :=
      Metric.dist_lt_add_of_nonempty_ball_inter_ball
        (x := x) (y := (b : ParabolicPoint))
        (ε₁ := radius ⟨x, hx⟩) (ε₂ := radius b) hbne
    have hsum : radius ⟨x, hx⟩ + dist x (b : ParabolicPoint) < 5 * radius b := by
      calc radius ⟨x, hx⟩ + dist x (b : ParabolicPoint)
          < radius ⟨x, hx⟩ + (radius ⟨x, hx⟩ + radius b) := add_lt_add_right hdist _
        _ ≤ 5 * radius b := by linarith only [hbrad, (radius_spec b).1]
    refine mem_iUnion.mpr ⟨⟨b, hb⟩, ?_⟩
    exact Metric.ball_subset_ball' (le_of_lt hsum)
      (Metric.mem_ball_self (radius_spec ⟨x, hx⟩).1)
  have hrad_sum : (∑' i : index, ENNReal.ofReal (radius i.1)) ≤
      2 / (ε : ℝ≥0∞) * ∫⁻ y in V, g y := by
    have hmain := CKN.sum_radii_le_of_disjoint_defect_balls (g := g) (V := V) hε
      (z := fun i : index => (i.1 : ParabolicPoint))
      (r := fun i : index => radius i.1)
      (fun i => (radius_spec i.1).1)
      (fun i => (radius_spec i.1).2.2.1)
      (fun i j hij => hdisj i.2 j.2 (fun h => hij (Subtype.ext h)))
      (fun i => (radius_spec i.1).2.2.2)
    exact hmain.1.trans hmain.2
  have hcontent : parabolicBallRadiusContent 1 (5 * δ) S ≤
      ∑' i : index, ENNReal.ofReal (5 * radius i.1) ^ (1 : ℝ) := by
    have h := radiusCoverContent_le_of_countable
      (fun z r => Metric.ball z r) 1 (5 * δ) S
      (fun i : index => (i.1 : ParabolicPoint)) (fun i : index => 5 * radius i.1)
      (fun i => ⟨mul_pos (by norm_num) (radius_spec i.1).1,
        by linarith only [(radius_spec i.1).2.1]⟩)
      hcover
    simpa [parabolicBallRadiusContent] using h
  have hterm (i : index) : ENNReal.ofReal (5 * radius i.1) ^ (1 : ℝ) =
      (5 : ℝ≥0∞) * ENNReal.ofReal (radius i.1) := by
    rw [ENNReal.rpow_one, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
    simp
  have hconst : (5 : ℝ≥0∞) * (2 / (ε : ℝ≥0∞) * ∫⁻ y in V, g y) =
      (10 : ℝ≥0∞) / (ε : ℝ≥0∞) * ∫⁻ y in V, g y := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    have h52 : (5 : ℝ≥0∞) * 2 = 10 := by norm_num
    rw [← h52]
    ac_rfl
  calc
    parabolicBallRadiusContent 1 (5 * δ) S
        ≤ ∑' i : index, ENNReal.ofReal (5 * radius i.1) ^ (1 : ℝ) := hcontent
    _ = ∑' i : index, (5 : ℝ≥0∞) * ENNReal.ofReal (radius i.1) := tsum_congr hterm
    _ = (5 : ℝ≥0∞) * ∑' i : index, ENNReal.ofReal (radius i.1) := ENNReal.tsum_mul_left
    _ ≤ (5 : ℝ≥0∞) * (2 / (ε : ℝ≥0∞) * ∫⁻ y in V, g y) :=
        mul_le_mul_of_nonneg_left hrad_sum bot_le
    _ = (10 : ℝ≥0∞) / (ε : ℝ≥0∞) * ∫⁻ y in V, g y := hconst

end CKN.Foundation.Parabolic
