-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.BallsVsCylindersFaithful
import CKN.Foundation.Parabolic.Covering

/-!
# The sum-of-radii estimate for disjoint defect balls

Paper label `eq:sum-radii` in `paper/ckn.tex` is the measure-theoretic
step closing Step 4 of the proof of `thm:C`.  A family of parabolic balls
`𝔅_{r_j}(z_j)` is pairwise disjoint and sits inside a set `V`; each of the
associated parabolic cylinders `Cyl_{r_j}(z_j)` carries a defect, meaning that
`(ε / 2) * r_j` is dominated strictly by the `g`-mass of the cylinder.  The
estimate sums the radii over the index set:

`∑_j r_j ≤ (2 / ε) * ∑_j ∫_{Cyl_{r_j}(z_j)} g ≤ (2 / ε) * ∫_V g`.

Because each cylinder is contained in the ball of the *same* centre and radius
(`parabolicCylinder_subset_metricBall_same_center`), the cylinders inherit the
pairwise disjointness of the balls; measurability of the cylinders and
`lintegral_iUnion` then collapse the sum of cylinder integrals into the integral
over their union, which lies in `V`.  No measurability hypothesis on `g` is
needed: set integrals of `ℝ≥0∞`-valued functions behave well with respect to
unions of pairwise disjoint measurable sets regardless.

Both the current manuscript and this theorem state the first inequality
non-strictly.  This includes the empty index family, for which both sides
are zero, and is the form used by the covering estimate.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- `eq:sum-radii` in `paper/ckn.tex`: for a countable family of
pairwise disjoint parabolic balls `𝔅_{r_j}(z_j)` contained in `V`, each with a
defect `(ε / 2) * r_j < ∫_{Cyl_{r_j}(z_j)} g`, the radii satisfy

`∑_j r_j ≤ (2 / ε) * ∑_j ∫_{Cyl_{r_j}(z_j)} g`

and the accumulated cylinder mass is controlled by the mass of `V`:

`(2 / ε) * ∑_j ∫_{Cyl_{r_j}(z_j)} g ≤ (2 / ε) * ∫_V g`.

The non-strict inequality includes the empty index family and agrees with
the current manuscript. -/
theorem sum_radii_le_of_disjoint_defect_balls {g : ParabolicPoint → ℝ≥0∞}
    {V : Set ParabolicPoint} {ε : ℝ≥0} (hε : 0 < ε) {T : Type*} [Countable T]
    {z : T → ParabolicPoint}
    {r : T → ℝ} (hr : ∀ j, 0 < r j) (hV : ∀ j, Metric.ball (z j) (r j) ⊆ V)
    (hdisj : Pairwise (Function.onFun Disjoint fun j => Metric.ball (z j) (r j)))
    (hdefect : ∀ j, (ε : ℝ≥0∞) / 2 * ENNReal.ofReal (r j) <
      ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y) :
    (∑' j, ENNReal.ofReal (r j)) ≤
        2 / (ε : ℝ≥0∞) * ∑' j, ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y ∧
      2 / (ε : ℝ≥0∞) * (∑' j, ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y) ≤
        2 / (ε : ℝ≥0∞) * ∫⁻ y in V, g y := by
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
  have hεtop : (ε : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  -- Step 1: each defect inequality is inverted into a bound on the radius.
  have hstep : ∀ j, ENNReal.ofReal (r j) ≤
      2 / (ε : ℝ≥0∞) *
        ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y := by
    intro j
    have h2 : (ε : ℝ≥0∞) * ENNReal.ofReal (r j) <
        2 * ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y := by
      have h := ENNReal.mul_lt_mul_right (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
        (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num) (hdefect j)
      rwa [← mul_assoc,
        ENNReal.mul_div_cancel (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
          (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num)] at h
    have h3 : ENNReal.ofReal (r j) * (ε : ℝ≥0∞) ≤
        2 * ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y :=
      le_of_lt (by simpa [mul_comm] using h2)
    calc ENNReal.ofReal (r j)
        ≤ (2 * ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y) /
            (ε : ℝ≥0∞) :=
          (ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl hεtop)).2 h3
      _ = 2 / (ε : ℝ≥0∞) *
            ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y :=
          ENNReal.mul_div_right_comm
  -- Step 2: sum the radius bounds and pull out the constant.
  have h1 : (∑' j, ENNReal.ofReal (r j)) ≤
      2 / (ε : ℝ≥0∞) *
        ∑' j, ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y :=
    calc (∑' j, ENNReal.ofReal (r j))
        ≤ ∑' j, 2 / (ε : ℝ≥0∞) *
            ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y :=
          ENNReal.tsum_le_tsum hstep
      _ = 2 / (ε : ℝ≥0∞) *
            ∑' j, ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y :=
          ENNReal.tsum_mul_left
  -- Step 3: the cylinders are pairwise disjoint and measurable, so their
  -- integrals sum to the integral of their union, which lies in `V`.
  have hcyl : (∑' j, ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y) ≤
      ∫⁻ y in V, g y := by
    have hsub : ∀ j, parabolicCylinder (z j).1 (z j).2 (r j) ⊆ Metric.ball (z j) (r j) :=
      fun j => parabolicCylinder_subset_metricBall_same_center (hr j)
    have hdisjQ : Pairwise
        (Function.onFun Disjoint fun j => parabolicCylinder (z j).1 (z j).2 (r j)) :=
      fun i j hij => Set.disjoint_of_subset (hsub i) (hsub j) (hdisj hij)
    calc (∑' j, ∫⁻ y in parabolicCylinder (z j).1 (z j).2 (r j), g y)
        = ∫⁻ y in ⋃ j, parabolicCylinder (z j).1 (z j).2 (r j), g y :=
          (lintegral_iUnion (fun j => measurableSet_parabolicCylinder _ _ _) hdisjQ g).symm
      _ ≤ ∫⁻ y in V, g y :=
          lintegral_mono_set (Set.iUnion_subset fun j => (hsub j).trans (hV j))
  exact ⟨h1, by gcongr⟩

end CKN
