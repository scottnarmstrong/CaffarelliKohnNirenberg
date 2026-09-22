-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Covering

/-!
# Local form of the parabolic covering estimate

The covering estimate of `CKN.Foundation.Parabolic.Covering` is combined here
with the dimension comparison `parabolicHausdorffMeasure_one_lt_top_imp_volume_zero`
so that the conclusion `volume S = 0` is reached from the finiteness of the
Dirichlet integral **on the open set `U` alone**, rather than from finiteness of
the integral over all of space.  This is the form in which the final measure
step of the theory uses the covering estimate.
-/

open scoped ENNReal NNReal

open MeasureTheory Set

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- From the small-cylinder energy lower bound on `S` and finiteness of the
Dirichlet integral over the ambient open set `U`, the parabolic Hausdorff
measure of dimension one of `S` is bounded by `(10/ε)·∫_U g`, is finite, and
`S` is Lebesgue null. -/
theorem parabolicHausdorffMeasure_one_lt_top_and_volume_zero_of_small_cylinders
    {g : ParabolicPoint → ℝ≥0∞} {U S : Set ParabolicPoint}
    (hg : Measurable g) (hU : IsOpen U) (hSU : S ⊆ U)
    {ε : ℝ≥0} (hε : 0 < ε)
    (hsmall : ∀ z ∈ S, ∀ n : ℕ, ∃ r : ℝ,
      0 < r ∧ r < 1 / ((n + 1 : ℕ) : ℝ) ∧
        parabolicCylinder z.1 z.2 r ⊆ U ∧
        (ε : ℝ≥0∞) * ENNReal.ofReal r <
          ∫⁻ y in parabolicCylinder z.1 z.2 r, g y)
    (hfin : (∫⁻ y in U, g y) < ∞) :
    parabolicHausdorffMeasure 1 S ≤
        ((10 : ℝ≥0∞) / (ε : ℝ≥0∞)) * (∫⁻ y in U, g y) ∧
      parabolicHausdorffMeasure 1 S < ∞ ∧ volume S = 0 := by
  have hbound :=
    parabolicHausdorffMeasure_one_le_integral_of_small_cylinders
      hg hU hSU hε hsmall hfin
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
  have hKtop : ((10 : ℝ≥0∞) / (ε : ℝ≥0∞)) < ∞ :=
    ENNReal.div_lt_top (by norm_num) hε0
  have hfiniteH : parabolicHausdorffMeasure 1 S < ∞ :=
    hbound.trans_lt (ENNReal.mul_lt_top hKtop hfin)
  exact ⟨hbound, hfiniteH,
    parabolicHausdorffMeasure_one_lt_top_imp_volume_zero hfiniteH⟩

end CKN.Foundation.Parabolic
