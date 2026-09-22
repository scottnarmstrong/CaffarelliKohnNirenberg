-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradient

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-- The same bridge with the scalar exponent written as an explicit real
number; this is convenient when the exponent is
`min ((1 / τ + 8 / 25)⁻¹) q`. -/
theorem pressure_gradient_morreyVecMem_of_cell_bounds_real
    {S : Set ParabolicPoint} {κ C : ℝ}
    {Dp : ParabolicPoint → Vec3}
    (hκ : 6 / 5 ≤ κ) (hC : ENNReal.ofReal C < ⊤)
    (hcell : ∀ i : Fin 3, ∀ z : ParabolicPoint,
      ∀ r : {r : ℝ // 0 < r},
      morreyCell (6 / 5 : ℝ) κ
        (S.indicator (fun w => Dp w i)) z r.1 ≤ ENNReal.ofReal C) :
    morreyVecMem (6 / 5 : ℝ) κ S Dp := by
  rw [morreyVecMem_iff_cylinder_lt_top (by norm_num) hκ]
  intro i
  exact (pressure_gradient_morrey_bound (fun z r => hcell i z r)).trans_lt hC

end CKN.Core.Step4
