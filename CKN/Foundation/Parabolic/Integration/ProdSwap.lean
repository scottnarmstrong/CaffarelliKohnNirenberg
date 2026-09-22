-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory MeasureTheory.Measure Set
open CKN.Foundation.Parabolic
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Integration

/-- Tonelli's theorem for set integrals on a product of a spatial set `S ⊆ Vec3`
and a time interval `T ⊆ ℝ`: the integral of a nonnegative measurable function over
the cylinder `S ×ˢ T` equals the iterated integral with the time variable outermost,
using the product Lebesgue measure on `Vec3 × ℝ`. -/
theorem prod_lintegral_swap_cyl {S : Set Vec3} {T : Set ℝ}
    {F : Vec3 × ℝ → ℝ≥0∞}
    (hF : AEMeasurable F ((volume.restrict S).prod (volume.restrict T))) :
    (∫⁻ z in S ×ˢ T, F z) = ∫⁻ s in T, ∫⁻ y in S, F (y, s) := by
  rw [show (volume : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) from
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict]
  calc
    _ = ∫⁻ y : Vec3, ∫⁻ s : ℝ, F (y, s)
        ∂(volume.restrict T) ∂(volume.restrict S) :=
      MeasureTheory.lintegral_prod F hF
    _ = _ := MeasureTheory.lintegral_lintegral_swap (by
      change AEMeasurable F ((volume.restrict S).prod (volume.restrict T))
      exact hF)

end CKN.Foundation.Parabolic.Integration
