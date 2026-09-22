-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Integration.Average

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Integration

/-- A single parabolic point has zero Lebesgue volume. -/
theorem volume_singleton_parabolicPoint (z : ParabolicPoint) :
    volume ({z} : Set ParabolicPoint) = 0 := by
  rcases z with ⟨x, t⟩
  rw [volume_parabolicPoint_eq_prod]
  change (volume.prod volume) ({(x, t)} : Set (Vec3 × ℝ)) = 0
  rw [show ({(x, t)} : Set (Vec3 × ℝ)) = {x} ×ˢ {t} by simp]
  rw [Measure.prod_prod]
  simp


end CKN.Foundation.Parabolic.Integration
