-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.BallDisplays
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

/-!
# Measure-theoretic arithmetic for the slicewise origin-clause majorant

This file collects the small measure-theoretic and real-arithmetic facts used
to bound an explicit slicewise majorant for the fixed selected pressure
gradient, in the situation where that gradient is bounded in absolute value.

The four statements are independent of any particular field: the first bounds
the `L^{6/5}` seminorm of an almost-everywhere bounded function on a slice by
the slice volume raised to the exponent `5/6` times the bound; the second and
third bound a parabolic space-time window and a spatial cell by their literal
volumes; the fourth records that for a radius in `(0, 1]` the real power
`r ↦ r ^ θ` is antitone, so the exponent `5` is the smallest power available
once the exponent is known to be at most `5`.
-/

/-- **Slice majorant.** An almost-everywhere bound `|g| ≤ β` on a slice `E`
controls the `L^{6/5}` seminorm of `g` on that slice by the slice volume raised
to the exponent `5/6` times `β`. This is the arithmetic behind the explicit
slicewise majorant for the pressure gradient. -/
theorem originClauseSliceMajorant_le {E : Set Vec3} {g : Vec3 → ℝ} {β : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict E))
    (hbd : ∀ᵐ y ∂(volume.restrict E), |g y| ≤ β) :
    eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict E)
      ≤ volume E ^ (5 / 6 : ℝ) * ENNReal.ofReal β := by
  have hle := eLpNorm_le_of_ae_bound (μ := volume.restrict E)
    (p := ENNReal.ofReal (6 / 5 : ℝ)) (C := β) hg
    (hbd.mono fun y hy => by simpa [Real.norm_eq_abs] using hy)
  have hp : (ENNReal.ofReal (6 / 5 : ℝ)).toReal⁻¹ = (5 / 6 : ℝ) := by
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5)]
    norm_num
  rw [Measure.restrict_apply_univ, hp] at hle
  exact hle

/-- **Window volume.** The one-dimensional window `(t - r², t]` cut down to the
origin window `(-R₁², 0]` has volume at most `r²`, the length of the full
window. -/
theorem originClauseWindowVolume_le (R₁ t r : ℝ) :
    volume (Set.Ioc (t - r ^ 2) t ∩ Set.Ioc (-(R₁ ^ 2)) 0) ≤ ENNReal.ofReal (r ^ 2) := by
  calc volume (Set.Ioc (t - r ^ 2) t ∩ Set.Ioc (-(R₁ ^ 2)) 0)
      ≤ volume (Set.Ioc (t - r ^ 2) t) := measure_mono Set.inter_subset_left
    _ = ENNReal.ofReal (t - (t - r ^ 2)) := Real.volume_Ioc
    _ = ENNReal.ofReal (r ^ 2) := by rw [show t - (t - r ^ 2) = r ^ 2 by ring]

/-- **Cell volume.** The intersection of a spatial ball of radius `r` with the
origin ball of radius `R₁` has volume at most the volume `(4π/3) r³` of the
former. -/
theorem originClauseCellVolume_le (x : Vec3) (R₁ r : ℝ) :
    volume (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)
      ≤ ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  calc volume (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)
      ≤ volume (vec3Ball x r) := measure_mono Set.inter_subset_left
    _ = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) :=
        volume_vec3Ball_eq x r

/-- **Radius arithmetic.** For a radius `r` with `0 < r ≤ 1` and an exponent
`θ ≤ 5`, the power `r ^ 5` is at most `r ^ θ`: on the unit interval the map
`θ ↦ r ^ θ` is antitone. -/
theorem originClauseRadius_rpow_le {r θ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hθ : θ ≤ 5) :
    ENNReal.ofReal (r ^ (5 : ℝ)) ≤ ENNReal.ofReal (r ^ θ) := by
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hr hr1 hθ)

end CKN.Core.Step4
