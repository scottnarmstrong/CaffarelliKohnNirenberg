-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.QuantitativeHolderScalar
import CKN.Core.Step4.SourceMorreyGradient
import CKN.Foundation.Parabolic.Morrey.Minkowski

/-!
# The numerical derivative-slot source bound of `thm:endgame`

In the proof of `thm:endgame` the derivative slot of the localized equation
is `h_i = -2 (∂_i φ) u`, where `φ` is the localization cutoff of
`lem:local-equation`. Its Morrey norm at the exponent pair `(6/5, τ₂)` used
there is therefore controlled by two numbers only: a bound for the first
spatial derivatives of the cutoff, and the Step 2 velocity Morrey bound on
the cutoff carrier.

Both numbers precede the solution: the cutoff bound depends on the radii
alone and the Step 2 bound on `M` and `r₂` alone. The exponent `6/5` is
reached from the velocity exponent `3` by lowering integrability on the unit
cylinder, which contributes the explicit volume factor below and nothing
else.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The numerical derivative-slot source constant of `thm:endgame`: twice the
cutoff derivative bound, times the integrability-lowering volume factor,
times the Step 2 velocity Morrey bound. -/
def endgameDerivativeSourceConstant (C : ℝ) (Kᵤ : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * C) *
    (volume (parabolicCylinder 0 0 1) ^ (1 / (6 / 5 : ℝ) - 1 / (3 : ℝ)) * Kᵤ)

/-- The derivative-slot constant is finite whenever the Step 2 velocity
bound is. -/
theorem endgameDerivativeSourceConstant_lt_top {C : ℝ} {Kᵤ : ℝ≥0∞}
    (hKᵤ : Kᵤ < ∞) : endgameDerivativeSourceConstant C Kᵤ < ∞ := by
  have hvol : volume (parabolicCylinder 0 0 1) ^ (1 / (6 / 5 : ℝ) - 1 / (3 : ℝ))
      < ∞ := by
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    exact Integration.volume_parabolicCylinder_lt_top.ne
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hvol hKᵤ)

/-- Pointwise domination of the derivative slot by the cutoff derivative
bound times the velocity on the cutoff carrier. -/
theorem abs_localizedGradientSourceH_le
    {φ : Vec3 × ℝ → ℝ} {u : ParabolicPoint → Vec3}
    {S : Set ParabolicPoint} {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ j w, |spatialPartial φ j w| ≤ C)
    (hsupp : ∀ j, ∀ w ∉ S, spatialPartial φ j w = 0)
    (j i : Fin 3) (w : ParabolicPoint) :
    |localizedGradientSourceH φ u j w i| ≤
      |2 * C * S.indicator (fun x => u x i) w| := by
  have hval : localizedGradientSourceH φ u j w i =
      (-2 * spatialPartial φ j w) * u w i := rfl
  by_cases hw : w ∈ S
  · have habs : |(-2 * spatialPartial φ j w) * u w i| =
        2 * |spatialPartial φ j w| * |u w i| := by
      rw [abs_mul, abs_mul]
      norm_num
    have hle : 2 * |spatialPartial φ j w| * |u w i| ≤ 2 * C * |u w i| := by
      have h := hderiv j w
      have habs' : (0 : ℝ) ≤ |u w i| := abs_nonneg _
      nlinarith only [h, habs', abs_nonneg (spatialPartial φ j w)]
    rw [hval, habs, indicator_of_mem hw, abs_mul, abs_of_nonneg
      (by linarith only [hC] : (0 : ℝ) ≤ 2 * C)]
    exact hle
  · rw [hval, hsupp j w hw]
    simp only [mul_zero, zero_mul, abs_zero]
    exact abs_nonneg _

/-- The numerical derivative-slot source bound of `thm:endgame`: with a
cutoff derivative bound `C` and the Step 2 velocity Morrey bound `Kᵤ` on the
cutoff carrier, the Morrey norm of the derivative slot at the exponent pair
`(6/5, τ₂)` of the proof is at most `endgameDerivativeSourceConstant C Kᵤ`.
Both numbers are fixed before the solution. -/
theorem morreyNorm_localizedGradientSourceH_le
    {φ : Vec3 × ℝ → ℝ} {u : ParabolicPoint → Vec3}
    {S : Set ParabolicPoint} {C : ℝ} {Kᵤ : ℝ≥0∞}
    (hC : 0 ≤ C) (hS : MeasurableSet S)
    (hderiv : ∀ j w, |spatialPartial φ j w| ≤ C)
    (hsupp : ∀ j, ∀ w ∉ S, spatialPartial φ j w = 0)
    (hmeas : ∀ i, AEMeasurable (fun w => u w i) (volume.restrict S))
    (hvel : ∀ i, morreyBallNorm 3 (25 / 3 : ℝ)
      (S.indicator (fun w => u w i)) ≤ Kᵤ)
    (j i : Fin 3) :
    morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
        (fun w => localizedGradientSourceH φ u j w i) ≤
      endgameDerivativeSourceConstant C Kᵤ := by
  have hind : AEMeasurable (S.indicator (fun w => u w i)) volume :=
    (aemeasurable_indicator_iff hS).mpr (hmeas i)
  have hstep : morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
      (S.indicator (fun w => u w i)) ≤
      volume (parabolicCylinder 0 0 1) ^ (1 / (6 / 5 : ℝ) - 1 / (3 : ℝ)) * Kᵤ := by
    refine (morreyNorm_lower_integrability (p' := (6 / 5 : ℝ)) (p := (3 : ℝ))
      (q := (25 / 3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) hind).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans (hvel i)
  calc
    morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
        (fun w => localizedGradientSourceH φ u j w i) ≤
        morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
          (fun w => 2 * C * S.indicator (fun x => u x i) w) :=
      morreyNorm_mono (by norm_num)
        (abs_localizedGradientSourceH_le hC hderiv hsupp j i)
    _ ≤ ENNReal.ofReal (2 * C) *
        morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ) (S.indicator (fun x => u x i)) :=
      morreyNorm_const_mul_le_of_nonneg (by norm_num) (by linarith only [hC]) _
    _ ≤ endgameDerivativeSourceConstant C Kᵤ := by
      exact mul_le_mul_of_nonneg_left hstep (by positivity)

end CKN.Core.Endgame
