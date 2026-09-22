-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.GaussianDisplay

open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN.Foundation.Heat

/-- The absolute constant used in the Gaussian test-function displays. -/
def gaussianC₂₄ : ℝ := 8000000

/-- The backward heat test function is positive, solves the backward heat
equation, and satisfies the lower, upper, and far-field displays with the
single absolute constant `gaussianC₂₄`. -/
theorem centeredBackwardHeatTest_gaussian_display
    {x₀ : Vec3} {t₀ r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hhalf : r ≤ ρ / 2) :
    (∀ z : ParabolicPoint, z.2 - t₀ < r ^ 2 →
        0 < centeredBackwardHeatTest x₀ t₀ r z) ∧
      (∀ z : ParabolicPoint, z.2 - t₀ < r ^ 2 →
        timePartial (centeredBackwardHeatTest x₀ t₀ r) z
          + ∑ i, spatialSecondPartial (centeredBackwardHeatTest x₀ t₀ r) i i z
            = 0) ∧
      (∀ z ∈ parabolicCylinder x₀ t₀ r,
        gaussianC₂₄⁻¹ * r⁻¹ ≤ centeredBackwardHeatTest x₀ t₀ r z) ∧
      (∀ z : ParabolicPoint, z.2 ≤ t₀ →
        centeredBackwardHeatTest x₀ t₀ r z ≤ gaussianC₂₄ * r⁻¹ ∧
        centeredBackwardHeatTestGradientNorm x₀ t₀ r z ≤
          gaussianC₂₄ * r⁻¹ ^ 2) ∧
      (∀ z ∈ parabolicCylinder x₀ t₀ ρ \ parabolicCylinder x₀ t₀ (ρ / 2),
        centeredBackwardHeatTest x₀ t₀ r z ≤ gaussianC₂₄ * r ^ 2 / ρ ^ 3 ∧
        centeredBackwardHeatTestGradientNorm x₀ t₀ r z ≤
          gaussianC₂₄ * r ^ 2 / ρ ^ 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z ht
    exact centeredBackwardHeatTest_pos hr (by linarith only [ht])
  · intro z ht
    exact centeredBackwardHeatTest_heat_equation (r := r) (by linarith only [ht])
  · intro z hz
    have hlower := centeredBackwardHeatTest_lower_on_cylinder hr hz
    have hconstant : gaussianC₂₄⁻¹ * r⁻¹ ≤ 1 / (2000 * r) := by
      have hC : gaussianC₂₄⁻¹ ≤ (2000 : ℝ)⁻¹ := by
        norm_num [gaussianC₂₄]
      have hmul := mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hr.le)
      have hrewrite : (2000 : ℝ)⁻¹ * r⁻¹ = 1 / (2000 * r) := by
        field_simp [hr.ne']
      simpa [gaussianC₂₄] using hmul.trans_eq hrewrite
    exact hconstant.trans hlower
  · intro z ht
    have hvalue := centeredBackwardHeatTest_le_of_le
      (x₀ := x₀) (t₀ := t₀) hr ht
    have hgrad := centeredBackwardHeatTestGradientNorm_le_of_le
      (x₀ := x₀) (t₀ := t₀) hr ht
    have hvalue' : 1000 / r ≤ gaussianC₂₄ * r⁻¹ := by
      calc
        1000 / r = 1000 * r⁻¹ := by ring
        _ ≤ gaussianC₂₄ * r⁻¹ := by
          gcongr
          norm_num [gaussianC₂₄]
    have hgrad' : 300000 / r ^ 2 ≤ gaussianC₂₄ * r⁻¹ ^ 2 := by
      calc
        300000 / r ^ 2 = 300000 * r⁻¹ ^ 2 := by
          field_simp [hr.ne']
        _ ≤ gaussianC₂₄ * r⁻¹ ^ 2 := by
          gcongr
          norm_num [gaussianC₂₄]
    exact ⟨hvalue.trans hvalue', hgrad.trans hgrad'⟩
  · intro z hz
    have hvalue := centeredBackwardHeatTest_upper_on_annulus hr hρ hhalf hz
    have hgrad := centeredBackwardHeatTestGradient_upper_on_annulus hr hρ hhalf hz
    have hgrad' : 5000000 * r ^ 2 / ρ ^ 4 ≤
        gaussianC₂₄ * r ^ 2 / ρ ^ 4 := by
      have hfactor : (5000000 : ℝ) ≤ gaussianC₂₄ := by
        norm_num [gaussianC₂₄]
      have hnonneg : 0 ≤ r ^ 2 / ρ ^ 4 := by positivity
      calc
        5000000 * r ^ 2 / ρ ^ 4 = 5000000 * (r ^ 2 / ρ ^ 4) := by ring
        _ ≤ gaussianC₂₄ * (r ^ 2 / ρ ^ 4) :=
          mul_le_mul_of_nonneg_right hfactor hnonneg
        _ = gaussianC₂₄ * r ^ 2 / ρ ^ 4 := by ring
    exact ⟨by simpa [gaussianC₂₄] using hvalue, hgrad.trans hgrad'⟩

end CKN.Foundation.Heat
