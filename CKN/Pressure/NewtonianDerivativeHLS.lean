-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.NewtonianDerivativeAeIntegrable
import CKN.Foundation.Euclidean.PotentialLocalLpMeasure

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-! ## HLS bridge for the order-one Newtonian derivative potential

There exists a finite real constant `C ≥ 0` such that for every measurable
`g ∈ L^{5/2}(ℝ³)` and every `i`, the convolution with the `i`-th derivative of
the Newtonian kernel is absolutely convergent at almost every point, lies in
`L^{15}`, and has `L^{15}` norm at most `C ‖g‖_{5/2}`. -/

/-- A finite real constant `C ≥ 0` such that for every measurable `g ∈ L^{5/2}(ℝ³)`
and every `i`, the convolution with the `i`-th derivative of the Newtonian kernel
is absolutely convergent at almost every point, lies in `L^{15}`, and has `L^{15}`
norm at most `C ‖g‖_{5/2}`. -/
theorem newtonianDerivativePotential_hls_display :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Vec3 → ℝ), Measurable g →
      (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) < ∞ → ∀ i : Fin 3,
        (∀ᵐ x ∂volume, Integrable
          (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y) * g y) volume) ∧
        MemLp (pressureNewtonianDerivativePotential i g) (ENNReal.ofReal 15) volume ∧
        eLpNorm' (fun x => pressureNewtonianDerivativePotential i g x) (15 : ℝ) volume ≤
          ENNReal.ofReal C * (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  refine ⟨(4 * Real.pi)⁻¹ * hlsRieszConstant.toReal, by positivity, fun g hg hfin i => ⟨?_, ?_, ?_⟩⟩
  · -- (a) absolute convergence a.e.
    exact ae_integrable_spatialDeriv_newtonianKernel_mul hg hfin i
  · -- (b) MemLp: eLpNorm < ∞
    have h_ae_strongly : AEStronglyMeasurable (pressureNewtonianDerivativePotential i g) volume :=
      aestronglyMeasurable_pressureNewtonianDerivativePotential i hg
    have hright_lt_top : ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant *
        (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) < ∞ := by
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ hlsRieszConstant_lt_top) ?_
      · exact ENNReal.ofReal_lt_top
      · refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
    have hleft_lt_top : eLpNorm' (fun x => pressureNewtonianDerivativePotential i g x)
        (15 : ℝ) volume < ∞ :=
      lt_of_le_of_lt
        (pressureNewtonianDerivativePotential_eLpNorm15_le_hls_of_zero_or_good i hg hfin)
        hright_lt_top
    have hmem' : eLpNorm (pressureNewtonianDerivativePotential i g)
        (ENNReal.ofReal 15) volume < ∞ := by
      rw [eLpNorm_eq_eLpNorm' (by
        exact ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 15) |>.ne.symm)
        (by exact ENNReal.ofReal_ne_top) h_ae_strongly]
      simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 15)] using hleft_lt_top
    exact hmem'
  · -- (c) eLpNorm' bound
    have hbound := pressureNewtonianDerivativePotential_eLpNorm15_le_hls_of_zero_or_good
      i hg hfin
    -- Key rewrite: replace the constant
    have hC : ENNReal.ofReal ((4 * Real.pi)⁻¹ * hlsRieszConstant.toReal) =
        ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant := by
      calc
        ENNReal.ofReal ((4 * Real.pi)⁻¹ * hlsRieszConstant.toReal) =
            ENNReal.ofReal ((4 * Real.pi)⁻¹) * ENNReal.ofReal (hlsRieszConstant.toReal) :=
          ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * Real.pi)⁻¹)
        _ = ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant := by
          rw [ENNReal.ofReal_toReal hlsRieszConstant_lt_top.ne]
    -- The bound we need to show:
    -- eLpNorm' ... ≤ ENNReal.ofReal C * (∫⁻ ...) ^ (2/5)
    -- where C = (4*π)⁻¹ * hlsRieszConstant.toReal
    calc
      eLpNorm' (fun x => pressureNewtonianDerivativePotential i g x) (15 : ℝ) volume ≤
          ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant *
            (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := hbound
      _ = ENNReal.ofReal ((4 * Real.pi)⁻¹ * hlsRieszConstant.toReal) *
          (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
        rw [hC, mul_assoc]

end CKN
