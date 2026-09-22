-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.SliceSelectedGradientSymmetricGeometry
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Time integration of the slicewise bound of display (3.5)

Display (3.5) of `paper/ckn.tex` bounds the selected pressure gradient one time
slice at a time: for almost every `t` the spatial slice lies in `L^{6/5}` of
the spatial half ball.  This file raises that slicewise information to an
estimate on the whole space-time box.

Hölder's inequality on a ball `B` of finite volume compares the `L^1` norm of a
slice with its `L^{6/5}` norm and contributes the factor `|B|^{1/6}`, the gap
between reciprocal exponents.  Tonelli's theorem then integrates these slicewise
`L^1` bounds over the symmetric time window `(t₀ - R², t₀ + R²)` of display
`eq:parabolic-ball`.  When the resulting one-dimensional integral of the
time-dependent bound is finite, the field is integrable on the product box
`B_{R/2}(x₀) × (t₀ - R², t₀ + R²)`. -/

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-- If a real-valued field has, on almost every time slice `t` of the time set
`J`, an `L^{6/5}` bound on the spatial set `B` by the value `K t`, and if the
time-dependent bound `K` is integrable over `J`, then the field is integrable
on the product `B ×ˢ J` for Lebesgue measure.  Hölder on `B` converts each
slice bound into an `L^1` bound with the factor `|B|^{1/6}`, and Tonelli
integrates the result in time. -/
theorem integrableOn_prod_of_slice_eLpNorm_bounds
    {B : Set Vec3} {J : Set ℝ} {D : ParabolicPoint → ℝ} {K : ℝ → ℝ≥0∞}
    (hBfin : volume B < ∞)
    (hD : AEStronglyMeasurable D (volume.restrict (B ×ˢ J)))
    (hslice : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x => D (x, t)) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B) ≤ K t)
    (hK : (∫⁻ t in J, K t) < ∞) :
    IntegrableOn D (B ×ˢ J) volume := by
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J)
      = (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod Vec3 ℝ, Measure.prod_restrict]
  have hDmeas : AEStronglyMeasurable D ((volume.restrict B).prod (volume.restrict J)) := by
    rw [← hprod]
    exact hD
  refine ⟨hD, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  change ∫⁻ z : Vec3 × ℝ, ‖D z‖ₑ ∂((volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J)) < ∞
  rw [hprod]
  rw [lintegral_prod_symm (fun z => ‖D z‖ₑ) hDmeas.aemeasurable.enorm]
  have hsections := hDmeas.prodMk_right
  have hle : (∫⁻ t, ∫⁻ x, ‖D (x, t)‖ₑ ∂(volume.restrict B) ∂(volume.restrict J))
      ≤ ∫⁻ t, K t * volume B ^ ((1 : ℝ) / 6) ∂(volume.restrict J) := by
    apply lintegral_mono_ae
    filter_upwards [hslice, hsections] with t ht hmt
    rw [← eLpNorm_one_eq_lintegral_enorm hmt]
    have hpq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6 / 5 : ℝ) :=
      ENNReal.one_le_ofReal.2 (by norm_num)
    have hexp : (1 : ℝ) / (1 : ℝ≥0∞).toReal
        - 1 / (ENNReal.ofReal (6 / 5 : ℝ)).toReal = 1 / 6 := by
      rw [ENNReal.toReal_one, ENNReal.toReal_ofReal (by norm_num)]
      norm_num
    calc eLpNorm (fun x => D (x, t)) 1 (volume.restrict B)
        ≤ eLpNorm (fun x => D (x, t)) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B)
            * (volume.restrict B) Set.univ ^ ((1 : ℝ) / (1 : ℝ≥0∞).toReal
              - 1 / (ENNReal.ofReal (6 / 5 : ℝ)).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hmt
      _ = eLpNorm (fun x => D (x, t)) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B)
            * volume B ^ ((1 : ℝ) / 6) := by
          rw [hexp, Measure.restrict_apply_univ]
      _ ≤ K t * volume B ^ ((1 : ℝ) / 6) := mul_le_mul_left ht _
  have hfin : (∫⁻ t, K t * volume B ^ ((1 : ℝ) / 6) ∂(volume.restrict J)) < ∞ := by
    rw [lintegral_mul_const' (volume B ^ ((1 : ℝ) / 6)) K
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBfin.ne).ne]
    exact ENNReal.mul_lt_top hK (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBfin.ne)
  exact lt_of_le_of_lt hle hfin

end CKN.Core.Step4
