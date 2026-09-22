-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.AdamsEndpoints
import CKN.Foundation.Parabolic.Morrey.AdamsConstantFinite
import CKN.Foundation.Parabolic.Morrey.Cylinders
import CKN.Foundation.Parabolic.Morrey.Minkowski
import CKN.Foundation.Parabolic.BallDisplays

/-!
# Hedberg's inequality with a sum-gauge potential

Paper label `lem:hedberg` (display `eq:hedberg`): for `1 ≤ P ≤ τ < ∞` and
`0 < a < 5/τ`, with `ϰ = aτ/5 ∈ (0,1)`, there is a finite constant
`C₂₀ = C₂₀(a, τ)`, **independent of `P`**, such that

`I_a g(z) ≤ C₂₀ (𝓜g(z))^{1-ϰ} ‖g‖_{𝓜^{P,τ}}^{ϰ}`

for every `g ∈ 𝓜^{P,τ}` and every `z`, where `𝓜` is the **centred** maximal
function over the parabolic balls `𝔅_r(z)` of `ext:maximal` and the Morrey
norm is the ball norm of `def:parabolic-morrey`.  Here `I_a` denotes
`parabolicRieszPotential`, whose kernel uses
`√|t-s| + |x-y|₂`; the paper uses the maximum of these two terms.
The gauges satisfy `d_par ≤ parabolicRho₂ ≤ 2 * d_par`, so their
order-`a` kernels are comparable with factor `2^(5-a)` away from the diagonal.
The displayed Lean theorem is stated for the sum-gauge potential.

The established `parabolicRieszPotential_hedberg'` is stated for an arbitrary
maximal majorant and for the Morrey exponent `1`.  Two steps bring it to the
display above: the centred maximal function is a majorant in that sense
(`centredParabolicMaximal_isMajorant` below), and the passage from
`morreyNorm 1 τ` to the ball norm `morreyBallNorm P τ` costs the volume factor
`volume (parabolicCylinder 0 0 1)^{1 - 1/P} ≤ max 1 (volume (parabolicCylinder
0 0 1))`, which is bounded uniformly in `P` and therefore absorbed into a
single `C₂₀(a, τ)`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The centred parabolic maximal function of `ext:maximal`, written inline as
`𝓜g(z) = sup_{r > 0} ⨍_{𝔅_r(z)} |g|`, is a maximal majorant of `g` in the sense
of `IsParabolicMaximalMajorant`. -/
theorem centredParabolicMaximal_isMajorant (g : ParabolicPoint → ℝ) :
    IsParabolicMaximalMajorant g (fun z =>
      ⨆ r : {r : ℝ // 0 < r}, ⨍⁻ w in Metric.ball z r.1, ENNReal.ofReal |g w| ∂volume) := by
  intro z R hR
  have hvol := volume_metricBall z hR.le
  have hne0 : volume (Metric.ball z R) ≠ 0 := by
    rw [hvol]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hnetop : volume (Metric.ball z R) ≠ ∞ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have havg : (⨍⁻ w in Metric.ball z R, ENNReal.ofReal |g w| ∂volume) ≤
      ⨆ r : {r : ℝ // 0 < r}, ⨍⁻ w in Metric.ball z r.1, ENNReal.ofReal |g w| ∂volume :=
    le_iSup (fun r : {r : ℝ // 0 < r} =>
      ⨍⁻ w in Metric.ball z r.1, ENNReal.ofReal |g w| ∂volume) ⟨R, hR⟩
  calc (∫⁻ w in Metric.ball z R, ENNReal.ofReal |g w|)
      = (⨍⁻ w in Metric.ball z R, ENNReal.ofReal |g w| ∂volume) *
          volume (Metric.ball z R) := by
        rw [setLAverage_eq, ENNReal.div_mul_cancel hne0 hnetop]
    _ ≤ _ := by gcongr

/-- Sum-gauge counterpart of `lem:hedberg`, display `eq:hedberg`: one
finite `C₂₀(a, τ)` fixed before `P`, `g` and `z`, the centred maximal function
over parabolic balls, and the ball Morrey norm. -/
theorem parabolic_hedberg_display (a τ : ℝ) (ha : 0 < a) (hτ : 1 ≤ τ)
    (haτ : a * τ < 5) :
    ∃ C₂₀ : ℝ, 0 ≤ C₂₀ ∧ ∀ P : ℝ, 1 ≤ P → P ≤ τ →
      ∀ g : ParabolicPoint → ℝ, AEMeasurable g volume → ∀ z : ParabolicPoint,
        parabolicRieszPotential a g z ≤
          ENNReal.ofReal C₂₀ *
            (⨆ r : {r : ℝ // 0 < r}, ⨍⁻ w in Metric.ball z r.1, ENNReal.ofReal |g w| ∂volume) ^
              (1 - a * τ / 5) *
            morreyBallNorm P τ g ^ (a * τ / 5) := by
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos hτ
  have ha5 : a < 5 := by
    have : a ≤ a * τ := by nlinarith only [ha, hτ]
    exact lt_of_le_of_lt this haτ
  have hκ : 0 ≤ a * τ / 5 := by positivity
  set K : ℝ≥0∞ := parabolicHedbergNearConstant a + parabolicTailKernelConstant a τ with hK
  have hKtop : K ≠ ∞ := parabolicHedbergNear_add_tail_ne_top ha hτ0 haτ
  set V : ℝ≥0∞ := volume (parabolicCylinder 0 0 1) with hV
  have hVtop : V ≠ ∞ := Integration.volume_parabolicCylinder_lt_top.ne
  set W : ℝ≥0∞ := max 1 V with hW
  have hWtop : W ≠ ∞ := max_ne_top ENNReal.one_ne_top hVtop
  have hW1 : 1 ≤ W := le_max_left _ _
  have hCtop : K * W ^ (a * τ / 5) ≠ ∞ :=
    ENNReal.mul_ne_top hKtop (ENNReal.rpow_ne_top_of_nonneg hκ hWtop)
  refine ⟨(K * W ^ (a * τ / 5)).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P hP hPτ g hg z
  rw [ENNReal.ofReal_toReal hCtop]
  set Mc : ParabolicPoint → ℝ≥0∞ := fun z =>
    ⨆ r : {r : ℝ // 0 < r}, ⨍⁻ w in Metric.ball z r.1, ENNReal.ofReal |g w| ∂volume
  have hbase := parabolicRieszPotential_hedberg' ha ha5 hτ haτ hg
    (centredParabolicMaximal_isMajorant g) z
  have hlow := morreyNorm_lower_integrability (p' := (1 : ℝ)) (p := P) (q := τ)
    le_rfl hP hPτ hg
  have hball := morreyNorm_le_morreyBallNorm_of_range hP hPτ g
  have hexp : (1 / (1 : ℝ) - 1 / P) ≤ 1 := by
    have : 0 ≤ 1 / P := by positivity
    linarith only [this]
  have hexp0 : 0 ≤ 1 / (1 : ℝ) - 1 / P := by
    have : 1 / P ≤ 1 := (div_le_one (by linarith only [hP])).mpr hP
    linarith only [this]
  have hVW : V ^ (1 / (1 : ℝ) - 1 / P) ≤ W :=
    calc V ^ (1 / (1 : ℝ) - 1 / P) ≤ W ^ (1 / (1 : ℝ) - 1 / P) :=
          ENNReal.rpow_le_rpow (le_max_right _ _) hexp0
      _ ≤ W ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hW1 hexp
      _ = W := ENNReal.rpow_one W
  have hnorm : morreyNorm 1 τ g ≤ W * morreyBallNorm P τ g :=
    hlow.trans (mul_le_mul' hVW hball)
  calc parabolicRieszPotential a g z
      ≤ K * Mc z ^ (1 - a * τ / 5) * morreyNorm 1 τ g ^ (a * τ / 5) := hbase
    _ ≤ K * Mc z ^ (1 - a * τ / 5) * (W * morreyBallNorm P τ g) ^ (a * τ / 5) := by
        gcongr
    _ = K * W ^ (a * τ / 5) * Mc z ^ (1 - a * τ / 5) * morreyBallNorm P τ g ^ (a * τ / 5) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hκ]
        ring

end CKN.Foundation.Parabolic.Morrey
