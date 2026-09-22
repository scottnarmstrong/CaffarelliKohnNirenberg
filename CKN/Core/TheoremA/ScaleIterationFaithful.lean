-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.TheoremA.StartLin34Unconditional
import CKN.Core.Step2.IterationAbsoluteConstant

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

private theorem thmA_quarter_subset_unit
    {z : ParabolicPoint}
    (hz : z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0) :
    parabolicCylinder z.1 z.2 (1 / 4) ⊆ parabolicCylinder 0 0 1 := by
  intro w hw
  rcases hz with ⟨hzx, hzt⟩
  rcases hw with ⟨hwx, hwt⟩
  refine ⟨?_, ?_⟩
  · change vec3EuclideanNorm (w.1 - 0) < 1
    rw [sub_zero]
    have htriangle : vec3EuclideanNorm w.1 ≤
        vec3EuclideanNorm (w.1 - z.1) + vec3EuclideanNorm z.1 := by
      simpa only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub, sub_add_cancel] using
        (norm_add_le (WithLp.toLp 2 (w.1 - z.1)) (WithLp.toLp 2 z.1))
    have hwx' : vec3EuclideanNorm (w.1 - z.1) < 1 / 4 := hwx
    have hzx' : vec3EuclideanNorm z.1 < 3 / 4 := by
      simpa only [mem_vec3Ball, sub_zero] using hzx
    linarith only [htriangle, hwx', hzx']
  · refine ⟨?_, hwt.2.trans hzt.2⟩
    have ht := hwt.1
    have hzlow := hzt.1
    norm_num at ht ⊢
    linarith only [ht, hzlow]

/-- The scale-iteration conclusion of Theorem A, with the iteration constant
chosen absolutely before the force exponent and the smallness threshold chosen
for each force exponent. -/
theorem thmA_uniform_morrey_decay :
    ∃ C₂₇ : ℝ, 0 < C₂₇ ∧
      ∀ q : ℝ, 5 / 2 < q →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ {Ω : Set Vec3} {I : Set ℝ}
            {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
            {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
            IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
            closure (parabolicCylinder (0 : Vec3) (0 : ℝ) 1) ⊆
              spaceTimeSet Ω I →
            (∫⁻ w in parabolicCylinder (0 : Vec3) (0 : ℝ) 1,
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
                ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
                ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε₀ →
            ∀ z ∈ parabolicCylinder (0 : Vec3) (0 : ℝ) (3 / 4),
              ∀ r : ℝ, 0 < r → r ≤ iterationKappa C₂₇ / 4 →
                max (max (alpha u z r) (beta u Du z r))
                    (delta p z r ^ (2 : ℕ)) ≤
                  (iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) *
                    iterationEta C₂₇ *
                    (iterationKappa C₂₇ / 4) ^ (-iterationEpsilon)) *
                      r ^ iterationEpsilon := by
  obtain ⟨C₂₇, hC₂₇, hiterQ⟩ := iteration_of_sws_absolute
  refine ⟨C₂₇, hC₂₇, ?_⟩
  intro q hq
  obtain ⟨C₂₈, hC₂₈, hiter⟩ := hiterQ q
  obtain ⟨ε₀, hε₀, hstart⟩ :=
    thmA_start_unconditional q C₂₇ C₂₈ hq hC₂₇ hC₂₈
  refine ⟨ε₀, hε₀, ?_⟩
  intro Ω I u Du p f hsol hQ₁ hsmall z hz r hr hρ
  have hz' : z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0 := by
    norm_num [parabolicCylinder] at hz ⊢
    exact hz
  have hstartZ := hstart hsol hQ₁ hsmall z hz'
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hκhalf : iterationKappa C₂₇ ≤ 1 / 2 := iterationKappa_le_half C₂₇
  have hr₅ : 0 < iterationKappa C₂₇ / 4 := div_pos hκ (by norm_num)
  have hquarter :
      closure (parabolicCylinder z.1 z.2 (1 / 4)) ⊆ spaceTimeSet Ω I :=
    (closure_mono (thmA_quarter_subset_unit hz')).trans hQ₁
  have hκleone : iterationKappa C₂₇ ≤ 1 := by
    linarith only [hκhalf]
  have hscale : iterationKappa C₂₇ / 4 ≤ (1 / 4 : ℝ) :=
    div_le_div_of_nonneg_right hκleone (by norm_num)
  have hclosure :
      closure (parabolicCylinder z.1 z.2 (iterationKappa C₂₇ / 4)) ⊆
        spaceTimeSet Ω I :=
    (closure_parabolicCylinder_mono hr₅.le hscale).trans hquarter
  have hdecay :=
    (hiter hsol hr₅ hclosure hstartZ.1 hstartZ.2).2 r hr hρ
  exact hdecay.1.trans hdecay.2

end CKN
