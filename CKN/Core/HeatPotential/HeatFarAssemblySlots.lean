-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatFarAssemblyKernel
import CKN.Core.HeatPotential.MorreySources

/-!
# The two kernel slots of the far-shell oscillation

The general-symbol heat potential pairs a causal heat kernel with the scalar
source and a multiplier heat kernel with each vector source.  On a far shell
both pairings are estimated the same way: a uniform kernel size bound makes
the pairing integrable, a pointwise kernel oscillation bound multiplies the
Morrey mass of the source, and the part of the shell on which only the later
kernel is active is measured separately.

For the scalar slot the separate part is empty: the causal heat kernel is
compared across the interface directly.  For a multiplier slot it is the
moving time strip, and the established thin-strip estimate supplies its mass.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat

/-- Pairing a kernel with a restricted source is the same as restricting the
pairing. -/
theorem farShellAssembly_indicator_pairing {S : Set ParabolicPoint}
    (hS : MeasurableSet S) (K : ParabolicPoint → ℂ) (g : ParabolicPoint → ℝ) :
    (∫ v, K v * ((S.indicator g v : ℝ) : ℂ)) = ∫ v in S, K v * (g v : ℂ) := by
  rw [← integral_indicator hS]
  congr 1
  funext v
  by_cases hv : v ∈ S <;> simp [hv]

/-- **The slot estimate.**  Two bounded kernels paired with one integrable
source differ by the pointwise kernel oscillation times the source mass, plus
the mass carried by the exceptional set on which the first kernel vanishes. -/
private lemma farShellAssembly_pairing_diff_bound
    {S S₁ : Set ParabolicPoint} (hS : MeasurableSet S) (hS₁ : MeasurableSet S₁)
    (hsub : S₁ ⊆ S) {Kw Kw' : ParabolicPoint → ℂ} {g : ParabolicPoint → ℝ}
    {c₀ c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (hKwm : AEStronglyMeasurable Kw volume)
    (hKw'm : AEStronglyMeasurable Kw' volume)
    (hgm : AEMeasurable g volume) (hgint : IntegrableOn g S volume)
    (hKwb : ∀ v ∈ S, ‖Kw v‖ ≤ c₀) (hKw'b : ∀ v ∈ S, ‖Kw' v‖ ≤ c₀)
    (hptw : ∀ v ∈ S, v ∉ S₁ → ‖Kw v - Kw' v‖ ≤ c₁)
    (hzero : ∀ v ∈ S₁, Kw v = 0) :
    ‖(∫ v in S, Kw v * (g v : ℂ)) - ∫ v in S, Kw' v * (g v : ℂ)‖ ≤
      c₁ * (∫ v in S, |g v|) + ∫ v in S₁, ‖Kw' v * (g v : ℂ)‖ := by
  have hgabs : IntegrableOn (fun v => |g v|) S volume := hgint.abs
  have hgC : AEStronglyMeasurable (fun v => ((g v : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable hgm).aestronglyMeasurable
  have hmaj : ∀ (K : ParabolicPoint → ℂ), AEStronglyMeasurable K volume →
      (∀ v ∈ S, ‖K v‖ ≤ c₀) →
      IntegrableOn (fun v => K v * (g v : ℂ)) S volume := by
    intro K hKm hKb
    refine Integrable.mono' (hgabs.const_mul c₀)
      (hKm.restrict.mul hgC.restrict) ?_
    refine ae_restrict_of_forall_mem hS ?_
    intro v hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hKb v hv) (abs_nonneg _)
  have hfint := hmaj Kw hKwm hKwb
  have hf'int := hmaj Kw' hKw'm hKw'b
  rw [← integral_sub hfint hf'int]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hindint : IntegrableOn
      (S₁.indicator (fun v => ‖Kw' v * (g v : ℂ)‖)) S volume :=
    (hf'int.norm).indicator hS₁
  have hmajint : IntegrableOn
      (fun v => c₁ * |g v| + S₁.indicator (fun v => ‖Kw' v * (g v : ℂ)‖) v)
      S volume := (hgabs.const_mul c₁).add hindint
  have hstep : (∫ v in S, ‖Kw v * (g v : ℂ) - Kw' v * (g v : ℂ)‖) ≤
      ∫ v in S, (c₁ * |g v| +
        S₁.indicator (fun v => ‖Kw' v * (g v : ℂ)‖) v) := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun v => norm_nonneg _) hmajint ?_
    refine ae_restrict_of_forall_mem hS ?_
    intro v hv
    dsimp only
    by_cases hv₁ : v ∈ S₁
    · have hKz : Kw v = 0 := hzero v hv₁
      rw [hKz, zero_mul, zero_sub, norm_neg, Set.indicator_of_mem hv₁]
      have : (0 : ℝ) ≤ c₁ * |g v| := mul_nonneg hc₁ (abs_nonneg _)
      linarith only [this]
    · rw [Set.indicator_of_notMem hv₁, add_zero, ← sub_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hptw v hv hv₁) (abs_nonneg _)
  refine hstep.trans (le_of_eq ?_)
  rw [integral_add (hgabs.const_mul c₁) hindint, integral_const_mul,
    setIntegral_indicator hS₁, Set.inter_eq_self_of_subset_right hsub]

/-- Uniform size of the causal heat kernel on a far shell. -/
private lemma farShellAssembly_scalar_kernel_size {z v q : ParabolicPoint}
    {r : ℝ} {j : ℕ} (hr : 0 < r) (hj : 6 ≤ j)
    (hv : v ∈ multiplierHeatShellSet z r j)
    (hq : q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    |heatPotentialKernel q v| ≤ 1000 / ((2 : ℝ) ^ j * r / 2) ^ 3 := by
  by_cases ht : 0 < q.2 - v.2
  · refine heatPotentialKernel_abs_le (by positivity) ?_
    have hg := farShellAssembly_gauge_lower hr hj hv hq ht.le
    refine hg.trans ?_
    rw [rhoTwo]
    exact max_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg _))
  · have hz : heatPotentialKernel q v = 0 := by
      simp only [heatPotentialKernel, pointSub]
      exact heatKernelPlus_eq_zero_of_nonpos (le_of_not_gt ht)
    rw [hz, abs_zero]
    positivity

/-- **The scalar slot on a far shell.**  One constant, fixed before the
source and the shell data, bounds the oscillation of the causal heat
potential of a finite-Morrey source restricted to the shell of inner radius
`2 ^ j r`. -/
theorem farShellAssembly_exists_scalar_slot_bound {P θ : ℝ} (hP : 1 ≤ P)
    (hPθ : P ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : ParabolicPoint → ℝ}, AEMeasurable F volume → morreyNorm P θ F < ∞ →
        ∀ (z : ParabolicPoint) (r : ℝ) (j : ℕ), 0 < r → 6 ≤ j →
          ∀ w w' : ParabolicPoint, w ∈ Metric.ball z r → w' ∈ Metric.ball z r →
            w.2 ≤ w'.2 →
            ‖(∫ v in multiplierHeatShellSet z r j,
                (heatPotentialKernel w v : ℂ) * (F v : ℂ)) -
              ∫ v in multiplierHeatShellSet z r j,
                (heatPotentialKernel w' v : ℂ) * (F v : ℂ)‖ ≤
              C * parabolicDist w w' *
                ((2 : ℝ) ^ j * r) ^ (1 - 5 / θ : ℝ) *
                (morreyNorm P θ F).toReal := by
  obtain ⟨Cm, hCm, hmass⟩ := farShellAssembly_exists_shell_mass_bound hP hPθ
  refine ⟨32000000 * Cm, by positivity, ?_⟩
  intro F hF hFM z r j hr hj w w' hw hw' hww'
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ j * r := by positivity
  have hD0 : (0 : ℝ) ≤ parabolicDist w w' := by
    rw [← dist_eq_parabolicDist]; exact dist_nonneg
  have hS : MeasurableSet (multiplierHeatShellSet z r j) :=
    farShellAssembly_measurableSet_shell z r j
  obtain ⟨hFint, hFmass⟩ := hmass hF hFM z r j hr
  have hwc : w ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
    Metric.ball_subset_closedBall hw
  have hw'c : w' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
    Metric.ball_subset_closedBall hw'
  have hcx : ∀ q : ParabolicPoint,
      AEStronglyMeasurable (fun v => ((heatPotentialKernel q v : ℝ) : ℂ)) volume := by
    intro q
    exact (Complex.continuous_ofReal.measurable.comp
      (measurable_heatPotentialKernel_translate q)).aestronglyMeasurable
  have hsize : ∀ q : ParabolicPoint,
      q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r →
      ∀ v ∈ multiplierHeatShellSet z r j,
        ‖((heatPotentialKernel q v : ℝ) : ℂ)‖ ≤
          1000 / ((2 : ℝ) ^ j * r / 2) ^ 3 := by
    intro q hq v hv
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact farShellAssembly_scalar_kernel_size hr hj hv hq
  have hbound := farShellAssembly_pairing_diff_bound (S₁ := (∅ : Set ParabolicPoint))
    hS MeasurableSet.empty (Set.empty_subset _)
    (c₀ := 1000 / ((2 : ℝ) ^ j * r / 2) ^ 3)
    (c₁ := 32000000 / ((2 : ℝ) ^ j * r) ^ 4 * parabolicDist w w')
    (by positivity) (hcx w) (hcx w') hF hFint
    (hsize w hwc) (hsize w' hw'c) ?_ (by simp)
  · rw [setIntegral_empty, add_zero] at hbound
    refine hbound.trans ?_
    have hmul : 32000000 / ((2 : ℝ) ^ j * r) ^ 4 * parabolicDist w w' *
        (∫ v in multiplierHeatShellSet z r j, |F v|) ≤
        32000000 / ((2 : ℝ) ^ j * r) ^ 4 * parabolicDist w w' *
          (Cm * ((2 : ℝ) ^ j * r) ^ (5 - 5 / θ : ℝ) *
            (morreyNorm P θ F).toReal) :=
      mul_le_mul_of_nonneg_left hFmass (by positivity)
    refine hmul.trans (le_of_eq ?_)
    have hexp : ((2 : ℝ) ^ j * r) ^ (5 - 5 / θ : ℝ) /
        ((2 : ℝ) ^ j * r) ^ 4 = ((2 : ℝ) ^ j * r) ^ (1 - 5 / θ : ℝ) := by
      rw [show ((2 : ℝ) ^ j * r) ^ 4 = ((2 : ℝ) ^ j * r) ^ ((4 : ℕ) : ℝ) by
        rw [Real.rpow_natCast]]
      rw [← Real.rpow_sub hRpos]
      congr 1
      push_cast
      ring
    calc 32000000 / ((2 : ℝ) ^ j * r) ^ 4 * parabolicDist w w' *
          (Cm * ((2 : ℝ) ^ j * r) ^ (5 - 5 / θ : ℝ) *
            (morreyNorm P θ F).toReal)
        = 32000000 * Cm *
            (((2 : ℝ) ^ j * r) ^ (5 - 5 / θ : ℝ) / ((2 : ℝ) ^ j * r) ^ 4) *
            parabolicDist w w' * (morreyNorm P θ F).toReal := by ring
      _ = 32000000 * Cm * ((2 : ℝ) ^ j * r) ^ (1 - 5 / θ : ℝ) *
            parabolicDist w w' * (morreyNorm P θ F).toReal := by rw [hexp]
      _ = 32000000 * Cm * parabolicDist w w' *
            ((2 : ℝ) ^ j * r) ^ (1 - 5 / θ : ℝ) *
            (morreyNorm P θ F).toReal := by ring
  · intro v hv _
    have hdiff := farShellAssembly_scalar_kernel_diff hr hj hv hw hw' hww'
    calc ‖((heatPotentialKernel w v : ℝ) : ℂ) -
          ((heatPotentialKernel w' v : ℝ) : ℂ)‖
        = |heatPotentialKernel w v - heatPotentialKernel w' v| := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 32000000 / ((2 : ℝ) ^ j * r) ^ 4 * parabolicDist w w' := hdiff

/-- **A multiplier slot on a far shell.**  One constant, fixed after the
symbol and the exponents and before the source and the shell data, bounds the
oscillation of the multiplier heat potential of a finite-Morrey source
restricted to the shell of inner radius `2 ^ j r`.  The moving time strip,
on which only the later kernel is active, is measured by the established
thin-strip estimate. -/
theorem farShellAssembly_exists_multiplier_slot_bound (σ : Vec3 → ℂ)
    (hσ : SmoothOffOrigin σ) (hhom : IsDegreeOneHomogeneous σ)
    {P θ : ℝ} (hP : 1 ≤ P) (hPθ : P ≤ θ) (hθ : 5 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {G : ParabolicPoint → ℝ}, AEMeasurable G volume → morreyNorm P θ G < ∞ →
        ∀ (z : ParabolicPoint) (r : ℝ) (j : ℕ), 0 < r → 6 ≤ j →
          ∀ w w' : ParabolicPoint, w ∈ Metric.ball z r → w' ∈ Metric.ball z r →
            w.2 ≤ w'.2 →
            ‖(∫ v in multiplierHeatShellSet z r j,
                spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) *
                  (G v : ℂ)) -
              ∫ v in multiplierHeatShellSet z r j,
                spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2) *
                  (G v : ℂ)‖ ≤
              C * parabolicDist w w' * ((2 : ℝ) ^ j * r) ^ (-5 / θ : ℝ) *
                (morreyNorm P θ G).toReal := by
  obtain ⟨Cm, hCm, hmass⟩ := farShellAssembly_exists_shell_mass_bound hP hPθ
  obtain ⟨Ck, hCk, hksize, hkdiff⟩ :=
    farShellAssembly_exists_multiplier_kernel_bounds σ hσ hhom
  obtain ⟨Cs, hCs, hstrip⟩ := heatFarStripBound σ hσ hhom P θ hP hPθ hθ
  refine ⟨Ck * Cm + Cs, by positivity, ?_⟩
  intro G hG hGM z r j hr hj w w' hw hw' hww'
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ j * r := by positivity
  have hD0 : (0 : ℝ) ≤ parabolicDist w w' := by
    rw [← dist_eq_parabolicDist]; exact dist_nonneg
  have hMnn : (0 : ℝ) ≤ (morreyNorm P θ G).toReal := ENNReal.toReal_nonneg
  have hS : MeasurableSet (multiplierHeatShellSet z r j) :=
    farShellAssembly_measurableSet_shell z r j
  have hS₁ : MeasurableSet (multiplierHeatShellSet z r j ∩
      {v : ParabolicPoint | w.2 ≤ v.2 ∧ v.2 < w'.2}) := by
    refine hS.inter ?_
    have hpre : {v : ParabolicPoint | w.2 ≤ v.2 ∧ v.2 < w'.2} =
        (fun v : ParabolicPoint => v.2) ⁻¹' (Set.Ico w.2 w'.2) := rfl
    rw [hpre]
    exact measurable_snd measurableSet_Ico
  obtain ⟨hGint, hGmass⟩ := hmass hG hGM z r j hr
  have hwc : w ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
    Metric.ball_subset_closedBall hw
  have hw'c : w' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r :=
    Metric.ball_subset_closedBall hw'
  have hKm : ∀ q : ParabolicPoint, AEStronglyMeasurable
      (fun v : ParabolicPoint =>
        spatialMultiplierHeatKernel σ (q.1 - v.1) (q.2 - v.2)) volume := by
    intro q
    exact ((measurable_spatialMultiplierHeatKernel
      (contDiffOn_infty.mpr hσ) hhom).comp
      ((measurable_const.sub measurable_fst).prodMk
        (measurable_const.sub measurable_snd))).aestronglyMeasurable
  obtain ⟨-, hstripbd⟩ := hstrip G hG hGM z r j hr hj w w' hw hw' hww'
  have hbound := farShellAssembly_pairing_diff_bound
    (S₁ := multiplierHeatShellSet z r j ∩
      {v : ParabolicPoint | w.2 ≤ v.2 ∧ v.2 < w'.2})
    hS hS₁ Set.inter_subset_left
    (c₀ := Ck / ((2 : ℝ) ^ j * r) ^ 4)
    (c₁ := Ck / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w')
    (by positivity) (hKm w) (hKm w') hG hGint
    (fun v hv => hksize hr hj hv hwc) (fun v hv => hksize hr hj hv hw'c) ?_ ?_
  · refine hbound.trans ?_
    have hfirst : Ck / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w' *
        (∫ v in multiplierHeatShellSet z r j, |G v|) ≤
        Ck * Cm * parabolicDist w w' * ((2 : ℝ) ^ j * r) ^ (-5 / θ : ℝ) *
          (morreyNorm P θ G).toReal := by
      refine (mul_le_mul_of_nonneg_left hGmass (by positivity)).trans
        (le_of_eq ?_)
      have hexp : ((2 : ℝ) ^ j * r) ^ (5 - 5 / θ : ℝ) /
          ((2 : ℝ) ^ j * r) ^ 5 = ((2 : ℝ) ^ j * r) ^ (-5 / θ : ℝ) := by
        rw [show ((2 : ℝ) ^ j * r) ^ 5 = ((2 : ℝ) ^ j * r) ^ ((5 : ℕ) : ℝ) by
          rw [Real.rpow_natCast]]
        rw [← Real.rpow_sub hRpos]
        congr 1
        push_cast
        ring
      calc Ck / ((2 : ℝ) ^ j * r) ^ 5 * parabolicDist w w' *
            (Cm * ((2 : ℝ) ^ j * r) ^ (5 - 5 / θ : ℝ) *
              (morreyNorm P θ G).toReal)
          = Ck * Cm *
              (((2 : ℝ) ^ j * r) ^ (5 - 5 / θ : ℝ) / ((2 : ℝ) ^ j * r) ^ 5) *
              parabolicDist w w' * (morreyNorm P θ G).toReal := by ring
        _ = Ck * Cm * ((2 : ℝ) ^ j * r) ^ (-5 / θ : ℝ) *
              parabolicDist w w' * (morreyNorm P θ G).toReal := by rw [hexp]
        _ = Ck * Cm * parabolicDist w w' *
              ((2 : ℝ) ^ j * r) ^ (-5 / θ : ℝ) *
              (morreyNorm P θ G).toReal := by ring
    have hsecond : (∫ v in multiplierHeatShellSet z r j ∩
          {v : ParabolicPoint | w.2 ≤ v.2 ∧ v.2 < w'.2},
          ‖spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2) *
            (G v : ℂ)‖) ≤
        Cs * parabolicDist w w' * ((2 : ℝ) ^ j * r) ^ (-5 / θ : ℝ) *
          (morreyNorm P θ G).toReal := by
      rw [show ((2 : ℝ) ^ j * r) = ((2 : ℝ) ^ (j : ℝ) * r) by
        rw [Real.rpow_natCast]]
      exact hstripbd
    refine (add_le_add hfirst hsecond).trans (le_of_eq ?_)
    ring
  · intro v hv hv₁
    have hcase : v.2 < w.2 ∨ w'.2 ≤ v.2 := by
      by_contra hcon
      push Not at hcon
      exact hv₁ ⟨hv, hcon.1, hcon.2⟩
    rcases hcase with hlt | hge
    · exact hkdiff hr hj hv hw hw' hww' hlt
    · rw [spatialMultiplierHeatKernel_of_nonpos σ _
        (by linarith only [hge, hww'] : w.2 - v.2 ≤ 0),
        spatialMultiplierHeatKernel_of_nonpos σ _
        (by linarith only [hge] : w'.2 - v.2 ≤ 0), sub_zero, norm_zero]
      positivity
  · intro v hv
    exact spatialMultiplierHeatKernel_of_nonpos σ _
      (by linarith only [hv.2.1] : w.2 - v.2 ≤ 0)

end CKN.Core.HeatPotential
