-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.AdamsAEMeasurable
import CKN.Core.Endgame.BootstrapPotential
import CKN.Core.Step4.Bootstrap
import CKN.Core.Endgame.CarrierLocalAE
import CKN.Core.Endgame.CutoffDerivatives
import CKN.Core.Endgame.SourceComponents
import CKN.Core.Endgame.TheoremBCloser
import CKN.Core.Endgame.CompactBall
import CKN.Core.Step3.GradientSlotDuhamel
import CKN.Core.Step3.LocalizedEquationBasics
import CKN.Core.Step4.LocalizedEquationGradientData
import CKN.Core.Step4.LocalizedEquationGradientMeasurability
import CKN.Core.Step4.PointwisePotential
import CKN.Core.Step4.RouteAGradientProducerUniform
import CKN.Core.Step4.SourceMorreyGradientPackage
import CKN.Core.Step4.SourceMorreyKernels
import CKN.Core.Step4.SourceMorreyFirstRoundCutoff
import CKN.Core.Step4.SourceMorreyFirstRoundSupport
import CKN.Core.Step4.SourceMorreyData
import CKN.Core.Step4.WeakGradientGluingTCollarAssembly
import CKN.Core.Step4.WeakGradientGluingTRemainderMajorant
import CKN.Foundation.Parabolic.Morrey.AdamsM4
import CKN.Foundation.Parabolic.Morrey.BallVariants
import CKN.Foundation.Parabolic.Morrey.LowerBounds
import CKN.Foundation.Parabolic.Morrey.Neg
import CKN.Foundation.Parabolic.Morrey.VecMem

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3
open CKN.Core.Step4
open CKN.Core.Endgame

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-! # Potential estimates for one bootstrap round

These estimates control the localized source terms and the exponents used by
the parabolic Adams bounds in the faithful one-round proposition.
-/

/-- Exponent for the pressure-gradient source slot in one bootstrap round. -/
def bootstrapPressureExponent (τ : ℝ) : ℝ :=
  (1 / τ + 8 / 25)⁻¹

/-- Exponent for the derivative source slot in one bootstrap round. -/
def bootstrapDerivativeExponent (τ : ℝ) : ℝ :=
  (1 / τ + 3 / 25)⁻¹

/-- Improved velocity exponent determined by the round's reciprocal-exponent gain. -/
def bootstrapOutputExponent (τ : ℝ) : ℝ :=
  (1 / τ - 2 / 25)⁻¹

/-- Bounds the source and output exponents under the round's numerical hypotheses. -/
theorem bootstrap_exponent_facts {τ : ℝ}
    (hτ : 5 < τ) (hcond : 1 / (25 / 8 : ℝ) + 1 / τ > 2 / 5) :
    0 < τ ∧ τ < 25 / 2 ∧
      6 / 5 ≤ bootstrapPressureExponent τ ∧
      3 / 2 ≤ bootstrapPressureExponent τ ∧
      bootstrapPressureExponent τ < 5 / 2 ∧
      3 < bootstrapDerivativeExponent τ ∧
      bootstrapDerivativeExponent τ < 5 ∧
      5 < bootstrapOutputExponent τ := by
  have hτpos : 0 < τ := by linarith only [hτ]
  have hrecip : 2 / 25 < 1 / τ := by
    norm_num at hcond ⊢
    linarith only [hcond]
  have hτtop : τ < 25 / 2 := by
    have hmul := (mul_lt_mul_of_pos_right hrecip hτpos)
    have hmul' : τ * (2 / 25 : ℝ) < 1 := by
      convert hmul using 1 <;> field_simp [ne_of_gt hτpos]
    nlinarith only [hmul']
  have hinv5 : 1 / τ < 1 / 5 := by
    exact one_div_lt_one_div_of_lt (by norm_num) hτ
  have hpresspos : 0 < 1 / τ + 8 / 25 := by positivity
  have hpresslo : 1 / τ + 8 / 25 < 13 / 25 := by
    linarith only [hinv5]
  have hpresshi : 2 / 5 < 1 / τ + 8 / 25 := by
    linarith only [hrecip]
  have hderivpos : 0 < 1 / τ + 3 / 25 := by positivity
  have hderivlo : 1 / τ + 3 / 25 < 8 / 25 := by
    linarith only [hinv5]
  have hderivhi : 1 / 5 < 1 / τ + 3 / 25 := by
    linarith only [hrecip]
  have hgainpos : 0 < 1 / τ - 2 / 25 := by
    linarith only [hrecip]
  constructor
  · exact hτpos
  constructor
  · exact hτtop
  constructor
  · have hrecip' : 1 / τ + 8 / 25 < 5 / 6 := by
      linarith only [hpresslo]
    have hinv := one_div_lt_one_div_of_lt hpresspos hrecip'
    have hinv' : 6 / 5 < bootstrapPressureExponent τ := by
      norm_num [bootstrapPressureExponent] at hinv ⊢
      exact hinv
    exact hinv'.le
  constructor
  · have hrecip' : 1 / τ + 8 / 25 < 2 / 3 := by
      linarith only [hpresslo]
    have hinv := one_div_lt_one_div_of_lt hpresspos hrecip'
    have hinv' : 3 / 2 < bootstrapPressureExponent τ := by
      norm_num [bootstrapPressureExponent] at hinv ⊢
      exact hinv
    exact hinv'.le
  constructor
  · have hinv := one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 / 5 by norm_num)
      hpresshi
    have hident : (2 / 5 : ℝ)⁻¹ = 5 / 2 := by norm_num
    have hresult : bootstrapPressureExponent τ < 5 / 2 := by
      simpa [bootstrapPressureExponent, hident] using hinv
    exact hresult
  constructor
  · have hinv := one_div_lt_one_div_of_lt hderivpos hderivlo
    have hident : (8 / 25 : ℝ)⁻¹ = 25 / 8 := by norm_num
    have hgt : (3 : ℝ) < 25 / 8 := by norm_num
    have hresult : 3 < bootstrapDerivativeExponent τ := by
      have hstep : 25 / 8 < bootstrapDerivativeExponent τ := by
        simpa [bootstrapDerivativeExponent] using hinv
      exact lt_trans hgt hstep
    exact hresult
  constructor
  · have hinv := one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 / 5 by norm_num)
      hderivhi
    have hident : (1 / 5 : ℝ)⁻¹ = 5 := by norm_num
    have hresult : bootstrapDerivativeExponent τ < 5 := by
      simpa [bootstrapDerivativeExponent, hident] using hinv
    exact hresult
  · have hgainhi : 1 / τ - 2 / 25 < 1 / 5 := by
      linarith only [hinv5]
    have hinv := one_div_lt_one_div_of_lt hgainpos hgainhi
    have hident : (1 / 5 : ℝ)⁻¹ = 5 := by norm_num
    have hresult : 5 < bootstrapOutputExponent τ := by
      simpa [bootstrapOutputExponent, hident] using hinv
    exact hresult

/-- Converts finite Morrey norm on a bounded ball into local integrability. -/
theorem bootstrap_integrable_of_ball_morrey
    {D : ParabolicPoint → ℝ} {κ : ℝ} {z : ParabolicPoint} {R : ℝ}
    [IsFiniteMeasure (volume.restrict (Metric.ball z R))]
    (hR : 0 < R)
    (hD : AEMeasurable D (volume.restrict (Metric.ball z R)))
    (hN : morreyBallNorm (6 / 5 : ℝ) κ
      ((Metric.ball z R).indicator D) < ∞) :
    Integrable D (volume.restrict (Metric.ball z R)) := by
  have hcell := morreyBallCell_lt_top_of_morreyBallNorm_lt_top hN z hR
  have hexp : 0 < 1 / (6 / 5 : ℝ) := by norm_num
  have hintegral : ballPowerIntegral (6 / 5 : ℝ)
      ((Metric.ball z R).indicator D) z R < ∞ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hfactor : 0 < ENNReal.ofReal R ^
        (-(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5 : ℝ))) :=
      ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hR) ENNReal.ofReal_ne_top
    have hcelltop : morreyBallCell (6 / 5 : ℝ) κ
        ((Metric.ball z R).indicator D) z R = ∞ := by
      unfold morreyBallCell
      rw [htop, ENNReal.top_rpow_of_pos hexp,
        ENNReal.mul_top hfactor.ne']
    exact (lt_top_iff_ne_top.mp hcell) hcelltop
  have hset : ballPowerIntegral (6 / 5 : ℝ)
      ((Metric.ball z R).indicator D) z R =
      ∫⁻ w in Metric.ball z R, ENNReal.ofReal |D w| ^ (6 / 5 : ℝ) := by
    rw [ballPowerIntegral_indicator (by norm_num) Metric.isOpen_ball.measurableSet D z R]
    simp only [Set.inter_self]
  have hmem : MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (Metric.ball z R)) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num) ENNReal.ofReal_ne_top hD.aestronglyMeasurable).mpr
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5),
      Real.enorm_eq_ofReal_abs, hset] using hintegral
  exact hmem.integrable (by norm_num)

/-- Controls the Morrey norm after restricting its carrier. -/
theorem bootstrap_norm_sub_le {P κ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) :
    morreyNorm P κ (fun z => f z - g z) ≤
      morreyNorm P κ f + morreyNorm P κ g := by
  have h := morrey_norm_add_le (τ := κ) hP hf hg.neg
  change morreyNorm P κ (fun z => f z + -g z) ≤
      morreyNorm P κ f + morreyNorm P κ (fun z => -g z) at h
  rw [morreyNorm_neg] at h
  simpa only [sub_eq_add_neg] using h

/-- Estimates the localized source terms from the Step 2 Morrey data. -/
theorem bootstrap_source_bounds
    {τ κ θ C R₀ : ℝ} {z₀ : ParabolicPoint}
    {Q : Set ParabolicPoint}
    {φ : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {f Dp : ParabolicPoint → Vec3}
    (hκlo : 6 / 5 ≤ κ)
    (hτlo : 3 ≤ τ) (hκτ : κ ≤ τ)
    (hθlo : 3 ≤ θ) (hθτ : θ ≤ τ)
    (hrecip : 1 / κ = 1 / τ + 8 / 25)
    (hC : 0 < C)
    (hUae : ∀ j, AEMeasurable (Q.indicator (fun z => u z j)) volume)
    (hDae : ∀ i j, AEMeasurable (Q.indicator (fun z => Du z i j)) volume)
    (hD : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      (Q.indicator (fun z => Du z i j)) < ⊤)
    (hU : ∀ j, morreyNorm 3 τ (Q.indicator (fun z => u z j)) < ⊤)
    (hR₀ : 0 < R₀)
    (hQ : Q ⊆ parabolicCylinder z₀.1 z₀.2 R₀)
    (hφbound : ∀ z, |φ z| ≤ C)
    (hφae : AEMeasurable φ volume)
    (htimeae : AEMeasurable (fun z => timePartial φ z) volume)
    (hlapae : AEMeasurable (fun z : ParabolicPoint =>
      spatialLaplacian (fun x => φ (x, z.2)) z.1) volume)
    (hDpAE : ∀ i, AEMeasurable (Q.indicator (fun z => Dp z i)) volume)
    (hforceAE : ∀ i, AEMeasurable (fun z => φ z * f z i) volume)
    (hforce : ∀ i, morreyNorm (6 / 5 : ℝ) κ
      (fun z => φ z * f z i) < ⊤)
    (hφzero : ∀ z ∉ Q, φ z = 0)
    (htimebound : ∀ z, |timePartial φ z| ≤ C)
    (hlapbound : ∀ z : ParabolicPoint,
      |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C)
    (hspbound : ∀ j (z : Vec3 × ℝ), |spatialPartial φ j z| ≤ C)
    (htimezero : ∀ z ∉ Q, timePartial φ z = 0)
    (hlapzero : ∀ z ∉ Q,
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0)
    (hspzero : ∀ j z, z ∉ Q → spatialPartial φ j z = 0)
    (hDp : ∀ i, morreyNorm (6 / 5 : ℝ) κ
      (Q.indicator (fun z => Dp z i)) < ⊤) :
    (∀ i, morreyNorm (6 / 5 : ℝ) κ
      (fun z => localizedGradientSourceG φ u Du f Dp z i) < ⊤) ∧
    (∀ j i, morreyNorm 3 θ
      (fun z => -localizedGradientSourceH φ u j z i) < ⊤) := by
  have hUlow (i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ
      (Q.indicator (fun z => u z i)) < ⊤ := by
    apply morreyNorm_lt_top_of_lower_exponents (P := (6 / 5 : ℝ)) (P₀ := 3)
      (θ := κ) (θ₀ := τ) (B := Q) (z₀ := z₀) (R := R₀)
      (by norm_num) (by norm_num) hτlo hκlo hκτ hR₀ hQ
      (hUae i) (fun z hz => indicator_of_notMem hz _) (hU i)
  have hconvProduct (i j : Fin 3) : morreyNorm (6 / 5 : ℝ) κ
      (fun z => Q.indicator (fun w => u w j) z *
        Q.indicator (fun w => Du w i j) z) < ⊤ := by
    have hrel : 1 / κ = 1 / τ + 1 / (25 / 8 : ℝ) := by
      rw [hrecip]
      norm_num
    exact (source_product_morrey_bound (P := (6 / 5 : ℝ))
      (P₁ := 3) (P₂ := 2) (θ := κ) (θ₁ := τ) (θ₂ := 25 / 8)
      (by norm_num) (by norm_num) (by norm_num) hrel
      (hUae j) (hDae i j) (hU j) (hD i j)).1
  have hconvProductsAE (i : Fin 3) : AEMeasurable
      (fun z => ∑ j : Fin 3,
        Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z)
      volume := by
    have h0 := (hUae 0).mul (hDae i 0)
    have h1 := (hUae 1).mul (hDae i 1)
    have h2 := (hUae 2).mul (hDae i 2)
    simpa [Fin.sum_univ_succ, Pi.add_def] using h0.add (h1.add h2)
  have hconvProducts (i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ
      (fun z => ∑ j : Fin 3,
        Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) < ⊤ := by
    have h12 := (morrey_norm_add_le (τ := κ) (by norm_num)
      ((hUae 1).mul (hDae i 1)) ((hUae 2).mul (hDae i 2))).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hconvProduct i 1, hconvProduct i 2⟩)
    have hall := (morrey_norm_add_le (τ := κ) (by norm_num)
      ((hUae 0).mul (hDae i 0)) (((hUae 1).mul (hDae i 1)).add
        ((hUae 2).mul (hDae i 2)))).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hconvProduct i 0, h12⟩)
    simpa [Fin.sum_univ_succ, Pi.add_def] using hall
  have htimeBase (i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ
      (fun z => timePartial φ z * u z i) < ⊤ := by
    have hmul := morrey_norm_mul_le_indicator (6 / 5) κ C
      (by norm_num) (le_of_lt hC) Q (fun z => timePartial φ z)
      (fun z => u z i) htimebound (fun z hz => htimezero z hz)
    exact (hmul.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hUlow i)))
  have hlapBase (i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) < ⊤ := by
    have hmul := morrey_norm_mul_le_indicator (6 / 5) κ C
      (by norm_num) (le_of_lt hC) Q
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1)
      (fun z => u z i) hlapbound (fun z hz => hlapzero z hz)
    exact hmul.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hUlow i))
  have hconvBase (i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ
      (fun z => φ z * localizedConvection u Du z i) < ⊤ := by
    have hmul := morrey_norm_mul_le_indicator (6 / 5) κ C
      (by norm_num) (le_of_lt hC) Q φ
      (fun z => ∑ j : Fin 3,
        Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z)
      (fun z => hφbound z)
      (fun z hz => hφzero z hz)
    have heq : (fun z => φ z * localizedConvection u Du z i) =
        (fun z => φ z * ∑ j : Fin 3,
          Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) := by
      funext z
      by_cases hz : z ∈ Q
      · simp [hz, localizedConvection]
      · simp [hz, hφzero z hz]
    rw [heq]
    have hsumInd : morreyNorm (6 / 5 : ℝ) κ
        (Q.indicator (fun z => ∑ j : Fin 3,
          Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z)) < ⊤ :=
      (morreyNorm_indicator_le (by norm_num) Q _).trans_lt (hconvProducts i)
    exact hmul.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsumInd)
  have hpressureBase (i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ
      (fun z => φ z * Dp z i) < ⊤ := by
    have hmul := morrey_norm_mul_le_indicator (6 / 5) κ C
      (by norm_num) (le_of_lt hC) Q φ (fun z => Dp z i)
      (fun z => hφbound z) hφzero
    exact (hmul.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hDp i)))
  have htimeAE' (i : Fin 3) : AEMeasurable
      (fun z => timePartial φ z * u z i) volume := by
    have h : AEMeasurable
        (fun z => timePartial φ z * Q.indicator (fun w => u w i) z) volume :=
      htimeae.mul (hUae i)
    have heq : (fun z => timePartial φ z * u z i) =
        (fun z => timePartial φ z * Q.indicator (fun w => u w i) z) := by
      funext z
      by_cases hz : z ∈ Q
      · simp [hz]
      · simp [hz, htimezero z hz]
    rw [heq]
    exact h
  have hlapAE' (i : Fin 3) : AEMeasurable
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) volume := by
    have h : AEMeasurable
        (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 *
          Q.indicator (fun w => u w i) z) volume := hlapae.mul (hUae i)
    have heq : (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) =
        (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 *
          Q.indicator (fun w => u w i) z) := by
      funext z
      by_cases hz : z ∈ Q
      · simp [hz]
      · simp [hz, hlapzero z hz]
    rw [heq]
    exact h
  have hconvAE' (i : Fin 3) : AEMeasurable
      (fun z => φ z * localizedConvection u Du z i) volume := by
    have h := hφae.mul (hconvProductsAE i)
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ Q
    · simp [hz, localizedConvection]
    · simp [hz, hφzero z hz]
  have hpressAE' (i : Fin 3) : AEMeasurable
      (fun z => φ z * Dp z i) volume := by
    have h : AEMeasurable
        (fun z => φ z * Q.indicator (fun w => Dp w i) z) volume :=
      hφae.mul (hDpAE i)
    have heq : (fun z => φ z * Dp z i) =
        (fun z => φ z * Q.indicator (fun w => Dp w i) z) := by
      funext z
      by_cases hz : z ∈ Q
      · simp [hz]
      · simp [hz, hφzero z hz]
    rw [heq]
    exact h
  constructor
  · intro i
    have htl := (morrey_norm_add_le (τ := κ) (by norm_num)
      (htimeAE' i) (hlapAE' i)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨htimeBase i, hlapBase i⟩)
    have htlc := bootstrap_norm_sub_le (P := (6 / 5 : ℝ))
      (κ := κ) (by norm_num) ((htimeAE' i).add (hlapAE' i)) (hconvAE' i)
    have htlc' : morreyNorm (6 / 5 : ℝ) κ
        (fun z => (timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
            φ z * localizedConvection u Du z i) < ⊤ :=
      htlc.trans_lt (ENNReal.add_lt_top.mpr ⟨htl, hconvBase i⟩)
    have hpre : morreyNorm (6 / 5 : ℝ) κ
        (fun z => ((timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
            φ z * localizedConvection u Du z i) + φ z * f z i) < ⊤ := by
      have hsum := (morrey_norm_add_le (P := (6 / 5 : ℝ)) (τ := κ) (by norm_num)
        (((htimeAE' i).add (hlapAE' i)).sub (hconvAE' i)) (hforceAE i))
      exact hsum.trans_lt (ENNReal.add_lt_top.mpr ⟨htlc', hforce i⟩)
    have hfinal := bootstrap_norm_sub_le (P := (6 / 5 : ℝ))
      (κ := κ) (by norm_num)
      ((((htimeAE' i).add (hlapAE' i)).sub (hconvAE' i)).add (hforceAE i))
      (hpressAE' i)
    have hfinaltop := hfinal.trans_lt
      (ENNReal.add_lt_top.mpr ⟨hpre, hpressureBase i⟩)
    have heq : (fun z => localizedGradientSourceG φ u Du f Dp z i) =
        (fun z => ((timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
            φ z * localizedConvection u Du z i) + φ z * f z i - φ z * Dp z i) := by
      funext z
      simp [localizedGradientSourceG, localizedEquationG, localizedConvection]
    rw [heq]
    simpa [sub_eq_add_neg, add_assoc] using hfinaltop
  · intro j i
    have hθU : morreyNorm 3 θ (Q.indicator (fun z => u z i)) < ⊤ := by
      apply morreyNorm_lt_top_of_lower_exponents (P := 3) (P₀ := 3)
        (θ := θ) (θ₀ := τ) (B := Q) (z₀ := z₀) (R := R₀)
        (by norm_num) (by norm_num) hτlo hθlo hθτ hR₀ hQ
        (hUae i) (fun z hz => indicator_of_notMem hz _) (hU i)
    have hmul := morrey_norm_mul_le_indicator 3 θ (2 * C)
      (by norm_num) (by positivity) Q
      (fun z => 2 * spatialPartial φ j z) (fun z => u z i)
      (fun z => by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left (hspbound j (z.1, z.2)) (by norm_num))
      (fun z hz => by rw [hspzero j z hz]; ring)
    have hheq : (fun z => -localizedGradientSourceH φ u j z i) =
        (fun z => 2 * spatialPartial φ j z * u z i) := by
      funext z
      simp [localizedGradientSourceH, localizedEquationH]
    rw [hheq]
    exact hmul.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hθU)

/-- Records the reciprocal-exponent identities for the two Adams estimates. -/
theorem bootstrap_adams_exponent_identities {τ : ℝ}
    (hτ : 5 < τ)
    (hcond : 1 / (25 / 8 : ℝ) + 1 / τ > 2 / 5) :
    bootstrapPressureExponent τ /
        (1 - 2 * bootstrapPressureExponent τ / 5) =
          bootstrapOutputExponent τ ∧
      bootstrapDerivativeExponent τ /
        (1 - bootstrapDerivativeExponent τ / 5) =
          bootstrapOutputExponent τ := by
  have hτpos : 0 < τ := by linarith only [hτ]
  have hτtop : τ < 25 / 2 := by
    have hfacts := bootstrap_exponent_facts hτ hcond
    exact hfacts.2.1
  have hrecip : 2 / 25 < 1 / τ := by
    norm_num at hcond ⊢
    linarith only [hcond]
  have hκbase : 0 < 1 / τ + 8 / 25 := by positivity
  have hθbase : 0 < 1 / τ + 3 / 25 := by positivity
  have hσbase : 0 < 1 / τ - 2 / 25 := by linarith only [hrecip]
  have hden : 0 < 25 - 2 * τ := by nlinarith only [hτtop]
  have hden' : 0 < 125 - 10 * τ := by nlinarith only [hden]
  have hκden : 0 < 1 - 2 * bootstrapPressureExponent τ / 5 := by
    have hfacts := bootstrap_exponent_facts hτ hcond
    rcases hfacts with ⟨_, _, _, _, hκlt, _, _, _⟩
    nlinarith only [hκlt]
  have hθden : 0 < 1 - bootstrapDerivativeExponent τ / 5 := by
    have hfacts := bootstrap_exponent_facts hτ hcond
    rcases hfacts with ⟨_, _, _, _, _, _, hθlt, _⟩
    nlinarith only [hθlt]
  constructor
  · unfold bootstrapPressureExponent bootstrapOutputExponent
    field_simp [ne_of_gt hτpos, ne_of_gt hκbase, ne_of_gt hσbase,
      ne_of_gt hκden]
    ring_nf
    have hrel : 125 - τ * 10 = 5 * (25 - 2 * τ) := by ring
    rw [hrel, mul_inv_rev]
    field_simp [ne_of_gt hden]
  · unfold bootstrapDerivativeExponent bootstrapOutputExponent
    field_simp [ne_of_gt hτpos, ne_of_gt hθbase, ne_of_gt hσbase,
      ne_of_gt hθden]
    ring_nf
    have hrel : 125 - τ * 10 = 5 * (25 - 2 * τ) := by ring
    rw [hrel, mul_inv_rev]
    field_simp [ne_of_gt hden]

/-- Establishes finite Morrey norm for the pointwise potential majorant. -/
theorem bootstrap_pointwise_majorant_finite
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {κ θ σ : ℝ}
    (hκlo : 3 / 2 ≤ κ) (hκhi : κ < 5 / 2)
    (hθlo : 3 ≤ θ) (hθhi : θ < 5)
    (hσg : κ / (1 - 2 * κ / 5) = σ)
    (hσh : θ / (1 - θ / 5) = σ)
    (hg : ∀ i, AEMeasurable (fun z => g z i) volume)
    (hh : ∀ j i, AEMeasurable (fun z => h j z i) volume)
    (hgN : morreyNorm (6 / 5 : ℝ) κ
      (fun z => vec3EuclideanNorm (g z)) < ∞)
    (hhN : ∀ j, morreyNorm 3 θ
      (fun z => vec3EuclideanNorm (h j z)) < ∞) :
    morreyNorm 3 σ (pointwisePotentialMajorant g h) < ∞ := by
  let P₂ : ParabolicPoint → ℝ := fun z =>
    (parabolicRieszPotential 2 (fun w => vec3EuclideanNorm (g w)) z).toReal
  let P₁ : Fin 3 → ParabolicPoint → ℝ := fun j z =>
    (parabolicRieszPotential 1 (fun w => vec3EuclideanNorm (h j w)) z).toReal
  have hκpos : 0 < κ := by linarith only [hκlo]
  have hθpos : 0 < θ := by linarith only [hθlo]
  have hden₂ : 0 < 1 - 2 * κ / 5 := by nlinarith only [hκhi]
  have hden₁ : 0 < 1 - θ / 5 := by nlinarith only [hθhi]
  have hP₂ : 3 ≤ (6 / 5 : ℝ) / (1 - 2 * κ / 5) := by
    apply (le_div_iff₀ hden₂).2
    nlinarith only [hκlo]
  have hP₂σ : (6 / 5 : ℝ) / (1 - 2 * κ / 5) ≤ σ := by
    rw [← hσg]
    exact div_le_div_of_nonneg_right (by linarith only [hκlo]) hden₂.le
  have hP₁ : 3 ≤ 3 / (1 - θ / 5) := by
    apply (le_div_iff₀ hden₁).2
    have hdenle : 1 - θ / 5 ≤ 1 := by linarith only [hθlo]
    nlinarith only [hdenle]
  have hP₁σ : 3 / (1 - θ / 5) ≤ σ := by
    rw [← hσh]
    exact div_le_div_of_nonneg_right hθlo hden₁.le
  have hAdams₂ := riesz_adams_of_aemeasurable
    (P := (6 / 5 : ℝ)) (τ := κ) (β := (2 : ℝ))
    (by norm_num) (by linarith only [hκlo]) (by norm_num) (by nlinarith only [hκhi])
    (aemeasurable_euclidean_norm_of_components hg)
  have hC₂ := adams_potential_constant_lt_top
    (β := (2 : ℝ)) (P := (6 / 5 : ℝ)) (τ := κ)
    (by norm_num) (by norm_num) (by linarith only [hκlo]) (by nlinarith only [hκhi])
  have h₂top : morreyNorm ((6 / 5 : ℝ) / (1 - 2 * κ / 5)) σ P₂ < ∞ := by
    have hbound : morreyNorm ((6 / 5 : ℝ) / (1 - 2 * κ / 5))
        (κ / (1 - 2 * κ / 5)) P₂ ≤
        parabolicAdamsPotentialConstant 2 (6 / 5 : ℝ) κ *
          morreyNorm (6 / 5 : ℝ) κ
            (fun z => vec3EuclideanNorm (g z)) := by
      simpa [P₂] using hAdams₂
    have hprod : parabolicAdamsPotentialConstant 2 (6 / 5 : ℝ) κ *
        morreyNorm (6 / 5 : ℝ) κ
          (fun z => vec3EuclideanNorm (g z)) < ∞ :=
      ENNReal.mul_lt_top hC₂ hgN
    have hfinite := hbound.trans_lt hprod
    simpa only [hσg] using hfinite
  have hP₂ae : AEMeasurable P₂ volume := by
    exact (measurable_riesz_potential_of_aemeasurable 2
      (aemeasurable_euclidean_norm_of_components hg)).ennreal_toReal.aemeasurable
  have hP₂lower := morreyNorm_lower_integrability
    (p' := (3 : ℝ)) (p := (6 / 5 : ℝ) / (1 - 2 * κ / 5)) (q := σ)
    (by norm_num) hP₂ hP₂σ hP₂ae
  have hP₂pow : 0 ≤ 1 / (3 : ℝ) -
      1 / ((6 / 5 : ℝ) / (1 - 2 * κ / 5)) := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hP₂)
  have hP₂finite : morreyNorm 3 σ P₂ < ∞ :=
    hP₂lower.trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hP₂pow
        Integration.volume_parabolicCylinder_lt_top.ne) h₂top)
  have hAdams₁ (j : Fin 3) := riesz_adams_of_aemeasurable
    (P := (3 : ℝ)) (τ := θ) (β := (1 : ℝ))
    (by norm_num) hθlo (by norm_num) (by simpa using hθhi)
    (aemeasurable_euclidean_norm_of_components (hh j))
  have hC₁ := adams_potential_constant_lt_top
    (β := (1 : ℝ)) (P := (3 : ℝ)) (τ := θ)
    (by norm_num) (by norm_num) hθlo (by simpa using hθhi)
  have hP₁top (j : Fin 3) :
      morreyNorm (3 / (1 - θ / 5)) σ (P₁ j) < ∞ := by
    have hbound : morreyNorm (3 / (1 - θ / 5))
        (θ / (1 - θ / 5)) (P₁ j) ≤
        parabolicAdamsPotentialConstant 1 3 θ *
          morreyNorm 3 θ (fun z => vec3EuclideanNorm (h j z)) := by
      simpa only [one_mul, P₁] using hAdams₁ j
    have hprod : parabolicAdamsPotentialConstant 1 3 θ *
        morreyNorm 3 θ (fun z => vec3EuclideanNorm (h j z)) < ∞ :=
      ENNReal.mul_lt_top hC₁ (hhN j)
    have hfinite := hbound.trans_lt hprod
    simpa only [hσh] using hfinite
  have hP₁ae (j : Fin 3) : AEMeasurable (P₁ j) volume := by
    exact (measurable_riesz_potential_of_aemeasurable 1
      (aemeasurable_euclidean_norm_of_components (hh j))).ennreal_toReal.aemeasurable
  have hP₁lower (j : Fin 3) := morreyNorm_lower_integrability
    (p' := (3 : ℝ)) (p := 3 / (1 - θ / 5)) (q := σ)
    (by norm_num) hP₁ hP₁σ (hP₁ae j)
  have hP₁pow : ∀ j : Fin 3,
      0 ≤ 1 / (3 : ℝ) - 1 / (3 / (1 - θ / 5)) := by
    intro j
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hP₁)
  have hP₁finite (j : Fin 3) : morreyNorm 3 σ (P₁ j) < ∞ :=
    (hP₁lower j).trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (hP₁pow j)
        Integration.volume_parabolicCylinder_lt_top.ne) (hP₁top j))
  have h12 : morreyNorm 3 σ (fun z => P₁ 1 z + P₁ 2 z) < ∞ := by
    exact (morrey_norm_add_le (by norm_num) (hP₁ae 1) (hP₁ae 2)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hP₁finite 1, hP₁finite 2⟩)
  have hsum : morreyNorm 3 σ (fun z => P₁ 0 z + (P₁ 1 z + P₁ 2 z)) < ∞ := by
    exact (morrey_norm_add_le (by norm_num) (hP₁ae 0)
      ((hP₁ae 1).add (hP₁ae 2))).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hP₁finite 0, h12⟩)
  have hGscaled : morreyNorm 3 σ (fun z => 3000 * P₂ z) < ∞ := by
    have hbound := morreyNorm_const_mul_le (P := (3 : ℝ)) (τ := σ)
      (by norm_num) (3000 : ℝ) P₂
    exact hbound.trans_lt (ENNReal.mul_lt_top (by norm_num) hP₂finite)
  have hHscaled : morreyNorm 3 σ
      (fun z => 900000 * (P₁ 0 z + (P₁ 1 z + P₁ 2 z))) < ∞ := by
    have hbound := morreyNorm_const_mul_le (P := (3 : ℝ)) (τ := σ)
      (by norm_num) (900000 : ℝ) (fun z => P₁ 0 z + (P₁ 1 z + P₁ 2 z))
    exact hbound.trans_lt (ENNReal.mul_lt_top (by norm_num) hsum)
  have htotal := (morrey_norm_add_le (P := (3 : ℝ)) (τ := σ) (by norm_num)
      ((hP₂ae.const_mul 3000))
      (((hP₁ae 0).add ((hP₁ae 1).add (hP₁ae 2))).const_mul 900000)).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hGscaled, hHscaled⟩)
  change morreyNorm 3 σ (fun z => 3000 * P₂ z + 900000 * ∑ j, P₁ j z) < ∞
  simpa [P₂, P₁, pointwisePotentialMajorant, Fin.sum_univ_succ] using htotal

/-- Supplies the uniform Route A gradient producer from suitable-solution data. -/
theorem bootstrap_routeA_uniform : routeAGradientProducerUniform := by
  apply theoremB_gradient_producer_of_small_cell_majorant
  exact shared_binder_of_remainder_majorant (by
    intro Ω I q hq u Du p f hsol z ρ hρ hsub
    exact fixed_remainder_temporal_majorant_of_sws hq hsol hρ hsub)

/-- Bounds every vector component by the Euclidean vector norm. -/
theorem bootstrap_component_le_norm (v : Vec3) (i : Fin 3) :
    |v i| ≤ vec3EuclideanNorm v := by
  rw [vec3EuclideanNorm]
  exact Real.abs_le_sqrt
    (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

