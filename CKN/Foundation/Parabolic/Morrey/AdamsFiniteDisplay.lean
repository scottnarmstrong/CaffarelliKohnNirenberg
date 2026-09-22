-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.AdamsConstants
import CKN.Foundation.Parabolic.Morrey.MaximalMorrey
import CKN.Foundation.Parabolic.Morrey.Minkowski
import CKN.Foundation.Parabolic.Morrey.Cylinders

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

private theorem parabolicMaximalMajorant_ae_lt_top_of_morreyNorm_lt_top
    {P τ : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) {f : ParabolicPoint → ℝ}
    (hf : Measurable f) (hN : morreyNorm P τ f < ∞) :
    ∀ᵐ z ∂volume, parabolicMaximalMajorant f z < ∞ := by
  let M : ParabolicPoint → ℝ≥0∞ := parabolicMaximalMajorant f
  let B : ℕ → Set ParabolicPoint := fun n =>
    @Metric.ball ParabolicPoint parabolicPseudoMetricSpace
      ((0 : Vec3), (0 : ℝ)) ((n : ℝ) + 1)
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hτ0 : 0 < τ := lt_of_lt_of_le hP0 hPτ
  have hPinv : 1 / τ ≤ 1 / P := one_div_le_one_div_of_le hP0 hPτ
  have hballFactorExp : 0 ≤ 5 * (1 / P - 1 / τ) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hPinv)
  have hballFactor : (2 : ℝ≥0∞) ^ (5 * (1 / P - 1 / τ)) < ∞ :=
    lt_top_iff_ne_top.mpr
      (ENNReal.rpow_ne_top_of_nonneg hballFactorExp ENNReal.ofNat_ne_top)
  have hballNorm : morreyBallNorm P τ f < ∞ := by
    have hmul := ENNReal.mul_lt_top hballFactor hN
    exact lt_of_le_of_lt
      (morreyBallNorm_le_two_rpow_mul_morreyNorm hP.le hPτ f) hmul
  have hscaleExp : 0 ≤ 5 * (1 - P / τ) := by
    have hPτ' : P / τ ≤ 1 := (div_le_one hτ0).mpr hPτ
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr hPτ')
  have hcoeff : parabolicAdamsMaximalConstant P τ < ∞ :=
    CKN.Core.Endgame.adams_maximal_constant_lt_top hP hPτ
  have hMpowerMeas : Measurable (fun z => M z ^ P) :=
    ENNReal.continuous_rpow_const.measurable.comp (by
      dsimp [M, parabolicMaximalMajorant]
      exact measurable_parabolicMaximalFunction _)
  have hballIntegral (n : ℕ) :
      (∫⁻ z in B n, M z ^ P) < ∞ := by
    have hr : 0 < (n : ℝ) + 1 := by positivity
    have hmax := setLIntegral_rpow_parabolicMaximalFunction_morreyBall_le
      hP.le hPτ hf.aemeasurable (z₀ := ((0 : Vec3), (0 : ℝ)))
        (r := (n : ℝ) + 1) hr
    have hscale : ENNReal.ofReal ((n : ℝ) + 1) ^ (5 * (1 - P / τ)) < ∞ :=
      lt_top_iff_ne_top.mpr
        (ENNReal.rpow_ne_top_of_nonneg hscaleExp ENNReal.ofReal_ne_top)
    have hpow : morreyBallNorm P τ f ^ P < ∞ :=
      lt_top_iff_ne_top.mpr
        (ENNReal.rpow_ne_top_of_nonneg hP0.le hballNorm.ne)
    have hright : parabolicAdamsMaximalConstant P τ *
        ENNReal.ofReal ((n : ℝ) + 1) ^ (5 * (1 - P / τ)) *
          morreyBallNorm P τ f ^ P < ∞ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top hcoeff hscale) hpow
    simpa [B, M, parabolicMaximalMajorant] using lt_of_le_of_lt hmax hright
  have hMfiniteOnBall (n : ℕ) :
      ∀ᵐ z ∂(volume.restrict (B n)), M z < ∞ := by
    have hpow := ae_lt_top hMpowerMeas (hballIntegral n).ne
    filter_upwards [hpow] with z hz
    by_contra hzM
    have htop : M z = ∞ := top_unique (le_of_not_gt hzM)
    rw [htop, ENNReal.top_rpow_of_pos hP0] at hz
    exact (lt_irrefl ∞) hz
  have hMfiniteOnBall' (n : ℕ) :
      ∀ᵐ z ∂volume,
        z ∈ B n → M z < ∞ :=
    (ae_restrict_iff' (Metric.isOpen_ball.measurableSet (α := ParabolicPoint))).mp
      (hMfiniteOnBall n)
  have hall : ∀ᵐ z ∂volume, ∀ n : ℕ,
      z ∈ B n → M z < ∞ :=
    ae_all_iff.mpr hMfiniteOnBall'
  filter_upwards [hall] with z hz
  obtain ⟨n, hn⟩ := exists_nat_gt (dist z ((0 : Vec3), (0 : ℝ)))
  exact hz n (by
    change dist z ((0 : Vec3), (0 : ℝ)) < (n : ℝ) + 1
    exact lt_trans hn (by exact_mod_cast Nat.lt_succ_self n))

/-- The finite-constant Adams display, including almost-everywhere finiteness
of the extended potential, using the cylinder seminorm `morreyNorm` and
the sum-gauge potential `parabolicRieszPotential`. -/
theorem parabolic_adams_finite (P τ β : ℝ) (hP : 1 < P) (hPτ : P ≤ τ)
    (hβ : 0 < β) (hβτ : β * τ < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ParabolicPoint → ℝ, Measurable f →
      morreyNorm P τ f < ⊤ →
        (∀ᵐ z ∂volume, parabolicRieszPotential β f z < ⊤) ∧
        morreyNorm (P / (1 - β * τ / 5)) (τ / (1 - β * τ / 5))
          (fun z => (parabolicRieszPotential β f z).toReal) ≤
            ENNReal.ofReal C * morreyNorm P τ f := by
  let C : ℝ := (parabolicAdamsPotentialConstant β P τ).toReal
  have hCtop : parabolicAdamsPotentialConstant β P τ < ∞ :=
    CKN.Core.Endgame.adams_potential_constant_lt_top hβ hP hPτ hβτ
  refine ⟨C, ENNReal.toReal_nonneg, ?_⟩
  intro f hf hN
  have hNlt : morreyNorm P τ f < ∞ := by simpa using hN
  have hτ1 : 1 < τ := lt_of_lt_of_le hP hPτ
  have hτ0 : 0 < τ := lt_trans zero_lt_one hτ1
  have hβ5 : β < 5 := by
    have hβle : β ≤ β * τ := by
      simpa using mul_le_mul_of_nonneg_left hτ1.le hβ.le
    exact lt_of_le_of_lt hβle hβτ
  have htheta : 0 < β * τ / 5 := by positivity
  have hlam : 0 < 1 - β * τ / 5 := by
    exact sub_pos.mpr ((div_lt_one (by norm_num)).2 hβτ)
  have hN1le := morreyNorm_lower_integrability (p' := (1 : ℝ))
    (p := P) (q := τ) (by norm_num) hP.le hPτ hf.aemeasurable
  have hVtop : volume (parabolicCylinder 0 0 1) ≠ ∞ :=
    Integration.volume_parabolicCylinder_lt_top.ne
  have hVexp : 0 ≤ 1 - 1 / P := by
    have hdiv : 1 / P ≤ 1 := (div_le_one (lt_trans zero_lt_one hP)).mpr hP.le
    exact sub_nonneg.mpr hdiv
  have hVpow : volume (parabolicCylinder 0 0 1) ^ (1 / (1 : ℝ) - 1 / P) < ∞ := by
    simpa using lt_top_iff_ne_top.mpr
      (ENNReal.rpow_ne_top_of_nonneg hVexp hVtop)
  have hN1 : morreyNorm 1 τ f < ∞ :=
    (hN1le.trans_lt (ENNReal.mul_lt_top hVpow hNlt))
  have hMfinite :=
    parabolicMaximalMajorant_ae_lt_top_of_morreyNorm_lt_top hP hPτ hf hNlt
  have hA : parabolicHedbergNearConstant β +
      parabolicTailKernelConstant β τ < ∞ :=
    ENNReal.add_lt_top.mpr ⟨
      CKN.Core.Endgame.hedberg_near_constant_lt_top hβ,
      CKN.Core.Endgame.tail_kernel_constant_lt_top hτ0 hβτ⟩
  have hIfinite : ∀ᵐ z ∂volume, parabolicRieszPotential β f z < ∞ := by
    have hbetaExp : 0 ≤ β * τ / 5 := le_of_lt htheta
    have hlam' : 0 ≤ 1 - β * τ / 5 := le_of_lt hlam
    filter_upwards [hMfinite] with z hMz
    have hhed := parabolicRieszPotential_hedberg'
      hβ hβ5 hτ1.le hβτ hf.aemeasurable
      (isParabolicMaximalMajorant_parabolicMaximalMajorant f) z
    have hMpow : parabolicMaximalMajorant f z ^
        (1 - β * τ / 5) < ∞ :=
      lt_top_iff_ne_top.mpr
        (ENNReal.rpow_ne_top_of_nonneg hlam' hMz.ne)
    have hNpow : morreyNorm 1 τ f ^ (β * τ / 5) < ∞ :=
      lt_top_iff_ne_top.mpr
        (ENNReal.rpow_ne_top_of_nonneg hbetaExp hN1.ne)
    have hRhs : (parabolicHedbergNearConstant β +
        parabolicTailKernelConstant β τ) *
          parabolicMaximalMajorant f z ^ (1 - β * τ / 5) *
            morreyNorm 1 τ f ^ (β * τ / 5) < ∞ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top hA hMpow) hNpow
    exact lt_of_le_of_lt hhed hRhs
  have hAdams := parabolicRieszPotential_adams hP hPτ hβ hβτ hf
  have hAdams' :
      morreyNorm (P / (1 - β * τ / 5)) (τ / (1 - β * τ / 5))
        (fun z => (parabolicRieszPotential β f z).toReal) ≤
          ENNReal.ofReal C * morreyNorm P τ f := by
    simpa only [C, ENNReal.ofReal_toReal hCtop.ne] using hAdams
  exact ⟨hIfinite, hAdams'⟩

end CKN.Foundation.Parabolic.Morrey

end
