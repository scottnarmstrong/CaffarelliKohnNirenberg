-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.MaximalMorreyCore

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

private theorem setLIntegral_rpow_parabolicMaximalFunction_morreyBall_le_of_measurable_finite
    {P τ : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) {f : ParabolicPoint → ℝ}
    (hf : Measurable f) (hNtop : morreyBallNorm P τ f ≠ ∞)
    {z₀ : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    ∫⁻ w in Metric.ball z₀ r,
        parabolicMaximalFunction (fun y => ENNReal.ofReal |f y|) w ^ P ≤
      parabolicAdamsMaximalConstant P τ *
        ENNReal.ofReal r ^ (5 * (1 - P / τ)) * morreyBallNorm P τ f ^ P := by
  let F : ParabolicPoint → ℝ≥0∞ := fun w ↦ ENNReal.ofReal |f w|
  let U : Set ParabolicPoint := Metric.ball z₀ (4 * r)
  let F₁ : ParabolicPoint → ℝ≥0∞ := U.indicator F
  let F₂ : ParabolicPoint → ℝ≥0∞ := Uᶜ.indicator F
  let N : ℝ≥0∞ := morreyBallNorm P τ f
  let V : ℝ≥0∞ := volume (parabolicCylinder 0 0 1)
  let Vb : ℝ≥0∞ := volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
    ((0 : Vec3), (0 : ℝ)) 1)
  let e : ℝ := 5 * (1 - P / τ)
  let Kb : ℝ≥0∞ := Vb ^ (-(1 / P))
  let A : ℝ≥0∞ := ENNReal.ofReal r
  let Kold : ℝ≥0∞ := (ENNReal.ofReal (2 : ℝ) ^ (5 * (1 - 1 / τ)) / V) *
    V ^ (1 - 1 / P)
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hτ0 : 0 < τ := lt_of_lt_of_le hP0 hPτ
  have he : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr ((div_le_one hτ0).2 hPτ))
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact (ENNReal.ofReal_pos.mpr hr).ne'
  have hAtop : A ≠ ∞ := by dsimp [A]; exact ENNReal.ofReal_ne_top
  have hVb0 : Vb ≠ 0 := by
    dsimp [Vb]
    exact (volume_parabolicBall_pos
      (z := ((0 : Vec3), (0 : ℝ))) (by norm_num)).ne'
  have hVbtop : Vb ≠ ∞ := by
    dsimp [Vb]
    exact (volume_parabolicBall_lt_top
      (z := ((0 : Vec3), (0 : ℝ))) (by norm_num)).ne
  have hKtop : Kb ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hVb0 hVbtop
  have hAnegTop : A ^ (-(5 / τ)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hA0 hAtop
  have hNpowtop : N ^ P ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hP0.le hNtop
  have hF : Measurable F := by
    exact hf.norm.ennreal_ofReal
  have hUmeas : MeasurableSet U := Metric.isOpen_ball.measurableSet
  have hEmeas : MeasurableSet (Metric.ball z₀ r) := Metric.isOpen_ball.measurableSet
  have hEsub : Metric.ball z₀ r ⊆ U := by
    exact Metric.ball_subset_ball (by linarith only [hr])
  have hUbound : ∫⁻ w in U, F w ^ P ≤
      ENNReal.ofReal (4 * r) ^ e * N ^ P := by
    simpa [U, F, N, e, ballPowerIntegral] using
      (ballPowerIntegral_le_morreyBallNorm_pow (p := P) (q := τ)
        (f := f) (z := z₀) (r := 4 * r) hP0 (by positivity))
  have hscaleTop : ENNReal.ofReal (4 * r) ^ e ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg he ENNReal.ofReal_ne_top
  have hfinite : ENNReal.ofReal (4 * r) ^ e * N ^ P < ∞ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hscaleTop)
      (lt_top_iff_ne_top.mpr hNpowtop)
  have hUfp : ∫⁻ w in U, F w ^ P < ∞ := lt_of_le_of_lt hUbound hfinite
  have hstrong := setLIntegral_rpow_parabolicMaximalFunction_indicator_le
    U hUmeas Metric.isOpen_ball Metric.isBounded_ball hF hP hUfp
  have hF₁ : Measurable F₁ := hF.indicator hUmeas
  have hF₂ : Measurable F₂ := hF.indicator hUmeas.compl
  have hsplit : F₁ + F₂ = F := by
    funext w
    by_cases hw : w ∈ U
    · simp [F₁, F₂, hw]
    · simp [F₁, F₂, hw]
  have hmax : ∀ w, parabolicMaximalFunction F w ≤
      parabolicMaximalFunction F₁ w + parabolicMaximalFunction F₂ w := by
    intro w
    rw [← hsplit]
    exact parabolicMaximalFunction_add_le' hF₁ hF₂ w
  have hfar : ∀ w ∈ Metric.ball z₀ r,
      parabolicMaximalFunction F₂ w ≤ Kb *
        ENNReal.ofReal r ^ (-(5 / τ)) * N := by
    intro w hw
    simpa [F₂, U, Kb, Vb, N, mul_assoc, mul_left_comm, mul_comm] using
      (parabolicMaximalFunction_compl_ball_le_morreyBallNorm
        (p := P) (q := τ) (c := z₀) (z := w) (r := r)
        hP hPτ hf.aemeasurable hr hw)
  have hpow : ∀ w ∈ Metric.ball z₀ r,
      parabolicMaximalFunction F w ^ P ≤
        (2 : ℝ≥0∞) ^ (P - 1) *
          (parabolicMaximalFunction F₁ w ^ P + parabolicMaximalFunction F₂ w ^ P) := by
    intro w hw
    exact (ENNReal.rpow_le_rpow (hmax w) (by positivity)).trans
      (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hP.le)
  have hpoint :
      (∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction F w ^ P) ≤
        (2 : ℝ≥0∞) ^ (P - 1) *
          ((∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction F₁ w ^ P) +
            ∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction F₂ w ^ P) := by
    calc
      _ ≤ ∫⁻ w in Metric.ball z₀ r,
          (2 : ℝ≥0∞) ^ (P - 1) *
            (parabolicMaximalFunction F₁ w ^ P +
              parabolicMaximalFunction F₂ w ^ P) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hEmeas] with w hw
        exact hpow w hw
      _ = _ := by
        have hMF₁ : Measurable (fun w ↦ parabolicMaximalFunction F₁ w ^ P) :=
          ENNReal.continuous_rpow_const.measurable.comp
            (measurable_parabolicMaximalFunction F₁)
        have htwoTop : (2 : ℝ≥0∞) ^ (P - 1) ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hP.le)
            ENNReal.ofNat_ne_top
        rw [lintegral_const_mul' _ _ htwoTop, lintegral_add_left
          (μ := volume.restrict (Metric.ball z₀ r)) hMF₁]
  have hlocal :
      (∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction F₁ w ^ P) ≤
        parabolicMaximalStrongConstant P *
          (ENNReal.ofReal (4 * r) ^ e * N ^ P) := by
    calc
      _ ≤ ∫⁻ w in U, parabolicMaximalFunction F₁ w ^ P :=
        lintegral_mono_set hEsub
      _ ≤ parabolicMaximalStrongConstant P *
          ∫⁻ w in U, F w ^ P := hstrong
      _ ≤ parabolicMaximalStrongConstant P *
          (ENNReal.ofReal (4 * r) ^ e * N ^ P) := by
        exact mul_le_mul_right hUbound _
      _ = parabolicMaximalStrongConstant P *
          (ENNReal.ofReal (4 * r) ^ e * N ^ P) := by rfl
  have hfarint :
      (∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction F₂ w ^ P) ≤
        A ^ e * N ^ P := by
    let B : ℝ≥0∞ := Kb * A ^ (-(5 / τ)) * N
    have hB : ∀ᵐ w ∂volume.restrict (Metric.ball z₀ r),
        parabolicMaximalFunction F₂ w ^ P ≤ B ^ P := by
      filter_upwards [ae_restrict_mem hEmeas] with w hw
      exact ENNReal.rpow_le_rpow (hfar w hw) (by positivity)
    calc
      _ ≤ ∫⁻ w in Metric.ball z₀ r, B ^ P := lintegral_mono_ae hB
      _ = B ^ P * volume (Metric.ball z₀ r) := by rw [setLIntegral_const]
      _ = A ^ e * N ^ P := by
        have hvol : volume (Metric.ball z₀ r) = Vb * A ^ (5 : ℝ) := by
          simpa [A, Vb] using metricBall_volume_scale (z := z₀) hr
        have hKpow : Kb ^ P = Vb⁻¹ := by
          dsimp [Kb]
          rw [← ENNReal.rpow_mul]
          have hexp : (-(1 / P)) * P = -1 := by field_simp [hP0.ne']
          rw [hexp, ENNReal.rpow_neg_one]
        have hApow : (A ^ (-(5 / τ))) ^ P * A ^ (5 : ℝ) = A ^ e := by
          rw [← ENNReal.rpow_mul]
          have hexp : (-(5 / τ)) * P + 5 = e := by
            dsimp [e]
            field_simp [hτ0.ne']
            ring
          rw [← ENNReal.rpow_add _ _ hA0 hAtop, hexp]
        have hBpow : B ^ P = Kb ^ P * (A ^ (-(5 / τ))) ^ P * N ^ P := by
          dsimp [B]
          rw [ENNReal.mul_rpow_of_ne_top
            (ENNReal.mul_ne_top hKtop hAnegTop) hNtop]
          rw [ENNReal.mul_rpow_of_ne_top hKtop hAnegTop]
        rw [hBpow, hvol]
        calc
          Kb ^ P * (A ^ (-(5 / τ))) ^ P * N ^ P *
              (Vb * A ^ (5 : ℝ)) =
              (Kb ^ P * Vb) * ((A ^ (-(5 / τ))) ^ P * A ^ (5 : ℝ)) * N ^ P := by
                ac_rfl
          _ = A ^ e * N ^ P := by
            rw [hKpow, ENNReal.inv_mul_cancel hVb0 hVbtop, one_mul, hApow]
  have h4scale : ENNReal.ofReal (4 * r) ^ e =
      ENNReal.ofReal (4 : ℝ) ^ e * A ^ e := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ he]
  have h4le8 : ENNReal.ofReal (4 : ℝ) ^ e ≤ ENNReal.ofReal (8 : ℝ) ^ e :=
    ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (by norm_num)) he
  have hlocal' :
      (∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction F₁ w ^ P) ≤
        parabolicMaximalStrongConstant P * ENNReal.ofReal (8 : ℝ) ^ e *
          A ^ e * N ^ P := by
    calc
      _ ≤ parabolicMaximalStrongConstant P *
          (ENNReal.ofReal (4 * r) ^ e * N ^ P) := hlocal
      _ = parabolicMaximalStrongConstant P *
          (ENNReal.ofReal (4 : ℝ) ^ e * A ^ e * N ^ P) := by rw [h4scale]
      _ ≤ parabolicMaximalStrongConstant P * ENNReal.ofReal (8 : ℝ) ^ e *
          A ^ e * N ^ P := by
        have hcoeff := mul_le_mul_left h4le8 (parabolicMaximalStrongConstant P)
        have hmul := mul_le_mul_right hcoeff (A ^ e * N ^ P)
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hfarCoeff := one_le_adamsFarCoefficient hP hPτ
  have hfar' :
      (∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction F₂ w ^ P) ≤
        V * Kold ^ P * A ^ e * N ^ P := by
    calc
      _ ≤ A ^ e * N ^ P := hfarint
      _ ≤ V * Kold ^ P * A ^ e * N ^ P := by
        have hmul := mul_le_mul_right hfarCoeff (A ^ e * N ^ P)
        simpa [V, Kold, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (P - 1) *
        ((∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction F₁ w ^ P) +
          ∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction F₂ w ^ P) := hpoint
    _ ≤ (2 : ℝ≥0∞) ^ (P - 1) *
        (parabolicMaximalStrongConstant P * ENNReal.ofReal (8 : ℝ) ^ e *
            A ^ e * N ^ P + V * Kold ^ P * A ^ e * N ^ P) := by
      gcongr
    _ = parabolicAdamsMaximalConstant P τ * A ^ e * N ^ P := by
      dsimp [parabolicAdamsMaximalConstant, Kold, V, e]
      rw [mul_add]
      ring

private theorem setLIntegral_rpow_parabolicMaximalFunction_morreyBall_le_of_aemeasurable_finite
    {P τ : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hNtop : morreyBallNorm P τ f ≠ ∞)
    {z₀ : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    ∫⁻ w in Metric.ball z₀ r,
        parabolicMaximalFunction (fun y => ENNReal.ofReal |f y|) w ^ P ≤
      parabolicAdamsMaximalConstant P τ *
        ENNReal.ofReal r ^ (5 * (1 - P / τ)) * morreyBallNorm P τ f ^ P := by
  let g : ParabolicPoint → ℝ := hf.mk f
  let F : ParabolicPoint → ℝ≥0∞ := fun y => ENNReal.ofReal |f y|
  let G : ParabolicPoint → ℝ≥0∞ := fun y => ENNReal.ofReal |g y|
  have hg : Measurable g := hf.measurable_mk
  have hfg : f =ᵐ[volume] g := hf.ae_eq_mk
  have hnorm := morreyBallNorm_congr_ae (p := P) (q := τ) hfg
  have hNtopg : morreyBallNorm P τ g ≠ ∞ := by
    rw [← hnorm]
    exact hNtop
  have hFG : F =ᵐ[volume] G := by
    filter_upwards [hfg] with y hy
    simp [F, G, hy]
  have hMF := parabolicMaximalFunction_congr_ae hFG
  have hMFeq : parabolicMaximalFunction F = parabolicMaximalFunction G :=
    funext hMF
  calc
    _ = ∫⁻ w in Metric.ball z₀ r,
        parabolicMaximalFunction G w ^ P := by
      change ∫⁻ w in Metric.ball z₀ r,
          parabolicMaximalFunction F w ^ P =
        ∫⁻ w in Metric.ball z₀ r, parabolicMaximalFunction G w ^ P
      rw [hMFeq]
    _ ≤ parabolicAdamsMaximalConstant P τ *
        ENNReal.ofReal r ^ (5 * (1 - P / τ)) * morreyBallNorm P τ g ^ P :=
      setLIntegral_rpow_parabolicMaximalFunction_morreyBall_le_of_measurable_finite
        hP hPτ hg hNtopg hr
    _ = parabolicAdamsMaximalConstant P τ *
        ENNReal.ofReal r ^ (5 * (1 - P / τ)) * morreyBallNorm P τ f ^ P := by
      rw [hnorm]

private theorem parabolicMaximalFunction_eq_zero_of_morreyBallNorm_one_eq_zero
    {τ : ℝ} {f : ParabolicPoint → ℝ}
    (hN : morreyBallNorm 1 τ f = 0) :
    parabolicMaximalFunction (fun y => ENNReal.ofReal |f y|) = fun _ => 0 := by
  let F : ParabolicPoint → ℝ≥0∞ := fun y => ENNReal.ofReal |f y|
  have havg : ∀ c : ParabolicPoint, ∀ s : ℝ,
      (⨍⁻ y in @Metric.ball ParabolicPoint parabolicPseudoMetricSpace c s,
        F y ∂volume) = 0 := by
    intro c s
    by_cases hs : 0 < s
    · rw [setLAverage_eq]
      have hI := ballPowerIntegral_le_morreyBallNorm_pow
        (p := 1) (q := τ) (f := f) (z := c) (r := s) (by norm_num) hs
      rw [hN, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1), mul_zero]
        at hI
      have hzero : ballPowerIntegral 1 f c s = 0 := le_antisymm hI bot_le
      have hnum : (∫⁻ y in @Metric.ball ParabolicPoint parabolicPseudoMetricSpace c s,
          F y) = 0 := by
        simpa [F, ballPowerIntegral] using hzero
      rw [hnum]
      simp
    · have hball : Metric.ball c s = ∅ :=
        Metric.ball_eq_empty.mpr (le_of_not_gt hs)
      simp [hball]
  funext z
  apply le_antisymm
  · unfold parabolicMaximalFunction
    apply iSup_le
    intro c
    apply iSup_le
    intro s
    change ((@Metric.ball ParabolicPoint parabolicPseudoMetricSpace c s).indicator
      (fun _ : ParabolicPoint =>
        ⨍⁻ y in @Metric.ball ParabolicPoint parabolicPseudoMetricSpace c s,
          F y ∂volume) z) ≤ 0
    by_cases hz : z ∈ @Metric.ball ParabolicPoint parabolicPseudoMetricSpace c s
    · simp [Set.indicator_of_mem hz, havg]
    · simp [Set.indicator, hz]
  · exact bot_le

private theorem parabolicAdamsMaximalConstant_pos_of_gt_one
    {P τ : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) :
    0 < parabolicAdamsMaximalConstant P τ := by
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hτ0 : 0 < τ := lt_of_lt_of_le hP0 hPτ
  have he : 0 ≤ 5 * (1 - P / τ) := by
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr ((div_le_one hτ0).2 hPτ))
  have hstrong : 0 < parabolicMaximalStrongConstant P := by
    unfold parabolicMaximalStrongConstant
    apply ENNReal.div_pos
    · positivity
    · exact ENNReal.ofReal_ne_top
  have hlocal : 0 < ENNReal.ofReal (8 : ℝ) ^ (5 * (1 - P / τ)) :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by norm_num)) ENNReal.ofReal_ne_top
  have hsum : 0 < parabolicMaximalStrongConstant P *
        ENNReal.ofReal (8 : ℝ) ^ (5 * (1 - P / τ)) +
      volume (parabolicCylinder 0 0 1) *
        (((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / τ)) /
          volume (parabolicCylinder 0 0 1)) *
            volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)) ^ P := by
    exact lt_of_lt_of_le (ENNReal.mul_pos hstrong.ne' hlocal.ne')
      (le_add_right le_rfl)
  unfold parabolicAdamsMaximalConstant
  exact ENNReal.mul_pos
    (ENNReal.rpow_pos (by norm_num : (0 : ℝ≥0∞) < 2) ENNReal.ofNat_ne_top).ne'
    hsum.ne'

theorem setLIntegral_rpow_parabolicMaximalFunction_morreyBall_le
    {P τ : ℝ} (hP : 1 ≤ P) (hPτ : P ≤ τ) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) {z₀ : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    ∫⁻ w in Metric.ball z₀ r,
        parabolicMaximalFunction (fun y => ENNReal.ofReal |f y|) w ^ P ≤
      parabolicAdamsMaximalConstant P τ *
        ENNReal.ofReal r ^ (5 * (1 - P / τ)) * morreyBallNorm P τ f ^ P := by
  let N : ℝ≥0∞ := morreyBallNorm P τ f
  by_cases hPone : P = 1
  · subst P
    by_cases hNzero : N = 0
    · rw [parabolicMaximalFunction_eq_zero_of_morreyBallNorm_one_eq_zero hNzero]
      simp [N, hNzero]
    · have hstrong : parabolicMaximalStrongConstant 1 = ∞ := by
        unfold parabolicMaximalStrongConstant
        norm_num [ENNReal.div_eq_top]
      have hCtop : parabolicAdamsMaximalConstant 1 τ = ∞ := by
        unfold parabolicAdamsMaximalConstant
        rw [hstrong]
        have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one hPτ
        have he : 0 ≤ 5 * (1 - 1 / τ) := by
          exact mul_nonneg (by norm_num)
            (sub_nonneg.mpr ((div_le_one hτ0).2 hPτ))
        simp
      have hscale : 0 < ENNReal.ofReal r ^ (5 * (1 - 1 / τ)) :=
        ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top
      have hright : parabolicAdamsMaximalConstant 1 τ *
          ENNReal.ofReal r ^ (5 * (1 - 1 / τ)) * N = ∞ := by
        rw [hCtop]
        rw [ENNReal.top_mul hscale.ne', ENNReal.top_mul hNzero]
      have hright' : parabolicAdamsMaximalConstant 1 τ *
          ENNReal.ofReal r ^ (5 * (1 - 1 / τ)) * N ^ (1 : ℝ) = ∞ := by
        simpa only [ENNReal.rpow_one] using hright
      rw [show morreyBallNorm 1 τ f = N by rfl, hright']
      exact le_top
  · have hPgt : 1 < P := lt_of_le_of_ne hP (Ne.symm hPone)
    by_cases hNtop : N = ∞
    · have hCpos := parabolicAdamsMaximalConstant_pos_of_gt_one hPgt hPτ
      have hscale : 0 < ENNReal.ofReal r ^ (5 * (1 - P / τ)) :=
        ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top
      have hNpow : N ^ P = ∞ := by
        rw [hNtop]
        exact ENNReal.top_rpow_of_pos (lt_trans zero_lt_one hPgt)
      have hcoef : parabolicAdamsMaximalConstant P τ *
          ENNReal.ofReal r ^ (5 * (1 - P / τ)) ≠ 0 :=
        (ENNReal.mul_pos hCpos.ne' hscale.ne').ne'
      have hright : parabolicAdamsMaximalConstant P τ *
          ENNReal.ofReal r ^ (5 * (1 - P / τ)) * N ^ P = ∞ := by
        rw [hNpow]
        simp [hcoef]
      rw [hright]
      exact le_top
    · exact setLIntegral_rpow_parabolicMaximalFunction_morreyBall_le_of_aemeasurable_finite
        hPgt hPτ hf hNtop hr

end CKN.Foundation.Parabolic.Morrey
