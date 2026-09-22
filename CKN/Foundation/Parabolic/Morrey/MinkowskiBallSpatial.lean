-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.BallDisplays
import CKN.Foundation.Parabolic.Morrey.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Spatial convolution on parabolic metric balls

This module records the real-kernel Minkowski estimate for the metric-ball
Morrey seminorm.
-/

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

private theorem lintegral_minkowski_ball
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (hν : ν Set.univ ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    {F : α × β → ℝ≥0∞} (hF : AEMeasurable F (μ.prod ν)) :
    (∫⁻ y, (∫⁻ x, F (x, y) ∂μ) ^ p ∂ν) ^ (1 / p) ≤
      ∫⁻ x, (∫⁻ y, F (x, y) ^ p ∂ν) ^ (1 / p) ∂μ := by
  let h : β → ℝ≥0∞ := fun y => ∫⁻ x, F (x, y) ∂μ
  have hh : AEMeasurable h ν := hF.lintegral_prod_left'
  by_cases hpeq : p = 1
  · subst p
    simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), ENNReal.rpow_one]
    have hswap := MeasureTheory.lintegral_lintegral_swap
      (f := fun x y => F (x, y)) hF
    exact hswap.symm.le
  have hpgt : 1 < p := lt_of_le_of_ne hp (Ne.symm hpeq)
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact hpgt
    · dsimp [q]
      field_simp [ne_of_gt hpgt]
      ring
  let m : ℕ → β → ℝ≥0∞ := fun n y => min (h y) n
  have hm : ∀ n, AEMeasurable (m n) ν := fun n => hh.min measurable_const.aemeasurable
  have hmp : ∀ n, AEMeasurable (fun y => m n y ^ p) ν :=
    fun n => (hm n).pow_const p
  have hmp_mono : Monotone (fun n => fun y => m n y ^ p) := by
    intro n₁ n₂ hn y
    exact ENNReal.rpow_le_rpow (min_le_min_left _ (by exact_mod_cast hn))
      (le_trans zero_le_one hp)
  have hsup_m : ∀ y, (⨆ n, m n y) = h y := by
    intro y
    apply le_antisymm
    · exact iSup_le fun n => min_le_left _ _
    · by_cases hy : h y = ∞
      · rw [hy, ← ENNReal.iSup_natCast]
        apply iSup_mono
        intro n
        simp [m, hy]
      · obtain ⟨n, hn⟩ := exists_nat_gt (h y).toReal
        have hn' : h y < (n : ℝ≥0∞) :=
          (ENNReal.toReal_lt_toReal hy (ENNReal.natCast_ne_top n)).mp hn
        exact le_iSup_of_le n (by simp [m, min_eq_left hn'.le])
  have hsup_mp : (⨆ n, fun y => m n y ^ p) = fun y => h y ^ p := by
    funext y
    rw [iSup_apply]
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.rpow_le_rpow (min_le_left _ _)
        (le_trans zero_le_one hp)
    · by_cases hy : h y = ∞
      · rw [hy, ENNReal.top_rpow_of_pos (zero_lt_one.trans_le hp),
          ← ENNReal.iSup_natCast]
        apply iSup_mono
        intro n
        by_cases hn : n = 0
        · simp [hn]
        · have hbase : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
          simpa [m, hy] using (ENNReal.rpow_le_rpow_of_exponent_le hbase hp)
      · obtain ⟨n, hn⟩ := exists_nat_gt (h y).toReal
        have hn' : h y < (n : ℝ≥0∞) :=
          (ENNReal.toReal_lt_toReal hy (ENNReal.natCast_ne_top n)).mp hn
        exact le_iSup_of_le n (by simp [m, min_eq_left hn'.le])
  have hbound : ∀ n, (∫⁻ y, m n y ^ p ∂ν) ≠ ∞ := by
    intro n
    apply ne_of_lt
    calc
      (∫⁻ y, m n y ^ p ∂ν) ≤ ∫⁻ _y, (n : ℝ≥0∞) ^ p ∂ν := by
        apply lintegral_mono
        intro y
        exact ENNReal.rpow_le_rpow (min_le_right _ _) (le_trans zero_le_one hp)
      _ = (n : ℝ≥0∞) ^ p * ν Set.univ := lintegral_const _
      _ < ∞ := ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (le_trans zero_le_one hp) (ENNReal.natCast_ne_top n))
        (lt_top_iff_ne_top.mpr hν)
  have hfiber_x : ∀ᵐ x ∂μ, AEMeasurable (fun y => F (x, y)) ν := by
    obtain ⟨G, hG, hFG⟩ := hF
    have hFG' := Measure.ae_ae_eq_curry_of_prod hFG
    filter_upwards [hFG'] with x hx
    have hgx : AEMeasurable (fun y => G (x, y)) ν := by
      simpa [Function.comp_def] using (hG.comp measurable_prodMk_left).aemeasurable
    exact hgx.congr hx.symm
  have hfiber_y : ∀ᵐ y ∂ν, AEMeasurable (fun x => F (x, y)) μ := by
    obtain ⟨G, hG, hFG⟩ := hF
    have hFGswap : (fun z => F z.swap) =ᵐ[ν.prod μ] (fun z => G z.swap) :=
      hFG.comp_tendsto Measure.measurePreserving_swap.quasiMeasurePreserving.tendsto_ae
    have hFG' := Measure.ae_ae_eq_curry_of_prod hFGswap
    filter_upwards [hFG'] with y hy
    have hgy : AEMeasurable (fun x => G (x, y)) μ := by
      simpa [Function.comp_def] using (hG.comp measurable_prodMk_right).aemeasurable
    exact hgy.congr hy.symm
  let L : α → ℝ≥0∞ := fun x => (∫⁻ y, F (x, y) ^ p ∂ν) ^ (1 / p)
  have hL : AEMeasurable L μ := (hF.pow_const p).lintegral_prod_right'.pow_const (1 / p)
  have hlocal : ∀ n, (∫⁻ y, m n y ^ p ∂ν) ^ (1 / p) ≤ ∫⁻ x, L x ∂μ := by
    intro n
    let C : ℝ≥0∞ := (∫⁻ y, m n y ^ p ∂ν) ^ (1 / q)
    have hpoint : ∀ y, m n y ^ p ≤ h y * m n y ^ (p - 1) := by
      intro y
      by_cases hm0 : m n y = 0
      · simp [hm0, ENNReal.zero_rpow_of_pos (zero_lt_one.trans_le hp)]
      have hm_top : m n y ≠ ∞ :=
        ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
      calc
        m n y ^ p = m n y ^ ((p - 1) + 1) := by congr 1; ring
        _ = m n y ^ (p - 1) * m n y ^ (1 : ℝ) := ENNReal.rpow_add _ _ hm0 hm_top
        _ = m n y ^ (p - 1) * m n y := by rw [ENNReal.rpow_one]
        _ ≤ m n y ^ (p - 1) * h y := mul_le_mul_right (min_le_left _ _) _
        _ = h y * m n y ^ (p - 1) := by ac_rfl
    have hprod : AEMeasurable
        (fun z : α × β => F z * m n z.2 ^ (p - 1)) (μ.prod ν) :=
      hF.mul ((hm n).pow_const (p - 1)).comp_snd
    have hswap := MeasureTheory.lintegral_lintegral_swap
      (f := fun x y => F (x, y) * m n y ^ (p - 1)) hprod
    have hlow : (∫⁻ y, m n y ^ p ∂ν) ≤
        ∫⁻ y, ∫⁻ x, F (x, y) * m n y ^ (p - 1) ∂μ ∂ν := by
      calc
        (∫⁻ y, m n y ^ p ∂ν) ≤ ∫⁻ y, h y * m n y ^ (p - 1) ∂ν :=
          lintegral_mono (fun y => hpoint y)
        _ = ∫⁻ y, ∫⁻ x, F (x, y) * m n y ^ (p - 1) ∂μ ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hfiber_y] with y hy
          simp only [h]
          exact (lintegral_mul_const'' _ hy).symm
    have hholder : ∀ᵐ x ∂μ,
        (∫⁻ y, F (x, y) * m n y ^ (p - 1) ∂ν) ≤ L x * C := by
      filter_upwards [hfiber_x] with x hx
      exact (ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
        hpq hx (hm n)).trans_eq (by rfl)
    have houter : (∫⁻ x, (∫⁻ y, F (x, y) * m n y ^ (p - 1) ∂ν) ∂μ) ≤
        ∫⁻ x, L x * C ∂μ := lintegral_mono_ae hholder
    have hfactor : (∫⁻ x, L x * C ∂μ) = (∫⁻ x, L x ∂μ) * C :=
      lintegral_mul_const'' C hL
    have hmain : (∫⁻ y, m n y ^ p ∂ν) ≤ (∫⁻ x, L x ∂μ) * C :=
      hlow.trans (hswap.symm.le.trans (houter.trans_eq hfactor))
    by_cases hA0 : (∫⁻ y, m n y ^ p ∂ν) = 0
    · calc
        (∫⁻ y, m n y ^ p ∂ν) ^ (1 / p) = 0 := by
          rw [hA0, ENNReal.zero_rpow_of_pos (one_div_pos.mpr (zero_lt_one.trans_le hp))]
        _ ≤ ∫⁻ x, L x ∂μ := zero_le
    have hC0 : 0 < C := by
      dsimp [C]
      exact ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hA0) (hbound n)
    have hAeq : (∫⁻ y, m n y ^ p ∂ν) =
        (∫⁻ y, m n y ^ p ∂ν) ^ (1 / p) * C := by
      dsimp [C]
      rw [← ENNReal.rpow_add (1 / p) (1 / q)
        (ne_of_gt (bot_lt_iff_ne_bot.mpr hA0)) (hbound n)]
      have hexp : 1 / p + 1 / q = 1 := by
        dsimp [q]
        field_simp [ne_of_gt hpgt]
        ring
      rw [hexp, ENNReal.rpow_one]
    have hCtop : C ≠ ∞ := by
      dsimp [C]
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (hbound n)
    rw [hAeq] at hmain
    by_contra hnot
    have hlt : (∫⁻ x, L x ∂μ) < (∫⁻ y, m n y ^ p ∂ν) ^ (1 / p) := lt_of_not_ge hnot
    exact (not_lt_of_ge hmain) (by
      simpa [C] using ENNReal.mul_lt_mul_left hC0.ne' hCtop hlt)
  have hAeq : (∫⁻ y, h y ^ p ∂ν) = ⨆ n, ∫⁻ y, m n y ^ p ∂ν := by
    rw [← hsup_mp]
    have hfun : (⨆ n, fun y => m n y ^ p) = fun y => ⨆ n, m n y ^ p := by
      funext y
      exact iSup_apply
    rw [hfun]
    exact lintegral_iSup' hmp (Filter.Eventually.of_forall (fun y n₁ n₂ hn => hmp_mono hn y))
  have hsup_le : (⨆ n, ∫⁻ y, m n y ^ p ∂ν) ≤ (∫⁻ x, L x ∂μ) ^ p := by
    refine iSup_le fun n => ?_
    calc
      (∫⁻ y, m n y ^ p ∂ν) =
          ((∫⁻ y, m n y ^ p ∂ν) ^ (1 / p)) ^ p := by
            simpa only [one_div] using (ENNReal.rpow_inv_rpow
              (y := p) (ne_of_gt (zero_lt_one.trans_le hp)) _).symm
      _ ≤ (∫⁻ x, L x ∂μ) ^ p := ENNReal.rpow_le_rpow (hlocal n) (le_trans zero_le_one hp)
  calc
    (∫⁻ y, h y ^ p ∂ν) ^ (1 / p) ≤ ((∫⁻ x, L x ∂μ) ^ p) ^ (1 / p) :=
      ENNReal.rpow_le_rpow (by rw [hAeq]; exact hsup_le) (by positivity)
    _ = ∫⁻ x, L x ∂μ := by
      rw [← ENNReal.rpow_mul]
      simp [ne_of_gt (zero_lt_one.trans_le hp)]

end CKN.Foundation.Parabolic.Morrey

namespace CKN.Foundation.Parabolic.Morrey

private lemma measurePreserving_spatial_ball_shear :
    MeasurePreserving
      (fun yz : Vec3 × ParabolicPoint =>
        (yz.1, parabolicTranslate (-yz.1) 0 yz.2))
      ((volume : Measure Vec3).prod volume) ((volume : Measure Vec3).prod volume) := by
  let _ : SFinite (volume : Measure Vec3) := by infer_instance
  let _ : SFinite (volume : Measure ℝ) := by infer_instance
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  rw [Integration.volume_parabolicPoint_eq_prod]
  change MeasurePreserving
    (fun yz : Vec3 × (Vec3 × ℝ) => (yz.1, (-yz.1 + yz.2.1, 0 + yz.2.2)))
    ((volume : Measure Vec3).prod (volume.prod volume))
    ((volume : Measure Vec3).prod (volume.prod volume))
  let e : (Vec3 × Vec3) × ℝ ≃ᵐ Vec3 × (Vec3 × ℝ) := MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e ((volume.prod volume).prod volume)
      (volume.prod (volume.prod volume)) :=
    measurePreserving_prodAssoc volume volume volume
  have hs : MeasurePreserving (fun yz : Vec3 × Vec3 => (yz.1, -yz.1 + yz.2))
      (volume.prod volume) (volume.prod volume) :=
    measurePreserving_prod_neg_add (μ := (volume : Measure Vec3)) (ν := volume)
  have hsi : MeasurePreserving (fun p : (Vec3 × Vec3) × ℝ =>
      ((p.1.1, -p.1.1 + p.1.2), p.2))
      ((volume.prod volume).prod volume) ((volume.prod volume).prod volume) :=
    hs.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hcomp := he.comp (hsi.comp he.symm)
  convert hcomp using 1
  funext z
  rcases z with ⟨y, xt⟩
  rcases xt with ⟨x, t⟩
  simp [e, MeasurableEquiv.prodAssoc]

private lemma aemeasurable_ball_spatial_integrand
    {k : Vec3 → ℝ} {g : ParabolicPoint → ℝ}
    (hk : Integrable k volume) (hg : Measurable g) :
    AEMeasurable
      (fun yz : Vec3 × ParabolicPoint =>
        ENNReal.ofReal |k yz.1| *
          ENNReal.ofReal |g (parabolicTranslate (-yz.1) 0 yz.2)|)
      ((volume : Measure Vec3).prod volume) := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  have hk' : AEMeasurable (fun yz : Vec3 × ParabolicPoint => k yz.1)
      ((volume : Measure Vec3).prod volume) :=
    hk.aemeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
  have htrans : QuasiMeasurePreserving
      (fun yz : Vec3 × ParabolicPoint => parabolicTranslate (-yz.1) 0 yz.2)
      ((volume : Measure Vec3).prod volume) volume := by
    have h := quasiMeasurePreserving_snd.comp
      measurePreserving_spatial_ball_shear.quasiMeasurePreserving
    convert h using 1
    funext yz
    rfl
  have hgtrans : AEMeasurable
      (fun yz : Vec3 × ParabolicPoint =>
        g (parabolicTranslate (-yz.1) 0 yz.2))
      ((volume : Measure Vec3).prod volume) :=
    hg.aemeasurable.comp_quasiMeasurePreserving htrans
  have hK : AEMeasurable (fun y : Vec3 => ENNReal.ofReal |k y|) volume := by
    exact (ENNReal.continuous_ofReal.comp continuous_abs).measurable.comp_aemeasurable
      hk.aemeasurable
  have hG : AEMeasurable
      (fun yz : Vec3 × ParabolicPoint =>
        ENNReal.ofReal |g (parabolicTranslate (-yz.1) 0 yz.2)|)
      ((volume : Measure Vec3).prod volume) := by
    exact (ENNReal.continuous_ofReal.comp continuous_abs).measurable.comp_aemeasurable
      hgtrans
  have hK' : AEMeasurable
      (fun yz : Vec3 × ParabolicPoint => ENNReal.ofReal |k yz.1|)
      ((volume : Measure Vec3).prod volume) :=
    hK.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
  change AEMeasurable
    ((fun yz : Vec3 × ParabolicPoint => ENNReal.ofReal |k yz.1|) *
      (fun yz : Vec3 × ParabolicPoint =>
        ENNReal.ofReal |g (parabolicTranslate (-yz.1) 0 yz.2)|)) _
  exact hK'.mul hG

private lemma parabolicTranslate_ball_image (a : Vec3) (t : ℝ)
    (z : ParabolicPoint) (r : ℝ) :
    parabolicTranslate a t '' Metric.ball z r =
      Metric.ball (parabolicTranslate a t z) r := by
  have hdist (x y : ParabolicPoint) :
      parabolicDist (parabolicTranslate a t x) (parabolicTranslate a t y) =
        parabolicDist x y := by
    unfold parabolicDist parabolicTranslate
    rw [show (a + x.1) - (a + y.1) = x.1 - y.1 by abel,
      show (t + x.2) - (t + y.2) = x.2 - y.2 by abel]
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Metric.mem_ball, dist_eq_parabolicDist] at hv ⊢
    rw [hdist]
    exact hv
  · intro hw
    have hw' : parabolicDist w (parabolicTranslate a t z) < r := by
      simpa only [dist_eq_parabolicDist] using Metric.mem_ball.mp hw
    cases w with
    | mk wx wt =>
      refine ⟨parabolicTranslate (-a) (-t) (wx, wt), ?_, ?_⟩
      · have heq : parabolicDist (parabolicTranslate (-a) (-t) (wx, wt)) z =
            parabolicDist (wx, wt) (parabolicTranslate a t z) := by
          rw [← hdist (parabolicTranslate (-a) (-t) (wx, wt)) z]
          simp [parabolicTranslate]
        rw [Metric.mem_ball, dist_eq_parabolicDist, heq]
        exact hw'
      ·
          apply Prod.ext
          · change a + (-a + wx) = wx
            abel
          · change t + (-t + wt) = wt
            abel

private lemma ball_lintegral_translate (p : ℝ) (G : ParabolicPoint → ℝ≥0∞)
    (a : Vec3) (t : ℝ) (z : ParabolicPoint) (r : ℝ) :
    (∫⁻ w in Metric.ball z r, G (parabolicTranslate a t w) ^ p) =
      ∫⁻ w in Metric.ball (parabolicTranslate a t z) r, G w ^ p := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  let e : ParabolicPoint ≃ᵐ ParabolicPoint :=
    (MeasurableEquiv.addLeft a).prodCongr (MeasurableEquiv.addLeft t)
  have he : (e : ParabolicPoint → ParabolicPoint) = parabolicTranslate a t := by
    funext w
    rfl
  have hmp : MeasurePreserving e volume volume := by
    have hmp' : MeasurePreserving (parabolicTranslate a t) volume volume := by
      rw [Integration.volume_parabolicPoint_eq_prod]
      change MeasurePreserving (fun w : Vec3 × ℝ => (a + w.1, t + w.2))
        (volume.prod volume) (volume.prod volume)
      exact (measurePreserving_add_left (volume : Measure Vec3) a).prod
        (measurePreserving_add_left (volume : Measure ℝ) t)
    rw [he]
    exact hmp'
  have himage := parabolicTranslate_ball_image a t z r
  have himage' : e '' Metric.ball z r = Metric.ball (e z) r := by
    simpa only [he] using himage
  have hint := hmp.setLIntegral_comp_emb e.measurableEmbedding
    (fun w => G w ^ p) (Metric.ball z r)
  rw [himage'] at hint
  simpa only [he] using hint

/-- The real-kernel Minkowski inequality for the metric-ball Morrey seminorm. -/
theorem morreyBallNorm_spatialConvolution_real_le
    (P τ : ℝ) (hP : 1 ≤ P) (hPτ : P ≤ τ)
    (k : Vec3 → ℝ) (hk : Integrable k volume)
    (g : ParabolicPoint → ℝ) (hg : Measurable g) :
    morreyBallNorm P τ (fun z => ∫ y, k y * g (z.1 - y, z.2)) ≤
      ENNReal.ofReal (∫ y, |k y|) * morreyBallNorm P τ g := by
  let _ : SFinite (volume : Measure Vec3) := by infer_instance
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  let K : Vec3 → ℝ≥0∞ := fun y => ENNReal.ofReal |k y|
  let G : ParabolicPoint → ℝ≥0∞ := fun z => ENNReal.ofReal |g z|
  have hKG := aemeasurable_ball_spatial_integrand hk hg
  have hK : AEMeasurable K volume := by
    exact (ENNReal.continuous_ofReal.comp continuous_abs).measurable.comp_aemeasurable
      hk.aemeasurable
  have hKtop : ∀ y, K y ≠ ∞ := by
    intro y
    simp [K]
  have hmass : (∫⁻ y, K y ∂volume) = ENNReal.ofReal (∫ y, |k y|) := by
    have hkabs : Integrable (fun y : Vec3 => |k y|) volume := by
      simpa only [Real.norm_eq_abs] using hk.norm
    simp only [K]
    exact (ofReal_integral_eq_lintegral_ofReal hkabs
      (Filter.Eventually.of_forall fun y => abs_nonneg (k y))).symm
  have hPnonneg : 0 ≤ P := le_trans (by norm_num : 0 ≤ (1 : ℝ)) hP
  have hPinvnonneg : 0 ≤ 1 / P := one_div_nonneg.mpr (lt_of_lt_of_le zero_lt_one hP).le
  have hτpos : 0 < τ := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hP) hPτ
  have hnormexp : 5 * (1 / τ - 1 / P) = -(5 * (1 - P / τ) / P) := by
    field_simp [ne_of_gt hτpos, ne_of_gt (lt_of_lt_of_le zero_lt_one hP)]
    ring
  have hcell (z : ParabolicPoint) (r : {r : ℝ // 0 < r}) :
      morreyBallCell P τ
        (fun w => ∫ y, k y * g (w.1 - y, w.2)) z r.1 ≤
        ENNReal.ofReal (∫ y, |k y|) * morreyBallNorm P τ g := by
    let ballSet : Set ParabolicPoint := Metric.ball z r.1
    let ν : Measure ParabolicPoint := volume.restrict ballSet
    let F : Vec3 × ParabolicPoint → ℝ≥0∞ := fun yz =>
      K yz.1 * G (parabolicTranslate (-yz.1) 0 yz.2)
    let A : ℝ≥0∞ := (ENNReal.ofReal r.1) ^ (-(5 * (1 - P / τ) / P))
    have hQ : MeasurableSet ballSet := by
      dsimp [ballSet]
      exact Metric.isOpen_ball.measurableSet
    have hν : ν Set.univ ≠ ∞ := by
      rw [Measure.restrict_apply_univ]
      exact (volume_parabolicBall_lt_top r.2).ne
    have hνtop : volume ballSet ≠ ∞ := (volume_parabolicBall_lt_top r.2).ne
    let _ : IsFiniteMeasure ν := by
      dsimp [ν]
      exact isFiniteMeasure_restrict.mpr hνtop
    have hFν : AEMeasurable F ((volume : Measure Vec3).prod ν) := by
      rw [show ((volume : Measure Vec3).prod ν) =
          ((volume : Measure Vec3).prod volume).restrict (Set.univ ×ˢ ballSet) by
        dsimp [ν]
        rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
          (ν := (volume : Measure ParabolicPoint)) Set.univ ballSet]
        simp]
      exact hKG.restrict
    have hJ : AEMeasurable
        (fun y : Vec3 => (∫⁻ w, F (y, w) ^ P ∂ν) ^ (1 / P)) volume := by
      exact (hFν.pow_const P).lintegral_prod_right'.pow_const (1 / P)
    have hconvPoint : ∀ w : ParabolicPoint,
        ENNReal.ofReal |∫ y, k y * g (w.1 - y, w.2)| ≤
          ∫⁻ y, F (y, w) ∂volume := by
      intro w
      have h := enorm_integral_le_lintegral_enorm
        (μ := (volume : Measure Vec3))
        (fun y : Vec3 => k y * g (w.1 - y, w.2))
      simpa [F, K, G, parabolicTranslate, Real.enorm_eq_ofReal_abs,
        abs_mul, ENNReal.ofReal_mul, sub_eq_add_neg, add_comm] using h
    have hMink := lintegral_minkowski_ball (μ := (volume : Measure Vec3))
      (ν := ν) hν hP hFν
    have hleft :
        (∫⁻ w in ballSet,
          (ENNReal.ofReal |∫ y, k y * g (w.1 - y, w.2)|) ^ P) ^ (1 / P) ≤
          ∫⁻ y, (∫⁻ w in ballSet, F (y, w) ^ P) ^ (1 / P) ∂volume := by
      have hdom : ∫⁻ w in ballSet,
          (ENNReal.ofReal |∫ y, k y * g (w.1 - y, w.2)|) ^ P ≤
          ∫⁻ w, (∫⁻ y, F (y, w) ∂volume) ^ P ∂ν := by
        apply lintegral_mono
        intro w
        exact ENNReal.rpow_le_rpow (hconvPoint w) hPnonneg
      have hdom' := ENNReal.rpow_le_rpow hdom hPinvnonneg
      simpa [ν, ballSet, F] using hdom'.trans hMink
    have hAfinite : A ≠ ∞ := by
      dsimp [A]
      exact ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.ofReal_pos.mpr r.2).ne' ENNReal.ofReal_ne_top
    have hpoint : ∀ y : Vec3,
        A * (∫⁻ w, F (y, w) ^ P ∂ν) ^ (1 / P) ≤
          K y * morreyBallNorm P τ g := by
      intro y
      have hKpowtop : K y ^ P ≠ ∞ :=
        ENNReal.rpow_ne_top_of_nonneg hPnonneg (hKtop y)
      have hfactor : (∫⁻ w, F (y, w) ^ P ∂ν) = K y ^ P *
          ∫⁻ w in ballSet, G (parabolicTranslate (-y) 0 w) ^ P := by
        calc
          (∫⁻ w, F (y, w) ^ P ∂ν) =
              ∫⁻ w in ballSet, (K y * G (parabolicTranslate (-y) 0 w)) ^ P := by rfl
          _ = ∫⁻ w in ballSet, K y ^ P * G (parabolicTranslate (-y) 0 w) ^ P := by
            apply lintegral_congr
            intro w
            exact ENNReal.mul_rpow_of_nonneg _ _ hPnonneg
          _ = K y ^ P * ∫⁻ w in ballSet, G (parabolicTranslate (-y) 0 w) ^ P := by
            exact lintegral_const_mul' (K y ^ P)
              (fun w => G (parabolicTranslate (-y) 0 w) ^ P) hKpowtop
      have htranslated := ball_lintegral_translate P G (-y) 0 z r.1
      have hroot :
          (∫⁻ w, F (y, w) ^ P ∂ν) ^ (1 / P) =
            K y * (ballPowerIntegral P g (parabolicTranslate (-y) 0 z) r.1) ^ (1 / P) := by
        rw [hfactor, htranslated]
        have hKroot : (K y ^ P) ^ (1 / P) = K y := by
          rw [← ENNReal.rpow_mul]
          have hmul : P * (1 / P) = 1 := by
            field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hP)]
          rw [hmul, ENNReal.rpow_one]
        rw [ENNReal.mul_rpow_of_nonneg _ _ hPinvnonneg, hKroot]
        simp [ballPowerIntegral, G]
      have hcellle : morreyBallCell P τ g (parabolicTranslate (-y) 0 z) r.1 ≤
          morreyBallNorm P τ g := by
        unfold morreyBallNorm
        exact le_iSup_of_le (parabolicTranslate (-y) 0 z)
          (le_iSup_of_le r le_rfl)
      have hbound : A *
          (ballPowerIntegral P g (parabolicTranslate (-y) 0 z) r.1) ^ (1 / P) ≤
          morreyBallNorm P τ g := by
        simpa [A, hnormexp, morreyBallCell] using hcellle
      rw [hroot]
      calc
        A * (K y * (ballPowerIntegral P g (parabolicTranslate (-y) 0 z) r.1) ^ (1 / P)) =
            K y * (A * (ballPowerIntegral P g (parabolicTranslate (-y) 0 z) r.1) ^ (1 / P)) := by
              ac_rfl
        _ ≤ K y * morreyBallNorm P τ g := mul_le_mul_right hbound (K y)
    have hmassBall :
        A * (∫⁻ w in ballSet,
          (ENNReal.ofReal |∫ y, k y * g (w.1 - y, w.2)|) ^ P) ^ (1 / P) ≤
          ENNReal.ofReal (∫ y, |k y|) * morreyBallNorm P τ g := by
      calc
        _ ≤ A * (∫⁻ y, (∫⁻ w, F (y, w) ^ P ∂ν) ^ (1 / P) ∂volume) :=
          mul_le_mul_right hleft A
        _ = ∫⁻ y, A * (∫⁻ w, F (y, w) ^ P ∂ν) ^ (1 / P) ∂volume :=
          (lintegral_const_mul'' A hJ).symm
        _ ≤ ∫⁻ y, K y * morreyBallNorm P τ g ∂volume := lintegral_mono hpoint
        _ = (∫⁻ y, K y ∂volume) * morreyBallNorm P τ g :=
          lintegral_mul_const'' _ hK
        _ = ENNReal.ofReal (∫ y, |k y|) * morreyBallNorm P τ g := by rw [hmass]
    simpa [morreyBallCell, A, ballPowerIntegral, ballSet, hnormexp] using hmassBall
  unfold morreyBallNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  exact hcell z r

end CKN.Foundation.Parabolic.Morrey
