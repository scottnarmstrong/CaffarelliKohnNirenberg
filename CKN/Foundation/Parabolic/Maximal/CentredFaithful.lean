-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Maximal.StrongType
import CKN.Foundation.Parabolic.Campanato
import CKN.Foundation.Parabolic.BallDisplays
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The centred parabolic maximal theorem

This file assembles the centred maximal estimates and differentiation theorem
for the parabolic metric balls.
-/

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

private def centeredParabolicHomeomorphSnow : ParabolicPoint ≃ₜ L2Vec3 × SnowTime :=
  { parabolicMeasurableEquiv with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      apply continuous_induced_rng.mpr
      change Continuous (fun p : L2Vec3 × SnowTime =>
        parabolicMeasurableEquiv (parabolicMeasurableEquiv.symm p))
      simp only [parabolicMeasurableEquiv, Snowflaking.toSnowflaking]
      exact continuous_fst.prodMk continuous_snd }

private def centeredParabolicHomeomorphReal : ParabolicPoint ≃ₜ L2Vec3 × ℝ :=
  centeredParabolicHomeomorphSnow.trans
    (Homeomorph.prodCongr (Homeomorph.refl L2Vec3) Metric.Snowflaking.homeomorph)

private theorem centered_parabolic_closedBall_compact {z : ParabolicPoint} {r : ℝ}
    (_ : 0 < r) :
    IsCompact (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) := by
  let R : ℝ := max r (r ^ 2)
  have hprod : IsCompact (@Metric.closedBall (L2Vec3 × ℝ) inferInstance
      (centeredParabolicHomeomorphReal z) R) := isCompact_closedBall _ _
  have hsub : centeredParabolicHomeomorphReal ''
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) ⊆
      @Metric.closedBall (L2Vec3 × ℝ) inferInstance
        (centeredParabolicHomeomorphReal z) R := by
    rintro q ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, Prod.dist_eq]
    rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp
    rcases max_le_iff.mp hp with ⟨hspace, htime⟩
    have hsq : |p.2 - z.2| ≤ r ^ 2 := (Real.sqrt_le_iff.mp htime).2
    apply max_le
    · change ‖WithLp.toLp 2 (p.1 - z.1)‖ ≤ R
      have hspace' : ‖WithLp.toLp 2 (p.1 - z.1)‖ ≤ r := by
        simpa only [vec3EuclideanNorm_eq_l2] using hspace
      simpa only [WithLp.toLp_sub] using hspace'.trans (le_max_left _ _)
    · change |p.2 - z.2| ≤ R
      exact hsq.trans (le_max_right _ _)
  have himage : IsCompact (centeredParabolicHomeomorphReal ''
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)) := by
    apply hprod.of_isClosed_subset
    · exact centeredParabolicHomeomorphReal.isClosed_image.mpr isClosed_closedBall
    · exact hsub
  exact (centeredParabolicHomeomorphReal.isCompact_image).mp (by simpa using himage)

private def centeredParabolicMaximal (g : ParabolicPoint → ℝ)
    (z : ParabolicPoint) : ℝ≥0∞ :=
    ⨆ r : {r : ℝ // 0 < r},
    ⨍⁻ w in Metric.ball z r.1, ENNReal.ofReal |g w| ∂volume

private theorem centeredParabolicMaximal_le_uncentered (g : ParabolicPoint → ℝ)
    (z : ParabolicPoint) :
    centeredParabolicMaximal g z ≤
      parabolicMaximalFunction (fun w ↦ ENNReal.ofReal |g w|) z := by
  apply iSup_le
  intro r
  apply le_iSup₂_of_le z r.1
  rw [indicator_of_mem (Metric.mem_ball_self r.2)]

private lemma centered_average_expand
    (g : ParabolicPoint → ℝ) {x y : ParabolicPoint} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hxy : dist y x < δ) :
    (⨍⁻ w in Metric.ball x r, ENNReal.ofReal |g w| ∂volume) *
        ENNReal.ofReal ((r / (r + δ)) ^ 5) ≤
      ⨍⁻ w in Metric.ball y (r + δ), ENNReal.ofReal |g w| ∂volume := by
  have hset : Metric.ball x r ⊆ Metric.ball y (r + δ) := by
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    calc
      dist w y ≤ dist w x + dist x y := dist_triangle _ _ _
      _ < r + δ := add_lt_add hw (by simpa [dist_comm] using hxy)
  have hvolx := volume_metricBall x hr.le
  have hvoly := volume_metricBall y (le_of_lt (add_pos hr hδ))
  have hvolratio :
      volume (Metric.ball x r) / volume (Metric.ball y (r + δ)) =
        ENNReal.ofReal ((r / (r + δ)) ^ 5) := by
    rw [hvolx, hvoly]
    rw [← ENNReal.ofReal_div_of_pos
      (by positivity : 0 < (8 * Real.pi / 3) * (r + δ) ^ 5)]
    congr 1
    field_simp
  have hvolxpos : 0 < volume (Metric.ball x r) := volume_parabolicBall_pos hr
  have hvolxtop : volume (Metric.ball x r) < ∞ := volume_parabolicBall_lt_top hr
  calc
    (⨍⁻ w in Metric.ball x r, ENNReal.ofReal |g w| ∂volume) *
        ENNReal.ofReal ((r / (r + δ)) ^ 5) =
        (⨍⁻ w in Metric.ball x r, ENNReal.ofReal |g w| ∂volume) *
          (volume (Metric.ball x r) / volume (Metric.ball y (r + δ))) := by
            rw [hvolratio]
    _ = (∫⁻ w in Metric.ball x r, ENNReal.ofReal |g w| ∂volume) /
          volume (Metric.ball y (r + δ)) := by
            rw [setLAverage_eq]
            exact ENNReal.div_mul_div_cancel hvolxpos.ne' hvolxtop.ne
    _ ≤ (∫⁻ w in Metric.ball y (r + δ), ENNReal.ofReal |g w| ∂volume) /
          volume (Metric.ball y (r + δ)) := by
            gcongr
    _ = ⨍⁻ w in Metric.ball y (r + δ), ENNReal.ofReal |g w| ∂volume := by
            rw [setLAverage_eq]

private theorem lowerSemicontinuous_centeredParabolicMaximal (g : ParabolicPoint → ℝ) :
    LowerSemicontinuous (centeredParabolicMaximal g) := by
  rw [lowerSemicontinuous_iff]
  intro x a hax
  obtain ⟨r, haxr⟩ := exists_lt_of_lt_ciSup' hax
  let A : ℝ≥0∞ := ⨍⁻ w in Metric.ball x r.1, ENNReal.ofReal |g w| ∂volume
  have haxA : a < A := haxr
  by_cases hAtop : A = ∞
  · have hδ : 0 < r.1 := r.2
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
    have hratio : 0 < ENNReal.ofReal ((r.1 / (r.1 + r.1)) ^ 5) := by
      apply ENNReal.ofReal_pos.mpr
      positivity
    have hscale := centered_average_expand g r.2 r.2 hy
    have htopmul : A * ENNReal.ofReal ((r.1 / (r.1 + r.1)) ^ 5) = ∞ := by
      rw [hAtop]
      simp [hratio.ne']
    have hM : ⨍⁻ w in Metric.ball y (r.1 + r.1), ENNReal.ofReal |g w| ∂volume ≤
        centeredParabolicMaximal g y := by
      apply le_iSup_of_le ⟨r.1 + r.1, add_pos r.2 r.2⟩
      rfl
    have hscale' : ∞ ≤ ⨍⁻ w in Metric.ball y (r.1 + r.1),
        ENNReal.ofReal |g w| ∂volume := by
      change A * ENNReal.ofReal ((r.1 / (r.1 + r.1)) ^ 5) ≤ _ at hscale
      rw [htopmul] at hscale
      exact hscale
    exact lt_of_lt_of_le (by simpa [A, hAtop] using haxA) (hscale'.trans hM)
  · have hAfinite : A < ∞ := lt_top_iff_ne_top.mpr hAtop
    have hratio : Tendsto (fun d : ℝ =>
        ENNReal.ofReal ((r.1 / (r.1 + d)) ^ 5)) (𝓝 0) (𝓝 1) := by
      have hreal : ContinuousAt (fun d : ℝ => (r.1 / (r.1 + d)) ^ 5) 0 := by
        have hdiv : ContinuousAt (fun d : ℝ => r.1 / (r.1 + d)) 0 :=
          continuousAt_const.div (continuousAt_const.add continuousAt_id)
            (by simpa using r.2.ne')
        exact hdiv.pow 5
      have h := (ENNReal.continuous_ofReal.continuousAt.comp hreal).tendsto
      have hzero : (r.1 / (r.1 + 0)) ^ 5 = 1 := by
        rw [add_zero, div_self (ne_of_gt r.2), one_pow]
      simpa only [Function.comp_def, hzero, ENNReal.ofReal_one] using h
    have hprod : Tendsto (fun d : ℝ => A * ENNReal.ofReal ((r.1 / (r.1 + d)) ^ 5))
        (𝓝 0) (𝓝 A) := by
      simpa using ENNReal.Tendsto.const_mul hratio (Or.inr hAfinite.ne)
    have hsmall : ∀ᶠ d in 𝓝[>] (0 : ℝ),
        a < A * ENNReal.ofReal ((r.1 / (r.1 + d)) ^ 5) := by
      have hnb : {v : ℝ≥0∞ | a < v} ∈ 𝓝 A := isOpen_Ioi.mem_nhds haxA
      have hev := hprod.eventually hnb
      exact hev.filter_mono nhdsWithin_le_nhds
    have hpos : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < d := eventually_mem_nhdsWithin
    obtain ⟨δ, hδpos, hδsmall⟩ := (hpos.and hsmall).exists
    filter_upwards [Metric.ball_mem_nhds x hδpos] with y hy
    have hscale := centered_average_expand g r.2 hδpos hy
    have hδsmall' : a <
        (⨍⁻ w in Metric.ball x r.1, ENNReal.ofReal |g w| ∂volume) *
          ENNReal.ofReal ((r.1 / (r.1 + δ)) ^ 5) := by
      simpa only [A, add_comm] using hδsmall
    have hM : ⨍⁻ w in Metric.ball y (r.1 + δ), ENNReal.ofReal |g w| ∂volume ≤
        centeredParabolicMaximal g y := by
      apply le_iSup_of_le ⟨r.1 + δ, add_pos r.2 hδpos⟩
      rfl
    exact lt_of_lt_of_le hδsmall' (hscale.trans hM)

private theorem centeredParabolicMaximal_congr_ae
    {f g : ParabolicPoint → ℝ} (hfg : f =ᵐ[volume] g) :
    centeredParabolicMaximal f = centeredParabolicMaximal g := by
  funext z
  unfold centeredParabolicMaximal
  apply iSup_congr
  intro r
  rw [setLAverage_eq, setLAverage_eq]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hfg] with w hw
  rw [hw]

private theorem centeredParabolicMaximal_strong_type
    {P : ℝ} (hP : 1 < P) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : ParabolicPoint → ℝ, MemLp g (ENNReal.ofReal P) volume →
        (∫⁻ z, centeredParabolicMaximal g z ^ P ∂volume) ^ (1 / P) ≤
          ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal P) volume := by
  have hPpos : 0 < P := lt_trans zero_lt_one hP
  let K : ℝ≥0∞ := parabolicMaximalStrongConstant P
  have hKtop : K < ∞ := by
    dsimp [K, parabolicMaximalStrongConstant]
    finiteness
  let C : ℝ := (K ^ (1 / P)).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  refine ⟨C, hC, ?_⟩
  intro g hmem
  let gbar : ParabolicPoint → ℝ := hmem.aestronglyMeasurable.mk g
  have hgb : g =ᵐ[volume] gbar := hmem.aestronglyMeasurable.ae_eq_mk
  have hbarMem : MemLp gbar (ENNReal.ofReal P) volume :=
    (memLp_congr_ae hgb).mp hmem
  have hPto : (ENNReal.ofReal P).toReal = P := ENNReal.toReal_ofReal hPpos.le
  have hfpbar : ∫⁻ z, ‖gbar z‖ₑ ^ (ENNReal.ofReal P).toReal ∂volume < ∞ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (f := gbar) (p := ENNReal.ofReal P)
      (by positivity) (by simp) hbarMem.eLpNorm_lt_top
  have hsource :
      (∫⁻ z, (ENNReal.ofReal ‖gbar z‖₊) ^ P ∂volume) =
        ∫⁻ z, ‖gbar z‖ₑ ^ P ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [] with z
    rw [ENNReal.ofReal_coe_nnreal, enorm_eq_nnnorm]
  have hfp : ∫⁻ z, (ENNReal.ofReal ‖gbar z‖₊) ^ P ∂volume < ∞ := by
    rw [hsource]
    simpa only [hPto] using hfpbar
  have hdom : ∀ z, centeredParabolicMaximal g z ≤
      parabolicMaximalFunction (fun w ↦ ENNReal.ofReal |gbar w|) z := by
    intro z
    rw [centeredParabolicMaximal_congr_ae hgb]
    exact centeredParabolicMaximal_le_uncentered gbar z
  have hstrong := lintegral_rpow_parabolicMaximalFunction_ofReal_le
    gbar hmem.aestronglyMeasurable.measurable_mk hP hfp
  have hLpformula :
      eLpNorm gbar (ENNReal.ofReal P) volume =
        (∫⁻ z, ‖gbar z‖ₑ ^ P ∂volume) ^ (1 / P) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by positivity : ENNReal.ofReal P ≠ 0)
      (by simp : ENNReal.ofReal P ≠ ∞) hbarMem.aestronglyMeasurable]
    rw [hPto]
  have hLpEq : eLpNorm gbar (ENNReal.ofReal P) volume =
      eLpNorm g (ENNReal.ofReal P) volume := eLpNorm_congr_ae hgb.symm
  have hroot : ENNReal.ofReal C = K ^ (1 / P) := by
    change ENNReal.ofReal (K ^ (1 / P)).toReal = K ^ (1 / P)
    exact ENNReal.ofReal_toReal (ne_of_lt
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt hKtop)))
  calc
    (∫⁻ z, centeredParabolicMaximal g z ^ P ∂volume) ^ (1 / P) ≤
        (∫⁻ z, parabolicMaximalFunction
          (fun w ↦ ENNReal.ofReal |gbar w|) z ^ P ∂volume) ^ (1 / P) := by
      gcongr with z
      exact hdom z
    _ ≤ (K * ∫⁻ z, (ENNReal.ofReal ‖gbar z‖₊) ^ P ∂volume) ^ (1 / P) := by
      gcongr
      exact hstrong
    _ = K ^ (1 / P) *
        (∫⁻ z, ‖gbar z‖ₑ ^ P ∂volume) ^ (1 / P) := by
      rw [ENNReal.mul_rpow_of_nonneg K _ (by positivity : 0 ≤ 1 / P), hsource]
    _ = ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal P) volume := by
      rw [hroot, ← hLpformula, hLpEq]

private theorem centeredParabolicMaximal_weak (g : ParabolicPoint → ℝ)
    (hg : Integrable g volume) :
    ∀ a : ℝ, 0 < a →
      volume {z | ENNReal.ofReal a < centeredParabolicMaximal g z} ≤
        ENNReal.ofReal ((10 ^ 5 : ℝ) / a) * eLpNorm g 1 volume := by
  intro a ha
  have hsubset :
      {z | ENNReal.ofReal a < centeredParabolicMaximal g z} ⊆
        {z | ENNReal.ofReal a <
          parabolicMaximalFunction (fun w ↦ ENNReal.ofReal |g w|) z} := by
    intro z hz
    exact hz.trans_le (centeredParabolicMaximal_le_uncentered g z)
  have hweak := measure_parabolicMaximalFunction_lt_le
    (fun w ↦ ENNReal.ofReal |g w|)
    (l := ENNReal.ofReal a) (ENNReal.ofReal_pos.mpr ha)
  have hnorm : eLpNorm g 1 volume = ∫⁻ z, ENNReal.ofReal |g z| ∂volume := by
    rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
    exact lintegral_congr fun z ↦ Real.enorm_eq_ofReal_abs (g z)
  calc
    volume {z | ENNReal.ofReal a < centeredParabolicMaximal g z} ≤
        volume {z | ENNReal.ofReal a <
          parabolicMaximalFunction (fun w ↦ ENNReal.ofReal |g w|) z} :=
      measure_mono hsubset
    _ ≤ (ENNReal.ofReal (10 ^ 5) / ENNReal.ofReal a) *
          ∫⁻ z, ENNReal.ofReal |g z| ∂volume := hweak
    _ = ENNReal.ofReal ((10 ^ 5 : ℝ) / a) * eLpNorm g 1 volume := by
      rw [ENNReal.ofReal_div_of_pos ha, ← hnorm]

private theorem average_abs_le_outer_average_abs_local
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {A B : Set α} (hBA : B ⊆ A)
    (hApos : 0 < μ A) (hAtop : μ A < ∞)
    (hBpos : 0 < μ B) (hBtop : μ B < ∞)
    (hfA : IntegrableOn f A μ) :
    (⨍ x in B, |f x| ∂μ) ≤
      (μ A).toReal / (μ B).toReal * (⨍ x in A, |f x| ∂μ) := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  have hmono :
      ∫ x in B, |f x| ∂μ ≤ ∫ x in A, |f x| ∂μ := by
    apply MeasureTheory.integral_mono_measure
    · exact Measure.restrict_mono hBA le_rfl
    · exact Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x)
    · exact hfA.norm
  have hAreal : 0 < (μ A).toReal := ENNReal.toReal_pos hApos.ne' hAtop.ne
  have hBreal : 0 < (μ B).toReal := ENNReal.toReal_pos hBpos.ne' hBtop.ne
  have hBinv : 0 ≤ (μ B).toReal⁻¹ := le_of_lt (inv_pos.mpr hBreal)
  change (μ B).toReal⁻¹ * ∫ x in B, |f x| ∂μ ≤
    (μ A).toReal / (μ B).toReal *
      ((μ A).toReal⁻¹ * ∫ x in A, |f x| ∂μ)
  calc
    (μ B).toReal⁻¹ * ∫ x in B, |f x| ∂μ ≤
        (μ B).toReal⁻¹ * ∫ x in A, |f x| ∂μ :=
      mul_le_mul_of_nonneg_left hmono hBinv
    _ = (μ A).toReal / (μ B).toReal *
        ((μ A).toReal⁻¹ * ∫ x in A, |f x| ∂μ) := by
      field_simp

private theorem centeredAverage_abs_le_closedBall
    {g : ParabolicPoint → ℝ} (hg : LocallyIntegrable g volume)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (⨍ y in Metric.ball z r, |g y - g z| ∂volume) ≤
      (10 ^ 5 : ℝ) *
        (⨍ y in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
          |g y - g z| ∂volume) := by
  let A : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r
  let B : Set ParabolicPoint := Metric.ball z r
  have hBA : B ⊆ A := Metric.ball_subset_closedBall
  have hApos : 0 < volume A :=
    (volume_parabolicBall_pos hr).trans_le (measure_mono hBA)
  have hBpos : 0 < volume B := volume_parabolicBall_pos hr
  have hBtop : volume B < ∞ := volume_parabolicBall_lt_top hr
  have hAsub : A ⊆ Metric.ball z (2 * r) :=
    Metric.closedBall_subset_ball (by linarith only [hr])
  have hAtop : volume A < ∞ :=
    (measure_mono hAsub).trans_lt (volume_parabolicBall_lt_top (by positivity))
  have hvol : volume A ≤ ENNReal.ofReal (10 ^ 5 : ℝ) * volume B := by
    calc
      volume A ≤ volume (Metric.ball z (2 * r)) := measure_mono hAsub
      _ ≤ ENNReal.ofReal (10 ^ 5 : ℝ) * volume B :=
        volume_parabolicBall_two_mul_le hr
  have hvolReal : (volume A).toReal ≤ (10 ^ 5 : ℝ) * (volume B).toReal := by
    calc
      (volume A).toReal ≤ (ENNReal.ofReal (10 ^ 5 : ℝ) * volume B).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBtop).ne hvol
      _ = (10 ^ 5 : ℝ) * (volume B).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
        positivity
  have hBreal : 0 < (volume B).toReal := ENNReal.toReal_pos hBpos.ne' hBtop.ne
  have hratio : (volume A).toReal / (volume B).toReal ≤ (10 ^ 5 : ℝ) := by
    apply (div_le_iff₀ hBreal).2
    simpa only [mul_comm] using hvolReal
  have hfA : IntegrableOn (fun y : ParabolicPoint ↦ g y - g z) A volume := by
    have hcompact : IsCompact A := centered_parabolic_closedBall_compact hr
    have hint : IntegrableOn g A volume := by
      exact hg.integrableOn_isCompact hcompact
    have hconst : IntegrableOn (fun _ : ParabolicPoint ↦ g z) A volume :=
      integrableOn_const hAtop.ne
    exact hint.sub hconst
  have havg := average_abs_le_outer_average_abs_local hBA hApos hAtop hBpos hBtop hfA
  calc
    (⨍ y in B, |g y - g z| ∂volume) ≤
        (volume A).toReal / (volume B).toReal *
          (⨍ y in A, |g y - g z| ∂volume) := by
      simpa only [Pi.sub_apply] using havg
    _ ≤ (10 ^ 5 : ℝ) * (⨍ y in A, |g y - g z| ∂volume) := by
      exact mul_le_mul_of_nonneg_right hratio
        (Integration.setAverage_nonneg_of_ae
          (Filter.Eventually.of_forall fun y ↦ abs_nonneg (g y - g z)))

private theorem ae_tendsto_centered_average_abs
    {g : ParabolicPoint → ℝ} (hg : LocallyIntegrable g volume) :
    ∀ᵐ z ∂volume,
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball z r, |g y - g z| ∂volume)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (volume : Measure ParabolicPoint) hg 1
  filter_upwards [hdiff] with z hz
  have hδ : Tendsto (fun r : ℝ ↦ r) (nhdsWithin 0 (Ioi 0)) (𝓝[>] 0) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_nhds_of_tendsto_nhdsWithin tendsto_id, eventually_mem_nhdsWithin⟩
  have hzball : ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0),
      z ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r := by
    filter_upwards [eventually_mem_nhdsWithin] with r hr
    rw [Metric.mem_closedBall, dist_self]
    exact (mem_Ioi.mp hr).le
  have hclosed := hz (w := fun _ : ℝ ↦ z) (δ := fun r : ℝ ↦ r) hδ
    (by simpa only [one_mul] using hzball)
  have hscaled : Tendsto
      (fun r : ℝ => (10 ^ 5 : ℝ) *
        (⨍ y in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
          |g y - g z| ∂volume))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [Real.norm_eq_abs, mul_zero] using hclosed.const_mul (10 ^ 5 : ℝ)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' ?_ ?_ hscaled
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    exact abs_nonneg _
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    have hrpos : 0 < r := mem_Ioi.mp hr
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (Integration.setAverage_nonneg_of_ae
      (Filter.Eventually.of_forall fun y ↦ abs_nonneg (g y - g z)))]
    exact centeredAverage_abs_le_closedBall hg z hrpos

/-- The centered parabolic maximal theorem, including differentiation at almost
every point for averages over all positive radii. -/
theorem parabolic_maximal_and_differentiation :
  let M : (ParabolicPoint → ℝ) → ParabolicPoint → ℝ≥0∞ := fun g z =>
    ⨆ r : {r : ℝ // 0 < r}, ⨍⁻ w in Metric.ball z r.1, ENNReal.ofReal |g w| ∂volume
  (∀ g : ParabolicPoint → ℝ, LocallyIntegrable g volume →
    LowerSemicontinuous (M g) ∧
    ∀ᵐ z ∂volume, Tendsto
      (fun r : ℝ => ⨍ w in Metric.ball z r, |g w - g z|)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ g : ParabolicPoint → ℝ, Integrable g volume →
    ∀ a : ℝ, 0 < a →
      volume {z | ENNReal.ofReal a < M g z} ≤
        ENNReal.ofReal (C / a) * eLpNorm g 1 volume) ∧
  (∀ P : ℝ, 1 < P → ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ParabolicPoint → ℝ,
    MemLp g (ENNReal.ofReal P) volume →
    (∫⁻ z, M g z ^ P) ^ (1 / P) ≤
      ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal P) volume) := by
  dsimp
  constructor
  · intro g hg
    constructor
    · change LowerSemicontinuous (centeredParabolicMaximal g)
      exact lowerSemicontinuous_centeredParabolicMaximal g
    · exact ae_tendsto_centered_average_abs hg
  constructor
  · refine ⟨10 ^ 5, by positivity, ?_⟩
    intro g hg a ha
    change volume {z | ENNReal.ofReal a < centeredParabolicMaximal g z} ≤
      ENNReal.ofReal ((10 ^ 5 : ℝ) / a) * eLpNorm g 1 volume
    exact centeredParabolicMaximal_weak g hg a ha
  · intro P hP
    simpa only [centeredParabolicMaximal] using
      (centeredParabolicMaximal_strong_type (P := P) hP)

end CKN.Foundation.Parabolic

end
