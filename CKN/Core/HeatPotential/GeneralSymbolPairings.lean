-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step3.LocalizedEquationDuhamel

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic

private lemma parabolic_sub_measurePreserving (y : ParabolicPoint) :
    MeasurePreserving (fun x : ParabolicPoint => pointSub x y)
      (volume : Measure ParabolicPoint) volume := by
  have h := (measurePreserving_add_right (volume : Measure Vec3) (-y.1)).prod
    (measurePreserving_add_right (volume : Measure ℝ) (-y.2))
  rw [Integration.volume_parabolicPoint_eq_prod]
  change MeasurePreserving (fun x : Vec3 × ℝ =>
    (x.1 + -y.1, x.2 + -y.2)) (volume.prod volume) (volume.prod volume)
  convert h using 1
  rfl

private lemma parabolic_integrableOn_shift_complex
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    {K : Set ParabolicPoint} (hK : IsCompact K) (y : ParabolicPoint) :
    IntegrableOn (fun x : ParabolicPoint => k (pointSub x y)) K volume := by
  let S : Set ParabolicPoint := (fun x : ParabolicPoint => pointSub x y) '' K
  have hS : IsCompact S := by
    apply hK.image
    change Continuous (fun x : ParabolicPoint =>
      parabolicHomeomorph.symm (x.1 - y.1, x.2 - y.2))
    apply parabolicHomeomorph.continuous_symm.comp
    exact ((continuous_fst_parabolicPoint.sub continuous_const).prodMk
      (continuous_snd_parabolicPoint.sub continuous_const))
  have hkS : IntegrableOn k S volume := hk.integrableOn_isCompact hS
  have hInd := hkS.integrable_indicator hS.measurableSet
  have hcomp := (parabolic_sub_measurePreserving y).integrable_comp
    hInd.aestronglyMeasurable |>.mpr hInd
  have heq : (fun x : ParabolicPoint =>
      S.indicator k (pointSub x y)) =
      (fun x : ParabolicPoint => K.indicator
        (fun z : ParabolicPoint => k (pointSub z y)) x) := by
    funext x
    by_cases hx : x ∈ K
    · have hxy : pointSub x y ∈ S := ⟨x, hx, rfl⟩
      simp only [Set.indicator_of_mem hxy, Set.indicator_of_mem hx]
    · have hxy : pointSub x y ∉ S := by
        rintro ⟨z, hz, hzx⟩
        have hzx' : z = x := by
          apply Prod.ext
          · exact sub_left_injective (b := y.1)
              (by simpa [pointSub] using congrArg Prod.fst hzx)
          · exact sub_left_injective (b := y.2)
              (by simpa [pointSub] using congrArg Prod.snd hzx)
        exact hx (by simpa only [hzx'] using hz)
      simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxy]
  have hcomp' : Integrable (fun x : ParabolicPoint =>
      K.indicator (fun z : ParabolicPoint => k (pointSub z y)) x) volume := by
    rw [← heq]
    change Integrable (fun x : ParabolicPoint =>
      S.indicator k (pointSub x y)) volume at hcomp
    exact hcomp
  exact (integrable_indicator_iff hK.measurableSet).mp hcomp'

private lemma parabolic_setIntegral_norm_shift_le_complex
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    {K L : Set ParabolicPoint} (hK : IsCompact K) (hL : IsCompact L)
    (y : ParabolicPoint)
    (hsub : (fun x : ParabolicPoint => pointSub x y) '' K ⊆ L) :
    (∫ x in K, ‖k (pointSub x y)‖) ≤ ∫ z in L, ‖k z‖ := by
  have hkn : LocallyIntegrable (fun z : ParabolicPoint => ‖k z‖) volume := by
    intro x
    rcases hk x with ⟨U, hU, hInt⟩
    exact ⟨U, hU, hInt.norm⟩
  have hshift : IntegrableOn (fun x : ParabolicPoint =>
      ‖k (pointSub x y)‖) K volume := by
    exact (parabolic_integrableOn_shift_complex hk hK y).integrable.norm
  have hleft := hshift.integrable_indicator hK.measurableSet
  have hright0 := hkn.integrableOn_isCompact hL
  have hright := hright0.integrable_indicator hL.measurableSet
  have hcomp := (parabolic_sub_measurePreserving y).integrable_comp
    hright.aestronglyMeasurable |>.mpr hright
  have hle : ∀ᵐ x : ParabolicPoint, K.indicator
      (fun z : ParabolicPoint => ‖k (pointSub z y)‖) x ≤
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y) := by
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · have hxy : pointSub x y ∈ L := hsub ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxy]
    · rw [Set.indicator_of_notMem hx]
      by_cases hLxy : pointSub x y ∈ L
      · rw [Set.indicator_of_mem hLxy]
        exact norm_nonneg _
      · rw [Set.indicator_of_notMem hLxy]
  have hint := integral_mono_ae hleft hcomp hle
  rw [integral_indicator hK.measurableSet] at hint
  let e := (Homeomorph.subRight y.1).prodCongr (Homeomorph.subRight y.2)
  have htrans := (parabolic_sub_measurePreserving y).integral_comp
    e.measurableEmbedding (L.indicator (fun z : ParabolicPoint => ‖k z‖))
  have htrans' : (∫ x : ParabolicPoint,
      (L.indicator (fun z : ParabolicPoint => ‖k z‖) ∘
        fun x : ParabolicPoint => pointSub x y) x) =
      ∫ z : ParabolicPoint, L.indicator (fun z : ParabolicPoint => ‖k z‖) z := by
    change (∫ x : ParabolicPoint,
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y)) =
      ∫ z : ParabolicPoint, L.indicator (fun z : ParabolicPoint => ‖k z‖) z at htrans
    exact htrans
  rw [htrans', integral_indicator hL.measurableSet] at hint
  exact hint

theorem kernel_product_integrableOn_of_compact
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) {g : ParabolicPoint → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    {K : Set ParabolicPoint} (hK : IsCompact K) :
    Integrable (fun z : ParabolicPoint × ParabolicPoint =>
      k (pointSub z.1 z.2) * (g z.2 : ℂ))
      (Measure.prod (volume.restrict K) (volume : Measure ParabolicPoint)) := by
  let S : Set ParabolicPoint := tsupport g
  have hS : IsCompact S := hgc.isCompact
  let L : Set ParabolicPoint :=
    (fun z : ParabolicPoint × ParabolicPoint => pointSub z.1 z.2) '' (K ×ˢ S)
  have hL : IsCompact L := by
    apply (hK.prod hS).image
    change Continuous (fun z : ParabolicPoint × ParabolicPoint =>
      parabolicHomeomorph.symm (z.1.1 - z.2.1, z.1.2 - z.2.2))
    apply parabolicHomeomorph.continuous_symm.comp
    exact ((continuous_fst_parabolicPoint.comp continuous_fst).sub
      (continuous_fst_parabolicPoint.comp continuous_snd)).prodMk
      ((continuous_snd_parabolicPoint.comp continuous_fst).sub
        (continuous_snd_parabolicPoint.comp continuous_snd))
  have hLInt : IntegrableOn (fun z : ParabolicPoint => ‖k z‖) L volume :=
    (hk.integrableOn_isCompact hL).norm
  let μ : Measure ParabolicPoint := volume.restrict K
  let F : ParabolicPoint × ParabolicPoint → ℂ := fun z =>
    k (pointSub z.1 z.2) * (g z.2 : ℂ)
  have hFmeas : AEStronglyMeasurable F (μ.prod volume) := by
    have hk' : Measurable (fun z : ParabolicPoint × ParabolicPoint =>
        k (pointSub z.1 z.2)) := by
      apply hkm.comp
      exact ((measurable_fst.fst.sub measurable_snd.fst).prodMk
        (measurable_fst.snd.sub measurable_snd.snd))
    have hg' : Integrable (fun y : ParabolicPoint => (g y : ℂ)) volume := hg.ofReal
    exact hk'.aestronglyMeasurable.mul hg'.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff' hFmeas).2
  constructor
  · filter_upwards [] with y
    by_cases hy : y ∈ S
    · have hshift := parabolic_integrableOn_shift_complex hk hK y
      have hmul := hshift.integrable.mul_const (g y : ℂ)
      simpa only [F, Function.comp_apply, mul_comm] using hmul
    · have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [F, hgy]
  · have hmeas : AEStronglyMeasurable
        (fun y : ParabolicPoint => ∫ x, ‖F (x, y)‖ ∂μ) volume :=
      hFmeas.prod_swap.norm.integral_prod_right'
    have hmajor : Integrable (fun y : ParabolicPoint =>
        (∫ z in L, ‖k z‖) * ‖g y‖) volume := hg.norm.const_mul _
    apply hmajor.mono hmeas
    filter_upwards [] with y
    by_cases hy : y ∈ S
    · have hsub : (fun x : ParabolicPoint => pointSub x y) '' K ⊆ L := by
        rintro z ⟨x, hx, rfl⟩
        exact ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      have hbound := parabolic_setIntegral_norm_shift_le_complex hk hK hL y hsub
      dsimp [F, μ]
      have hnonleft : 0 ≤ ∫ x in K,
          ‖k (pointSub x y) * (g y : ℂ)‖ :=
        integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      have hnonright : 0 ≤ (∫ z in L, ‖k z‖) * |g y| :=
        mul_nonneg (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)) (abs_nonneg _)
      rw [abs_of_nonneg hnonleft, abs_of_nonneg hnonright]
      simp_rw [norm_mul, Complex.norm_real]
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
    · have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [F, hgy]

theorem kernel_potential_integrableOn_of_compact
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) {g : ParabolicPoint → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    {K : Set ParabolicPoint} (hK : IsCompact K) :
    IntegrableOn (fun x : ParabolicPoint =>
      ∫ y, k (pointSub x y) * (g y : ℂ)) K volume := by
  have hprod := kernel_product_integrableOn_of_compact hk hkm hg hgc hK
  change Integrable (fun x : ParabolicPoint =>
      ∫ y, k (pointSub x y) * (g y : ℂ)) (volume.restrict K)
  exact hprod.integral_prod_left

private def parabolicHomeomorphReal' : ParabolicPoint ≃ₜ Vec3 × ℝ :=
  parabolicHomeomorph

private lemma compact_parabolicMetricClosedBall' {z : ParabolicPoint} {r : ℝ} :
    IsCompact (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) := by
  let R : ℝ := max r (r ^ 2)
  have hprod : IsCompact (@Metric.closedBall (Vec3 × ℝ) inferInstance
      (parabolicHomeomorphReal' z) R) := isCompact_closedBall _ _
  have hsub : parabolicHomeomorphReal' ''
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) ⊆
      @Metric.closedBall (Vec3 × ℝ) inferInstance (parabolicHomeomorphReal' z) R := by
    rintro q ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, Prod.dist_eq]
    rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp
    rcases max_le_iff.mp hp with ⟨hspace, htime⟩
    have hsq : |p.2 - z.2| ≤ r ^ 2 := (Real.sqrt_le_iff.mp htime).2
    apply max_le
    · change dist p.1 z.1 ≤ R
      rw [dist_pi_le_iff (le_max_of_le_right (sq_nonneg r))]
      intro i
      have hspace' : ‖p.1 - z.1‖ ≤ r :=
        (CKN.space_norm_le_euclideanNorm (p.1 - z.1)).trans hspace
      simpa [Real.dist_eq, abs_sub_comm] using
        (le_trans (norm_le_pi_norm (p.1 - z.1) i)
          (hspace'.trans (le_max_left _ _)))
    · change |p.2 - z.2| ≤ R
      exact hsq.trans (le_max_right _ _)
  have himage : IsCompact (parabolicHomeomorphReal' ''
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)) := by
    apply hprod.of_isClosed_subset
    · exact parabolicHomeomorphReal'.isClosed_image.mpr isClosed_closedBall
    · exact hsub
  exact (parabolicHomeomorphReal'.isCompact_image).mp (by simpa using himage)

theorem kernel_potential_locallyIntegrable_of_compact
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) {g : ParabolicPoint → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g) :
    LocallyIntegrable (fun x : ParabolicPoint =>
      ∫ y, k (pointSub x y) * (g y : ℂ)) volume := by
  intro x
  let K : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace x 1
  have hK : IsCompact K := compact_parabolicMetricClosedBall'
  let U : Set ParabolicPoint :=
    @Metric.ball ParabolicPoint parabolicPseudoMetricSpace x 1
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hxU : x ∈ U := Metric.mem_ball_self (by norm_num)
  have hUK : U ⊆ K := Metric.ball_subset_closedBall
  exact ⟨U, hUopen.mem_nhds hxU,
    (kernel_potential_integrableOn_of_compact hk hkm hg hgc hK).mono_set hUK⟩

theorem kernel_pairings_ae_of_compact
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) {g : ParabolicPoint → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g) :
    ∀ᵐ x : ParabolicPoint, Integrable (fun y =>
      k (pointSub x y) * (g y : ℂ)) volume := by
  have hae : ∀ n : ℕ, ∀ᵐ x ∂volume.restrict
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace
        ((0 : Vec3), (0 : ℝ)) (n : ℝ)),
      Integrable (fun y => k (pointSub x y) * (g y : ℂ)) volume := by
    intro n
    have hK : IsCompact (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace
        ((0 : Vec3), (0 : ℝ)) (n : ℝ)) := compact_parabolicMetricClosedBall'
    exact (kernel_product_integrableOn_of_compact hk hkm hg hgc hK).prod_right_ae
  have hae' : ∀ n : ℕ, ∀ᵐ x ∂volume,
      x ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace
        ((0 : Vec3), (0 : ℝ)) (n : ℝ) →
        Integrable (fun y => k (pointSub x y) * (g y : ℂ)) volume := by
    intro n
    exact (ae_restrict_iff' measurableSet_closedBall).1 (hae n)
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      x ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace
        ((0 : Vec3), (0 : ℝ)) (n : ℝ) →
        Integrable (fun y => k (pointSub x y) * (g y : ℂ)) volume :=
    ae_all_iff.2 hae'
  filter_upwards [hall] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (dist x ((0 : Vec3), (0 : ℝ)))
  exact hx n ((mem_closedBall).2 hn.le)

end CKN.Core.HeatPotential
