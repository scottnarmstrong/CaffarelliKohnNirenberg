-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelBoundsAssembly
import CKN.Foundation.Parabolic.Morrey.Kernel
import CKN.Foundation.Parabolic.Topology

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

private lemma localKernelConstant_one_lt_top :
    parabolicLocalKernelConstant 1 < ∞ := by
  unfold parabolicLocalKernelConstant
  have hterm (n : ℕ) :
      ENNReal.ofReal (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ (1 : ℝ)) =
        (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
    rw [Real.rpow_one, Int.cast_negSucc,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity)]
    have hpow : ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) =
        (2 : ℝ≥0∞) ^ (n + 1) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num
    rw [hpow]
    exact @ENNReal.inv_pow (2 : ℝ≥0∞) (n + 1)
  have hsum : (∑' n : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ (1 : ℝ))) < ∞ := by
    simp only [show (fun n : ℕ => ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ (1 : ℝ))) =
      (fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ (n + 1)) by
        funext n
        exact hterm n]
    rw [ENNReal.tsum_geometric_add_one]
    apply ENNReal.mul_lt_top
    · apply ENNReal.inv_lt_top.2
      norm_num
    · apply ENNReal.inv_lt_top.2
      norm_num
  have hconst : (ENNReal.ofReal (2 ^ 5) *
      (ENNReal.ofReal (2 ^ 5) * volume (parabolicCylinder 0 0 1))) < ∞ := by
    apply ENNReal.mul_lt_top
    · exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
    · apply ENNReal.mul_lt_top
      · exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
      · exact CKN.Foundation.Parabolic.Integration.volume_parabolicCylinder_lt_top
  exact ENNReal.mul_lt_top hconst hsum

private lemma integrableOn_parabolicRho_neg_four {z : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) :
    IntegrableOn (fun w : ParabolicPoint => parabolicRho₂ z w ^ (-4 : ℝ))
      {w | parabolicRho₂ z w < R} volume := by
  have hle := parabolicRieszKernel_local_le (β := (1 : ℝ))
    (by norm_num) (by norm_num) hR z
  have hRpow : ENNReal.ofReal (R ^ (1 : ℝ)) < ∞ := by finiteness
  have hfin : (∫⁻ w in {w | parabolicRho₂ z w < R},
      parabolicRieszKernel 1 z w) < ∞ := by
    exact hle.trans_lt (ENNReal.mul_lt_top localKernelConstant_one_lt_top hRpow)
  have hkernel : Measurable
      (fun w : ParabolicPoint => parabolicRieszKernel 1 z w) := by
    unfold parabolicRieszKernel
    have ho : Measurable (fun w : ParabolicPoint =>
        ENNReal.ofReal (parabolicRho₂ z w)) :=
      (measurable_parabolicRho₂ z).ennreal_ofReal
    fun_prop
  have hmeas : AEMeasurable (fun w : ParabolicPoint =>
      parabolicRieszKernel 1 z w)
      (volume.restrict {w | parabolicRho₂ z w < R}) :=
    hkernel.aemeasurable.restrict
  have hiE : Integrable (fun w : ParabolicPoint =>
      (parabolicRieszKernel 1 z w).toReal)
      (volume.restrict {w | parabolicRho₂ z w < R}) :=
    integrable_toReal_of_lintegral_ne_top hmeas (ne_of_lt hfin)
  change Integrable (fun w : ParabolicPoint =>
      parabolicRho₂ z w ^ (-4 : ℝ))
    (volume.restrict {w | parabolicRho₂ z w < R})
  convert hiE using 1
  funext w
  unfold parabolicRieszKernel
  simp only [show -(5 - (1 : ℝ)) = -(4 : ℝ) by norm_num]
  rw [← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_ofReal (parabolicRho₂_nonneg z w)]

private lemma rpow_neg_four_le_of_le_mul {m ρ : ℝ}
    (hm : 0 < m) (hρ : 0 < ρ) (hρm : ρ ≤ 2 * m) :
    m ^ (-4 : ℝ) ≤ 16 * ρ ^ (-4 : ℝ) := by
  rw [Real.rpow_neg hm.le, Real.rpow_neg hρ.le]
  have hp : ρ ^ (4 : ℝ) ≤ (2 * m) ^ (4 : ℝ) := by
    exact Real.rpow_le_rpow hρ.le hρm (by norm_num)
  have hi : ((2 * m) ^ (4 : ℝ))⁻¹ ≤ (ρ ^ (4 : ℝ))⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hp
  calc
    (m ^ (4 : ℝ))⁻¹ = 16 * ((2 * m) ^ (4 : ℝ))⁻¹ := by
      rw [Real.mul_rpow (by norm_num) hm.le]
      norm_num
      field_simp
    _ ≤ 16 * (ρ ^ (4 : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hi (by norm_num)

theorem measurable_spatialMultiplierHeatKernel {σ : Vec3 → ℂ}
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    Measurable (fun z : ParabolicPoint =>
      spatialMultiplierHeatKernel σ z.1 z.2) := by
  obtain ⟨C, hC, hB⟩ :=
    exists_spatialMultiplierHeatKernel_bounds_of_degreeOne σ hσ hhom
  let T : Set ℝ := {t | 0 < t}
  let kpos : T → Vec3 → ℂ := fun t x =>
    spatialMultiplierHeatKernel σ x t.1
  have htime : ∀ x : Vec3, Continuous (fun t : T => kpos t x) := by
    intro x
    rw [continuous_iff_continuousAt]
    intro t
    exact ((hB x t.1 t.2).2.1.continuousAt).comp continuousAt_subtype_val
  have hspace : ∀ t : T, Measurable (kpos t) := by
    intro t
    exact (continuous_iff_continuousAt.2 (fun x =>
      (hB x t.1 t.2).1.continuousAt)).measurable
  have huncurry : Measurable (Function.uncurry kpos) :=
    measurable_uncurry_of_continuous_of_measurable htime hspace
  let tpos : ParabolicPoint → ℝ := fun z => if 0 < z.2 then z.2 else 1
  have htpos : ∀ z : ParabolicPoint, 0 < tpos z := by
    intro z
    dsimp [tpos]
    split <;> positivity
  have hmtpos : Measurable tpos := by
    dsimp [tpos]
    exact Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
      measurable_snd measurable_const
  have hsub : Measurable (fun z : ParabolicPoint =>
      (⟨tpos z, htpos z⟩ : T)) := hmtpos.subtype_mk
  have hmap : Measurable (fun z : ParabolicPoint =>
      ((⟨tpos z, htpos z⟩ : T), z.1)) := hsub.prod measurable_fst
  have hext : Measurable (fun z : ParabolicPoint =>
      Function.uncurry kpos ((⟨tpos z, htpos z⟩ : T), z.1)) :=
    huncurry.comp hmap
  have hpiece : Measurable (fun z : ParabolicPoint =>
      if 0 < z.2 then
        Function.uncurry kpos ((⟨tpos z, htpos z⟩ : T), z.1)
      else 0) :=
    Measurable.ite (measurableSet_Ioi.preimage measurable_snd) hext measurable_const
  have heq : (fun z : ParabolicPoint =>
      spatialMultiplierHeatKernel σ z.1 z.2) =
      (fun z : ParabolicPoint =>
        if 0 < z.2 then
          Function.uncurry kpos ((⟨tpos z, htpos z⟩ : T), z.1)
        else 0) := by
    funext z
    by_cases hz : 0 < z.2
    · simp [kpos, tpos, hz]
    · rw [spatialMultiplierHeatKernel_of_nonpos σ z.1 (le_of_not_gt hz)]
      simp [hz]
  rw [heq]
  exact hpiece

private lemma spatialMultiplierHeatKernel_norm_le_riesz {σ : Vec3 → ℂ}
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicPoint,
      ‖spatialMultiplierHeatKernel σ z.1 z.2‖ ≤
        16 * C * parabolicRho₂ (0, 0) z ^ (-4 : ℝ) := by
  obtain ⟨C, hC, hB⟩ :=
    exists_spatialMultiplierHeatKernel_bounds_of_degreeOne σ hσ hhom
  refine ⟨C, hC, ?_⟩
  intro z
  by_cases hz : 0 < z.2
  · let m : ℝ := max (vec3EuclideanNorm z.1) (Real.sqrt z.2)
    let ρ : ℝ := parabolicRho₂ (0, 0) z
    have hm : 0 < m := by
      dsimp [m]
      exact (Real.sqrt_pos.2 hz).trans_le (le_max_right _ _)
    have hρ : 0 < ρ := by
      dsimp [ρ, parabolicRho₂]
      have htime : Real.sqrt |(0, 0).2 - z.2| = Real.sqrt z.2 := by
        rw [show (0, 0).2 - z.2 = -z.2 by ring, abs_neg,
          abs_of_pos hz]
      have hneg : vec3EuclideanNorm ((0 : Vec3) - z.1) =
          vec3EuclideanNorm z.1 := by
        unfold vec3EuclideanNorm
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.sub_apply, Pi.zero_apply, zero_sub]
        ring
      rw [htime, hneg]
      exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hz)
        (vec3EuclideanNorm_nonneg _)
    have hρm : ρ ≤ 2 * m := by
      dsimp [ρ, parabolicRho₂, m]
      have htime : Real.sqrt |(0, 0).2 - z.2| = Real.sqrt z.2 := by
        rw [show (0, 0).2 - z.2 = -z.2 by ring, abs_neg,
          abs_of_pos hz]
      have hneg : vec3EuclideanNorm ((0 : Vec3) - z.1) =
          vec3EuclideanNorm z.1 := by
        unfold vec3EuclideanNorm
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.sub_apply, Pi.zero_apply, zero_sub]
        ring
      rw [htime, hneg]
      calc
        Real.sqrt z.2 + vec3EuclideanNorm z.1 ≤
            max (vec3EuclideanNorm z.1) (Real.sqrt z.2) +
              max (vec3EuclideanNorm z.1) (Real.sqrt z.2) :=
          add_le_add (le_max_right _ _) (le_max_left _ _)
        _ = 2 * max (vec3EuclideanNorm z.1) (Real.sqrt z.2) := by ring
    have hscale := rpow_neg_four_le_of_le_mul hm hρ hρm
    have hpoint := (hB z.1 z.2 hz).2.2.1
    calc
      ‖spatialMultiplierHeatKernel σ z.1 z.2‖ ≤ C * m ^ (-4 : ℝ) := by
        simpa [m] using hpoint
      _ ≤ C * (16 * ρ ^ (-4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hscale hC
      _ = 16 * C * parabolicRho₂ (0, 0) z ^ (-4 : ℝ) := by
        dsimp [ρ]
        ring
  · rw [spatialMultiplierHeatKernel_of_nonpos σ z.1 (le_of_not_gt hz)]
    simp only [norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (Real.rpow_nonneg (parabolicRho₂_nonneg (0, 0) z) _)

/-- The degree-one multiplier heat kernel is locally integrable in space-time.

The proof combines the positive-time order-four estimate from the assembled kernel
bounds with the order-one local parabolic Riesz estimate. -/
private lemma locallyIntegrable_spatialMultiplierHeatKernel_parabolic {σ : Vec3 → ℂ}
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    LocallyIntegrable (fun z : ParabolicPoint =>
      spatialMultiplierHeatKernel σ z.1 z.2) volume := by
  have hmeas := measurable_spatialMultiplierHeatKernel hσ hhom
  obtain ⟨C, hC, hdom⟩ := spatialMultiplierHeatKernel_norm_le_riesz hσ hhom
  intro p
  let top : ℝ := p.2 + 1 / 2
  let cyl : Set ParabolicPoint := parabolicCylinder p.1 top 1
  let small : Set ParabolicPoint :=
    {z | parabolicRho₂ (0, 0) z < 1}
  let big : Set ParabolicPoint :=
    {z | 1 ≤ parabolicRho₂ (0, 0) z} ∩ cyl
  have hsmallRiesz : IntegrableOn
      (fun z : ParabolicPoint => parabolicRho₂ (0, 0) z ^ (-4 : ℝ)) small volume := by
    exact integrableOn_parabolicRho_neg_four (z := (0, 0)) (R := 1) (by norm_num)
  have hsmall : IntegrableOn
      (fun z : ParabolicPoint => spatialMultiplierHeatKernel σ z.1 z.2) small volume := by
    change Integrable (fun z : ParabolicPoint =>
      spatialMultiplierHeatKernel σ z.1 z.2) (volume.restrict small)
    have hmajor : Integrable (fun z : ParabolicPoint =>
        16 * C * parabolicRho₂ (0, 0) z ^ (-4 : ℝ))
        (volume.restrict small) := by
      exact hsmallRiesz.integrable.const_mul (16 * C)
    exact hmajor.mono' hmeas.aestronglyMeasurable.restrict
      (ae_restrict_of_ae (ae_of_all volume (fun z => hdom z)))
  have hcyl : volume cyl < ∞ := by
    dsimp [cyl]
    exact CKN.Foundation.Parabolic.Integration.volume_parabolicCylinder_lt_top
  have hbigmeas : MeasurableSet big := by
    dsimp [big, cyl, small]
    have hnorm : Measurable (fun y : Vec3 =>
        vec3EuclideanNorm (y - p.1)) := by
      have hvec : Measurable vec3EuclideanNorm := by
        rw [show vec3EuclideanNorm =
            (fun v : Vec3 => ‖WithLp.toLp 2 v‖) by
              funext v
              exact vec3EuclideanNorm_eq_l2 v]
        exact (continuous_norm.comp
          (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ))).measurable
      exact hvec.comp (measurable_id.sub measurable_const)
    have hball : MeasurableSet (vec3Ball p.1 1) :=
      measurableSet_lt hnorm measurable_const
    have hcylmeas : MeasurableSet (parabolicCylinder p.1 top 1) := by
      rw [parabolicCylinder]
      exact hball.prod measurableSet_Ioc
    exact (measurableSet_le measurable_const
      (measurable_parabolicRho₂ (0, 0))).inter hcylmeas
  have hbigmeasure : volume big < ∞ := by
    apply lt_of_le_of_lt (measure_mono inter_subset_right) hcyl
  have hbig : IntegrableOn
      (fun z : ParabolicPoint => spatialMultiplierHeatKernel σ z.1 z.2) big volume := by
    change Integrable (fun z : ParabolicPoint =>
      spatialMultiplierHeatKernel σ z.1 z.2) (volume.restrict big)
    have hconst : Integrable (fun _ : ParabolicPoint => (16 * C : ℝ))
        (volume.restrict big) := by
      exact integrableOn_const (ne_of_lt hbigmeasure)
    apply hconst.mono' hmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem hbigmeas] with z hz
    exact (hdom z).trans (by
      have hrho : 1 ≤ parabolicRho₂ (0, 0) z := hz.1
      have hpow : parabolicRho₂ (0, 0) z ^ (-4 : ℝ) ≤ (1 : ℝ) := by
        rw [Real.rpow_neg (parabolicRho₂_nonneg (0, 0) z)]
        exact (inv_le_one₀ (by positivity)).2
          (Real.one_le_rpow hrho (by norm_num))
      nlinarith only [hpow, hC, mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hC])
  have hunion : IntegrableOn
      (fun z : ParabolicPoint => spatialMultiplierHeatKernel σ z.1 z.2)
      (small ∪ big) volume := hsmall.union hbig
  have hsub : cyl ⊆ small ∪ big := by
    intro z hz
    by_cases hsmall' : parabolicRho₂ (0, 0) z < 1
    · exact Or.inl hsmall'
    · exact Or.inr ⟨le_of_not_gt hsmall', hz⟩
  have hcyl' := hunion.mono_set hsub
  have hball := metricBall_subset_parabolicCylinder (x := p.1)
    (t := top) (r := 1) (by norm_num)
  have hcenter : (p.1, top - (1 : ℝ) ^ 2 / 2) = p := by
    apply Prod.ext
    · rfl
    · dsimp [top]
      ring_nf
  rw [hcenter] at hball
  exact ⟨@Metric.ball ParabolicPoint parabolicPseudoMetricSpace p (1 / 2 : ℝ),
    @Metric.ball_mem_nhds ParabolicPoint parabolicPseudoMetricSpace p
      (1 / 2 : ℝ) (by norm_num), hcyl'.mono_set hball⟩

theorem locallyIntegrable_spatialMultiplierHeatKernel {σ : Vec3 → ℂ}
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    LocallyIntegrable (fun z : Vec3 × ℝ =>
      spatialMultiplierHeatKernel σ z.1 z.2) volume := by
  have hpar := locallyIntegrable_spatialMultiplierHeatKernel_parabolic hσ hhom
  intro z
  rcases hpar (parabolicHomeomorph.symm z) with ⟨U, hU, hInt⟩
  refine ⟨parabolicHomeomorph '' U, ?_, ?_⟩
  · have h := parabolicHomeomorph.isOpenMap.image_mem_nhds hU
    change parabolicHomeomorph '' U ∈
      𝓝 (parabolicHomeomorph (parabolicHomeomorph.symm z))
    simpa using h
  · have himg : parabolicHomeomorph '' U = U := by
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp
      · intro hw
        exact ⟨w, hw, rfl⟩
    rw [himg]
    exact hInt

end CKN.Foundation.Euclidean
