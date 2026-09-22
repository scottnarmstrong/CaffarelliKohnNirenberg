-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.PotentialFiniteness
import CKN.Core.HeatPotential.MorreySources
import CKN.Core.Step4.SourceMorreyData
import CKN.Foundation.Parabolic.Morrey.Minkowski
import CKN.Foundation.Parabolic.Integration.SingletonNull

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Step4

private lemma compact_support_in_cylinder {F : ParabolicPoint → ℝ}
    (hF : HasCompactSupport F) :
    ∃ (R T : ℝ), 0 < R ∧ tsupport F ⊆ parabolicCylinder 0 T R := by
  let o : ParabolicPoint := ((0 : Vec3), (0 : ℝ))
  have hb : Bornology.IsBounded (tsupport F) :=
    (show IsCompact (tsupport F) from hF).isBounded
  rcases (@Metric.isBounded_iff_subset_closedBall ParabolicPoint
    (tsupport F) parabolicPseudoMetricSpace o).mp hb with ⟨R, hR⟩
  let S : ℝ := max R 0 + 1
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hsubset : tsupport F ⊆ Metric.closedBall o S := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    apply (Metric.mem_closedBall.mp (hR hz)).trans
    dsimp [S]
    exact le_max_left R 0 |>.trans (le_add_of_nonneg_right (by norm_num))
  let T : ℝ := S ^ 2 + 1
  let A : ℝ := 2 * S + 2
  refine ⟨A, T, ?_, ?_⟩
  · dsimp [A]
    positivity
  intro z hz
  have hzball : dist z o ≤ S := Metric.mem_closedBall.mp (hsubset hz)
  have hzpar : parabolicDist z o ≤ S := by
    rw [← dist_eq_parabolicDist z o]
    exact hzball
  have hmax : max (vec3EuclideanNorm z.1) (Real.sqrt |z.2|) ≤ S := by
    simpa [o, parabolicDist, sub_zero] using hzpar
  have hspace : vec3EuclideanNorm (z.1 - 0) < A := by
    change vec3EuclideanNorm (z.1 - 0) < 2 * S + 2
    have hnorm : vec3EuclideanNorm z.1 ≤ S := (max_le_iff.mp hmax).1
    calc
      vec3EuclideanNorm (z.1 - 0) = vec3EuclideanNorm z.1 := by simp
      _ ≤ S := hnorm
      _ < 2 * S + 2 := by nlinarith only [hS]
  have htimeabs : Real.sqrt |z.2| ≤ S := (max_le_iff.mp hmax).2
  have htime : -S ^ 2 ≤ z.2 ∧ z.2 ≤ S ^ 2 := by
    have hsqrt : (Real.sqrt |z.2|) ^ 2 = |z.2| :=
      Real.sq_sqrt (abs_nonneg _)
    have habs : |z.2| ≤ S ^ 2 := by
      nlinarith only [hsqrt, htimeabs, Real.sqrt_nonneg (|z.2|), hS,
        sq_nonneg (Real.sqrt |z.2|)]
    exact abs_le.mp habs
  dsimp [T, A]
  refine ⟨hspace, ?_, ?_⟩
  · nlinarith only [htime.1, hS]
  · nlinarith only [htime.2, hS]

private lemma morreyNorm_congr_ae {P θ : ℝ} {F G : ParabolicPoint → ℝ}
    (hFG : F =ᵐ[volume] G) : morreyNorm P θ F = morreyNorm P θ G := by
  unfold morreyNorm
  congr 1
  funext z
  congr 1
  funext r
  unfold morreyCell cylinderPowerIntegral
  congr 2
  apply lintegral_congr_ae
  filter_upwards [hFG.filter_mono ae_restrict_le] with w hw
  simp only [hw]

private lemma vec3_norm_le_sum_abs_source (v : Vec3) :
    vec3EuclideanNorm v ≤ ∑ i, |v i| := by
  rw [vec3EuclideanNorm]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg fun i _ => abs_nonneg (v i)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) ≤
      (|v 0| + (|v 1| + |v 2|)) ^ 2
    nlinarith only [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]

private lemma riesz_two_finite {z w : ParabolicPoint}
    (hρ : 0 < parabolicRho₂ z w) : parabolicRieszKernel 2 z w ≠ ∞ := by
  unfold parabolicRieszKernel
  rw [show -(5 - (2 : ℝ)) = -(3 : ℝ) by norm_num, ENNReal.rpow_neg]
  apply ENNReal.inv_ne_top.mpr
  intro hz
  have hbase : ENNReal.ofReal (parabolicRho₂ z w) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hρ).ne'
  rcases ENNReal.rpow_eq_zero_iff.mp hz with h | h
  · exact hbase h.1
  · exact ENNReal.ofReal_ne_top h.1

private lemma riesz_one_finite {z w : ParabolicPoint}
    (hρ : 0 < parabolicRho₂ z w) : parabolicRieszKernel 1 z w ≠ ∞ := by
  unfold parabolicRieszKernel
  rw [show -(5 - (1 : ℝ)) = -(4 : ℝ) by norm_num, ENNReal.rpow_neg]
  apply ENNReal.inv_ne_top.mpr
  intro hz
  have hbase : ENNReal.ofReal (parabolicRho₂ z w) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hρ).ne'
  rcases ENNReal.rpow_eq_zero_iff.mp hz with h | h
  · exact hbase h.1
  · exact ENNReal.ofReal_ne_top h.1

private lemma ofReal_riesz_two_mul_abs {z w : ParabolicPoint} {a : ℝ}
    (hρ : 0 < parabolicRho₂ z w) :
    ENNReal.ofReal ((parabolicRieszKernel 2 z w).toReal * |a|) =
      parabolicRieszKernel 2 z w * ENNReal.ofReal |a| := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  rw [ENNReal.ofReal_toReal (riesz_two_finite hρ)]

private lemma ofReal_riesz_one_mul_abs {z w : ParabolicPoint} {a : ℝ}
    (hρ : 0 < parabolicRho₂ z w) :
    ENNReal.ofReal ((parabolicRieszKernel 1 z w).toReal * |a|) =
      parabolicRieszKernel 1 z w * ENNReal.ofReal |a| := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  rw [ENNReal.ofReal_toReal (riesz_one_finite hρ)]

private lemma riesz_potential_ae_of_measurable_data
    {β : ℝ} (hβ : 0 < β) (hβ5 : β < 5) (hβ2 : β * 2 < 5)
    {P : ℝ} (hP : 1 < P) {F : ParabolicPoint → ℝ}
    (hF : Measurable F)
    (hglobal : (∫⁻ z, ENNReal.ofReal |F z| ^ P) < ∞)
    (hN1 : morreyNorm 1 2 F < ∞) :
    ∀ᵐ z, parabolicRieszPotential β F z < ∞ := by
  have hmax := lintegral_rpow_parabolicMaximalFunction_ofReal_le
    F hF hP hglobal
  have hmax' : (∫⁻ z, parabolicMaximalFunction
      (fun z => ENNReal.ofReal |F z|) z ^ P) < ∞ := by
    simpa only [Real.norm_eq_abs] using hmax.trans_lt (ENNReal.mul_lt_top
      (CKN.Core.Endgame.maximal_strong_constant_lt_top hP) hglobal)
  have hmaxae : ∀ᵐ z, parabolicMaximalMajorant F z < ∞ := by
    have hmeas := (measurable_parabolicMaximalFunction
      (fun z => ENNReal.ofReal |F z|)).pow_const P
    filter_upwards [ae_lt_top hmeas hmax'.ne] with z hz
    exact (ENNReal.rpow_lt_top_iff_of_pos (lt_trans zero_lt_one hP)).mp hz
  have hbound : ∀ z, parabolicRieszPotential β F z ≤
      parabolicHedbergNearConstant β * parabolicMaximalMajorant F z +
        parabolicTailKernelConstant β 2 * morreyNorm 1 2 F := by
    intro z
    have hscale := parabolicRieszPotential_scale_le hβ hβ5
      (by norm_num) hβ2 (R := 1) one_pos hF.aemeasurable
      (isParabolicMaximalMajorant_parabolicMaximalMajorant F) z
    simpa using hscale
  exact hmaxae.mono (fun z hz => (hbound z).trans_lt (ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (CKN.Core.Endgame.hedberg_near_constant_lt_top hβ) hz,
      ENNReal.mul_lt_top
        (CKN.Core.Endgame.tail_kernel_constant_lt_top (by norm_num) hβ2)
        hN1⟩))

private lemma riesz_integrable_of_potential_ae
    {β : ℝ} (hβ : β = 1 ∨ β = 2)
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    {z : ParabolicPoint} (hpot : parabolicRieszPotential β F z < ∞) :
    Integrable (fun w => (parabolicRieszKernel β z w).toReal * |F w|)
      volume := by
  let K : ParabolicPoint → ℝ≥0∞ := fun w =>
    parabolicRieszKernel β z w * ENNReal.ofReal |F w|
  have hKm : AEMeasurable K volume := by
    have hKbase : Measurable (fun w => parabolicRieszKernel β z w) := by
      unfold parabolicRieszKernel
      exact ENNReal.continuous_rpow_const.measurable.comp
        (ENNReal.measurable_ofReal.comp (measurable_parabolicRho₂ z))
    dsimp [K]
    exact hKbase.aemeasurable.mul hF.norm.ennreal_ofReal
  have hKint : Integrable (fun w => (K w).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hKm (by
      change parabolicRieszPotential β F z ≠ ∞
      exact ne_of_lt hpot)
  have hKae : (fun w => (K w).toReal) =ᵐ[volume]
      (fun w => (parabolicRieszKernel β z w).toReal * |F w|) := by
    have hzero : volume {w : ParabolicPoint | parabolicRho₂ z w = 0} = 0 :=
      measure_mono_null (parabolicRho₂_zero_subset_singleton z)
        (CKN.Foundation.Parabolic.Integration.volume_singleton_parabolicPoint z)
    have hae : ∀ᵐ w : ParabolicPoint, parabolicRho₂ z w ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using hzero
    filter_upwards [hae] with w hw
    have hρ : 0 < parabolicRho₂ z w :=
      lt_of_le_of_ne (parabolicRho₂_nonneg z w) (Ne.symm hw)
    rcases hβ with rfl | rfl
    · have heq := ofReal_riesz_one_mul_abs hρ (a := F w)
      change (parabolicRieszKernel 1 z w * ENNReal.ofReal |F w|).toReal = _
      rw [← heq, ENNReal.toReal_ofReal]
      positivity
    · have heq := ofReal_riesz_two_mul_abs hρ (a := F w)
      change (parabolicRieszKernel 2 z w * ENNReal.ofReal |F w|).toReal = _
      rw [← heq, ENNReal.toReal_ofReal]
      positivity
  exact hKint.congr hKae

private lemma compact_morrey_power_integral
    {θ : ℝ} {F : ParabolicPoint → ℝ}
    (hF : AEMeasurable F volume) (hN : morreyNorm (6 / 5 : ℝ) θ F < ∞)
    (hSupport : HasCompactSupport F) :
    ∃ (R T : ℝ), 0 < R ∧
      (∀ w ∉ parabolicCylinder 0 T R, F w = 0) ∧
    (∫⁻ z, ENNReal.ofReal |F z| ^ (6 / 5 : ℝ)) < ∞ := by
  obtain ⟨R, T, hR, hT⟩ := compact_support_in_cylinder hSupport
  have hglobal := CKN.Core.Endgame.source_power_integral_lt_top
    (P := (6 / 5 : ℝ)) (τ := θ) (R := R)
    (z₀ := ((0 : Vec3), T)) (by norm_num) hR hF hN
    (fun w hw => image_eq_zero_of_notMem_tsupport (by
      intro htw
      exact hw (hT htw)))
  exact ⟨R, T, hR, fun w hw => image_eq_zero_of_notMem_tsupport (by
    intro htw
    exact hw (hT htw)), hglobal⟩

private lemma morrey_two_of_compact_morrey
    {θ : ℝ} (hPθ : (6 / 5 : ℝ) ≤ θ)
    (h2θ : 2 ≤ θ)
    {F : ParabolicPoint → ℝ} (hN : morreyNorm (6 / 5 : ℝ) θ F < ∞)
    {R T : ℝ} (hR : 0 < R)
    (hSupport : ∀ w ∉ parabolicCylinder 0 T R, F w = 0) :
    morreyNorm (6 / 5 : ℝ) 2 F < ∞ := by
  have hlow := morreyNorm_lower_morrey_exponent (p := (6 / 5 : ℝ)) (q := θ)
    (q' := (2 : ℝ)) (z₀ := ((0 : Vec3), T)) (R := R)
    (by norm_num) hPθ (by norm_num) h2θ hR hSupport
  have hθpos : 0 < θ := lt_of_lt_of_le (by norm_num) hPθ
  have hθinv : 1 / θ ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) h2θ
  have hexp : 0 ≤ 5 * (1 / 2 - 1 / θ) := by
    nlinarith only [hθinv]
  exact hlow.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hexp ENNReal.ofReal_ne_top) hN)

private lemma morrey_one_two_of_morrey_two
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    (hN : morreyNorm (6 / 5 : ℝ) 2 F < ∞) :
    morreyNorm 1 2 F < ∞ := by
  have hlow := morreyNorm_lower_p (p' := 1) (p := (6 / 5 : ℝ)) (q := (2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hF
  have hvol : volume (parabolicCylinder 0 0 1) < ∞ :=
    Integration.volume_parabolicCylinder_lt_top
  have hpow : volume (parabolicCylinder 0 0 1) ^
      (1 / (1 : ℝ) - 1 / (6 / 5 : ℝ)) < ∞ := by
    apply ENNReal.rpow_lt_top_of_nonneg
    · have hp : 1 / (6 / 5 : ℝ) ≤ (1 : ℝ) :=
        (div_le_one (by norm_num : (0 : ℝ) < 6 / 5)).mpr (by norm_num)
      linarith only [hp]
    · exact hvol.ne
  exact lt_of_le_of_lt hlow (ENNReal.mul_lt_top hpow hN)

private lemma riesz_potential_ae_of_morrey
    {β θ : ℝ} (hβ : β = 1 ∨ β = 2)
    (hPθ : (6 / 5 : ℝ) ≤ θ) (h2θ : 2 ≤ θ) (hβθ : β * 2 < 5)
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    (hN : morreyNorm (6 / 5 : ℝ) θ F < ∞)
    (hSupport : HasCompactSupport F) :
    ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      parabolicRieszPotential β F z < ∞ := by
  obtain ⟨R, T, hR, hSupport', hglobal⟩ :=
    compact_morrey_power_integral hF hN hSupport
  let Fm : ParabolicPoint → ℝ := hF.mk F
  have hFm : Measurable Fm := hF.measurable_mk
  have hFFm : F =ᵐ[volume] Fm := hF.ae_eq_mk
  have hglobalm : (∫⁻ z, ENNReal.ofReal |Fm z| ^ (6 / 5 : ℝ)) < ∞ := by
    have hpowae : (fun z => ENNReal.ofReal |F z| ^ (6 / 5 : ℝ)) =ᵐ[volume]
        (fun z => ENNReal.ofReal |Fm z| ^ (6 / 5 : ℝ)) := by
      filter_upwards [hFFm] with z hz
      simp [hz]
    rw [← lintegral_congr_ae hpowae]
    simpa only [Real.norm_eq_abs] using hglobal
  have hN2 : morreyNorm (6 / 5 : ℝ) 2 Fm < ∞ := by
    have heqN : morreyNorm (6 / 5 : ℝ) 2 F =
        morreyNorm (6 / 5 : ℝ) 2 Fm :=
      morreyNorm_congr_ae hFFm
    rw [← heqN]
    exact morrey_two_of_compact_morrey hPθ h2θ hN hR hSupport'
  have hN1 : morreyNorm 1 2 Fm < ∞ :=
    morrey_one_two_of_morrey_two hFm.aemeasurable hN2
  have hpota := riesz_potential_ae_of_measurable_data
    (β := β) (P := (6 / 5 : ℝ)) (F := Fm)
    (by rcases hβ with rfl | rfl <;> norm_num)
    (by rcases hβ with rfl | rfl <;> norm_num) hβθ (by norm_num)
    hFm hglobalm hN1
  filter_upwards [hpota] with z hz
  have heq : parabolicRieszPotential β F z =
      parabolicRieszPotential β Fm z := by
    unfold parabolicRieszPotential
    apply lintegral_congr_ae
    filter_upwards [hFFm] with w hw
    simp [hw]
  rw [heq]
  exact hz

private lemma riesz_pairing_ae_of_morrey
    {β θ : ℝ} (hβ : β = 1 ∨ β = 2)
    (hPθ : (6 / 5 : ℝ) ≤ θ) (h2θ : 2 ≤ θ) (hβθ : β * 2 < 5)
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    (hN : morreyNorm (6 / 5 : ℝ) θ F < ∞)
    (hSupport : HasCompactSupport F) :
    ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      Integrable (fun w => (parabolicRieszKernel β z w).toReal * |F w|)
        volume := by
  have hp := riesz_potential_ae_of_morrey hβ hPθ h2θ hβθ hF hN hSupport
  filter_upwards [hp] with z hz
  exact riesz_integrable_of_potential_ae hβ hF hz

/-- The ENNReal potential-finiteness interface used by the pointwise
comparison.  In particular, this exports an almost-everywhere statement and
does not ask for a kernel pairing at every evaluation point. -/
theorem source_riesz_potential_ae_of_morrey
    {β P τ R : ℝ} (hβ : 0 < β) (hP : 1 < P)
    (hPτ : P ≤ τ) (hβτ : β * τ < 5) (hR : 0 < R)
    {z₀ : ParabolicPoint} {F : ParabolicPoint → ℝ}
    (hF : AEMeasurable F volume) (hN : morreyNorm P τ F < ∞)
    (hSupport : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, F z = 0) :
    ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      parabolicRieszPotential β F z < ∞ := by
  exact CKN.Core.Endgame.riesz_potential_ae_lt_top_of_aemeasurable_morrey
    hβ hP hPτ hβτ hR hF hN hSupport

/-- Componentwise source data can be consumed directly by the a.e. potential
interface after the Euclidean source norm and its support have been supplied.
The two orders are kept explicit because the heat and spatial kernels have
different singularity orders. -/
theorem source_vector_riesz_potential_ae_of_morrey
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {P₀ τ₀ P₁ τ₁ R₀ R₁ : ℝ}
    {z₀₀ z₀₁ : ParabolicPoint}
    (hβ₀ : 0 < (2 : ℝ)) (hP₀ : 1 < P₀) (hP₀τ₀ : P₀ ≤ τ₀)
    (hβ₀τ₀ : (2 : ℝ) * τ₀ < 5) (hR₀ : 0 < R₀)
    (hβ₁ : 0 < (1 : ℝ)) (hP₁ : 1 < P₁) (hP₁τ₁ : P₁ ≤ τ₁)
    (hβ₁τ₁ : (1 : ℝ) * τ₁ < 5) (hR₁ : 0 < R₁)
    (hg : AEMeasurable (fun z => vec3EuclideanNorm (g z)) volume)
    (hh : ∀ j, AEMeasurable (fun z => vec3EuclideanNorm (h j z)) volume)
    (hNg : morreyNorm P₀ τ₀
      (fun z => vec3EuclideanNorm (g z)) < ∞)
    (hNh : ∀ j, morreyNorm P₁ τ₁
      (fun z => vec3EuclideanNorm (h j z)) < ∞)
    (hsg : ∀ z ∉ parabolicCylinder z₀₀.1 z₀₀.2 R₀,
      vec3EuclideanNorm (g z) = 0)
    (hsh : ∀ j z, z ∉ parabolicCylinder z₀₁.1 z₀₁.2 R₁ →
      vec3EuclideanNorm (h j z) = 0) :
    (∀ᵐ z ∂(volume : Measure ParabolicPoint),
      parabolicRieszPotential 2
        (fun w => vec3EuclideanNorm (g w)) z < ∞) ∧
    (∀ j, ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      parabolicRieszPotential 1
        (fun w => vec3EuclideanNorm (h j w)) z < ∞) := by
  constructor
  · exact source_riesz_potential_ae_of_morrey
      (β := (2 : ℝ)) (P := P₀) (τ := τ₀) (R := R₀)
      (z₀ := z₀₀)
      (F := fun z => vec3EuclideanNorm (g z))
      hβ₀ hP₀ hP₀τ₀ hβ₀τ₀ hR₀ hg hNg hsg
  · intro j
    exact source_riesz_potential_ae_of_morrey
      (β := (1 : ℝ)) (P := P₁) (τ := τ₁) (R := R₁)
      (z₀ := z₀₁)
      (F := fun z => vec3EuclideanNorm (h j z))
      hβ₁ hP₁ hP₁τ₁ hβ₁τ₁ hR₁ (hh j) (hNh j) (hsh j)

theorem source_bootstrap_riesz_potential_ae
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hg : AEMeasurable (fun z => vec3EuclideanNorm (g z)) volume)
    (hh : ∀ j, AEMeasurable (fun z => vec3EuclideanNorm (h j z)) volume)
    (hgN : morreyNorm (6 / 5 : ℝ) (25 / 11 : ℝ)
      (fun z => vec3EuclideanNorm (g z)) < ∞)
    (hhN : ∀ j, morreyNorm (3 : ℝ) (25 / 6 : ℝ)
      (fun z => vec3EuclideanNorm (h j z)) < ∞)
    (hgsupp : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R,
      vec3EuclideanNorm (g z) = 0)
    (hhsupp : ∀ j z, z ∉ parabolicCylinder z₀.1 z₀.2 R →
      vec3EuclideanNorm (h j z) = 0) :
    (∀ᵐ z ∂(volume : Measure ParabolicPoint),
      parabolicRieszPotential 2
        (fun w => vec3EuclideanNorm (g w)) z < ∞) ∧
    (∀ j, ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      parabolicRieszPotential 1
        (fun w => vec3EuclideanNorm (h j w)) z < ∞) := by
  exact source_vector_riesz_potential_ae_of_morrey
    (z₀₀ := z₀) (z₀₁ := z₀) (P₀ := (6 / 5 : ℝ))
    (τ₀ := (25 / 11 : ℝ)) (P₁ := (3 : ℝ)) (τ₁ := (25 / 6 : ℝ))
    (R₀ := R) (R₁ := R) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hR (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hR hg hh hgN hhN hgsupp hhsupp

theorem source_riesz_kernel_data_of_morrey
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {θ₀ θ₁ : ℝ}
    (hPθ₀ : (6 / 5 : ℝ) ≤ θ₀) (hPθ₁ : (6 / 5 : ℝ) ≤ θ₁)
    (h2θ₀ : 2 ≤ θ₀) (h2θ₁ : 2 ≤ θ₁)
    (hg : ∀ i : Fin 3, AEMeasurable (fun z => g z i) volume)
    (hh : ∀ j i : Fin 3, AEMeasurable (fun z => h j z i) volume)
    (hNg : ∀ i : Fin 3,
      morreyNorm (6 / 5 : ℝ) θ₀ (fun z => g z i) < ∞)
    (hNh : ∀ j i : Fin 3,
      morreyNorm (6 / 5 : ℝ) θ₁ (fun z => h j z i) < ∞)
    (hsg : ∀ i : Fin 3, HasCompactSupport (fun z => g z i))
    (hsh : ∀ j i : Fin 3, HasCompactSupport (fun z => h j z i)) :
    (∀ᵐ z ∂(volume : Measure ParabolicPoint), ∀ i,
      Integrable (fun w => (parabolicRieszKernel 2 z w).toReal * |g w i|)
        volume) ∧
    (∀ᵐ z ∂(volume : Measure ParabolicPoint), ∀ j i,
      Integrable
        (fun w => (parabolicRieszKernel 1 z w).toReal * |h j w i|)
          volume) ∧
    (∀ᵐ z ∂(volume : Measure ParabolicPoint),
      Integrable
        (fun w => (parabolicRieszKernel 2 z w).toReal *
          vec3EuclideanNorm (g w)) volume) ∧
    (∀ᵐ z ∂(volume : Measure ParabolicPoint), ∀ j,
      Integrable
        (fun w => (parabolicRieszKernel 1 z w).toReal *
          vec3EuclideanNorm (h j w)) volume) := by
  have hg' : ∀ i, ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      Integrable (fun w => (parabolicRieszKernel 2 z w).toReal * |g w i|)
        volume := by
    intro i
    exact riesz_pairing_ae_of_morrey (β := 2) (θ := θ₀)
      (Or.inr rfl) hPθ₀ h2θ₀ (by norm_num) (hg i) (hNg i) (hsg i)
  have hh' : ∀ j i, ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      Integrable
        (fun w => (parabolicRieszKernel 1 z w).toReal * |h j w i|)
          volume := by
    intro j i
    exact riesz_pairing_ae_of_morrey (β := 1) (θ := θ₁)
      (Or.inl rfl) hPθ₁ h2θ₁ (by norm_num) (hh j i) (hNh j i) (hsh j i)
  have hgnorm : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      Integrable
        (fun w => (parabolicRieszKernel 2 z w).toReal *
          vec3EuclideanNorm (g w)) volume := by
    have hga : ∀ᵐ z ∂(volume : Measure ParabolicPoint), ∀ i,
        Integrable
          (fun w => (parabolicRieszKernel 2 z w).toReal * |g w i|)
            volume := by
      rw [ae_all_iff]
      exact hg'
    have hgvec : AEMeasurable g volume := aemeasurable_pi_iff.mpr hg
    filter_upwards [hga] with z hz
    let K : ParabolicPoint → ℝ :=
      fun w => (parabolicRieszKernel 2 z w).toReal
    have hK : AEMeasurable K volume := by
      have hbase : Measurable (fun w => parabolicRieszKernel 2 z w) := by
        unfold parabolicRieszKernel
        exact ENNReal.continuous_rpow_const.measurable.comp
          (ENNReal.measurable_ofReal.comp (measurable_parabolicRho₂ z))
      exact hbase.ennreal_toReal.aemeasurable
    have hnorm : AEMeasurable
        (fun w => vec3EuclideanNorm (g w)) volume := by
      rw [show (fun w => vec3EuclideanNorm (g w)) =
          (fun w => ‖WithLp.toLp 2 (g w)‖) by
            funext w
            exact vec3EuclideanNorm_eq_l2 _]
      exact (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable
        |>.comp_aemeasurable hgvec
    have hsum : Integrable
        (fun w => ∑ i, K w * |g w i|) volume := by
      simpa only [Finset.sum_apply] using
        integrable_finsetSum (Finset.univ : Finset (Fin 3))
          (fun i _ => by simpa [K] using hz i)
    apply hsum.mono' (hK.mul hnorm).aestronglyMeasurable
    filter_upwards [] with w
    change |K w * vec3EuclideanNorm (g w)| ≤
      ∑ i, K w * |g w i|
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    calc
      _ ≤ K w * ∑ i, |g w i| :=
        mul_le_mul_of_nonneg_left
          (vec3_norm_le_sum_abs_source (g w)) (ENNReal.toReal_nonneg)
      _ = ∑ i, K w * |g w i| := by rw [Finset.mul_sum]
  have hhnorm : ∀ᵐ z ∂(volume : Measure ParabolicPoint), ∀ j,
      Integrable
        (fun w => (parabolicRieszKernel 1 z w).toReal *
          vec3EuclideanNorm (h j w)) volume := by
    rw [ae_all_iff]
    intro j
    have hjae : ∀ᵐ z ∂(volume : Measure ParabolicPoint), ∀ i,
        Integrable
          (fun w => (parabolicRieszKernel 1 z w).toReal * |h j w i|)
            volume := by
      rw [ae_all_iff]
      exact hh' j
    have hjvec : AEMeasurable (h j) volume :=
      aemeasurable_pi_iff.mpr (fun i => hh j i)
    filter_upwards [hjae] with z hz
    let K : ParabolicPoint → ℝ :=
      fun w => (parabolicRieszKernel 1 z w).toReal
    have hK : AEMeasurable K volume := by
      have hbase : Measurable (fun w => parabolicRieszKernel 1 z w) := by
        unfold parabolicRieszKernel
        exact ENNReal.continuous_rpow_const.measurable.comp
          (ENNReal.measurable_ofReal.comp (measurable_parabolicRho₂ z))
      exact hbase.ennreal_toReal.aemeasurable
    have hnorm : AEMeasurable
        (fun w => vec3EuclideanNorm (h j w)) volume := by
      rw [show (fun w => vec3EuclideanNorm (h j w)) =
          (fun w => ‖WithLp.toLp 2 (h j w)‖) by
            funext w
            exact vec3EuclideanNorm_eq_l2 _]
      exact (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable
        |>.comp_aemeasurable hjvec
    have hsum : Integrable
        (fun w => ∑ i, K w * |h j w i|) volume := by
      simpa only [Finset.sum_apply] using
        integrable_finsetSum (Finset.univ : Finset (Fin 3))
          (fun i _ => by simpa [K] using hz i)
    apply hsum.mono' (hK.mul hnorm).aestronglyMeasurable
    filter_upwards [] with w
    change |K w * vec3EuclideanNorm (h j w)| ≤
      ∑ i, K w * |h j w i|
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    calc
      _ ≤ K w * ∑ i, |h j w i| :=
        mul_le_mul_of_nonneg_left
          (vec3_norm_le_sum_abs_source (h j w)) (ENNReal.toReal_nonneg)
      _ = ∑ i, K w * |h j w i| := by rw [Finset.mul_sum]
  refine ⟨?_, ?_, hgnorm, hhnorm⟩
  · rw [ae_all_iff]
    exact hg'
  · rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    exact hh' j

theorem source_kernel_pairing_package_of_morrey
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {q : ℝ} (hq : 5 / 2 < q)
    (hg : ∀ i : Fin 3, AEMeasurable (fun z => g z i) volume)
    (hh : ∀ j i : Fin 3,
      AEMeasurable (fun z => h j z i) volume)
    (hNg : ∀ i : Fin 3,
      morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
        (fun z => g z i) < ∞)
    (hNh : ∀ j i : Fin 3,
      morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
        (fun z => h j z i) < ∞)
    (hsg : ∀ i : Fin 3, HasCompactSupport (fun z => g z i))
    (hsh : ∀ j i : Fin 3, HasCompactSupport (fun z => h j z i)) :
    (∀ z i, Integrable
      (fun w => heatPotentialKernel z w * g w i) volume) ∧
    (∀ z j i, Integrable
      (fun w => heatPotentialSpatialKernel j z w * h j w i) volume) ∧
    (∀ᵐ z ∂(volume : Measure ParabolicPoint), ∀ i,
      Integrable
        (fun w => (parabolicRieszKernel 2 z w).toReal * |g w i|)
        volume) ∧
    (∀ᵐ z ∂(volume : Measure ParabolicPoint), ∀ j i,
      Integrable
        (fun w => (parabolicRieszKernel 1 z w).toReal * |h j w i|)
        volume) ∧
    (∀ᵐ z ∂(volume : Measure ParabolicPoint),
      Integrable
        (fun w => (parabolicRieszKernel 2 z w).toReal *
          vec3EuclideanNorm (g w)) volume) ∧
    (∀ᵐ z ∂(volume : Measure ParabolicPoint), ∀ j,
      Integrable
        (fun w => (parabolicRieszKernel 1 z w).toReal *
          vec3EuclideanNorm (h j w)) volume) := by
  have hθ₀ : (6 / 5 : ℝ) ≤ min q (25 / 9 : ℝ) := by
    exact le_min (by linarith only [hq]) (by norm_num)
  have hθ₀₂ : (2 : ℝ) ≤ min q (25 / 9 : ℝ) := by
    exact le_min (by linarith only [hq]) (by norm_num)
  have hθ₀gt : (5 / 2 : ℝ) < min q (25 / 9 : ℝ) := by
    exact lt_min hq (by norm_num)
  have hδ₀ : 0 < 2 - 5 / min q (25 / 9 : ℝ) := by
    have hpos : 0 < min q (25 / 9 : ℝ) := by linarith only [hθ₀gt]
    apply sub_pos.mpr
    apply (div_lt_iff₀ hpos).mpr
    nlinarith only [hθ₀gt]
  have hθ₁ : (6 / 5 : ℝ) ≤ (25 / 3 : ℝ) := by norm_num
  have hθ₁₂ : (2 : ℝ) ≤ (25 / 3 : ℝ) := by norm_num
  have hδ₁ : 0 < 1 - 5 / (25 / 3 : ℝ) := by norm_num
  have hheat := source_heat_kernel_data_of_morrey
    (P := (6 / 5 : ℝ)) (θ₀ := min q (25 / 9 : ℝ))
    (θ₁ := (25 / 3 : ℝ)) (by norm_num) hθ₀ hθ₁ (by norm_num)
    hδ₀ hδ₁ hg hh hNg hNh hsg hsh
  have hriesz := source_riesz_kernel_data_of_morrey
    (θ₀ := min q (25 / 9 : ℝ)) (θ₁ := (25 / 3 : ℝ))
    hθ₀ hθ₁ hθ₀₂ hθ₁₂ hg hh hNg hNh hsg hsh
  rcases hheat with ⟨hGf, hHf⟩
  rcases hriesz with ⟨hGR, hHR, hGRnorm, hHRnorm⟩
  exact ⟨hGf, hHf, hGR, hHR, hGRnorm, hHRnorm⟩

end CKN.Core.Step4
