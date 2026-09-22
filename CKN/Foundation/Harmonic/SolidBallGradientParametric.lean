-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.SolidBallMeanValueOrigin
import CKN.Foundation.Sobolev.Cutoff.NormTriangle
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Set Filter
open scoped Topology ENNReal
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Harmonic

private lemma euclideanBall_subset_closedBall {x : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x r ⊆ euclideanClosedBall x r := by
  intro y hy
  apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
  exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy |>.le

private theorem translate_euclideanBall_image (x : Vec3) {r : ℝ} (hr : 0 < r) :
    (Homeomorph.addLeft x : Vec3 ≃ₜ Vec3) '' euclideanBall (0 : Vec3) r =
      euclideanBall x r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
    have hz' := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hz
    simpa [sub_eq_add_neg, add_assoc] using hz'
  · intro hy
    refine ⟨y - x, ?_, ?_⟩
    · apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
      have hy' := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
      simpa [sub_eq_add_neg, add_assoc] using hy'
    · change x + (y - x) = y
      abel

/-- Translation preserves the integral over a solid Euclidean ball. -/
theorem integral_translate_euclideanBall {f : Vec3 → ℝ} (x : Vec3)
    {r : ℝ} (hr : 0 < r) :
    ∫ z in euclideanBall (0 : Vec3) r, f (x + z) =
      ∫ z in euclideanBall x r, f z := by
  rw [← translate_euclideanBall_image x hr]
  symm
  exact (measurePreserving_add_left (volume : Measure Vec3) x).setIntegral_image_emb
    (Homeomorph.addLeft x).measurableEmbedding f (euclideanBall (0 : Vec3) r)

/-- A solid Euclidean ball has the same volume at every center. -/
theorem euclideanBall_center_volume (x : Vec3) {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall x r) = volume (euclideanBall (0 : Vec3) r) := by
  have hpre : (fun z : Vec3 => x + z) ⁻¹' euclideanBall x r =
      euclideanBall (0 : Vec3) r := by
    ext z
    change x + z ∈ euclideanBall x r ↔ z ∈ euclideanBall 0 r
    rw [CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr,
      CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
    simp
  calc
    volume (euclideanBall x r) =
        volume ((fun z : Vec3 => x + z) ⁻¹' euclideanBall x r) := by
      symm
      exact (measurePreserving_add_left (volume : Measure Vec3) x).measure_preimage
        (CKN.measurableSet_euclideanBall x r).nullMeasurableSet
    _ = volume (euclideanBall (0 : Vec3) r) := by rw [hpre]

/-- Differentiating the integral over a fixed centered ball integrates the first derivative. -/
theorem hasFDerivAt_integral_fixed_euclideanBall
    {U : Set Vec3} (hU : IsOpen U) {f : Vec3 → ℝ}
    (hf : ContDiffOn ℝ 2 f U) {x : Vec3} {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) (hrs : r < s)
    (hball : closure (euclideanBall x s) ⊆ U) :
    HasFDerivAt
      (fun y : Vec3 => ∫ z in euclideanBall (0 : Vec3) r, f (y + z))
      (∫ z in euclideanBall (0 : Vec3) r, fderiv ℝ f (x + z)) x := by
  let B : Set Vec3 := euclideanBall (0 : Vec3) r
  let K : Set Vec3 := euclideanClosedBall (0 : Vec3) r
  let δ : ℝ := (s - r) / 2
  let S : Set Vec3 := euclideanBall x δ
  let μ : Measure Vec3 := volume.restrict B
  let F : Vec3 → Vec3 → ℝ := fun y z => f (y + z)
  let F' : Vec3 → Vec3 → Vec3 →L[ℝ] ℝ :=
    fun y z => fderiv ℝ f (y + z)
  have hsr : 0 < s - r := by linarith only [hrs]
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hrs]
  have hδr : δ + r < s := by dsimp [δ]; linarith only [hrs]
  have hK : IsCompact K := CKN.isCompact_euclideanClosedBall 0 hr.le
  have hBmeas : MeasurableSet B := CKN.measurableSet_euclideanBall 0 r
  have hBK : B ⊆ K := euclideanBall_subset_closedBall hr
  have hSopen : IsOpen S := CKN.isOpen_euclideanBall x δ
  have hxS : x ∈ S := by
    apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).2
    have hzero : vecEuclideanNorm (0 : Vec3) = 0 :=
      vecEuclideanNorm_eq_zero_iff.mpr rfl
    simpa [hzero] using hδ
  have hSnhds : S ∈ 𝓝 x := hSopen.mem_nhds hxS
  have houterClosed : euclideanBall x s ⊆ euclideanClosedBall x s :=
    euclideanBall_subset_closedBall hs
  have hclosureSub : closure (euclideanBall x s) ⊆ euclideanClosedBall x s :=
    closure_minimal houterClosed (CKN.isClosed_euclideanClosedBall x s)
  have houter : IsCompact (closure (euclideanBall x s)) :=
    (CKN.isCompact_euclideanClosedBall x hs.le).of_isClosed_subset isClosed_closure
      hclosureSub
  have hderivCont : ContinuousOn (fderiv ℝ f) U :=
    hf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hderivNormCont : ContinuousOn (fun y : Vec3 => ‖fderiv ℝ f y‖)
      (closure (euclideanBall x s)) := (hderivCont.mono hball).norm
  obtain ⟨C, hC⟩ := bddAbove_def.mp (houter.bddAbove_image hderivNormCont)
  have hCbound (y : Vec3) (hy : y ∈ closure (euclideanBall x s)) :
      ‖fderiv ℝ f y‖ ≤ C := hC _ ⟨y, hy, rfl⟩
  have hmap (y : Vec3) (hy : y ∈ S) (z : Vec3) (hz : z ∈ B) :
      y + z ∈ euclideanBall x s := by
    have hy' := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1 hy
    have hz'0 := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hz
    have hz' : vecEuclideanNorm z < r := by simpa only [sub_zero] using hz'0
    have hadd : vecEuclideanNorm (y + z - x) ≤
        vecEuclideanNorm (y - x) + vecEuclideanNorm z := by
      rw [show y + z - x = (y - x) + z by abel]
      exact CKN.vecEuclideanNorm_add_le _ _
    apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
    exact hadd.trans_lt (by
      calc
        vecEuclideanNorm (y - x) + vecEuclideanNorm z < δ + r :=
          add_lt_add hy' hz'
        _ < s := hδr)
  have hmapClosed (y : Vec3) (hy : y ∈ S) (z : Vec3) (hz : z ∈ K) :
      y + z ∈ U := by
    have hzB : z ∈ euclideanClosedBall 0 r := hz
    have hznorm0 := (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).1 hzB
    have hznorm : vecEuclideanNorm z ≤ r := by simpa only [sub_zero] using hznorm0
    have hynorm := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1 hy
    have hadd : vecEuclideanNorm (y + z - x) ≤
        vecEuclideanNorm (y - x) + vecEuclideanNorm z := by
      rw [show y + z - x = (y - x) + z by abel]
      exact CKN.vecEuclideanNorm_add_le _ _
    have hzys : y + z ∈ euclideanBall x s := by
      apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
      exact hadd.trans_lt (by
        calc
          vecEuclideanNorm (y - x) + vecEuclideanNorm z < δ + r :=
            add_lt_add_of_lt_of_le hynorm hznorm
          _ < s := hδr)
    exact hball (subset_closure hzys)
  have hFcont (y : Vec3) (hy : y ∈ S) : ContinuousOn (F y) K := by
    change ContinuousOn (fun z : Vec3 => f (y + z)) K
    exact hf.continuousOn.comp (continuous_const_add y).continuousOn
      (hmapClosed y hy)
  have hFmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) μ := by
    filter_upwards [hSnhds] with y hy
    exact (hFcont y hy).aestronglyMeasurable_of_subset_isCompact hK hBmeas hBK
  have hFint : Integrable (F x) μ := by
    change Integrable (fun z : Vec3 => f (x + z)) (volume.restrict B)
    have hcont := hFcont x hxS
    have hintK : IntegrableOn (fun z : Vec3 => f (x + z)) K volume :=
      hcont.integrableOn_compact hK
    exact hintK.mono_set hBK
  have hF'cont (y : Vec3) (hy : y ∈ S) : ContinuousOn (F' y) K := by
    change ContinuousOn (fun z : Vec3 => fderiv ℝ f (y + z)) K
    exact hderivCont.comp (continuous_const_add y).continuousOn (hmapClosed y hy)
  have hF'meas : AEStronglyMeasurable (F' x) μ :=
    (hF'cont x hxS).aestronglyMeasurable_of_subset_isCompact hK hBmeas hBK
  have hboundInt : Integrable (fun _ : Vec3 => C) μ := by
    change IntegrableOn (fun _ : Vec3 => C) B volume
    exact integrableOn_const (CKN.volume_euclideanBall_ne_top 0 hr)
  have hbound : ∀ᵐ z ∂μ, ∀ y ∈ S, ‖F' y z‖ ≤ C := by
    filter_upwards [ae_restrict_mem hBmeas] with z hz
    intro y hy
    change ‖fderiv ℝ f (y + z)‖ ≤ C
    apply hCbound
    exact subset_closure (hmap y hy z hz)
  have hdiff : ∀ᵐ z ∂μ, ∀ y ∈ S,
      HasFDerivAt (F · z) (F' y z) y := by
    filter_upwards [ae_restrict_mem hBmeas] with z hz
    intro y hy
    have hyU : y + z ∈ U := hmapClosed y hy z (hBK hz)
    have hfat := hf.contDiffAt (hU.mem_nhds hyU)
    have hfy := (hfat.differentiableAt (by norm_num)).hasFDerivAt
    have hadd : HasFDerivAt (fun a : Vec3 => a + z)
        (ContinuousLinearMap.id ℝ Vec3) y := (hasFDerivAt_id y).add_const z
    have hcomp := hfy.comp y hadd
    convert hcomp using 1
    · rfl
    · simp [F', ContinuousLinearMap.comp_id]
  have hparam := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (H := Vec3) (α := Vec3) (μ := μ) (x₀ := x) (s := S)
    (bound := fun _ : Vec3 => C) hSnhds hFmeas hFint hF'meas hbound hboundInt hdiff
  simpa [F', μ, B] using hparam

end CKN.Foundation.Harmonic
