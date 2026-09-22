-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.LocalZeroMeanPairing
import CKN.Foundation.Harmonic.RadialBumpDensities
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.PeakFunction

open MeasureTheory Set Filter
open scoped Topology ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

/-!
# Solid-ball mean value property at the origin

The local radial pairing identity compares smooth radial probability densities. A peaked
family converges to point evaluation, while radial cutoffs converge to the indicator of the
solid ball.
-/

namespace CKN.Foundation.Harmonic

private lemma euclideanClosedBall_mono {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R) :
    euclideanClosedBall (0 : Vec3) r ⊆ euclideanClosedBall 0 R := by
  intro y hy
  have hR0 : 0 ≤ R := le_trans hr hR
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR0).2
  exact ((mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr).1 hy).trans hR

private lemma vec3Norm_eq_vecNorm (x : Vec3) :
    vec3EuclideanNorm x = vecEuclideanNorm x := by
  simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- The spatial Laplacian commutes with translation of its argument. -/
theorem spatialLaplacian_comp_add_left (f : Vec3 → ℝ) (x z : Vec3) :
    CKN.spatialLaplacian (fun y => f (x + y)) z =
      CKN.spatialLaplacian f (x + z) := by
  have hfirst (i : Fin 3) :
      CKN.spatialDeriv (fun y => f (x + y)) i =
        fun y => CKN.spatialDeriv f i (x + y) := by
    funext y
    simp [CKN.spatialDeriv, fderiv_comp_add_left]
  rw [CKN.spatialLaplacian, CKN.spatialLaplacian]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfirst i]
  change (fderiv ℝ (fun y => CKN.spatialDeriv f i (x + y)) z)
    (CKN.basisVec i) = _
  rw [fderiv_comp_add_left]
  rfl

private def solidApproxInner (n : ℕ) : ℝ := 1 - ((n : ℝ) + 2)⁻¹

private def solidApproxRadius (s : ℝ) (n : ℕ) : ℝ :=
  s * solidApproxInner n

private lemma solidApproxInner_pos (n : ℕ) : 0 < solidApproxInner n := by
  unfold solidApproxInner
  have hn : 1 < (n : ℝ) + 2 := by exact_mod_cast Nat.one_lt_succ_succ n
  have hinv : ((n : ℝ) + 2)⁻¹ < 1 := (inv_lt_one₀ (by linarith only [hn])).2 hn
  linarith only [hinv]

private lemma solidApproxInner_lt_one (n : ℕ) : solidApproxInner n < 1 := by
  unfold solidApproxInner
  have hinv : 0 < ((n : ℝ) + 2)⁻¹ := inv_pos.mpr (by positivity)
  linarith only [hinv]

private lemma tendsto_solidApproxInner :
    Tendsto solidApproxInner atTop (𝓝 (1 : ℝ)) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop b]
      with n hn
    linarith only [hn]
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub : Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 1) := by
    simpa using hconst.sub hinv
  change Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 1)
  exact hsub

private lemma tendsto_solidApproxRadius (s : ℝ) :
    Tendsto (solidApproxRadius s) atTop (𝓝 s) := by
  have hconst : Tendsto (fun _ : ℕ => s) atTop (𝓝 s) := tendsto_const_nhds
  have h := hconst.mul tendsto_solidApproxInner
  change Tendsto (fun n => s * solidApproxInner n) atTop (𝓝 s)
  simpa only [mul_one] using h

private lemma tendsto_solidApproxThreshold (s : ℝ) :
    Tendsto (fun n => solidApproxInner n * solidApproxRadius s n ^ 2)
      atTop (𝓝 (s ^ 2)) := by
  have h := tendsto_solidApproxInner.mul ((tendsto_solidApproxRadius s).pow 2)
  simpa [solidApproxRadius, mul_one] using h

/-- If `f` is `C²` and harmonic on an open neighbourhood of the closed Euclidean ball,
then its value at the origin is its solid-ball average. -/
theorem harmonic_solidBall_mean_value_at_origin
    {U : Set Vec3} (hU : IsOpen U) {f : Vec3 → ℝ}
    (hf : ContDiffOn ℝ 2 f U)
    (hHarm : ∀ y ∈ U, CKN.spatialLaplacian f y = 0)
    {s : ℝ} (hs : 0 < s)
    (hball : closure (euclideanBall (0 : Vec3) s) ⊆ U) :
    f 0 = (volume (euclideanBall (0 : Vec3) s)).toReal⁻¹ *
      ∫ y in euclideanBall (0 : Vec3) s, f y := by
  classical
  let S : Set Vec3 := closure (euclideanBall (0 : Vec3) s)
  have hSsub : S ⊆ euclideanClosedBall (0 : Vec3) s := by
    apply closure_minimal
    · intro y hy
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hs.le).2
      exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hy).le
    · exact isClosed_euclideanClosedBall 0 s
  have hScompact : IsCompact S :=
    (isCompact_euclideanClosedBall 0 hs.le).of_isClosed_subset isClosed_closure hSsub
  have hBallMeas : MeasurableSet (euclideanBall (0 : Vec3) s) :=
    measurableSet_euclideanBall 0 s
  have hBallFinite : volume (euclideanBall (0 : Vec3) s) ≠ ∞ :=
    volume_euclideanBall_ne_top 0 hs
  have : IsFiniteMeasure (volume.restrict (euclideanBall (0 : Vec3) s)) :=
    isFiniteMeasure_restrict.mpr hBallFinite
  have h0ball : (0 : Vec3) ∈ euclideanBall 0 s := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
    have hzero : vecEuclideanNorm (0 : Vec3) = 0 := vecEuclideanNorm_eq_zero_iff.mpr rfl
    simpa only [sub_self, hzero] using hs
  have h0U : (0 : Vec3) ∈ U := hball (subset_closure h0ball)
  have hfcontU : ContinuousOn f U := hf.continuousOn
  have hfcontS : ContinuousOn f S := hfcontU.mono hball
  have hfintS : IntegrableOn f S volume := hfcontS.integrableOn_compact hScompact
  have hfintBall : IntegrableOn f (euclideanBall 0 s) volume :=
    hfintS.mono_set (fun y hy => subset_closure hy)
  have hfcontAt : ContinuousAt f 0 := hf.contDiffAt (hU.mem_nhds h0U) |>.continuousAt
  have hSnhds : S ∈ 𝓝[ S] (0 : Vec3) := self_mem_nhdsWithin
  have hfcontWithin : ContinuousWithinAt f S 0 := hfcontAt.continuousWithinAt

  let rb : ℝ := s / 2
  have hrb : 0 < rb := by dsimp [rb]; positivity
  have hrbs : rb < s := by dsimp [rb]; linarith only [hs]
  let η : Vec3 → ℝ := radialQBump rb (1 / 4) hrb (by norm_num) (by norm_num)
  have hηcd : ContDiff ℝ (⊤ : ℕ∞) η :=
    radialQBump_contDiff rb (1 / 4) hrb (by norm_num) (by norm_num)
  have hηnonneg (y : Vec3) : 0 ≤ η y :=
    radialQBump_nonneg rb (1 / 4) hrb (by norm_num) (by norm_num) y
  have hηle (y : Vec3) : η y ≤ 1 :=
    radialQBump_le_one rb (1 / 4) hrb (by norm_num) (by norm_num) y
  have hηrad : ∀ y z, vec3EuclideanNorm y = vec3EuclideanNorm z → η y = η z := by
    intro y z hyz
    exact radialQBump_radial rb (1 / 4) hrb (by norm_num) (by norm_num) hyz
  have hηsupp : Function.support η ⊆ euclideanBall 0 rb :=
    radialQBump_support_subset rb (1 / 4) hrb (by norm_num) (by norm_num)
  have hηtsupp : tsupport η ⊆ euclideanClosedBall 0 rb :=
    radialQBump_tsupport_subset rb (1 / 4) hrb (by norm_num) (by norm_num)
  have hηcompact : HasCompactSupport η :=
    radialQBump_hasCompactSupport rb (1 / 4) hrb (by norm_num) (by norm_num)
  have hηzero : η 0 = 1 := by
    apply radialQBump_one_of_norm_le_inner rb (1 / 4) hrb (by norm_num) (by norm_num)
    simp [vec3EuclideanNorm_zero]
    positivity
  have hqcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => q y) := by
    unfold q
    exact ContDiff.sum (fun i hi => (contDiff_apply ℝ ℝ i).pow 2)
  have hdenCD : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => 1 + q y) :=
    contDiff_const.add hqcd
  have hqnonneg (y : Vec3) : 0 ≤ q y := by
    rw [q_eq_vec3Norm_sq]
    positivity
  have hdenPos (y : Vec3) : 0 < 1 + q y := by
    have hq := hqnonneg y
    linarith only [hq]
  have hdenCDinv : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => (1 + q y)⁻¹) :=
    hdenCD.inv (fun y => ne_of_gt (hdenPos y))
  let profile : Vec3 → ℝ := fun y => η y / (1 + q y)
  have hprofileCD : ContDiff ℝ (⊤ : ℕ∞) profile := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => η y * (1 + q y)⁻¹)
    exact hηcd.mul hdenCDinv
  have hprofileNonneg (y : Vec3) : 0 ≤ profile y := by
    exact div_nonneg (hηnonneg y) (le_of_lt (hdenPos y))
  have hprofileRad : ∀ y z, vec3EuclideanNorm y = vec3EuclideanNorm z →
      profile y = profile z := by
    intro y z hyz
    have hq : q y = q z := by rw [q_eq_vec3Norm_sq, q_eq_vec3Norm_sq, hyz]
    simp [profile, hηrad y z hyz, hq]
  have hprofileSupp : Function.support profile ⊆ euclideanBall 0 rb := by
    intro y hy
    have hηy : η y ≠ 0 := by
      intro hy0
      apply hy
      simp [profile, hy0]
    exact hηsupp (Function.mem_support.mpr hηy)
  have hprofileTsupp : tsupport profile ⊆ euclideanClosedBall 0 rb :=
    closure_minimal (by
      intro y hy
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hrb.le).2
        (((mem_euclideanBall_iff_vecEuclideanNorm_lt hrb).1
          (hprofileSupp hy)).le)) (isClosed_euclideanClosedBall 0 rb)
  have hprofileCompact : HasCompactSupport profile :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_euclideanClosedBall 0 hrb.le) (by
        intro y hy
        exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hrb.le).2
          (((mem_euclideanBall_iff_vecEuclideanNorm_lt hrb).1
            (hprofileSupp hy)).le))
  have hprofileZero : profile 0 = 1 := by
    simp [profile, hηzero, q]
  have hprofile_lt_one {y : Vec3} (hy : y ≠ 0) : profile y < 1 := by
    have hqpos : 0 < q y := q_pos hy
    have hden : 1 < 1 + q y := by linarith only [hqpos]
    have hfirst : profile y ≤ (1 + q y)⁻¹ := by
      dsimp [profile]
      simpa [div_eq_mul_inv] using
        (div_le_div_of_nonneg_right (hηle y) (le_of_lt (hdenPos y)))
    have hsecond : (1 + q y)⁻¹ < 1 := (inv_lt_one₀ (by linarith only [hden])).2 hden
    exact lt_of_le_of_lt hfirst hsecond

  have hBallbSubset : euclideanBall (0 : Vec3) rb ⊆ S := by
    intro y hy
    exact subset_closure ((euclideanClosedBall_subset_euclideanBall
      (x₀ := (0 : Vec3)) (r := rb) (R := s) hrb.le hrbs)
        ((mem_euclideanBall_iff_vecEuclideanNorm_lt hrb).1 hy |> fun hn =>
          (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hrb.le).2 hn.le))
  have hOpenb : IsOpen (euclideanBall (0 : Vec3) rb) := isOpen_euclideanBall 0 rb
  have h0interior : 0 ∈ interior S :=
    interior_maximal hBallbSubset hOpenb (by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hrb).2
      have hzero : vecEuclideanNorm (0 : Vec3) = 0 := vecEuclideanNorm_eq_zero_iff.mpr rfl
      simpa only [sub_self, hzero] using hrb)
  have h0closureInterior : 0 ∈ closure (interior S) := subset_closure h0interior
  have hPeak : Tendsto
      (fun n : ℕ => (∫ y in S, profile y ^ n)⁻¹ •
        ∫ y in S, profile y ^ n • f y) atTop (𝓝 (f 0)) := by
    exact tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
      hScompact (hprofileCD.continuous.continuousOn)
      (fun y hy hne => by rw [hprofileZero]; exact hprofile_lt_one hne)
      (fun y hy => hprofileNonneg y) (by rw [hprofileZero]; norm_num)
      h0closureInterior hfcontS
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    exact le_trans hn (Nat.le_add_right n 1)
  have hPeakShift := hPeak.comp hshift

  let θ : ℕ → Vec3 → ℝ := fun n y =>
    radialQBump (solidApproxRadius s n) (solidApproxInner n)
      (mul_pos hs (solidApproxInner_pos n))
      (solidApproxInner_pos n) (solidApproxInner_lt_one n) y
  have hthetaCD (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (θ n) := by
    exact radialQBump_contDiff _ _ (mul_pos hs (solidApproxInner_pos n))
      (solidApproxInner_pos n) (solidApproxInner_lt_one n)
  have hthetaNonneg (n : ℕ) (y : Vec3) : 0 ≤ θ n y := by
    exact radialQBump_nonneg _ _ (mul_pos hs (solidApproxInner_pos n))
      (solidApproxInner_pos n) (solidApproxInner_lt_one n) y
  have hthetaLe (n : ℕ) (y : Vec3) : θ n y ≤ 1 := by
    exact radialQBump_le_one _ _ (mul_pos hs (solidApproxInner_pos n))
      (solidApproxInner_pos n) (solidApproxInner_lt_one n) y
  have hthetaRad (n : ℕ) : ∀ y z, vec3EuclideanNorm y = vec3EuclideanNorm z →
      θ n y = θ n z := by
    intro y z hyz
    exact radialQBump_radial _ _ (mul_pos hs (solidApproxInner_pos n))
      (solidApproxInner_pos n) (solidApproxInner_lt_one n) hyz
  have hthetaSupport (n : ℕ) : Function.support (θ n) ⊆ euclideanBall 0 s := by
    have hradn : 0 < solidApproxRadius s n :=
      mul_pos hs (solidApproxInner_pos n)
    have hradlt : solidApproxRadius s n < s := by
      dsimp [solidApproxRadius]
      simpa [mul_comm] using mul_lt_of_lt_one_left hs (solidApproxInner_lt_one n)
    exact (radialQBump_support_subset _ _ hradn (solidApproxInner_pos n)
      (solidApproxInner_lt_one n)).trans (by
        intro y hy
        have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hradn).1 hy
        exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2 (hy'.trans hradlt))
  have hthetaTsupp (n : ℕ) : tsupport (θ n) ⊆ euclideanClosedBall 0 (solidApproxRadius s n) :=
    radialQBump_tsupport_subset _ _ (mul_pos hs (solidApproxInner_pos n))
      (solidApproxInner_pos n) (solidApproxInner_lt_one n)
  have hthetaSupportRaw (n : ℕ) : Function.support (θ n) ⊆
      euclideanBall 0 (solidApproxRadius s n) := by
    exact radialQBump_support_subset _ _ (mul_pos hs (solidApproxInner_pos n))
      (solidApproxInner_pos n) (solidApproxInner_lt_one n)
  have hthetaIntegralEq (n : ℕ) : ∫ y, θ n y =
      ∫ y in euclideanBall (0 : Vec3) s, θ n y := by
    calc
      ∫ y, θ n y = ∫ y, (euclideanBall (0 : Vec3) s).indicator (θ n) y := by
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ euclideanBall (0 : Vec3) s
        · simp [Set.indicator, hy]
        · have hzero : θ n y = 0 := by
            by_contra hne
            exact hy (hthetaSupport n (Function.mem_support.mpr hne))
          simp [Set.indicator, hy, hzero]
      _ = ∫ y in euclideanBall (0 : Vec3) s, θ n y := by
        rw [integral_indicator hBallMeas]
  have hthetaIntPos (n : ℕ) : 0 < ∫ y in euclideanBall (0 : Vec3) s, θ n y := by
    have hfull : 0 < ∫ y, θ n y :=
      radialQBump_integral_pos _ _ (mul_pos hs (solidApproxInner_pos n))
        (solidApproxInner_pos n) (solidApproxInner_lt_one n)
    rw [← hthetaIntegralEq n]
    exact hfull
  let Zθ : ℕ → ℝ := fun n => ∫ y in euclideanBall (0 : Vec3) s, θ n y
  let ballKernel : ℕ → Vec3 → ℝ := fun n y => θ n y / Zθ n
  have hballKernelCD (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ballKernel n) := by
    exact (hthetaCD n).div_const (Zθ n) 
  have hballKernelCompact (n : ℕ) : HasCompactSupport (ballKernel n) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_euclideanClosedBall 0 (le_of_lt
        (mul_pos hs (solidApproxInner_pos n))))
    intro y hy
    have hyθ : y ∈ Function.support (θ n) := by
      apply Function.mem_support.mpr
      intro hzero
      exact hy (by simp [ballKernel, hzero])
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (mul_pos hs (solidApproxInner_pos n)).le).2
      (((mem_euclideanBall_iff_vecEuclideanNorm_lt
        (mul_pos hs (solidApproxInner_pos n))).1 (hthetaSupportRaw n hyθ)).le)
  have hballKernelTsupp (n : ℕ) : tsupport (ballKernel n) ⊆
      euclideanClosedBall 0 (solidApproxRadius s n) := by
    apply closure_minimal
    · intro y hy
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (mul_pos hs (solidApproxInner_pos n)).le).2
        (((mem_euclideanBall_iff_vecEuclideanNorm_lt
        (mul_pos hs (solidApproxInner_pos n))).1 (hthetaSupportRaw n (by
          apply Function.mem_support.mpr
          intro hzero
          exact hy (by simp [ballKernel, hzero])))).le)
    · exact isClosed_euclideanClosedBall 0 (solidApproxRadius s n)
  have hballKernelRad (n : ℕ) : ∀ y z,
      vec3EuclideanNorm y = vec3EuclideanNorm z → ballKernel n y = ballKernel n z := by
    intro y z hyz
    simp [ballKernel, hthetaRad n y z hyz]
  have hballKernelMass (n : ℕ) : ∫ y, ballKernel n y = 1 := by
    unfold ballKernel Zθ
    calc
      ∫ y, θ n y / (∫ y in euclideanBall (0 : Vec3) s, θ n y) =
          (∫ y in euclideanBall (0 : Vec3) s, θ n y)⁻¹ * ∫ y, θ n y := by
        rw [integral_div]
        ring
      _ = 1 := by
        rw [hthetaIntegralEq n]
        exact inv_mul_cancel₀ (ne_of_gt (hthetaIntPos n))

  have hdenSeq : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop b]
      with n hn
    linarith only [hn]
  have hthreshold : Tendsto
      (fun n => solidApproxInner n * solidApproxRadius s n ^ 2)
      atTop (𝓝 (s ^ 2)) := tendsto_solidApproxThreshold s
  have hthetaTendsto (y : Vec3) (hy : y ∈ euclideanBall (0 : Vec3) s) :
      Tendsto (fun n => θ n y) atTop (𝓝 1) := by
    have hqy : q y < s ^ 2 := by
      have hn := (mem_euclideanBall_iff_vecEuclideanNorm_lt hs).1 hy
      have hn' : vec3EuclideanNorm y < s := by
        simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two, sub_zero]
          using hn
      have hnormNonneg : 0 ≤ vec3EuclideanNorm y := by
        unfold vec3EuclideanNorm
        exact Real.sqrt_nonneg _
      rw [q_eq_vec3Norm_sq]
      nlinarith only [hn', hs, hnormNonneg]
    have hev : ∀ᶠ n in atTop,
        q y < solidApproxInner n * solidApproxRadius s n ^ 2 :=
      hthreshold.eventually (Ioi_mem_nhds hqy)
    have heq : (fun n => θ n y) =ᶠ[atTop] fun _ => (1 : ℝ) := by
      filter_upwards [hev] with n hn
      exact radialQBump_one_of_norm_le_inner _ _
        (mul_pos hs (solidApproxInner_pos n)) (solidApproxInner_pos n)
        (solidApproxInner_lt_one n) (by
          rw [← q_eq_vec3Norm_sq]
          exact hn.le)
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

  let Fθ : ℕ → Vec3 → ℝ := fun n y => f y * θ n y
  let μ : Measure Vec3 := volume.restrict (euclideanBall (0 : Vec3) s)
  have hFθint (n : ℕ) : Integrable (Fθ n) μ := by
    have hθcont : ContinuousOn (θ n) S := (hthetaCD n).continuous.continuousOn
    have hFcont : ContinuousOn (fun y => f y * θ n y) S := hfcontS.mul hθcont
    have hFS : IntegrableOn (fun y => f y * θ n y) S volume :=
      hFcont.integrableOn_compact hScompact
    have hBallS : euclideanBall (0 : Vec3) s ⊆ S := subset_closure
    exact hFS.mono_set hBallS
  have hFθmeas (n : ℕ) : AEStronglyMeasurable (Fθ n) μ := (hFθint n).aestronglyMeasurable
  have hboundInt : Integrable (fun y : Vec3 => |f y|) μ := by
    exact (hfintBall.norm)
  have hFθbound (n : ℕ) : ∀ᵐ y ∂μ, ‖Fθ n y‖ ≤ |f y| := by
    filter_upwards [] with y
    dsimp [Fθ]
    rw [abs_mul]
    rw [abs_of_nonneg (hthetaNonneg n y)]
    exact mul_le_of_le_one_right (abs_nonneg _) (hthetaLe n y)
  have hFθlim : ∀ᵐ y ∂μ,
      Tendsto (fun n => Fθ n y) atTop (𝓝 (f y)) := by
    filter_upwards [ae_restrict_mem hBallMeas] with y hy
    have htend := hthetaTendsto y hy
    simpa [Fθ] using (tendsto_const_nhds.mul htend)
  have hFθDCT := tendsto_integral_of_dominated_convergence
    (fun y => |f y|) hFθmeas hboundInt hFθbound hFθlim
  have hθmeas (n : ℕ) : AEStronglyMeasurable (θ n) μ := by
    exact ((hthetaCD n).continuous.measurable).aestronglyMeasurable
  have hθbound (n : ℕ) : ∀ᵐ y ∂μ, ‖θ n y‖ ≤ 1 :=
    Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (hthetaNonneg n y)] using hthetaLe n y)
  have hθlim : ∀ᵐ y ∂μ, Tendsto (fun n => θ n y) atTop (𝓝 (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem hBallMeas] with y hy
    exact hthetaTendsto y hy
  have hZθlim : Tendsto Zθ atTop (𝓝 ((volume (euclideanBall (0 : Vec3) s)).toReal)) := by
    have hDCT := tendsto_integral_of_dominated_convergence
      (fun _ : Vec3 => (1 : ℝ)) hθmeas (integrable_const 1) hθbound hθlim
    simpa [Zθ, μ, Measure.real_def] using hDCT
  have hFθlimInt : Tendsto (fun n => ∫ y in euclideanBall (0 : Vec3) s,
      f y * θ n y) atTop (𝓝 (∫ y in euclideanBall (0 : Vec3) s, f y)) := by
    simpa [μ, Fθ] using hFθDCT

  have hVolpos : 0 < (volume (euclideanBall (0 : Vec3) s)).toReal := by
    have hpos := volume_euclideanBall_pos (0 : Vec3) hs
    exact ENNReal.toReal_pos hpos.ne' hBallFinite
  have hRatio : Tendsto (fun n => (Zθ n)⁻¹ *
      (∫ y in euclideanBall (0 : Vec3) s, f y * θ n y)) atTop
      (𝓝 ((volume (euclideanBall (0 : Vec3) s)).toReal⁻¹ *
        ∫ y in euclideanBall (0 : Vec3) s, f y)) := by
    exact hZθlim.inv₀ (ne_of_gt hVolpos) |>.mul hFθlimInt

  have hprofilePowIntegralEq (n : ℕ) :
      ∫ y, profile y ^ (n + 1) = ∫ y in S, profile y ^ (n + 1) := by
    calc
      ∫ y, profile y ^ (n + 1) =
          ∫ y, S.indicator (fun y => profile y ^ (n + 1)) y := by
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y ∈ S
        · simp [Set.indicator, hy]
        · have hzero : profile y ^ (n + 1) = 0 := by
            by_contra hne
            have hbase : profile y ≠ 0 := by
              intro hz
              exact hne (by simp [hz])
            exact hy (hBallbSubset (hprofileSupp (Function.mem_support.mpr hbase)))
          simp [Set.indicator, hy, hzero]
      _ = ∫ y in S, profile y ^ (n + 1) := by
        rw [integral_indicator hScompact.measurableSet]
  have hZpeakPos (n : ℕ) : 0 < ∫ y in S, profile y ^ (n + 1) := by
    have hpcont : Continuous (fun y => profile y ^ (n + 1)) :=
      (hprofileCD.pow (n + 1)).continuous
    have hpsupp : HasCompactSupport (fun y => profile y ^ (n + 1)) := by
      apply HasCompactSupport.of_support_subset_isCompact
        (isCompact_euclideanClosedBall 0 hrb.le)
      intro y hy
      have hbase : profile y ≠ 0 := by
        intro hzero
        exact hy (by simp [hzero])
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hrb.le).2
        (((mem_euclideanBall_iff_vecEuclideanNorm_lt hrb).1
          (hprofileSupp (Function.mem_support.mpr hbase))).le)
    have hpnonneg (y : Vec3) : 0 ≤ profile y ^ (n + 1) := pow_nonneg (hprofileNonneg y) _
    have hp0 : profile 0 ^ (n + 1) ≠ 0 := by rw [hprofileZero]; positivity
    have hfull : 0 < ∫ y, profile y ^ (n + 1) :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hpcont hpsupp hpnonneg
        hp0
    rw [← hprofilePowIntegralEq n]
    exact hfull
  let Zpeak : ℕ → ℝ := fun n => ∫ y in S, profile y ^ (n + 1)
  let peakKernel : ℕ → Vec3 → ℝ := fun n y => profile y ^ (n + 1) / Zpeak n
  have hpeakKernelCD (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (peakKernel n) :=
    (hprofileCD.pow (n + 1)).div_const (Zpeak n)
  have hpeakKernelSupport (n : ℕ) : Function.support (peakKernel n) ⊆ euclideanBall 0 rb := by
    intro y hy
    have hpow : profile y ^ (n + 1) ≠ 0 := by
      intro hz
      exact hy (by simp [peakKernel, hz])
    have hbase : profile y ≠ 0 := by
      intro hz
      exact hpow (by simp [hz])
    exact hprofileSupp (Function.mem_support.mpr hbase)
  have hpeakKernelTsupp (n : ℕ) : tsupport (peakKernel n) ⊆ euclideanClosedBall 0 rb :=
    closure_minimal (by
      intro y hy
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hrb.le).2
        (((mem_euclideanBall_iff_vecEuclideanNorm_lt hrb).1
          (hpeakKernelSupport n hy)).le)) (isClosed_euclideanClosedBall 0 rb)
  have hpeakKernelCompact (n : ℕ) : HasCompactSupport (peakKernel n) :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_euclideanClosedBall 0 hrb.le) (by
        intro y hy
        exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hrb.le).2
          (((mem_euclideanBall_iff_vecEuclideanNorm_lt hrb).1
            (hpeakKernelSupport n hy)).le))
  have hpeakKernelRad (n : ℕ) : ∀ y z,
      vec3EuclideanNorm y = vec3EuclideanNorm z → peakKernel n y = peakKernel n z := by
    intro y z hyz
    simp [peakKernel, hprofileRad y z hyz]
  have hpeakKernelMass (n : ℕ) : ∫ y, peakKernel n y = 1 := by
    have hEq := hprofilePowIntegralEq n
    unfold peakKernel Zpeak
    calc
      ∫ y, profile y ^ (n + 1) / ∫ y in S, profile y ^ (n + 1) =
          (∫ y in S, profile y ^ (n + 1))⁻¹ * ∫ y, profile y ^ (n + 1) := by
        rw [integral_div]
        ring
      _ = 1 := by
        rw [hEq]
        exact inv_mul_cancel₀ (ne_of_gt (hZpeakPos n))

  have hcmp (n : ℕ) :
      ∫ y in euclideanBall (0 : Vec3) s, f y * peakKernel n y =
        ∫ y in euclideanBall (0 : Vec3) s, f y * ballKernel n y := by
    let rN : ℝ := max rb (solidApproxRadius s n)
    have hrN : 0 < rN := by
      dsimp [rN]
      exact lt_of_lt_of_le hrb (le_max_left _ _)
    have hrNs : rN < s := by
      dsimp [rN]
      exact max_lt hrbs (by
        dsimp [solidApproxRadius]
        simpa [mul_comm] using mul_lt_of_lt_one_left hs (solidApproxInner_lt_one n))
    let aN : ℝ := (rN + s) / 2
    let bN : ℝ := (aN + s) / 2
    have hrNa : rN < aN := by dsimp [aN]; linarith only [hrNs]
    have haNb : aN < bN := by dsimp [aN, bN]; linarith only [hrNs]
    have hbNs : bN < s := by dsimp [aN, bN]; linarith only [hrNs]
    let gN : Vec3 → ℝ := peakKernel n - ballKernel n
    have hgNcd : ContDiff ℝ (⊤ : ℕ∞) gN := hpeakKernelCD n |>.sub (hballKernelCD n)
    have hradN : ∀ y z, vec3EuclideanNorm y = vec3EuclideanNorm z → gN y = gN z := by
      intro y z hyz
      have hyz' : vec3EuclideanNorm y = vec3EuclideanNorm z := by
        simpa [sub_zero] using hyz
      simp [gN, hpeakKernelRad n y z hyz', hballKernelRad n y z hyz']
    have hmassN : ∫ y, gN y = 0 := by
      have hpint : Integrable (peakKernel n) volume :=
        (hpeakKernelCD n).continuous.integrable_of_hasCompactSupport (hpeakKernelCompact n)
      have hbint : Integrable (ballKernel n) volume :=
        (hballKernelCD n).continuous.integrable_of_hasCompactSupport (hballKernelCompact n)
      change ∫ y, (peakKernel n y - ballKernel n y) = 0
      rw [integral_sub hpint hbint, hpeakKernelMass n, hballKernelMass n]
      ring
    have hsupportN : Function.support gN ⊆ euclideanClosedBall 0 rN := by
      intro y hy
      by_contra hnot
      have hpnot : y ∉ tsupport (peakKernel n) := by
        intro hp
        have hp' : y ∈ euclideanClosedBall 0 rN := by
          apply euclideanClosedBall_mono hrb.le (le_max_left _ _)
          exact hpeakKernelTsupp n hp
        exact hnot hp'
      have hbnot : y ∉ tsupport (ballKernel n) := by
        intro hb
        have hb' : y ∈ euclideanClosedBall 0 rN := by
          apply euclideanClosedBall_mono (mul_pos hs (solidApproxInner_pos n)).le
            (le_max_right _ _)
          exact hballKernelTsupp n hb
        exact hnot hb'
      have hpzero := image_eq_zero_of_notMem_tsupport hpnot
      have hbzero := image_eq_zero_of_notMem_tsupport hbnot
      exact hy (by simp [gN, hpzero, hbzero])
    have htsuppN : tsupport gN ⊆ euclideanClosedBall 0 rN :=
      closure_minimal hsupportN (isClosed_euclideanClosedBall 0 rN)
    have hgcN : HasCompactSupport gN :=
      HasCompactSupport.of_support_subset_isCompact
        (isCompact_euclideanClosedBall 0 hrN.le) hsupportN
    have hlocal := local_harmonic_radial_zeroMean_pairing_at hU hf hHarm
      hrN hrNa haNb hbNs hball hgNcd (by
        intro y z hyz
        apply hradN y z
        simpa [sub_zero] using hyz) hmassN htsuppN
    have hballSupportKernel : tsupport (peakKernel n) ⊆ euclideanBall 0 s := by
      exact (hpeakKernelTsupp n).trans
        (euclideanClosedBall_subset_euclideanBall hrb.le hrbs)
    have hballSupportBallKernel : tsupport (ballKernel n) ⊆ euclideanBall 0 s := by
      have hradn : 0 < solidApproxRadius s n := mul_pos hs (solidApproxInner_pos n)
      have hradlt : solidApproxRadius s n < s := by
        dsimp [solidApproxRadius]
        simpa [mul_comm] using mul_lt_of_lt_one_left hs (solidApproxInner_lt_one n)
      exact (hballKernelTsupp n).trans (euclideanClosedBall_subset_euclideanBall hradn.le hradlt)
    have hprodIntP : IntegrableOn (fun y => f y * peakKernel n y)
        (euclideanBall 0 s) volume :=
      hfintBall.mul_continuousOn_of_subset (hpeakKernelCD n).continuous.continuousOn
        hBallMeas hScompact (subset_closure)
    have hprodIntB : IntegrableOn (fun y => f y * ballKernel n y)
        (euclideanBall 0 s) volume :=
      hfintBall.mul_continuousOn_of_subset (hballKernelCD n).continuous.continuousOn
        hBallMeas hScompact (subset_closure)
    have hlocalSet : ∫ y in euclideanBall (0 : Vec3) s, f y * gN y = 0 := by
      have hEq : (fun y => f y * gN y) =
          fun y => (euclideanBall (0 : Vec3) s).indicator
            (fun y => f y * gN y) y := by
        funext y
        by_cases hy : y ∈ euclideanBall (0 : Vec3) s
        · simp [Set.indicator, hy]
        · have hpzero : peakKernel n y = 0 := by
            by_contra hne
            exact hy (hballSupportKernel (subset_closure (Function.mem_support.mpr hne)))
          have hbzero : ballKernel n y = 0 := by
            by_contra hne
            exact hy (hballSupportBallKernel (subset_closure (Function.mem_support.mpr hne)))
          simp [gN, Set.indicator, hy, hpzero, hbzero]
      calc
        ∫ y in euclideanBall (0 : Vec3) s, f y * gN y =
            ∫ y, (euclideanBall (0 : Vec3) s).indicator
              (fun y => f y * gN y) y := by rw [← integral_indicator hBallMeas]
        _ = ∫ y, f y * gN y := by
          apply integral_congr_ae
          filter_upwards [] with y
          exact (congrFun hEq y).symm
        _ = 0 := hlocal.2
    have hsub := integral_sub hprodIntP hprodIntB
    have heqSet :
        (∫ y in euclideanBall (0 : Vec3) s, f y * peakKernel n y) -
          ∫ y in euclideanBall 0 s, f y * ballKernel n y = 0 := by
      calc
        (∫ y in euclideanBall (0 : Vec3) s, f y * peakKernel n y) -
            ∫ y in euclideanBall 0 s, f y * ballKernel n y =
          ∫ y in euclideanBall 0 s, f y * (peakKernel n y - ballKernel n y) := by
            rw [← hsub]
            congr 1
            funext y
            ring
        _ = 0 := by simpa [gN] using hlocalSet
    linarith only [heqSet]

  have hpeakValues : Tendsto (fun n =>
      (Zpeak n)⁻¹ * ∫ y in S, profile y ^ (n + 1) * f y)
      atTop (𝓝 (f 0)) := by
    change Tendsto
      ((fun k : ℕ => (∫ y in S, profile y ^ k)⁻¹ *
        ∫ y in S, profile y ^ k * f y) ∘ fun n : ℕ => n + 1)
      atTop (𝓝 (f 0))
    exact hPeakShift
  have hcmp' : ∀ n, (Zpeak n)⁻¹ * ∫ y in S, profile y ^ (n + 1) * f y =
      (Zθ n)⁻¹ * ∫ y in euclideanBall (0 : Vec3) s, f y * θ n y := by
    intro n
    have hnormP : ∫ y in euclideanBall (0 : Vec3) s, f y * peakKernel n y =
        (Zpeak n)⁻¹ * ∫ y in S, profile y ^ (n + 1) * f y := by
      have hZ : Zpeak n ≠ 0 := ne_of_gt (hZpeakPos n)
      have hbaseSet : ∫ y in euclideanBall (0 : Vec3) s,
          f y * profile y ^ (n + 1) =
          ∫ y in S, profile y ^ (n + 1) * f y := by
        have hfun : (euclideanBall (0 : Vec3) s).indicator
            (fun y => f y * profile y ^ (n + 1)) =
            S.indicator (fun y => profile y ^ (n + 1) * f y) := by
          funext y
          by_cases hy : y ∈ euclideanBall (0 : Vec3) s
          · have hyS : y ∈ S := subset_closure hy
            simp [Set.indicator, hy, hyS, mul_comm]
          · have hzero : profile y ^ (n + 1) = 0 := by
              by_contra hne
              have hbase : profile y ≠ 0 := by
                intro hz
                exact hne (by simp [hz])
              have hyb := hprofileSupp (Function.mem_support.mpr hbase)
              have hn := (mem_euclideanBall_iff_vecEuclideanNorm_lt hrb).1 hyb
              have hns : vecEuclideanNorm (y - 0) < s := by
                have hn' : vec3EuclideanNorm y < rb := by
                  rw [vec3Norm_eq_vecNorm]
                  simpa [sub_zero] using hn
                have hns' : vec3EuclideanNorm y < s := lt_of_lt_of_le hn' hrbs.le
                rw [vec3Norm_eq_vecNorm] at hns'
                simpa [sub_zero] using hns'
              exact hy ((mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2 hns)
            simp [Set.indicator, hy, hzero]
        calc
          ∫ y in euclideanBall (0 : Vec3) s, f y * profile y ^ (n + 1) =
              ∫ y, (euclideanBall (0 : Vec3) s).indicator
                (fun y => f y * profile y ^ (n + 1)) y := by
            rw [← integral_indicator hBallMeas]
          _ = ∫ y, S.indicator (fun y => profile y ^ (n + 1) * f y) y := by
            rw [hfun]
          _ = ∫ y in S, profile y ^ (n + 1) * f y := by
            rw [integral_indicator hScompact.measurableSet]
      calc
        ∫ y in euclideanBall (0 : Vec3) s, f y * peakKernel n y =
            ∫ y in euclideanBall (0 : Vec3) s,
              (Zpeak n)⁻¹ * (f y * profile y ^ (n + 1)) := by
          congr 1
          funext y
          change f y * (profile y ^ (n + 1) / Zpeak n) = _
          field_simp [hZ]
        _ = (Zpeak n)⁻¹ *
            ∫ y in euclideanBall (0 : Vec3) s, f y * profile y ^ (n + 1) := by
          rw [integral_const_mul]
        _ = (Zpeak n)⁻¹ * ∫ y in S, profile y ^ (n + 1) * f y := by
          rw [hbaseSet]
    have hnormB : ∫ y in euclideanBall (0 : Vec3) s, f y * ballKernel n y =
        (Zθ n)⁻¹ * ∫ y in euclideanBall (0 : Vec3) s, f y * θ n y := by
      have hZ : Zθ n ≠ 0 := ne_of_gt (hthetaIntPos n)
      calc
        ∫ y in euclideanBall (0 : Vec3) s, f y * ballKernel n y =
            ∫ y in euclideanBall (0 : Vec3) s, (Zθ n)⁻¹ * (f y * θ n y) := by
          congr 1
          funext y
          change f y * (θ n y / Zθ n) = _
          field_simp [hZ]
        _ = (Zθ n)⁻¹ * ∫ y in euclideanBall (0 : Vec3) s, f y * θ n y := by
          rw [integral_const_mul]
    have := hcmp n
    rw [hnormP, hnormB] at this
    exact this
  have hpeakEqRatio : Tendsto (fun n => (Zθ n)⁻¹ *
      ∫ y in euclideanBall (0 : Vec3) s, f y * θ n y) atTop (𝓝 (f 0)) := by
    refine hpeakValues.congr' ?_
    filter_upwards [] with n
    exact hcmp' n
  exact tendsto_nhds_unique hpeakEqRatio hRatio

end CKN.Foundation.Harmonic
