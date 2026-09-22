-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.InterpolationBall
import CKN.Foundation.Parabolic.BallBasics
import CKN.Foundation.Parabolic.BallDisplays
import CKN.Foundation.Sobolev.Cutoff.BallTopology
import CKN.Pressure.PkBoundsUnconditionalConstants

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private def sharpCutoff (r : ℝ) : Vec3 → ℝ :=
  canonicalBallCutoff (0 : Vec3) r (2 * r)

private noncomputable def sharpH1 (r : ℝ) (hr : 0 < r) :
    H1Function (euclideanBall (0 : Vec3) 1) :=
  let f := sharpCutoff r
  let hfTop : ContDiff ℝ (⊤ : ℕ∞) f := by
    simpa [f, sharpCutoff] using
      (canonicalBallCutoff_smooth (0 : Vec3) (r := r) (R := 2 * r)
        hr.le (by linarith only [hr]))
  let hf : ContDiff ℝ 1 f := hfTop.of_le (by simp)
  let hfsupport : HasCompactSupport f := by
    simpa [f, sharpCutoff] using
      (canonicalBallCutoff_hasCompactSupport (x₀ := (0 : Vec3))
        (r := r) (R := 2 * r) hr.le (by linarith only [hr]))
  { toFun := f
    grad := classicalGradient f
    memL2 := by
      have hfcont : Continuous f :=
        (hf.differentiable (by simp)).continuous
      exact (hfcont.memLp_of_hasCompactSupport hfsupport).restrict _
    gradMemL2 := by
      intro i
      have hgradcont : Continuous (fun x => (fderiv ℝ f x) (basisVec i)) := by
        simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const
      have hgradsupport : HasCompactSupport
          (fun x => (fderiv ℝ f x) (basisVec i)) := by
        simpa using hfsupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
      exact (hgradcont.memLp_of_hasCompactSupport hgradsupport).restrict _
    hasWeakGradient := HasWeakGradientOn.of_contDiff hf }

private lemma sharp_volume {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall (0 : Vec3) r) =
      ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℝ)) := by
  rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr]
  rw [pressure_volume_ball hr]
  congr 1
  norm_num [Real.rpow_natCast]

private lemma sharp_ball_inner_subset_unit {r : ℝ} (hr : 0 < r)
    (h2r : 2 * r < 1) :
    euclideanBall (0 : Vec3) r ⊆ euclideanBall (0 : Vec3) 1 := by
  intro x hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
  exact lt_trans hx' (by linarith only [h2r])

private lemma sharp_cutoff_eLpNorm_le {r : ℝ} (hr : 0 < r)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (sharpCutoff r) p (volume.restrict (euclideanBall (0 : Vec3) 1)) ≤
      volume (euclideanBall (0 : Vec3) (2 * r)) ^ (1 / p.toReal) := by
  let B : Set Vec3 := euclideanBall (0 : Vec3) (2 * r)
  let η : Vec3 → ℝ := sharpCutoff r
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η, sharpCutoff] using
      (canonicalBallCutoff_smooth (0 : Vec3) (r := r) (R := 2 * r)
        hr.le (by linarith only [hr]))
  have hηcont : Continuous η := hηsmooth.continuous
  have hηmeas : AEStronglyMeasurable η
      (volume.restrict (euclideanBall (0 : Vec3) 1)) :=
    hηcont.aestronglyMeasurable
  have hBmeas : MeasurableSet B := measurableSet_euclideanBall (0 : Vec3) (2 * r)
  have hBpos : 0 < volume B := by
    change 0 < volume (euclideanBall (0 : Vec3) (2 * r))
    rw [sharp_volume (mul_pos (by norm_num) hr)]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hBtop : volume B ≠ ∞ := by
    change volume (euclideanBall (0 : Vec3) (2 * r)) ≠ ∞
    exact (volume_euclideanBall_lt_top (0 : Vec3) (mul_pos (by norm_num) hr)).ne
  have hdom : ∀ x, ‖η x‖ₑ ≤ ‖B.indicator (fun _ : Vec3 => (1 : ℝ)) x‖ₑ := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have hn := canonicalBallCutoff_nonneg (0 : Vec3) r (2 * r) x
      have hu := canonicalBallCutoff_le_one (0 : Vec3) r (2 * r) x
      have hηx : η x = canonicalBallCutoff (0 : Vec3) r (2 * r) x := rfl
      rw [hηx]
      calc
        ‖canonicalBallCutoff (0 : Vec3) r (2 * r) x‖ₑ =
            ENNReal.ofReal (canonicalBallCutoff (0 : Vec3) r (2 * r) x) := by
              rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hn]
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hu
        _ = ‖(1 : ℝ)‖ₑ := by norm_num
    · have hsupp := canonicalBallCutoff_tsupport_subset_outer
        (x₀ := (0 : Vec3)) (r := r) (R := 2 * r) hr.le (by linarith only [hr])
      have hnot : x ∉ tsupport (canonicalBallCutoff (0 : Vec3) r (2 * r)) :=
        fun h => hx (hsupp h)
      have hz : η x = 0 := by
        simpa [η, sharpCutoff] using
          (image_eq_zero_of_notMem_tsupport hnot :
            canonicalBallCutoff (0 : Vec3) r (2 * r) x = 0)
      simp [hz, Set.indicator_of_notMem hx]
  calc
    eLpNorm η p (volume.restrict (euclideanBall (0 : Vec3) 1)) ≤ eLpNorm η p volume :=
      eLpNorm_mono_measure η Measure.restrict_le_self
    _ ≤ eLpNorm (B.indicator (fun _ : Vec3 => (1 : ℝ))) p volume :=
      eLpNorm_mono_enorm hηcont.aestronglyMeasurable hdom
    _ = ‖(1 : ℝ)‖ₑ * volume B ^ (1 / p.toReal) := by
      rw [eLpNorm_indicator_const hBmeas.nullMeasurableSet hp0 hptop]
    _ = volume (euclideanBall (0 : Vec3) (2 * r)) ^ (1 / p.toReal) := by
      simp [B]

private lemma sharp_gradient_eLpNorm_le {r : ℝ} (hr : 0 < r) :
    weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) 1) (sharpH1 r hr).grad ≤
      ENNReal.ofReal (32 / r) *
        volume (euclideanBall (0 : Vec3) (2 * r)) ^ (1 / 2 : ℝ) := by
  let B : Set Vec3 := euclideanBall (0 : Vec3) (2 * r)
  let η : Vec3 → ℝ := sharpCutoff r
  let H := sharpH1 r hr
  have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η := by
    simpa [η, sharpCutoff] using
      (canonicalBallCutoff_smooth (0 : Vec3) (r := r) (R := 2 * r)
        hr.le (by linarith only [hr]))
  have hgradEq : H.grad = classicalGradient η := by
    rfl
  have hgradcont : Continuous H.grad := by
    rw [hgradEq]
    apply continuous_pi
    intro i
    simpa only [classicalGradient_apply] using
      (hηsmooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hBmeas : MeasurableSet B := measurableSet_euclideanBall (0 : Vec3) (2 * r)
  have hBtop : volume B ≠ ∞ := by
    change volume (euclideanBall (0 : Vec3) (2 * r)) ≠ ∞
    exact (volume_euclideanBall_lt_top (0 : Vec3) (mul_pos (by norm_num) hr)).ne
  have hdom : ∀ x,
      ‖H.grad x‖ₑ ≤ ‖B.indicator (fun _ : Vec3 => (32 / r : ℝ)) x‖ₑ := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have hvec := canonicalBallCutoff_gradient_bound
        (x₀ := (0 : Vec3)) (r := r) (R := 2 * r) hr.le
        (by linarith only [hr]) x
      have hgrad : ‖H.grad x‖ ≤ 32 / r := by
        rw [hgradEq]
        calc
          ‖classicalGradient η x‖ ≤ vecEuclideanNorm (classicalGradient η x) :=
            pi_norm_le_vecEuclideanNorm _
          _ ≤ 32 / (2 * r - r) := by simpa [η, sharpCutoff] using hvec
          _ = 32 / r := by congr 1; ring
      calc
        ‖H.grad x‖ₑ = ENNReal.ofReal ‖H.grad x‖ := by simp
        _ ≤ ENNReal.ofReal (32 / r) := ENNReal.ofReal_le_ofReal hgrad
        _ = ‖(32 / r : ℝ)‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (div_nonneg (by norm_num) hr.le)]
    · have hsupp := canonicalBallCutoff_tsupport_subset_outer
        (x₀ := (0 : Vec3)) (r := r) (R := 2 * r) hr.le (by linarith only [hr])
      have hnot : x ∉ tsupport η := by
        intro h
        exact hx (by simpa [B, η, sharpCutoff] using hsupp h)
      have hfd : fderiv ℝ η x = 0 := fderiv_of_notMem_tsupport ℝ hnot
      have hz : H.grad x = 0 := by
        rw [hgradEq]
        ext i
        simp [classicalGradient_apply, hfd]
      simp [hz, Set.indicator_of_notMem hx]
  calc
    weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) 1) H.grad ≤
        eLpNorm H.grad 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ eLpNorm (B.indicator (fun _ : Vec3 => (32 / r : ℝ))) 2 volume :=
      eLpNorm_mono_enorm hgradcont.aestronglyMeasurable hdom
    _ = ‖(32 / r : ℝ)‖ₑ * volume B ^ (1 / (2 : ℝ≥0∞).toReal) := by
      rw [eLpNorm_indicator_const hBmeas.nullMeasurableSet (by norm_num) (by norm_num)]
    _ = ENNReal.ofReal (32 / r) * volume B ^ (1 / 2 : ℝ) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (div_nonneg (by norm_num) hr.le)]
      norm_num
    _ = _ := by simp [B]

private lemma sharp_cutoff_eLpNorm_lower {r q : ℝ} (hr : 0 < r)
    (h2r : 2 * r < 1) (hq : 0 < q) :
    volume (euclideanBall (0 : Vec3) r) ^ (1 / q) ≤
      eLpNorm (sharpCutoff r) (ENNReal.ofReal q)
        (volume.restrict (euclideanBall (0 : Vec3) 1)) := by
  let B : Set Vec3 := euclideanBall (0 : Vec3) r
  let U : Set Vec3 := euclideanBall (0 : Vec3) 1
  let p : ℝ≥0∞ := ENNReal.ofReal q
  have hBU : B ⊆ U := sharp_ball_inner_subset_unit hr h2r
  have hrestrict : volume.restrict B ≤ volume.restrict U :=
    Measure.restrict_mono_set volume hBU
  have hBmeas : MeasurableSet B := measurableSet_euclideanBall (0 : Vec3) r
  have hBpos : 0 < volume B := by
    change 0 < volume (euclideanBall (0 : Vec3) r)
    exact volume_euclideanBall_pos 0 hr
  have hμ : volume.restrict B ≠ 0 := by
    intro hzero
    have hzeroU : (volume.restrict B) Set.univ = 0 := by rw [hzero]; simp
    rw [Measure.restrict_apply_univ] at hzeroU
    exact (ne_of_gt hBpos) hzeroU
  have hp0 : p ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hptop : p ≠ ∞ := ENNReal.ofReal_ne_top
  have hηae : sharpCutoff r =ᵐ[volume.restrict B] fun _ => (1 : ℝ) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hBmeas]
    filter_upwards [] with x hx
    exact canonicalBallCutoff_eq_one_on_inner hr.le
      (by linarith only [hr]) (by simpa [B] using hx)
  have hinner : eLpNorm (sharpCutoff r) p (volume.restrict B) =
      volume B ^ (1 / q) := by
    rw [eLpNorm_congr_ae hηae, eLpNorm_const (1 : ℝ) hp0 hμ]
    simp [p, B, ENNReal.toReal_ofReal hq.le]
  calc
    volume B ^ (1 / q) = eLpNorm (sharpCutoff r) p (volume.restrict B) := hinner.symm
    _ ≤ eLpNorm (sharpCutoff r) p (volume.restrict U) :=
      eLpNorm_mono_measure _ hrestrict
    _ = _ := by rfl

private noncomputable def sharpVolumeConstant : ℝ≥0∞ :=
  ENNReal.ofReal (4 * Real.pi / 3)

private noncomputable def sharpScaleConstant : ℝ≥0∞ :=
  ((8 : ℝ≥0∞) * sharpVolumeConstant) ^ (1 / 2 : ℝ)

private lemma sharp_volume_scale {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall (0 : Vec3) r) =
      sharpVolumeConstant * (ENNReal.ofReal r) ^ (3 : ℝ) := by
  rw [sharp_volume hr]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi / 3)]
  rw [← ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num : 0 ≤ (3 : ℝ))]
  norm_num [sharpVolumeConstant]

private lemma sharp_outer_volume_scale {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall (0 : Vec3) (2 * r)) =
      (8 : ℝ≥0∞) * sharpVolumeConstant * (ENNReal.ofReal r) ^ (3 : ℝ) := by
  rw [sharp_volume (mul_pos (by norm_num) hr)]
  have hreal : (4 * Real.pi / 3) * (2 * r) ^ (3 : ℝ) =
      (8 * (4 * Real.pi / 3)) * r ^ (3 : ℝ) := by
    rw [Real.mul_rpow (by positivity) hr.le]
    norm_num
    ring
  rw [hreal]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * (4 * Real.pi / 3))]
  rw [← ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num : 0 ≤ (3 : ℝ))]
  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (8 : ℝ))]
  norm_num [sharpVolumeConstant, mul_assoc]

private lemma sharp_outer_sqrt_scale {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall (0 : Vec3) (2 * r)) ^ (1 / 2 : ℝ) =
      sharpScaleConstant * (ENNReal.ofReal r) ^ (3 / 2 : ℝ) := by
  rw [sharp_outer_volume_scale hr]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  rw [← ENNReal.rpow_mul (ENNReal.ofReal r) 3 (1 / 2 : ℝ)]
  norm_num [sharpScaleConstant]

private lemma sharp_cutoff_l2_scale {r : ℝ} (hr : 0 < r) :
    lpNormOn 2 (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ≤
      sharpScaleConstant * (ENNReal.ofReal r) ^ (3 / 2 : ℝ) := by
  change eLpNorm (sharpCutoff r) 2
      (volume.restrict (euclideanBall (0 : Vec3) 1)) ≤ _
  have h := sharp_cutoff_eLpNorm_le hr (2 : ℝ≥0∞) (by norm_num) (by norm_num)
  have hs := sharp_outer_sqrt_scale hr
  norm_num at h
  exact h.trans_eq hs

private lemma sharp_gradient_scale {r : ℝ} (hr : 0 < r) :
    weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) 1) (sharpH1 r hr).grad ≤
      32 * sharpScaleConstant * (ENNReal.ofReal r) ^ (1 / 2 : ℝ) := by
  let t : ℝ≥0∞ := ENNReal.ofReal r
  have ht0 : t ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have htop : t ≠ ∞ := ENNReal.ofReal_ne_top
  have hsqrt := sharp_outer_sqrt_scale hr
  have hbase := sharp_gradient_eLpNorm_le hr
  change eLpNorm (sharpH1 r hr).grad 2
      (volume.restrict (euclideanBall (0 : Vec3) 1)) ≤ _ at hbase
  rw [hsqrt] at hbase
  have hcoeff : ENNReal.ofReal (32 / r) = 32 * t⁻¹ := by
    rw [show (32 / r : ℝ) = 32 * r⁻¹ by field_simp]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
    rw [ENNReal.ofReal_inv_of_pos hr]
    norm_num [t]
  have hpow := ENNReal.rpow_add (-1) (3 / 2) ht0 htop
  rw [show -1 + 3 / 2 = (1 / 2 : ℝ) by norm_num] at hpow
  calc
    eLpNorm (sharpH1 r hr).grad 2
        (volume.restrict (euclideanBall (0 : Vec3) 1)) ≤
      ENNReal.ofReal (32 / r) *
        (sharpScaleConstant * t ^ (3 / 2 : ℝ)) := hbase
    _ = 32 * sharpScaleConstant * t ^ (1 / 2 : ℝ) := by
      rw [hcoeff]
      calc
        (32 * t⁻¹) * (sharpScaleConstant * t ^ (3 / 2 : ℝ)) =
            32 * sharpScaleConstant * (t ^ (-1 : ℝ) * t ^ (3 / 2 : ℝ)) := by
          rw [← ENNReal.rpow_neg_one]
          ac_rfl
        _ = 32 * sharpScaleConstant * t ^ (1 / 2 : ℝ) := by rw [← hpow]
    _ = 32 * sharpScaleConstant * (ENNReal.ofReal r) ^ (1 / 2 : ℝ) := by simp [t]

private lemma sharp_scaled_inequality
    (q : ℝ) (hq3 : 3 < q) (hq6 : q ≤ 6)
    {r : ℝ} (hr : 0 < r) (h2r : 2 * r < 1)
    (C : ℝ≥0∞)
    (hbound : ∀ v : H1Function (euclideanBall (0 : Vec3) 1),
      lpNormOn (ENNReal.ofReal q) (euclideanBall (0 : Vec3) 1) v.toFun ^ q ≤
        C * weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) 1) v.grad ^
            (2 * (q / 2 - 3 * (q - 2) / 4)) *
          lpNormOn 2 (euclideanBall (0 : Vec3) 1) v.toFun ^
            (2 * (3 * (q - 2) / 4)) +
        C * lpNormOn 2 (euclideanBall (0 : Vec3) 1) v.toFun ^ q) :
    sharpVolumeConstant ≤
      C * ((32 * sharpScaleConstant) ^
          (2 * (q / 2 - 3 * (q - 2) / 4)) * sharpScaleConstant ^
            (2 * (3 * (q - 2) / 4))) *
          (ENNReal.ofReal r) ^ (2 * q - 6) +
        C * sharpScaleConstant ^ q * (ENNReal.ofReal r) ^ (3 * q / 2 - 3) := by
  let a : ℝ := 2 * (q / 2 - 3 * (q - 2) / 4)
  let b : ℝ := 2 * (3 * (q - 2) / 4)
  let t : ℝ≥0∞ := ENNReal.ofReal r
  have hq : 0 < q := by linarith only [hq3]
  have hq2 : 2 ≤ q := by linarith only [hq3]
  have ha : 0 ≤ a := by dsimp [a]; nlinarith only [hq6]
  have hb : 0 ≤ b := by dsimp [b]; nlinarith only [hq3]
  have hsum : a + b = q := by dsimp [a, b]; ring
  have hexp : a / 2 + 3 * b / 2 = 2 * q - 3 := by
    dsimp [a, b]
    ring
  have hqinv : (1 / q) * q = 1 := by
    field_simp
  have ht0 : t ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have httop : t ≠ ∞ := ENNReal.ofReal_ne_top
  have ht3top : t ^ (3 : ℝ) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    exact httop
  have ht3zero : t ^ (3 : ℝ) ≠ 0 := by positivity
  have hlow0 := sharp_cutoff_eLpNorm_lower hr h2r hq
  have hlow : volume (euclideanBall (0 : Vec3) r) ≤
      lpNormOn (ENNReal.ofReal q) (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ^ q := by
    change volume (euclideanBall (0 : Vec3) r) ≤
      eLpNorm (sharpCutoff r) (ENNReal.ofReal q)
        (volume.restrict (euclideanBall (0 : Vec3) 1)) ^ q
    calc
      volume (euclideanBall (0 : Vec3) r) =
          (volume (euclideanBall (0 : Vec3) r) ^ (1 / q)) ^ q := by
            rw [← ENNReal.rpow_mul, hqinv, ENNReal.rpow_one]
      _ ≤ eLpNorm (sharpCutoff r) (ENNReal.ofReal q)
          (volume.restrict (euclideanBall (0 : Vec3) 1)) ^ q :=
        ENNReal.rpow_le_rpow hlow0 hq.le
  have hvol := sharp_volume_scale hr
  have hvol' : volume (euclideanBall (0 : Vec3) r) =
      sharpVolumeConstant * t ^ (3 : ℝ) := by simpa [t] using hvol
  have hG := sharp_gradient_scale hr
  have hL := sharp_cutoff_l2_scale hr
  have hinterp := hbound (sharpH1 r hr)
  have hfun : (sharpH1 r hr).toFun = sharpCutoff r := rfl
  have hinterp' :
      lpNormOn (ENNReal.ofReal q) (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ^ q ≤
        C * weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) 1)
              (sharpH1 r hr).grad ^ a *
            lpNormOn 2 (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ^ b +
          C * lpNormOn 2 (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ^ q := by
    simpa only [hfun, a, b] using hinterp
  have hupper :
      C * weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) 1)
              (sharpH1 r hr).grad ^ a *
            lpNormOn 2 (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ^ b +
          C * lpNormOn 2 (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ^ q ≤
        C * (32 * sharpScaleConstant * t ^ (1 / 2 : ℝ)) ^ a *
            (sharpScaleConstant * t ^ (3 / 2 : ℝ)) ^ b +
          C * (sharpScaleConstant * t ^ (3 / 2 : ℝ)) ^ q := by
    gcongr
  have hterm1 :
      (32 * sharpScaleConstant * t ^ (1 / 2 : ℝ)) ^ a *
          (sharpScaleConstant * t ^ (3 / 2 : ℝ)) ^ b =
        ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
          t ^ (2 * q - 3) := by
    rw [show 32 * sharpScaleConstant * t ^ (1 / 2 : ℝ) =
        (32 * sharpScaleConstant) * t ^ (1 / 2 : ℝ) by ac_rfl]
    rw [ENNReal.mul_rpow_of_nonneg (32 * sharpScaleConstant)
      (t ^ (1 / 2 : ℝ)) ha]
    rw [ENNReal.mul_rpow_of_nonneg sharpScaleConstant
      (t ^ (3 / 2 : ℝ)) hb]
    rw [← ENNReal.rpow_mul t (1 / 2 : ℝ) a,
      ← ENNReal.rpow_mul t (3 / 2 : ℝ) b]
    have hpow := ENNReal.rpow_add (a / 2) (3 * b / 2) ht0 httop
    rw [hexp] at hpow
    calc
      (32 * sharpScaleConstant) ^ a * t ^ ((1 / 2 : ℝ) * a) *
          (sharpScaleConstant ^ b * t ^ ((3 / 2 : ℝ) * b)) =
        ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
          (t ^ (a / 2) * t ^ (3 * b / 2)) := by
            rw [show (1 / 2 : ℝ) * a = a / 2 by ring,
              show (3 / 2 : ℝ) * b = 3 * b / 2 by ring]
            ac_rfl
      _ = ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
          t ^ (2 * q - 3) := by rw [← hpow]
  have hterm2 :
      (sharpScaleConstant * t ^ (3 / 2 : ℝ)) ^ q =
        sharpScaleConstant ^ q * t ^ (3 * q / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg sharpScaleConstant
      (t ^ (3 / 2 : ℝ)) hq.le,
      ← ENNReal.rpow_mul t (3 / 2 : ℝ) q]
    rw [show (3 / 2 : ℝ) * q = 3 * q / 2 by ring]
  have hraw :
      sharpVolumeConstant * t ^ (3 : ℝ) ≤
        C * ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
            t ^ (2 * q - 3) +
          C * sharpScaleConstant ^ q * t ^ (3 * q / 2) := by
    calc
      sharpVolumeConstant * t ^ (3 : ℝ) = volume (euclideanBall (0 : Vec3) r) := hvol'.symm
      _ ≤ lpNormOn (ENNReal.ofReal q) (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ^ q := hlow
      _ ≤ C * weakGradientLpNormOn 2 (euclideanBall (0 : Vec3) 1)
              (sharpH1 r hr).grad ^ a *
            lpNormOn 2 (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ^ b +
          C * lpNormOn 2 (euclideanBall (0 : Vec3) 1) (sharpCutoff r) ^ q := hinterp'
      _ ≤ C * (32 * sharpScaleConstant * t ^ (1 / 2 : ℝ)) ^ a *
            (sharpScaleConstant * t ^ (3 / 2 : ℝ)) ^ b +
          C * (sharpScaleConstant * t ^ (3 / 2 : ℝ)) ^ q := hupper
      _ = C * ((32 * sharpScaleConstant * t ^ (1 / 2 : ℝ)) ^ a *
            (sharpScaleConstant * t ^ (3 / 2 : ℝ)) ^ b) +
          C * ((sharpScaleConstant * t ^ (3 / 2 : ℝ)) ^ q) := by ac_rfl
      _ = _ := by rw [hterm1, hterm2]; ac_rfl
  have hfac1 :
      C * ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
          t ^ (2 * q - 3) =
        (C * ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
          t ^ (2 * q - 6)) * t ^ (3 : ℝ) := by
    have he : 2 * q - 3 = (2 * q - 6) + 3 := by ring
    rw [he, ENNReal.rpow_add (2 * q - 6) 3 ht0 httop]
    ac_rfl
  have hfac2 :
      C * sharpScaleConstant ^ q * t ^ (3 * q / 2) =
        (C * sharpScaleConstant ^ q * t ^ (3 * q / 2 - 3)) * t ^ (3 : ℝ) := by
    have he : 3 * q / 2 = (3 * q / 2 - 3) + 3 := by ring
    conv_lhs => rw [he, ENNReal.rpow_add (3 * q / 2 - 3) 3 ht0 httop]
    ac_rfl
  have hfactored :
      C * ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
          t ^ (2 * q - 3) + C * sharpScaleConstant ^ q * t ^ (3 * q / 2) =
        (C * ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
            t ^ (2 * q - 6) +
          C * sharpScaleConstant ^ q * t ^ (3 * q / 2 - 3)) * t ^ (3 : ℝ) := by
    rw [hfac1, hfac2, add_mul]
  have hcancel :
      sharpVolumeConstant * t ^ (3 : ℝ) ≤
        (C * ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
            t ^ (2 * q - 6) +
          C * sharpScaleConstant ^ q * t ^ (3 * q / 2 - 3)) * t ^ (3 : ℝ) :=
    hraw.trans_eq hfactored
  have hcancel' :
      t ^ (3 : ℝ) * sharpVolumeConstant ≤
        t ^ (3 : ℝ) *
          (C * ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b) *
              t ^ (2 * q - 6) +
            C * sharpScaleConstant ^ q * t ^ (3 * q / 2 - 3)) := by
    simpa [mul_comm] using hcancel
  have hresult := (ENNReal.mul_le_mul_iff_right ht3zero ht3top).mp hcancel'
  simpa [t, a, b] using hresult

/-- The proposed swapped interpolation exponents cannot hold uniformly on the unit ball. -/
theorem lin_swapped_interpolation_false
    (q : ℝ) (hq3 : 3 < q) (hq6 : q ≤ 6) :
    ¬ ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ v : H1Function (euclideanBall (0 : Vec 3) 1),
      lpNormOn (ENNReal.ofReal q) (euclideanBall (0 : Vec 3) 1) v.toFun ^ q ≤
        C * weakGradientLpNormOn 2 (euclideanBall (0 : Vec 3) 1) v.grad ^
            (2 * (q / 2 - 3 * (q - 2) / 4)) *
          lpNormOn 2 (euclideanBall (0 : Vec 3) 1) v.toFun ^
            (2 * (3 * (q - 2) / 4)) +
        C * lpNormOn 2 (euclideanBall (0 : Vec 3) 1) v.toFun ^ q := by
  rintro ⟨C, hC, hbound⟩
  let a : ℝ := 2 * (q / 2 - 3 * (q - 2) / 4)
  let b : ℝ := 2 * (3 * (q - 2) / 4)
  let c₁ : ℝ≥0∞ := C * ((32 * sharpScaleConstant) ^ a * sharpScaleConstant ^ b)
  let c₂ : ℝ≥0∞ := C * sharpScaleConstant ^ q
  let d₁ : ℝ := 2 * q - 6
  let d₂ : ℝ := 3 * q / 2 - 3
  let rhs : ℝ → ℝ≥0∞ := fun r => c₁ * (ENNReal.ofReal r) ^ d₁ +
    c₂ * (ENNReal.ofReal r) ^ d₂
  have ha : 0 ≤ a := by dsimp [a]; nlinarith only [hq6]
  have hb : 0 ≤ b := by dsimp [b]; nlinarith only [hq3]
  have hd₁ : 0 < d₁ := by dsimp [d₁]; nlinarith only [hq3]
  have hd₂ : 0 < d₂ := by dsimp [d₂]; nlinarith only [hq3]
  have hS : sharpScaleConstant ≠ ∞ := by
    unfold sharpScaleConstant sharpVolumeConstant
    finiteness
  have hbase : (32 : ℝ≥0∞) * sharpScaleConstant ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hS
  have hc₁ : c₁ ≠ ∞ := by
    apply ENNReal.mul_ne_top hC
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg ha hbase
    · exact ENNReal.rpow_ne_top_of_nonneg hb hS
  have hc₂ : c₂ ≠ ∞ := by
    apply ENNReal.mul_ne_top hC
    exact ENNReal.rpow_ne_top_of_nonneg (by linarith only [hq3]) hS
  have htend : Filter.Tendsto (fun r : ℝ => ENNReal.ofReal r)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa using (ENNReal.continuous_ofReal.continuousAt.tendsto (x := (0 : ℝ)))
  have hlim₁ : Filter.Tendsto (fun r : ℝ => c₁ * (ENNReal.ofReal r) ^ d₁)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc₁ hd₁).comp htend
  have hlim₂ : Filter.Tendsto (fun r : ℝ => c₂ * (ENNReal.ofReal r) ^ d₂)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc₂ hd₂).comp htend
  have hlim : Filter.Tendsto rhs (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [rhs] using hlim₁.add hlim₂
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 2 * r < 1 := by
    have hnear : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), r < 1 / 2 :=
      eventually_lt_nhds (by norm_num)
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with r hr
    nlinarith only [hr]
  have hpositive : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  have hconst : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      sharpVolumeConstant ≤ rhs r := by
    filter_upwards [hsmall, hpositive] with r hr hpos
    simpa [rhs, c₁, c₂, a, b, d₁, d₂] using
      sharp_scaled_inequality q hq3 hq6 hpos hr C hbound
  have hvolume : sharpVolumeConstant ≤ 0 := ge_of_tendsto hlim hconst
  have hvolume_pos : 0 < sharpVolumeConstant := by
    unfold sharpVolumeConstant
    exact ENNReal.ofReal_pos.mpr (by positivity)
  exact (not_le_of_gt hvolume_pos) hvolume

end CKN

end
