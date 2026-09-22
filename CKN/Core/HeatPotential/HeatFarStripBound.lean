-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelCrossZero
import CKN.Foundation.Parabolic.Morrey.StripMass

/-!
# The causal thin-strip estimate on a far shell

Fix a degree-one Fourier multiplier `σ`, a base point `z`, a radius `r` and a
far shell index `j ≥ 6`, and two observation points `w, w'` in the ball of
radius `r` around `z` with `w.2 ≤ w'.2`.  The two causal kernels
`spatialMultiplierHeatKernel σ (w.1 - ·) (w.2 - ·)` and
`spatialMultiplierHeatKernel σ (w'.1 - ·) (w'.2 - ·)` differ, on the moving
time strip `{v | w.2 ≤ v.2 ∧ v.2 < w'.2}`, by the later kernel alone: the
earlier one vanishes there.  The strip's contribution to the far shell must
therefore be estimated on its own, with a factor that tends to zero as
`parabolicDist w w'` does.

That is what this module proves.  Two facts combine:

* on the far shell the two points are separated in **space**, because their
  time separation is at most `2 r ^ 2` while the shell sits at parabolic
  distance at least `2 ^ j r ≥ 64 r`; so the all-time order-four kernel size
  estimate applies with gauge at least `(2 ^ j r) / 2`;
* the strip is a thin time slab of width `w'.2 - w.2` inside a spatial ball
  of radius `2 ^ (j+1) r`, so the strip mass estimate
  `stripAbsLintegral_le_morreyNorm` applies with
  `d = 2 √(w'.2 - w.2)`.

Multiplying the two gives `(2 ^ j r) ^ (-1) √(w'.2 - w.2) ^ (2 - 5/θ)`, which
is at most `parabolicDist w w' * (2 ^ j r) ^ (-5/θ)` because
`√(w'.2 - w.2) ≤ 2 ^ j r` and `θ > 5`.

No hypothesis beyond the symbol class, measurability of the source and the
finiteness of its Morrey seminorm enters the statement.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean

/-- The scalar exchange behind the strip estimate: for `θ > 5` and
`0 < d ≤ R`, one power of `R` in the denominator together with the strip
exponent `2 - 5/θ` is worth one factor of `d` and the shell exponent
`-5/θ`. -/
private lemma rpow_strip_exponent_le {θ d R : ℝ} (hθ : 5 < θ) (hd : 0 < d)
    (hdR : d ≤ R) :
    R ^ (-1 : ℝ) * d ^ (2 - 5 / θ) ≤ d * R ^ (-5 / θ) := by
  have hR : 0 < R := hd.trans_le hdR
  have hθpos : 0 < θ := lt_trans (by norm_num) hθ
  have he : 0 ≤ 1 - 5 / θ := sub_nonneg.mpr ((div_le_one hθpos).mpr hθ.le)
  have hpow : d ^ (1 - 5 / θ) ≤ R ^ (1 - 5 / θ) := Real.rpow_le_rpow hd.le hdR he
  calc R ^ (-1 : ℝ) * d ^ (2 - 5 / θ)
      = d * (R ^ (-1 : ℝ) * d ^ (1 - 5 / θ)) := by
        rw [show (2 - 5 / θ : ℝ) = 1 + (1 - 5 / θ) by ring, Real.rpow_add hd,
          Real.rpow_one]
        ring
    _ ≤ d * (R ^ (-1 : ℝ) * R ^ (1 - 5 / θ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hR.le _)) hd.le
    _ = d * R ^ (-5 / θ) := by
        rw [← Real.rpow_add hR]
        congr 2
        ring

/-- **The causal thin-strip estimate on a far shell.**  One constant, fixed
after the symbol and the Morrey exponents and before the source, the base
point, the radius, the shell index and the two observation points, bounds the
kernel-source mass carried by the moving time strip
`{v | w.2 ≤ v.2 ∧ v.2 < w'.2}` inside the shell of radius `2 ^ j r`, by
`parabolicDist w w'` times the shell factor `(2 ^ j r) ^ (-5/θ)` times the
Morrey seminorm of the source. -/
theorem heatFarStripBound (σ : Vec3 → ℂ)
    (hσ : ∀ n : ℕ, ContDiffOn ℝ (n : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ)
    (P θ : ℝ) (hP : 1 ≤ P) (hPθ : P ≤ θ) (hθ : 5 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ParabolicPoint → ℝ),
        AEMeasurable G volume → morreyNorm P θ G < ∞ →
        ∀ (z : ParabolicPoint) (r : ℝ) (j : ℕ), 0 < r → 6 ≤ j →
          ∀ (w w' : ParabolicPoint),
            w ∈ Metric.ball z r → w' ∈ Metric.ball z r → w.2 ≤ w'.2 →
            IntegrableOn
              (fun v : ParabolicPoint =>
                spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2) * (G v : ℂ))
              ((Metric.ball z ((2 : ℝ) ^ (j + 1) * r) \
                Metric.ball z ((2 : ℝ) ^ j * r)) ∩
                {v : ParabolicPoint | w.2 ≤ v.2 ∧ v.2 < w'.2}) volume ∧
            (∫ v in ((Metric.ball z ((2 : ℝ) ^ (j + 1) * r) \
                Metric.ball z ((2 : ℝ) ^ j * r)) ∩
                {v : ParabolicPoint | w.2 ≤ v.2 ∧ v.2 < w'.2}),
              ‖spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2) *
                (G v : ℂ)‖) ≤
              C * parabolicDist w w' *
                ((2 : ℝ) ^ (j : ℝ) * r) ^ (-5 / θ) *
                (morreyNorm P θ G).toReal := by
  have hθ0 : (0 : ℝ) < θ := lt_trans (by norm_num) hθ
  obtain ⟨CK, hCK0, hKB⟩ :=
    exists_spatialMultiplierHeatKernel_crossZero_bounds σ
      (contDiffOn_infty.mpr hσ) hhom
  obtain ⟨CS, hCS0, hSB⟩ := exists_stripAbsIntegral_bound hP hPθ
  refine ⟨512 * CK * CS, by positivity, ?_⟩
  intro G hG hGM z r j hr hj w w' hw hw' hww'
  set R : ℝ := (2 : ℝ) ^ j * r with hRdef
  have hRr : ((2 : ℝ) ^ (j : ℝ) * r) = R := by rw [hRdef, Real.rpow_natCast]
  rw [hRr]
  set S : Set ParabolicPoint :=
    (Metric.ball z ((2 : ℝ) ^ (j + 1) * r) \ Metric.ball z R) ∩
      {v : ParabolicPoint | w.2 ≤ v.2 ∧ v.2 < w'.2} with hSdef
  set f : ParabolicPoint → ℂ := fun v =>
    spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2) * (G v : ℂ) with hfdef
  have hRpos : (0 : ℝ) < R := by
    rw [hRdef]; positivity
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hR64 : 64 * r ≤ R := by
    rw [hRdef, show (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) by norm_num]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hr.le
  have hMnn : (0 : ℝ) ≤ (morreyNorm P θ G).toReal := ENNReal.toReal_nonneg
  have hDnn : (0 : ℝ) ≤ parabolicDist w w' := by
    rw [← dist_eq_parabolicDist]; exact dist_nonneg
  have hsp : ∀ p q : ParabolicPoint,
      vec3EuclideanNorm (p.1 - q.1) ≤ dist p q := by
    intro p q
    rw [dist_eq_parabolicDist]
    exact le_max_left _ _
  have htm : ∀ p q : ParabolicPoint,
      Real.sqrt |p.2 - q.2| ≤ dist p q := by
    intro p q
    rw [dist_eq_parabolicDist]
    exact le_max_right _ _
  have hwz : dist w z < r := Metric.mem_ball.mp hw
  have hw'z : dist w' z < r := Metric.mem_ball.mp hw'
  have hwt : |w.2 - z.2| < r ^ 2 :=
    (Real.sqrt_lt' hr).mp (lt_of_le_of_lt (htm w z) hwz)
  have hw't : |w'.2 - z.2| < r ^ 2 :=
    (Real.sqrt_lt' hr).mp (lt_of_le_of_lt (htm w' z) hw'z)
  have htimegap : w'.2 - w.2 < 2 * r ^ 2 := by
    have h1 := le_abs_self (w'.2 - z.2)
    have h2 := neg_abs_le (w.2 - z.2)
    linarith only [h1, h2, hwt, hw't]
  rcases eq_or_lt_of_le hww' with heq | hlt
  · -- Equal observation times: the strip is empty.
    have hempty : {v : ParabolicPoint | w.2 ≤ v.2 ∧ v.2 < w'.2} =
        (∅ : Set ParabolicPoint) := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
        not_lt]
      intro h1
      rw [← heq]
      exact h1
    have hSempty : S = (∅ : Set ParabolicPoint) := by
      rw [hSdef, hempty, Set.inter_empty]
    rw [hSempty]
    refine ⟨integrableOn_empty, ?_⟩
    rw [setIntegral_empty]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hDnn)
      (Real.rpow_nonneg hRpos.le _)) hMnn
  · -- Genuinely moving strip.
    set h : ℝ := Real.sqrt (w'.2 - w.2) with hhdef
    have hgap : 0 < w'.2 - w.2 := sub_pos.mpr hlt
    have hhpos : 0 < h := by rw [hhdef]; exact Real.sqrt_pos.mpr hgap
    have hhsq : h ^ 2 = w'.2 - w.2 := by
      rw [hhdef]; exact Real.sq_sqrt hgap.le
    have hh2r : h < 2 * r := by
      rw [hhdef]
      refine (Real.sqrt_lt' (by positivity)).mpr ?_
      have hsq4 : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
      have hrsq : (0 : ℝ) < r ^ 2 := pow_pos hr 2
      linarith only [htimegap, hrsq, hsq4]
    have hhR : h ≤ R := by linarith only [hh2r, hR64, hRpos]
    -- The strip sits inside a thin slab over the doubled spatial ball.
    have hincl : S ⊆ parabolicStrip z.1 w'.2 (2 * R) (2 * h) := by
      intro v hv
      rw [hSdef] at hv
      obtain ⟨⟨hvin, hvout⟩, hvt1, hvt2⟩ := hv
      have hballR : dist v z < 2 * R := by
        have hd := Metric.mem_ball.mp hvin
        have h2R : (2 : ℝ) ^ (j + 1) * r = 2 * R := by rw [hRdef, pow_succ]; ring
        rwa [h2R] at hd
      have h4 : (2 * h) ^ 2 = 4 * (w'.2 - w.2) := by rw [← hhsq]; ring
      refine ⟨lt_of_le_of_lt (hsp v z) hballR, ?_, hvt2.le⟩
      rw [h4]
      linarith only [hvt1, hlt]
    -- The far shell forces spatial separation, so the kernel is uniformly small.
    have hAbound : ∀ v ∈ S,
        ‖spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2)‖ ≤
          CK * (16 / R ^ 4) := by
      intro v hv
      rw [hSdef] at hv
      obtain ⟨⟨hvin, hvout⟩, hvt1, hvt2⟩ := hv
      have hvz : R ≤ dist v z := by
        by_contra hcon
        exact hvout (Metric.mem_ball.mpr (not_le.mp hcon))
      have hvw' : R - r ≤ dist v w' := by
        have htri : dist v z ≤ dist v w' + dist w' z := dist_triangle v w' z
        linarith only [htri, hvz, hw'z]
      have htimesmall : Real.sqrt |v.2 - w'.2| < 2 * r := by
        refine (Real.sqrt_lt' (by positivity)).mpr ?_
        have habs : |v.2 - w'.2| = w'.2 - v.2 := by
          rw [abs_of_nonpos (by linarith only [hvt2])]
          ring
        have hsq4 : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
        have hrsq : (0 : ℝ) < r ^ 2 := pow_pos hr 2
        rw [habs]
        linarith only [hvt1, htimegap, hrsq, hsq4]
      have hmaxeq : dist v w' =
          max (vec3EuclideanNorm (v.1 - w'.1)) (Real.sqrt |v.2 - w'.2|) := by
        rw [dist_eq_parabolicDist]
        rfl
      have hspatial : R - r ≤ vec3EuclideanNorm (v.1 - w'.1) := by
        rw [hmaxeq] at hvw'
        rcases le_max_iff.mp hvw' with hcase | hcase
        · exact hcase
        · exact absurd hcase (not_le.mpr (by linarith only [htimesmall, hR64, hr]))
      have hnormeq : vec3EuclideanNorm (w'.1 - v.1) =
          vec3EuclideanNorm (v.1 - w'.1) := by
        rw [← vec3EuclideanNorm_neg (v.1 - w'.1), neg_sub]
      have hhalf : (0 : ℝ) < R / 2 := by positivity
      have hm : R / 2 ≤
          max (vec3EuclideanNorm (w'.1 - v.1)) (Real.sqrt |w'.2 - v.2|) := by
        refine le_trans ?_ (le_max_left _ _)
        rw [hnormeq]
        linarith only [hspatial, hR64, hr, hRpos]
      have hpow : (max (vec3EuclideanNorm (w'.1 - v.1))
          (Real.sqrt |w'.2 - v.2|)) ^ (-4 : ℝ) ≤ 16 / R ^ 4 := by
        refine (Real.rpow_le_rpow_of_nonpos hhalf hm (by norm_num)).trans_eq ?_
        rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg hhalf.le,
          show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp
        ring
      calc ‖spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2)‖
          ≤ CK * (max (vec3EuclideanNorm (w'.1 - v.1))
              (Real.sqrt |w'.2 - v.2|)) ^ (-4 : ℝ) :=
            (hKB (w'.1 - v.1) (w'.2 - v.2)).1
        _ ≤ CK * (16 / R ^ 4) := mul_le_mul_of_nonneg_left hpow hCK0
    have hAnn : (0 : ℝ) ≤ CK * (16 / R ^ 4) :=
      mul_nonneg hCK0 (by positivity)
    have hSmeas : MeasurableSet S := by
      rw [hSdef]
      refine (Metric.isOpen_ball.measurableSet.diff
        Metric.isOpen_ball.measurableSet).inter ?_
      have hpre : {v : ParabolicPoint | w.2 ≤ v.2 ∧ v.2 < w'.2} =
          (fun v : ParabolicPoint => v.2) ⁻¹' (Set.Ico w.2 w'.2) := rfl
      rw [hpre]
      exact measurable_snd measurableSet_Ico
    have hKmeas : Measurable (fun v : ParabolicPoint =>
        spatialMultiplierHeatKernel σ (w'.1 - v.1) (w'.2 - v.2)) :=
      (measurable_spatialMultiplierHeatKernel (contDiffOn_infty.mpr hσ) hhom).comp
        ((measurable_const.sub measurable_fst).prodMk
          (measurable_const.sub measurable_snd))
    have hfmeas : AEStronglyMeasurable f volume := by
      rw [hfdef]
      exact hKmeas.aestronglyMeasurable.mul
        (Complex.continuous_ofReal.measurable.comp_aemeasurable hG).aestronglyMeasurable
    have hptw : ∀ v ∈ S, ‖f v‖ ≤ (CK * (16 / R ^ 4)) * |G v| := by
      intro v hv
      simp only [hfdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hAbound v hv) (abs_nonneg _)
    obtain ⟨hGint, hGbound⟩ :=
      hSB hG hGM z.1 w'.2 (2 * R) (2 * h) (by positivity)
        (by linarith only [hhR])
    have hGabs : Integrable (fun v => |G v|)
        (volume.restrict (parabolicStrip z.1 w'.2 (2 * R) (2 * h))) := hGint.abs
    have hInonneg : (0 : ℝ) ≤
        ∫ v in parabolicStrip z.1 w'.2 (2 * R) (2 * h), |G v| :=
      integral_nonneg fun v => abs_nonneg _
    have hlintstrip :
        (∫⁻ v in parabolicStrip z.1 w'.2 (2 * R) (2 * h), ENNReal.ofReal |G v|) =
          ENNReal.ofReal
            (∫ v in parabolicStrip z.1 w'.2 (2 * R) (2 * h), |G v|) :=
      (ofReal_integral_eq_lintegral_ofReal hGabs
        (Filter.Eventually.of_forall fun v => abs_nonneg (G v))).symm
    have hlintS : (∫⁻ v in S, ‖f v‖ₑ) ≤
        ENNReal.ofReal ((CK * (16 / R ^ 4)) *
          ∫ v in parabolicStrip z.1 w'.2 (2 * R) (2 * h), |G v|) := by
      have step1 : (∫⁻ v in S, ‖f v‖ₑ) ≤
          ∫⁻ v in S, ENNReal.ofReal ((CK * (16 / R ^ 4)) * |G v|) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem hSmeas ?_)
        intro v hv
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hptw v hv)
      have step2 : (∫⁻ v in S, ENNReal.ofReal ((CK * (16 / R ^ 4)) * |G v|)) =
          ENNReal.ofReal (CK * (16 / R ^ 4)) * ∫⁻ v in S, ENNReal.ofReal |G v| := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun v => ENNReal.ofReal_mul hAnn
      have step3 : (∫⁻ v in S, ENNReal.ofReal |G v|) ≤
          ∫⁻ v in parabolicStrip z.1 w'.2 (2 * R) (2 * h), ENNReal.ofReal |G v| :=
        lintegral_mono_set hincl
      calc (∫⁻ v in S, ‖f v‖ₑ)
          ≤ ∫⁻ v in S, ENNReal.ofReal ((CK * (16 / R ^ 4)) * |G v|) := step1
        _ = ENNReal.ofReal (CK * (16 / R ^ 4)) *
              ∫⁻ v in S, ENNReal.ofReal |G v| := step2
        _ ≤ ENNReal.ofReal (CK * (16 / R ^ 4)) *
              ∫⁻ v in parabolicStrip z.1 w'.2 (2 * R) (2 * h),
                ENNReal.ofReal |G v| := mul_le_mul_right step3 _
        _ = ENNReal.ofReal (CK * (16 / R ^ 4)) *
              ENNReal.ofReal
                (∫ v in parabolicStrip z.1 w'.2 (2 * R) (2 * h), |G v|) := by
              rw [hlintstrip]
        _ = ENNReal.ofReal ((CK * (16 / R ^ 4)) *
              ∫ v in parabolicStrip z.1 w'.2 (2 * R) (2 * h), |G v|) :=
              (ENNReal.ofReal_mul hAnn).symm
    have hfint : IntegrableOn f S volume := by
      refine ⟨hfmeas.restrict, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      exact lt_of_le_of_lt hlintS ENNReal.ofReal_lt_top
    refine ⟨hfint, ?_⟩
    rw [integral_norm_eq_lintegral_enorm hfmeas.restrict]
    have htoR : (∫⁻ v in S, ‖f v‖ₑ).toReal ≤
        (CK * (16 / R ^ 4)) *
          ∫ v in parabolicStrip z.1 w'.2 (2 * R) (2 * h), |G v| := by
      have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlintS
      rwa [ENNReal.toReal_ofReal (mul_nonneg hAnn hInonneg)] at hmono
    refine htoR.trans ?_
    refine (mul_le_mul_of_nonneg_left hGbound hAnn).trans ?_
    -- the remaining inequality is scalar
    have h2h : (2 * h) ^ (2 - 5 / θ : ℝ) ≤ 4 * h ^ (2 - 5 / θ : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hhpos.le]
      have h5 : (0 : ℝ) ≤ 5 / θ := by positivity
      have hle : (2 : ℝ) ^ (2 - 5 / θ : ℝ) ≤ 4 := by
        refine (Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (show (2 - 5 / θ : ℝ) ≤ 2 by linarith only [h5])).trans_eq ?_
        norm_num
      exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hhpos.le _)
    have hexp := rpow_strip_exponent_le (θ := θ) (d := h) (R := R) hθ hhpos hhR
    have hCSnn : (0 : ℝ) ≤ CS * (2 * R) ^ 3 := mul_nonneg hCS0 (by positivity)
    have hCCnn : (0 : ℝ) ≤ 512 * CK * CS := by positivity
    calc (CK * (16 / R ^ 4)) *
          (CS * (2 * R) ^ 3 * (2 * h) ^ (2 - 5 / θ : ℝ) *
            (morreyNorm P θ G).toReal)
        ≤ (CK * (16 / R ^ 4)) *
            (CS * (2 * R) ^ 3 * (4 * h ^ (2 - 5 / θ : ℝ)) *
              (morreyNorm P θ G).toReal) := by
          refine mul_le_mul_of_nonneg_left ?_ hAnn
          refine mul_le_mul_of_nonneg_right ?_ hMnn
          exact mul_le_mul_of_nonneg_left h2h hCSnn
      _ = (512 * CK * CS) * (R ^ (-1 : ℝ) * h ^ (2 - 5 / θ : ℝ)) *
            (morreyNorm P θ G).toReal := by
          rw [Real.rpow_neg_one]
          field_simp
          ring
      _ ≤ (512 * CK * CS) * (h * R ^ (-5 / θ : ℝ)) *
            (morreyNorm P θ G).toReal := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp hCCnn) hMnn
      _ ≤ (512 * CK * CS) * (parabolicDist w w' * R ^ (-5 / θ : ℝ)) *
            (morreyNorm P θ G).toReal := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ?_ hCCnn) hMnn
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hRpos.le _)
          have habs : |w.2 - w'.2| = w'.2 - w.2 := by
            rw [abs_of_nonpos (by linarith only [hlt])]
            ring
          have hmax : parabolicDist w w' =
              max (vec3EuclideanNorm (w.1 - w'.1))
                (Real.sqrt |w.2 - w'.2|) := rfl
          rw [hmax, hhdef, ← habs]
          exact le_max_right _ _
      _ = (512 * CK * CS) * parabolicDist w w' * R ^ (-5 / θ : ℝ) *
            (morreyNorm P θ G).toReal := by ring

end CKN.Core.HeatPotential
