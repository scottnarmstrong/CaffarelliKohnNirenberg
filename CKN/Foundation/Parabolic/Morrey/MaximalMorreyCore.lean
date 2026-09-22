-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.AdamsM4
import CKN.Foundation.Parabolic.BallDisplays

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The Morrey ball norm controls each local power integral at the scaling exponent. -/
theorem ballPowerIntegral_le_morreyBallNorm_pow
    {p q : ℝ} (hp : 0 < p) {f : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    ballPowerIntegral p f z r ≤
      (ENNReal.ofReal r) ^ (5 * (1 - p / q)) * morreyBallNorm p q f ^ p := by
  let A : ℝ≥0∞ := ENNReal.ofReal r
  let I : ℝ≥0∞ := ballPowerIntegral p f z r
  let α : ℝ := 5 * (1 - p / q)
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact (ENNReal.ofReal_pos.mpr hr).ne'
  have hAtop : A ≠ ∞ := by
    dsimp [A]
    exact ENNReal.ofReal_ne_top
  have hcell : morreyBallCell p q f z r ≤ morreyBallNorm p q f := by
    unfold morreyBallNorm
    exact le_iSup_of_le z (le_iSup_of_le ⟨r, hr⟩ le_rfl)
  have hpow' := ENNReal.rpow_le_rpow hcell hp.le
  rw [morreyBallCell] at hpow'
  have hpow_raw : ((A ^ (-α / p) * (I ^ (1 / p))) ^ p) ≤
      morreyBallNorm p q f ^ p := by
    have hexp : -(5 * (1 - p / q) / p) = -(5 * (1 - p / q)) / p := by
      ring_nf
    rw [hexp] at hpow'
    simpa [A, I, α] using hpow'
  have hpow_eq : (A ^ (-α / p) * (I ^ (1 / p))) ^ p =
      A ^ (-α) * I := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    have hα : (-α / p) * p = -α := by
      field_simp [hp.ne']
    have hpone : (1 / p) * p = 1 := by
      field_simp [hp.ne']
    rw [hα, hpone, ENNReal.rpow_one]
  have hpow : A ^ (-α) * I ≤ morreyBallNorm p q f ^ p := by
    rw [← hpow_eq]
    exact hpow_raw
  have hscale : A ^ α * (A ^ (-α) * I) = I := by
    calc
      A ^ α * (A ^ (-α) * I) = (A ^ α * A ^ (-α)) * I := by ac_rfl
      _ = A ^ (α + (-α)) * I := by
        rw [← ENNReal.rpow_add _ _ hA0 hAtop]
      _ = I := by rw [add_neg_cancel, ENNReal.rpow_zero, one_mul]
  have hmul := mul_le_mul_left hpow (A ^ α)
  have hmul' : A ^ α * (A ^ (-α) * I) ≤
      A ^ α * morreyBallNorm p q f ^ p := by
    simpa [mul_comm] using hmul
  rw [hscale] at hmul'
  calc
    I ≤ A ^ α * morreyBallNorm p q f ^ p := hmul'
    _ = (ENNReal.ofReal r) ^ (5 * (1 - p / q)) * morreyBallNorm p q f ^ p := by
      rfl

/-- The parabolic metric ball volume scales as the fifth power of its radius. -/
theorem metricBall_volume_scale {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) :
    volume (Metric.ball z r) =
      volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
        ((0 : Vec3), (0 : ℝ)) 1) * ENNReal.ofReal r ^ (5 : ℝ) := by
  let A : ℝ≥0∞ := ENNReal.ofReal r
  have hVb : volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
      ((0 : Vec3), (0 : ℝ)) 1) =
      ENNReal.ofReal (8 * Real.pi / 3) := by
    simpa using (volume_metricBall ((0 : Vec3), (0 : ℝ))
      (r := 1) (by norm_num : (0 : ℝ) ≤ 1))
  calc
    volume (Metric.ball z r) = ENNReal.ofReal (8 * Real.pi / 3 * r ^ 5) :=
      volume_metricBall z hr.le
    _ = ENNReal.ofReal (8 * Real.pi / 3) * ENNReal.ofReal (r ^ 5) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * Real.pi / 3)]
    _ = ENNReal.ofReal (8 * Real.pi / 3) * A ^ (5 : ℝ) := by
      rw [ENNReal.ofReal_pow hr.le]
      simp [A]
    _ = volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
        ((0 : Vec3), (0 : ℝ)) 1) * ENNReal.ofReal r ^ (5 : ℝ) := by
      rw [← hVb]

private theorem ballHolderExponents {p : ℝ} (hp : 1 < p) :
    p.HolderConjugate (p / (p - 1)) := by
  apply Real.holderConjugate_iff.mpr
  constructor
  · exact hp
  · have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
    field_simp [hp0, sub_ne_zero.mpr (ne_of_gt (sub_pos.mpr hp))]
    ring

/-- A local average is bounded by the parabolic Morrey ball norm. -/
theorem metricBall_average_le_morreyBallNorm
    {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in Metric.ball z r, ENNReal.ofReal |f w|) /
        volume (Metric.ball z r) ≤
    (volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
      ((0 : Vec3), (0 : ℝ)) 1)) ^ (-(1 / p)) *
        ENNReal.ofReal r ^ (-(5 / q)) * morreyBallNorm p q f := by
  let A : ℝ≥0∞ := ENNReal.ofReal r
  let V : ℝ≥0∞ := volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
    ((0 : Vec3), (0 : ℝ)) 1)
  let μ : Measure ParabolicPoint := volume.restrict (Metric.ball z r)
  let F : ParabolicPoint → ℝ≥0∞ := fun w => ENNReal.ofReal |f w|
  let e : ℝ := 5 * (1 - p / q)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le hp0 hpq
  have he : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr ((div_le_one hq0).2 hpq))
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact (ENNReal.ofReal_pos.mpr hr).ne'
  have hAtop : A ≠ ∞ := by dsimp [A]; exact ENNReal.ofReal_ne_top
  have hV0 : V ≠ 0 := by
    rw [show V = ENNReal.ofReal (8 * Real.pi / 3) by
      dsimp [V]
      simpa using (volume_metricBall ((0 : Vec3), (0 : ℝ))
        (r := 1) (by norm_num : (0 : ℝ) ≤ 1))]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hVtop : V ≠ ∞ := by
    rw [show V = ENNReal.ofReal (8 * Real.pi / 3) by
      dsimp [V]
      simpa using (volume_metricBall ((0 : Vec3), (0 : ℝ))
        (r := 1) (by norm_num : (0 : ℝ) ≤ 1))]
    exact ENNReal.ofReal_ne_top
  have hvol : volume (Metric.ball z r) = V * A ^ (5 : ℝ) := by
    have hV : V = ENNReal.ofReal (8 * Real.pi / 3) := by
      dsimp [V]
      simpa using (volume_metricBall ((0 : Vec3), (0 : ℝ))
        (r := 1) (by norm_num : (0 : ℝ) ≤ 1))
    rw [hV, volume_metricBall z hr.le]
    calc
      ENNReal.ofReal (8 * Real.pi / 3 * r ^ 5) =
          ENNReal.ofReal (8 * Real.pi / 3) * ENNReal.ofReal (r ^ 5) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * Real.pi / 3)]
      _ = ENNReal.ofReal (8 * Real.pi / 3) * A ^ (5 : ℝ) := by
        rw [ENNReal.ofReal_pow hr.le]
        simp [A]
  have hF : AEMeasurable F μ := by
    simpa [F, μ, Real.norm_eq_abs] using hf.norm.restrict.ennreal_ofReal
  have hconst : AEMeasurable (fun _ : ParabolicPoint => (1 : ℝ≥0∞)) μ :=
    aemeasurable_const
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (ballHolderExponents hp) hF hconst
  simp only [Pi.mul_apply, mul_one] at hHolder
  have hsource : (∫⁻ w, F w ^ p ∂μ) = ballPowerIntegral p f z r := by
    rfl
  rw [hsource] at hHolder
  have hvolint : (∫⁻ _w : ParabolicPoint, (1 : ℝ≥0∞) ^ (p / (p - 1)) ∂μ) =
      volume (Metric.ball z r) := by
    simp [μ]
  rw [hvolint] at hHolder
  have hconj : 1 / (p / (p - 1)) = 1 - 1 / p := by
    field_simp [hp0.ne', sub_ne_zero.mpr (ne_of_gt (sub_pos.mpr hp))]
  rw [hconj] at hHolder
  have hlocal := ballPowerIntegral_le_morreyBallNorm_pow
    (p := p) (q := q) (f := f) (z := z) (r := r) hp0 hr
  have hinvP : 0 ≤ 1 / p := one_div_nonneg.mpr hp0.le
  have hroot := ENNReal.rpow_le_rpow hlocal hinvP
  have hrootEq : ((A ^ e * morreyBallNorm p q f ^ p) ^ (1 / p)) =
      A ^ (e / p) * morreyBallNorm p q f := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hinvP, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    have hexp₁ : e * (1 / p) = e / p := by ring
    have hexp₂ : p * (1 / p) = 1 := by field_simp [hp0.ne']
    rw [hexp₁, hexp₂, ENNReal.rpow_one]
  have hlintegral : (∫⁻ w in Metric.ball z r, F w) ≤
      A ^ (e / p) * morreyBallNorm p q f *
        volume (Metric.ball z r) ^ (1 - 1 / p) := by
    calc
      _ ≤ (ballPowerIntegral p f z r) ^ (1 / p) *
          volume (Metric.ball z r) ^ (1 - 1 / p) := by
        simpa [μ, F] using hHolder
      _ ≤ (A ^ e * morreyBallNorm p q f ^ p) ^ (1 / p) *
          volume (Metric.ball z r) ^ (1 - 1 / p) := by
        gcongr
      _ = A ^ (e / p) * morreyBallNorm p q f *
          volume (Metric.ball z r) ^ (1 - 1 / p) := by rw [hrootEq]
  have htarget :
      (volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
        ((0 : Vec3), (0 : ℝ)) 1)) ^ (-(1 / p)) *
        ENNReal.ofReal r ^ (-(5 / q)) * morreyBallNorm p q f *
        volume (Metric.ball z r) =
      A ^ (e / p) * morreyBallNorm p q f *
        volume (Metric.ball z r) ^ (1 - 1 / p) := by
    change (V ^ (-(1 / p)) * ENNReal.ofReal r ^ (-(5 / q)) *
        morreyBallNorm p q f) * volume (Metric.ball z r) =
      A ^ (e / p) * morreyBallNorm p q f *
        volume (Metric.ball z r) ^ (1 - 1 / p)
    rw [hvol]
    have hA5top : A ^ (5 : ℝ) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAtop
    rw [ENNReal.mul_rpow_of_ne_top hVtop hA5top]
    have hA5pow : (A ^ (5 : ℝ)) ^ (1 - 1 / p) =
        A ^ (5 * (1 - 1 / p)) := by
      rw [← ENNReal.rpow_mul]
    rw [hA5pow]
    have hexpV : -(1 / p) + 1 = 1 - 1 / p := by ring
    have hexpA : -(5 / q) + 5 = e / p + 5 * (1 - 1 / p) := by
      dsimp [e]
      field_simp [hp0.ne', hq0.ne']
      ring
    have hVpow : V ^ (-(1 / p)) * V = V ^ (1 - 1 / p) := by
      calc
        V ^ (-(1 / p)) * V = V ^ (-(1 / p)) * V ^ (1 : ℝ) := by
          rw [ENNReal.rpow_one]
        _ = V ^ (-(1 / p) + 1) := by
          rw [← ENNReal.rpow_add _ _ hV0 hVtop]
        _ = V ^ (1 - 1 / p) := by rw [hexpV]
    have hApow : A ^ (-(5 / q)) * A ^ (5 : ℝ) =
        A ^ (e / p + 5 * (1 - 1 / p)) := by
      rw [← ENNReal.rpow_add _ _ hA0 hAtop, hexpA]
    calc
      (V ^ (-(1 / p)) * ENNReal.ofReal r ^ (-(5 / q)) *
          morreyBallNorm p q f) * (V * A ^ (5 : ℝ)) =
          (V ^ (-(1 / p)) * V) *
            (ENNReal.ofReal r ^ (-(5 / q)) * A ^ (5 : ℝ)) *
              morreyBallNorm p q f := by ac_rfl
      _ = V ^ (1 - 1 / p) *
          A ^ (e / p + 5 * (1 - 1 / p)) * morreyBallNorm p q f := by
        rw [hVpow, show ENNReal.ofReal r = A by rfl, hApow]
      _ = A ^ (e / p) * morreyBallNorm p q f *
          (V ^ (1 - 1 / p) * A ^ (5 * (1 - 1 / p))) := by
        rw [ENNReal.rpow_add _ _ hA0 hAtop]
        ac_rfl
  apply (ENNReal.div_le_iff (volume_parabolicBall_pos hr).ne'
    (volume_parabolicBall_lt_top hr).ne).2
  calc
    (∫⁻ w in Metric.ball z r, F w) ≤
        A ^ (e / p) * morreyBallNorm p q f *
          volume (Metric.ball z r) ^ (1 - 1 / p) := hlintegral
    _ = (V ^ (-(1 / p)) * ENNReal.ofReal r ^ (-(5 / q)) *
          morreyBallNorm p q f) * volume (Metric.ball z r) := htarget.symm

/-- Almost everywhere equal functions have the same parabolic Morrey ball norm. -/
theorem morreyBallNorm_congr_ae
    {p q : ℝ} {f g : ParabolicPoint → ℝ}
    (hfg : f =ᵐ[volume] g) : morreyBallNorm p q f = morreyBallNorm p q g := by
  unfold morreyBallNorm
  apply iSup_congr
  intro z
  apply iSup_congr
  intro r
  unfold morreyBallCell
  have hI : ballPowerIntegral p f z r = ballPowerIntegral p g z r := by
    unfold ballPowerIntegral
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hfg] with w hw
    simp [hw]
  rw [hI]

/-- Almost everywhere equal data have the same parabolic maximal function. -/
theorem parabolicMaximalFunction_congr_ae
    {F G : ParabolicPoint → ℝ≥0∞} (hFG : F =ᵐ[volume] G) :
    ∀ z, parabolicMaximalFunction F z = parabolicMaximalFunction G z := by
  intro z
  unfold parabolicMaximalFunction
  apply iSup_congr
  intro c
  apply iSup_congr
  intro r
  by_cases hz : z ∈ Metric.ball c r
  · simp only [indicator_of_mem hz]
    exact setLAverage_congr_fun_ae Metric.isOpen_ball.measurableSet
      (by
        filter_upwards [hFG] with w hw
        intro _
        exact hw)
  · simp only [indicator_of_notMem hz]

/-- The maximal function of the data outside a larger ball has a Morrey tail bound. -/
theorem parabolicMaximalFunction_compl_ball_le_morreyBallNorm
    {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) {c z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) (hz : z ∈ Metric.ball c r) :
    parabolicMaximalFunction
        ((Metric.ball c (4 * r))ᶜ.indicator (fun w ↦ ENNReal.ofReal |f w|)) z ≤
      (volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
        ((0 : Vec3), (0 : ℝ)) 1)) ^ (-(1 / p)) *
        ENNReal.ofReal r ^ (-(5 / q)) * morreyBallNorm p q f := by
  let F : ParabolicPoint → ℝ≥0∞ := fun w ↦ ENNReal.ofReal |f w|
  let U : Set ParabolicPoint := Metric.ball c (4 * r)
  let B : ℝ≥0∞ :=
    (volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
      ((0 : Vec3), (0 : ℝ)) 1)) ^ (-(1 / p)) *
      ENNReal.ofReal r ^ (-(5 / q)) * morreyBallNorm p q f
  have hq0 : 0 < q := lt_of_lt_of_le (lt_trans zero_lt_one hp) hpq
  have hB : ∀ {d : ParabolicPoint} {s : ℝ}, 0 < s →
      (⨍⁻ w in Metric.ball d s, F w ∂volume) ≤
        (volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
          ((0 : Vec3), (0 : ℝ)) 1)) ^ (-(1 / p)) *
          ENNReal.ofReal s ^ (-(5 / q)) * morreyBallNorm p q f := by
    intro d s hs
    rw [setLAverage_eq]
    simpa [F, B] using
      (metricBall_average_le_morreyBallNorm hp hpq hf (z := d) (r := s) hs)
  rw [parabolicMaximalFunction]
  refine iSup_le fun d ↦ iSup_le fun s ↦ ?_
  by_cases hzd : z ∈ Metric.ball d s
  · simp only [indicator_of_mem hzd]
    have hs : 0 < s := lt_of_le_of_lt dist_nonneg (by
      simpa [mem_ball] using hzd)
    by_cases hsub : Metric.ball d s ⊆ U
    · have hzero : ∀ᵐ w ∂volume.restrict (Metric.ball d s),
          Uᶜ.indicator F w = 0 := by
        filter_upwards [self_mem_ae_restrict
          (Metric.isOpen_ball.measurableSet : MeasurableSet (Metric.ball d s))]
          with w hw
        simp [hsub hw]
      rw [setLAverage_eq]
      have hzero' :
          (∫⁻ w in Metric.ball d s, Uᶜ.indicator F w) = 0 :=
        lintegral_eq_zero_of_ae_eq_zero hzero
      rw [hzero']
      simp
    · obtain ⟨w, hwd, hwU⟩ := Set.not_subset.mp hsub
      have hinner : 4 * r ≤ dist w c := by
        apply le_of_not_gt
        intro hlt
        apply hwU
        exact hlt
      have htriangle : dist w c ≤ dist w d + (dist d z + dist z c) := by
        exact (dist_triangle w d c).trans
          (add_le_add (le_refl _) (dist_triangle d z c))
      have hlt : dist w c < s + (s + r) := by
        calc
          dist w c ≤ dist w d + (dist d z + dist z c) := htriangle
          _ < s + (s + r) := by
            gcongr
            · simpa [mem_ball] using hwd
            · simpa [mem_ball, dist_comm] using hzd
            · simpa [mem_ball] using hz
      have hsr : r < s := by
        by_contra hnot
        have hsr' : s ≤ r := le_of_not_gt hnot
        linarith only [hinner, hlt, hr, hsr']
      rw [setLAverage_eq]
      calc
        (∫⁻ w in Metric.ball d s, Uᶜ.indicator F w) /
            volume (Metric.ball d s) ≤
          (∫⁻ w in Metric.ball d s, F w) /
              volume (Metric.ball d s) := by
          gcongr
          by_cases hy : w ∈ Uᶜ
          · simp [hy]
          · simp [hy]
        _ ≤ B := by
          have hBs :
              (∫⁻ w in Metric.ball d s, F w) / volume (Metric.ball d s) ≤
                (volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
                  ((0 : Vec3), (0 : ℝ)) 1)) ^ (-(1 / p)) *
                  ENNReal.ofReal s ^ (-(5 / q)) * morreyBallNorm p q f := by
            simpa only [setLAverage_eq] using hB (d := d) (s := s) hs
          exact hBs.trans (by
            have hbase : ENNReal.ofReal r ^ (5 / q) ≤
                ENNReal.ofReal s ^ (5 / q) := by
              exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hsr.le)
                (div_nonneg (by norm_num) hq0.le)
            have hinv : ENNReal.ofReal s ^ (-(5 / q)) ≤
                ENNReal.ofReal r ^ (-(5 / q)) := by
              rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ENNReal.inv_le_inv]
              exact hbase
            have hcoeff := mul_le_mul_left hinv
              ((volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace
                ((0 : Vec3), (0 : ℝ)) 1)) ^ (-(1 / p)))
            have hmul := mul_le_mul_right hcoeff (morreyBallNorm p q f)
            simpa [B, mul_assoc, mul_left_comm, mul_comm] using hmul)
  · change (Metric.ball d s).indicator _ z ≤ _
    rw [indicator_of_notMem hzd]
    exact bot_le

/-- The far-field coefficient in the Adams estimate is at least one. -/
theorem one_le_adamsFarCoefficient
    {P τ : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) :
    1 ≤ volume (parabolicCylinder 0 0 1) *
      (((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / τ)) /
        volume (parabolicCylinder 0 0 1)) *
          volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)) ^ P := by
  let V : ℝ≥0∞ := volume (parabolicCylinder 0 0 1)
  let α : ℝ := 5 * (1 - 1 / τ)
  let D : ℝ≥0∞ := ENNReal.ofReal (2 : ℝ) ^ α
  let K : ℝ≥0∞ := (D / V) * V ^ (1 - 1 / P)
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hτ1 : 1 < τ := lt_of_lt_of_le hP hPτ
  have hτ0 : 0 < τ := lt_trans zero_lt_one hτ1
  have hV0 : V ≠ 0 := by
    dsimp [V]
    exact (Integration.volume_parabolicCylinder_pos (by norm_num)).ne'
  have hVtop : V ≠ ∞ := by
    dsimp [V]
    exact Integration.volume_parabolicCylinder_lt_top.ne
  have hα : 0 < α := by
    dsimp [α]
    have hfrac : 1 / τ < 1 := (div_lt_one hτ0).2 hτ1
    exact mul_pos (by norm_num) (sub_pos.mpr hfrac)
  have hD : 1 ≤ D := by
    dsimp [D]
    exact ENNReal.one_le_rpow (by norm_num) hα
  have hfactor : V⁻¹ * V ^ (1 - 1 / P) = V ^ (-(1 / P)) := by
    calc
      V⁻¹ * V ^ (1 - 1 / P) = V ^ (-1 : ℝ) * V ^ (1 - 1 / P) := by
        rw [ENNReal.rpow_neg_one]
      _ = V ^ (-1 + (1 - 1 / P)) := by
        rw [← ENNReal.rpow_add _ _ hV0 hVtop]
      _ = V ^ (-(1 / P)) := by congr 1; ring
  have hK : K = D * V ^ (-(1 / P)) := by
    dsimp [K]
    rw [div_eq_mul_inv]
    calc
      D * V⁻¹ * V ^ (1 - 1 / P) = D * (V⁻¹ * V ^ (1 - 1 / P)) := by ac_rfl
      _ = D * V ^ (-(1 / P)) := by rw [hfactor]
  have hKpow : K ^ P = D ^ P * V⁻¹ := by
    rw [hK, ENNReal.mul_rpow_of_nonneg _ _ hP0.le,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    have hexp : (-(1 / P)) * P = -1 := by field_simp [hP0.ne']
    rw [hexp, ENNReal.rpow_neg_one]
  have hcancel : K ^ P * V = D ^ P := by
    rw [hKpow]
    calc
      D ^ P * V⁻¹ * V = D ^ P * (V⁻¹ * V) := by ac_rfl
      _ = D ^ P := by rw [ENNReal.inv_mul_cancel hV0 hVtop, mul_one]
  have htarget : V * K ^ P = D ^ P := by
    rw [mul_comm V (K ^ P), hcancel]
  calc
    1 ≤ D ^ P := ENNReal.one_le_rpow hD hP0
    _ = V * K ^ P := htarget.symm


end CKN.Foundation.Parabolic.Morrey
