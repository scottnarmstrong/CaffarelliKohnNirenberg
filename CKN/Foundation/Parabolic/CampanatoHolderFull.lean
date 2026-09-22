-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.CampanatoHolderFinal

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

private lemma parabolicCampanatoHolderConstant_nonneg_full {α p : ℝ}
    (hα : 0 < α) : 0 ≤ parabolicCampanatoHolderConstant α p := by
  have htail : 0 ≤ parabolicCampanatoTailConstant α := by
    unfold parabolicCampanatoTailConstant
    apply one_div_nonneg.mpr
    exact sub_nonneg.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hα])).le
  unfold parabolicCampanatoHolderConstant
  positivity

private lemma integrableOn_abs_rpow_of_integrableOn_sub_full
    {s : Set ParabolicPoint} {f : ParabolicPoint → ℝ} {p c : ℝ}
    (hp : 1 ≤ p) (hsTop : volume s < ∞)
    (hf : IntegrableOn f s volume)
    (hfp : IntegrableOn (fun x => |f x - c| ^ p) s volume) :
    IntegrableOn (fun x => |f x| ^ p) s volume := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hcont : Continuous (fun t : ℝ => |t| ^ p) :=
    continuous_abs.rpow_const (fun _ => Or.inr hp0)
  have hmeas : AEStronglyMeasurable (fun x => |f x| ^ p) (volume.restrict s) :=
    hcont.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hmajor : Integrable
      (fun x => (2 : ℝ) ^ (p - 1) * (|f x - c| ^ p + |c| ^ p))
      (volume.restrict s) :=
    (hfp.add (integrableOn_const hsTop.ne)).const_mul ((2 : ℝ) ^ (p - 1))
  refine hmajor.mono' hmeas ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (f x)) p)]
  have hsplit : |f x| ≤ |f x - c| + |c| := by
    calc
      |f x| = |(f x - c) + c| := congrArg abs (by ring)
      _ ≤ |f x - c| + |c| := abs_add_le _ _
  calc
    |f x| ^ p ≤ (|f x - c| + |c|) ^ p :=
      Real.rpow_le_rpow (abs_nonneg _) hsplit hp0
    _ ≤ (2 : ℝ) ^ (p - 1) * (|f x - c| ^ p + |c| ^ p) := by
      have h := NNReal.rpow_add_le_mul_rpow_add_rpow
        (⟨|f x - c|, abs_nonneg _⟩ : ℝ≥0) ⟨|c|, abs_nonneg _⟩ hp
      exact_mod_cast h

private theorem parabolicHolder_implies_globalCampanato_full
    {f : ParabolicPoint → ℝ} {α L p : ℝ}
    (hα : 0 < α) (hp : 1 ≤ p)
    (hdata : GlobalParabolicBallLpData f p)
    (hholder : ParabolicHolderSeminormLE Set.univ f α L) :
    GlobalParabolicBallCampanatoBound f α ((2 : ℝ) ^ α * L) p := by
  have hL : 0 ≤ L := by
    have h := hholder (0, 0) (Set.mem_univ _) (0, 1) (Set.mem_univ _)
    have h' : |f (0, 0) - f (0, 1)| ≤ L := by
      simpa [parabolicDist, vec3EuclideanNorm_zero] using h
    nlinarith only [h', abs_nonneg (f (0, 0) - f (0, 1))]
  intro z r hr
  let s : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r
  have hsPos : 0 < volume s := volume_parabolicBall_pos hr |>.trans_le
    (measure_mono Metric.ball_subset_closedBall)
  have hclosedSubset :
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r ⊆
        @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z (2 * r) :=
    Metric.closedBall_subset_ball (x := z) (ε₁ := r) (ε₂ := 2 * r)
      (by linarith only [hr])
  have hsTop : volume s < ∞ :=
    (measure_mono hclosedSubset).trans_lt (volume_parabolicBall_lt_top (by positivity))
  have hd := hdata z hr
  have hosc : ∀ x ∈ s, |f x - (⨍ y in s, f y)| ≤
      ((2 : ℝ) ^ α * L) * r ^ α := by
    intro x hx
    have hconst : IntegrableOn (fun _ : ParabolicPoint => f x) s volume :=
      integrableOn_const hsTop.ne
    have hdiffInt : IntegrableOn (fun y : ParabolicPoint => f x - f y) s volume :=
      hconst.sub hd.1
    have hdiffAvg : (⨍ y in s, f x - f y) = f x - (⨍ y in s, f y) := by
      calc
        (⨍ y in s, f x - f y) =
            (⨍ y in s, (fun _ : ParabolicPoint => f x) y - f y) := by rfl
        _ = (⨍ y in s, (fun _ : ParabolicPoint => f x) y) -
              (⨍ y in s, f y) :=
          Integration.setAverage_sub_of_integrableOn hconst hd.1
        _ = f x - (⨍ y in s, f y) := by
          rw [Integration.setAverage_const_of_pos_of_lt_top hsPos hsTop]
    have hrad : ∀ y ∈ s, parabolicDist x y ≤ 2 * r := by
      intro y hy
      have hx' : dist x z ≤ r := Metric.mem_closedBall.mp hx
      have hy' : dist y z ≤ r := Metric.mem_closedBall.mp hy
      have htri : dist x y ≤ 2 * r := by
        calc
          dist x y ≤ dist x z + dist z y := dist_triangle x z y
          _ ≤ r + r := add_le_add hx' (by simpa [dist_comm] using hy')
          _ = 2 * r := by ring
      simpa only [← dist_eq_parabolicDist] using htri
    have hpair : ∀ y ∈ s, |f x - f y| ≤ L * (2 * r) ^ α := by
      intro y hy
      have hxy := hholder x (Set.mem_univ x) y (Set.mem_univ y)
      have hpow : parabolicDist x y ^ α ≤ (2 * r) ^ α :=
        Real.rpow_le_rpow (parabolicDist_nonneg x y) (hrad y hy) hα.le
      exact hxy.trans (mul_le_mul_of_nonneg_left hpow hL)
    have habsAvg : |(⨍ y in s, (fun y => f x - f y) y)| ≤
        ⨍ y in s, |f x - f y| := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        (Integration.setAverage_norm_le volume s (fun y => f x - f y))
    have hpointAvg : (⨍ y in s, |f x - f y|) ≤ L * (2 * r) ^ α :=
      by
        simpa only [Integration.setAverage_const_of_pos_of_lt_top hsPos hsTop] using
          (Integration.setAverage_mono_of_ae (hdiffInt.abs)
        (integrableOn_const hsTop.ne)
        (ae_restrict_of_forall_mem Metric.isClosed_closedBall.measurableSet hpair))
    rw [← hdiffAvg]
    calc
      |⨍ y in s, (fun y => f x - f y) y| ≤ ⨍ y in s, |f x - f y| := habsAvg
      _ ≤ L * (2 * r) ^ α := hpointAvg
      _ = ((2 : ℝ) ^ α * L) * r ^ α := by
        rw [Real.mul_rpow (by norm_num) hr.le]
        ring
  have hoscPow : ∀ x ∈ s, |f x - (⨍ y in s, f y)| ^ p ≤
      (((2 : ℝ) ^ α * L) * r ^ α) ^ p := by
    intro x hx
    exact Real.rpow_le_rpow (abs_nonneg _) (hosc x hx) (le_trans zero_le_one hp)
  have havg := Integration.setAverage_mono_of_ae hd.2
    (integrableOn_const hsTop.ne)
    (ae_restrict_of_forall_mem Metric.isClosed_closedBall.measurableSet hoscPow)
  have havg' :
      (⨍ x in s, |f x - (⨍ y in s, f y)| ^ p) ≤
        (((2 : ℝ) ^ α * L) * r ^ α) ^ p := by
    simpa only [s, Integration.setAverage_const_of_pos_of_lt_top hsPos hsTop] using havg
  have hoscNonneg : 0 ≤ (⨍ x in s, |f x - (⨍ y in s, f y)| ^ p) :=
    Integration.setAverage_nonneg_of_ae (Filter.Eventually.of_forall fun _ =>
      Real.rpow_nonneg (abs_nonneg _) _)
  have hM : 0 ≤ ((2 : ℝ) ^ α * L) * r ^ α :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hL)
      (Real.rpow_nonneg hr.le _)
  change (⨍ x in s, |f x - (⨍ y in s, f y)| ^ p) ^ (1 / p) ≤
    (2 : ℝ) ^ α * L * r ^ α
  calc
    _ ≤ ((((2 : ℝ) ^ α * L) * r ^ α) ^ p) ^ (1 / p) :=
      Real.rpow_le_rpow hoscNonneg havg' (by positivity)
    _ = ((2 : ℝ) ^ α * L) * r ^ α := by
      rw [← Real.rpow_mul hM]
      rw [show p * (1 / p) = 1 by
        field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hp)]]
      exact Real.rpow_one _

theorem campanato_holder_full
    {f : ParabolicPoint → ℝ} {α K p : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hf : LocallyIntegrable f volume)
    (hdata : GlobalParabolicBallLpData f p)
    (hcamp : GlobalParabolicBallCampanatoBound f α K p) :
    ∃ g : ParabolicPoint → ℝ,
      g =ᵐ[volume] f ∧
      ParabolicHolderSeminormLE Set.univ g α
        (parabolicCampanatoHolderConstant α p * K) ∧
      (∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
        ∀ w ∈ Metric.ball z R, |g w| ≤
          2 ^ α * parabolicCampanatoHolderConstant α p * K * R ^ α
            + (⨍ x in Metric.ball z R, |f x| ^ p) ^ (1 / p)) ∧
      (∀ L : ℝ, 0 ≤ L → ParabolicHolderSeminormLE Set.univ f α L →
        GlobalParabolicBallCampanatoBound f α (2 ^ α * L) p) := by
  obtain ⟨g, hgeq, hholder⟩ := campanato_holder hα hα1 hp hK hf hdata hcamp
  have hlinf : ∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
      ∀ w ∈ Metric.ball z R, |g w| ≤
        2 ^ α * parabolicCampanatoHolderConstant α p * K * R ^ α +
          (⨍ x in Metric.ball z R, |f x| ^ p) ^ (1 / p) := by
    intro z R hR w hw
    let s : Set ParabolicPoint := Metric.ball z R
    have hsPos : 0 < volume s := volume_parabolicBall_pos hR
    have hsTop : volume s < ∞ := volume_parabolicBall_lt_top hR
    have hsMeas : MeasurableSet s := Metric.isOpen_ball.measurableSet
    have hd := hdata z hR
    have hfBall : IntegrableOn f s volume := hd.1.mono_set Metric.ball_subset_closedBall
    have hfpClosed := integrableOn_abs_rpow_of_integrableOn_sub_full hp
      (parabolicBall_closedBall_top hR) hd.1 hd.2
    have hfpBall : IntegrableOn (fun x => |f x| ^ p) s volume :=
      hfpClosed.mono_set Metric.ball_subset_closedBall
    have hgAE : g =ᵐ[volume.restrict s] f := ae_restrict_of_ae hgeq
    have hgBall : IntegrableOn g s volume := hfBall.congr hgAE.symm
    have hC : 0 ≤ parabolicCampanatoHolderConstant α p * K :=
      mul_nonneg (parabolicCampanatoHolderConstant_nonneg_full hα) hK
    have hpoint : ∀ w' ∈ s, |g w - g w'| ≤
        parabolicCampanatoHolderConstant α p * K * (2 * R) ^ α := by
      intro w' hw'
      have hdist : dist w w' < 2 * R := by
        calc
          dist w w' ≤ dist w z + dist z w' := dist_triangle w z w'
          _ < R + R := add_lt_add (Metric.mem_ball.mp hw) (Metric.mem_ball'.mp hw')
          _ = 2 * R := by ring
      have hh := hholder w (Set.mem_univ w) w' (Set.mem_univ w')
      have hpow : parabolicDist w w' ^ α ≤ (2 * R) ^ α := by
        rw [← dist_eq_parabolicDist]
        exact Real.rpow_le_rpow dist_nonneg hdist.le hα.le
      exact hh.trans (mul_le_mul_of_nonneg_left hpow hC)
    have hAInt : IntegrableOn (fun w' => |g w - g w'|) s volume := by
      have hsub : IntegrableOn (fun w' => g w' - g w) s volume :=
        hgBall.sub (integrableOn_const hsTop.ne)
      have habs := hsub.abs
      exact habs.congr (Filter.Eventually.of_forall fun x => abs_sub_comm (g x) (g w))
    have hBInt : IntegrableOn (fun w' => |g w'|) s volume := hgBall.abs
    have hmain : |g w| ≤ (⨍ w' in s, |g w - g w'|) + ⨍ w' in s, |g w'| := by
      have hpt : ∀ w' ∈ s, |g w| ≤ |g w - g w'| + |g w'| := by
        intro w' _
        calc
          |g w| = |(g w - g w') + g w'| := by rw [sub_add_cancel]
          _ ≤ |g w - g w'| + |g w'| := abs_add_le _ _
      calc
        |g w| = ⨍ w' in s, |g w| :=
          (Integration.setAverage_const_of_pos_of_lt_top hsPos hsTop _).symm
        _ ≤ ⨍ w' in s, (|g w - g w'| + |g w'|) :=
          Integration.setAverage_mono_of_ae (integrableOn_const hsTop.ne)
            (hAInt.add hBInt) (ae_restrict_of_forall_mem hsMeas hpt)
        _ = (⨍ w' in s, |g w - g w'|) + ⨍ w' in s, |g w'| :=
          Integration.setAverage_add_of_integrableOn hAInt hBInt
    have hfirst : (⨍ w' in s, |g w - g w'|) ≤
        parabolicCampanatoHolderConstant α p * K * (2 * R) ^ α := by
      simpa only [Integration.setAverage_const_of_pos_of_lt_top hsPos hsTop] using
        (Integration.setAverage_mono_of_ae hAInt (integrableOn_const hsTop.ne)
          (ae_restrict_of_forall_mem hsMeas hpoint))
    have hge : (⨍ w' in s, |g w'|) = ⨍ w' in s, |f w'| :=
      setAverage_congr_fun hsMeas (by
        filter_upwards [hgeq] with x hx _
        rw [hx])
    have hsecond : (⨍ w' in s, |g w'|) ≤
        (⨍ x in s, |f x| ^ p) ^ (1 / p) := by
      rw [hge]
      simpa using Integration.setAverage_abs_rpow_norm_mono
        (f := f) (s := s) (q := 1) (p := p) (by norm_num) hp hsPos hsTop
        hfBall hfpBall
    calc
      |g w| ≤ (⨍ w' in s, |g w - g w'|) + ⨍ w' in s, |g w'| := hmain
      _ ≤ parabolicCampanatoHolderConstant α p * K * (2 * R) ^ α +
            (⨍ x in s, |f x| ^ p) ^ (1 / p) := add_le_add hfirst hsecond
      _ = 2 ^ α * parabolicCampanatoHolderConstant α p * K * R ^ α +
            (⨍ x in s, |f x| ^ p) ^ (1 / p) := by
        rw [Real.mul_rpow (by norm_num) hR.le]
        ring
  have hconverse : ∀ L : ℝ, 0 ≤ L →
      ParabolicHolderSeminormLE Set.univ f α L →
      GlobalParabolicBallCampanatoBound f α (2 ^ α * L) p := by
    intro L _ hL
    exact parabolicHolder_implies_globalCampanato_full hα hp hdata hL
  exact ⟨g, hgeq, hholder, hlinf, hconverse⟩

end CKN.Foundation.Parabolic
