-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.CampanatoHolderFull

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

private theorem parabolicHolder_implies_globalCampanato_scope
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
    have hpointAvg : (⨍ y in s, |f x - f y|) ≤ L * (2 * r) ^ α := by
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

/-- The global Campanato equivalence separates the forward representative
construction from the converse estimate, which needs no Campanato hypothesis. -/
theorem repair_lem_campanato :
    ∀ {f : ParabolicPoint → ℝ} {α K p : ℝ}
      (_hα : 0 < α) (_hα1 : α < 1) (_hp : 1 ≤ p) (_hK : 0 ≤ K)
      (_hf : LocallyIntegrable f volume)
      (_hdata : GlobalParabolicBallLpData f p),
      (GlobalParabolicBallCampanatoBound f α K p →
        (∃ g : ParabolicPoint → ℝ,
          g =ᵐ[volume] f ∧
          ParabolicHolderSeminormLE Set.univ g α
            (parabolicCampanatoHolderConstant α p * K) ∧
          (∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
            ∀ w ∈ Metric.ball z R, |g w| ≤
              2 ^ α * parabolicCampanatoHolderConstant α p * K * R ^ α +
                (⨍ x in Metric.ball z R, |f x| ^ p) ^ (1 / p)))) ∧
      (∀ L : ℝ, 0 ≤ L → ParabolicHolderSeminormLE Set.univ f α L →
        GlobalParabolicBallCampanatoBound f α (2 ^ α * L) p) := by
  intro f α K p hα hα1 hp hK hf hdata
  constructor
  · intro hcamp
    obtain ⟨g, hgeq, hholder, hbound, _hconverse⟩ :=
      campanato_holder_full hα hα1 hp hK hf hdata hcamp
    exact ⟨g, hgeq, hholder, hbound⟩
  · intro L hL hholder
    exact parabolicHolder_implies_globalCampanato_scope hα hp hdata hholder

end CKN.Foundation.Parabolic
