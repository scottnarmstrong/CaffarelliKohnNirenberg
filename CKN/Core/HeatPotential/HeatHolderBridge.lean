-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatHolderComplex
import CKN.Core.HeatPotential.GeneralSymbolHeatNear
import CKN.Foundation.Parabolic.Integration.Slice

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic

private theorem nnreal_rpow_add_test {a b p : ℝ} (hp : 1 ≤ p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow
    (⟨a, ha⟩ : ℝ≥0) (⟨b, hb⟩ : ℝ≥0) hp
  exact_mod_cast h

private theorem component_ball_data_and_oscillation_le_pair
    {L : ℂ →L[ℝ] ℝ} {h : ParabolicPoint → ℂ}
    {z : ParabolicPoint} {r P : ℝ}
    (hL : ∀ w : ℂ, ‖L w‖ ≤ ‖w‖) (hP : 1 ≤ P) (hr : 0 < r)
    (hmem : MemLp h (ENNReal.ofReal P)
      (volume.restrict
        (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r))) :
    IntegrableOn (fun x => L (h x))
        (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume ∧
      IntegrableOn (fun x => ‖L (h x) -
        ⨍ y in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
          L (h y)‖ ^ P)
        (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume ∧
      ParabolicBallLpOscillation (fun x => L (h x)) z r P ≤
        multiplierHeatPairOscillation h z r P := by
  let B : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r
  let μB : Measure ParabolicPoint := volume.restrict B
  let _ : IsFiniteMeasure μB := ⟨by
    dsimp [μB, B]
    rw [Measure.restrict_apply_univ]
    exact parabolicBall_closedBall_top hr⟩
  have hBpos : 0 < volume B := by
    dsimp [B]
    exact parabolicBall_closedBall_pos hr
  have hBtop : volume B < ∞ := by
    dsimp [B]
    exact parabolicBall_closedBall_top hr
  have hq : 1 ≤ ENNReal.ofReal P := ENNReal.one_le_ofReal.mpr hP
  have hmem' : MemLp h (ENNReal.ofReal P) μB := by
    simpa [μB] using hmem
  have hInt : Integrable h μB := hmem'.integrable hq
  have hNormP : Integrable (fun x => ‖h x‖ ^ P) μB := by
    simpa only [ENNReal.toReal_ofReal (zero_le_one.trans hP)] using
      hmem'.integrable_norm_rpow'
  have hLmem : MemLp (fun x => L (h x)) (ENNReal.ofReal P) μB :=
    hmem'.continuousLinearMap_comp L
  have hLInt : Integrable (fun x => L (h x)) μB := hLmem.integrable hq
  have hLP : Integrable (fun x => ‖L (h x)‖ ^ P) μB := by
    simpa only [ENNReal.toReal_ofReal (zero_le_one.trans hP)] using
      hLmem.integrable_norm_rpow'
  let c : ℝ := ⨍ y in B, L (h y)
  have hcInt : Integrable (fun _ : ParabolicPoint => c) μB :=
    integrableOn_const hBtop.ne
  have hcenterInt : Integrable (fun x => L (h x) - c) μB := by
    exact hLInt.sub hcInt
  have hcenterMeas : AEStronglyMeasurable (fun x =>
      ‖L (h x) - c‖ ^ P) μB := by
    have hnorm : AEStronglyMeasurable (fun x => ‖L (h x) - c‖) μB :=
      continuous_norm.comp_aestronglyMeasurable hcenterInt.aestronglyMeasurable
    exact (Real.continuous_rpow_const (by linarith only [hP])).comp_aestronglyMeasurable
      hnorm
  have hcenterP : Integrable (fun x => ‖L (h x) - c‖ ^ P) μB := by
    have hconst : Integrable (fun _ : ParabolicPoint => ‖c‖ ^ P) μB :=
      integrableOn_const hBtop.ne
    have hsum : Integrable (fun x => ‖L (h x)‖ ^ P + ‖c‖ ^ P) μB :=
      hLP.add hconst
    have hdomInt : Integrable (fun x =>
        (2 : ℝ) ^ (P - 1) * (‖L (h x)‖ ^ P + ‖c‖ ^ P)) μB :=
      hsum.const_mul ((2 : ℝ) ^ (P - 1))
    refine hdomInt.mono' hcenterMeas ?_
    filter_upwards [] with x
    have hsub : ‖L (h x) - c‖ ≤ ‖L (h x)‖ + ‖c‖ := norm_sub_le _ _
    have hsubpow := Real.rpow_le_rpow (norm_nonneg _) hsub (zero_le_one.trans hP)
    have hadd := nnreal_rpow_add_test hP (norm_nonneg (L (h x))) (norm_nonneg c)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hsubpow.trans hadd
  have hsub : AEStronglyMeasurable
      (fun q : ParabolicPoint × ParabolicPoint => h q.1 - h q.2)
      (μB.prod μB) := by
    exact hmem'.aestronglyMeasurable.comp_fst.sub
      hmem'.aestronglyMeasurable.comp_snd
  have hQmeas : AEStronglyMeasurable
      (fun q : ParabolicPoint × ParabolicPoint => ‖h q.1 - h q.2‖ ^ P)
      (μB.prod μB) := by
    have hnorm := hsub.norm
    exact (Real.continuous_rpow_const (by linarith only [hP])).comp_aestronglyMeasurable
      hnorm
  have hQInt : Integrable
      (fun q : ParabolicPoint × ParabolicPoint => ‖h q.1 - h q.2‖ ^ P)
      (μB.prod μB) := by
    have hfst : Integrable (fun q : ParabolicPoint × ParabolicPoint =>
        ‖h q.1‖ ^ P) (μB.prod μB) := hNormP.comp_fst μB
    have hsnd : Integrable (fun q : ParabolicPoint × ParabolicPoint =>
        ‖h q.2‖ ^ P) (μB.prod μB) := hNormP.comp_snd μB
    have hsum : Integrable (fun q : ParabolicPoint × ParabolicPoint =>
        ‖h q.1‖ ^ P + ‖h q.2‖ ^ P) (μB.prod μB) := hfst.add hsnd
    have hdomInt : Integrable (fun q : ParabolicPoint × ParabolicPoint =>
        (2 : ℝ) ^ (P - 1) * (‖h q.1‖ ^ P + ‖h q.2‖ ^ P)) (μB.prod μB) :=
      hsum.const_mul ((2 : ℝ) ^ (P - 1))
    refine hdomInt.mono' hQmeas ?_
    filter_upwards [] with q
    have hsub : ‖h q.1 - h q.2‖ ≤ ‖h q.1‖ + ‖h q.2‖ := norm_sub_le _ _
    have hsubpow := Real.rpow_le_rpow (norm_nonneg _) hsub (zero_le_one.trans hP)
    have hadd := nnreal_rpow_add_test hP (norm_nonneg (h q.1))
      (norm_nonneg (h q.2))
    calc
      |‖h q.1 - h q.2‖ ^ P| = ‖h q.1 - h q.2‖ ^ P :=
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ (2 : ℝ) ^ (P - 1) *
          (‖h q.1‖ ^ P + ‖h q.2‖ ^ P) := hsubpow.trans hadd
  have hinnerInt : Integrable (fun x =>
      ∫ y, ‖h x - h y‖ ^ P ∂μB) μB := by
    simpa only [Prod.mk.eta] using hQInt.integral_prod_left
  have hinnerAvg : Integrable (fun x =>
      ⨍ y in B, ‖h x - h y‖ ^ P) μB := by
    have hscaled := hinnerInt.const_mul (μB Set.univ).toReal⁻¹
    simpa [MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def,
      MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul, μB, B] using hscaled
  have hmap_avg : ∀ {φ : ParabolicPoint → ℂ}, Integrable φ μB →
      L (⨍ y in B, φ y) = ⨍ y in B, L (φ y) := by
    intro φ hφ
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    change L ((volume B).toReal⁻¹ • ∫ y in B, φ y) =
      (volume B).toReal⁻¹ • ∫ y in B, L (φ y)
    rw [map_smul]
    rw [(L.integral_comp_comm hφ).symm]
  have hpoint : ∀ᵐ x ∂μB, ‖L (h x) - c‖ ^ P ≤
      ⨍ y in B, ‖h x - h y‖ ^ P := by
    filter_upwards [hQInt.prod_right_ae] with x hx
    have hconst : Integrable (fun _ : ParabolicPoint => h x) μB :=
      integrableOn_const hBtop.ne
    have hdiff : Integrable (fun y => h x - h y) μB := hconst.sub hInt
    have havg_sub : (⨍ y in B, h x - h y) = h x - ⨍ y in B, h y := by
      rw [show (fun y => h x - h y) = (fun _ : ParabolicPoint => h x) - h by
        funext y
        simp only [Pi.sub_apply], MeasureTheory.setAverage_sub hconst hInt,
        MeasureTheory.setAverage_const hBpos.ne' hBtop.ne]
    have hmapcenter : L (h x - ⨍ y in B, h y) = L (h x) - c := by
      rw [map_sub, hmap_avg hInt]
    have hdiffP : IntegrableOn (fun y => ‖h x - h y‖ ^ P) B volume := by
      change Integrable (fun y => ‖h x - h y‖ ^ P) μB
      exact hx
    have hj := Integration.setAverage_norm_rpow_le hP hBpos hBtop hdiff
      hdiffP
    rw [havg_sub] at hj
    calc
      ‖L (h x) - c‖ ^ P = ‖L (h x - ⨍ y in B, h y)‖ ^ P := by
        rw [hmapcenter]
      _ ≤ ‖h x - ⨍ y in B, h y‖ ^ P :=
        Real.rpow_le_rpow (norm_nonneg _) (hL _) (zero_le_one.trans hP)
      _ = ‖⨍ y in B, h x - h y‖ ^ P := by rw [havg_sub]
      _ ≤ ⨍ y in B, ‖h x - h y‖ ^ P := by simpa [havg_sub] using hj
  have havg_le : (⨍ x in B, ‖L (h x) - c‖ ^ P) ≤
      ⨍ x in B, ⨍ y in B, ‖h x - h y‖ ^ P :=
    Integration.setAverage_mono_of_ae hcenterP hinnerAvg hpoint
  have hroot : (⨍ x in B, ‖L (h x) - c‖ ^ P) ^ (1 / P) ≤
      (⨍ x in B, ⨍ y in B, ‖h x - h y‖ ^ P) ^ (1 / P) :=
    Real.rpow_le_rpow
      (Integration.setAverage_nonneg_of_ae
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)) havg_le
      (one_div_nonneg.mpr (zero_le_one.trans hP))
  refine ⟨?_, ?_, ?_⟩
  · change Integrable (fun x => L (h x)) μB
    exact hLInt
  · change Integrable (fun x =>
      |L (h x) - ⨍ y in B, L (h y)| ^ P) μB
    simpa [c, Real.norm_eq_abs] using hcenterP
  · change (⨍ x in B, |L (h x) - ⨍ y in B, L (h y)| ^ P) ^ (1 / P) ≤
      (⨍ x in B, ⨍ y in B, ‖h x - h y‖ ^ P) ^ (1 / P)
    simpa [c, Real.norm_eq_abs] using hroot

private theorem component_global_campanato_of_local_heat_data
    {L : ℂ →L[ℝ] ℝ} {h : ParabolicPoint → ℂ}
    {γ P A : ℝ} (hL : ∀ w : ℂ, ‖L w‖ ≤ ‖w‖)
    (hP : 1 ≤ P)
    (hmem : ∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
      MemLp h (ENNReal.ofReal P)
        (volume.restrict
          (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R)))
    (hpair : ∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
      multiplierHeatPairOscillation h z R P ≤ A * R ^ γ) :
    LocallyIntegrable (fun x => L (h x)) volume ∧
      GlobalParabolicBallLpData (fun x => L (h x)) P ∧
      GlobalParabolicBallCampanatoBound (fun x => L (h x)) γ A P := by
  have hlocal : LocallyIntegrable (fun x => L (h x)) volume := by
    intro x
    obtain ⟨hInt, _, _⟩ := component_ball_data_and_oscillation_le_pair
      hL hP one_pos (hmem x 1 one_pos)
    exact ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, hInt⟩
  refine ⟨hlocal, ?_, ?_⟩
  · intro z r hr
    obtain ⟨hInt, hcenter, _⟩ := component_ball_data_and_oscillation_le_pair
      hL hP hr (hmem z r hr)
    exact ⟨hInt, hcenter⟩
  · intro z r hr
    obtain ⟨_, _, hosc⟩ := component_ball_data_and_oscillation_le_pair
      hL hP hr (hmem z r hr)
    exact hosc.trans (hpair z r hr)

private theorem complex_components_global_campanato_of_local_heat_data
    {h : ParabolicPoint → ℂ} {γ P A : ℝ} (hP : 1 ≤ P)
    (hmem : ∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
      MemLp h (ENNReal.ofReal P)
        (volume.restrict
          (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R)))
    (hpair : ∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
      multiplierHeatPairOscillation h z R P ≤ A * R ^ γ) :
    (LocallyIntegrable (fun x => (h x).re) volume ∧
      GlobalParabolicBallLpData (fun x => (h x).re) P ∧
      GlobalParabolicBallCampanatoBound (fun x => (h x).re) γ A P) ∧
    (LocallyIntegrable (fun x => (h x).im) volume ∧
      GlobalParabolicBallLpData (fun x => (h x).im) P ∧
      GlobalParabolicBallCampanatoBound (fun x => (h x).im) γ A P) := by
  have hre := component_global_campanato_of_local_heat_data
    (L := RCLike.reCLM) (h := h) (γ := γ) (P := P) (A := A)
    (fun w => by simpa only [RCLike.reCLM_apply] using RCLike.norm_re_le_norm w)
    hP hmem hpair
  have him := component_global_campanato_of_local_heat_data
    (L := RCLike.imCLM) (h := h) (γ := γ) (P := P) (A := A)
    (fun w => by simpa only [RCLike.imCLM_apply] using RCLike.norm_im_le_norm w)
    hP hmem hpair
  simpa [RCLike.reCLM_apply, RCLike.imCLM_apply] using And.intro hre him

/-- Converts the local complex output and pair-oscillation estimate to the two
real component Campanato inputs required by the scalar Hölder theorem. -/
theorem heat_conclusion_component_campanato_bridge
    {K : ℕ} {γ θ₀ θ₁ P C : ℝ}
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    {hbar : ParabolicPoint → ℂ} (hP : 1 ≤ P)
    (hmem : ∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
      MemLp hbar (ENNReal.ofReal P)
        (volume.restrict
          (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R)))
    (hpair : ∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
      multiplierHeatPairOscillation hbar z R P ≤
        C * R ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G) :
    (LocallyIntegrable (fun x => (hbar x).re) volume ∧
      GlobalParabolicBallLpData (fun x => (hbar x).re) P ∧
      GlobalParabolicBallCampanatoBound (fun x => (hbar x).re) γ
        (C * multiplierHeatSourceSize P θ₀ θ₁ F G) P) ∧
    (LocallyIntegrable (fun x => (hbar x).im) volume ∧
      GlobalParabolicBallLpData (fun x => (hbar x).im) P ∧
      GlobalParabolicBallCampanatoBound (fun x => (hbar x).im) γ
        (C * multiplierHeatSourceSize P θ₀ θ₁ F G) P) := by
  apply complex_components_global_campanato_of_local_heat_data hP hmem
  intro z R hR
  calc
    multiplierHeatPairOscillation hbar z R P ≤
        C * R ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G := hpair z R hR
    _ = (C * multiplierHeatSourceSize P θ₀ θ₁ F G) * R ^ γ := by ring

end CKN.Core.HeatPotential
