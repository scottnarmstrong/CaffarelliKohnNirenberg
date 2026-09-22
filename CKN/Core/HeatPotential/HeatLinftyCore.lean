-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.CampanatoHolder
import CKN.Foundation.Parabolic.Integration.Slice
import CKN.Core.HeatPotential.GeneralSymbolHeatNear
import CKN.Core.HeatPotential.GeneralSymbolCharacterizationFinal

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

/-- A complex-valued Hölder representative satisfies the local supremum estimate
obtained by averaging its pointwise triangle inequality on a parabolic ball.
The two integrability assumptions are stated on the closed ball so that the
open-ball averages are obtained by restriction. -/
theorem complex_holder_linf_on_ball
    {h : ParabolicPoint → ℂ} {z : ParabolicPoint} {R γ P L : ℝ}
    (hγ : 0 < γ) (hP : 1 ≤ P) (hR : 0 < R) (hL : 0 ≤ L)
    (hclosed : IntegrableOn h
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R) volume)
    (hclosedP : IntegrableOn (fun x => ‖h x‖ ^ P)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R) volume)
    (hholder : ∀ x y : ParabolicPoint,
      ‖h x - h y‖ ≤ L * parabolicDist x y ^ γ) :
    ∀ w ∈ Metric.ball z R,
      ‖h w‖ ≤ (2 : ℝ) ^ γ * L * R ^ γ +
        (⨍ x in Metric.ball z R, ‖h x‖ ^ P) ^ (1 / P) := by
  intro w hw
  let s : Set ParabolicPoint := Metric.ball z R
  have hsPos : 0 < volume s := by
    dsimp [s]
    exact volume_parabolicBall_pos hR
  have hsTop : volume s < ∞ := by
    dsimp [s]
    exact volume_parabolicBall_lt_top hR
  have hsMeas : MeasurableSet s := by
    dsimp [s]
    exact Metric.isOpen_ball.measurableSet
  have hclosed_s : IntegrableOn h s volume := by
    exact hclosed.mono_set Metric.ball_subset_closedBall
  have hclosedP_s : IntegrableOn (fun x => ‖h x‖ ^ P) s volume := by
    exact hclosedP.mono_set Metric.ball_subset_closedBall
  have hnorm_s : IntegrableOn (fun x => ‖h x‖) s volume := hclosed_s.norm
  have hdiff_s : IntegrableOn (fun x => h w - h x) s volume := by
    have hconst : IntegrableOn (fun _ : ParabolicPoint => h w) s volume :=
      integrableOn_const hsTop.ne
    exact hconst.sub hclosed_s
  have hdiff_norm_s : IntegrableOn (fun x => ‖h w - h x‖) s volume :=
    hdiff_s.norm
  have hpoint : ∀ x ∈ s,
      ‖h w - h x‖ ≤ L * (2 * R) ^ γ := by
    intro x hx
    have hw' : dist w z < R := by
      simpa [s, Metric.mem_ball] using hw
    have hx' : dist x z < R := by
      simpa [s, Metric.mem_ball] using hx
    have hdist : dist w x < 2 * R := by
      calc
        dist w x ≤ dist w z + dist z x := dist_triangle w z x
        _ < R + R := add_lt_add hw' (by simpa [dist_comm] using hx')
        _ = 2 * R := by ring
    have hpar : parabolicDist w x ≤ 2 * R := by
      rw [← dist_eq_parabolicDist]
      exact hdist.le
    have hpow : parabolicDist w x ^ γ ≤ (2 * R) ^ γ :=
      Real.rpow_le_rpow (parabolicDist_nonneg w x) hpar hγ.le
    exact (hholder w x).trans (mul_le_mul_of_nonneg_left hpow hL)
  have hfirst : (⨍ x in s, ‖h w - h x‖) ≤ L * (2 * R) ^ γ := by
    have hmono := Integration.setAverage_mono_of_ae hdiff_norm_s
      (integrableOn_const hsTop.ne)
      (ae_restrict_of_forall_mem hsMeas hpoint)
    simpa only [Integration.setAverage_const_of_pos_of_lt_top hsPos hsTop] using hmono
  have hsecond : (⨍ x in s, ‖h x‖) ≤
      (⨍ x in s, ‖h x‖ ^ P) ^ (1 / P) := by
    have hclosedP_abs : IntegrableOn (fun x => |‖h x‖| ^ P) s volume := by
      simpa only [abs_of_nonneg (norm_nonneg _)] using hclosedP_s
    have hmono := Integration.setAverage_abs_rpow_norm_mono
      (f := fun x => ‖h x‖) (s := s) (q := 1) (p := P)
      (by norm_num) hP hsPos hsTop hnorm_s hclosedP_abs
    simpa only [abs_of_nonneg (norm_nonneg _), Real.rpow_one, one_div, inv_one]
      using hmono
  have havgdiff : (⨍ x in s, h w - h x) =
      h w - (⨍ x in s, h x) := by
    have hconst : IntegrableOn (fun _ : ParabolicPoint => h w) s volume :=
      integrableOn_const hsTop.ne
    have hsub :
        (⨍ x in s, ((fun _ : ParabolicPoint => h w) - h) x) =
          (⨍ x in s, (fun _ : ParabolicPoint => h w) x) -
            (⨍ x in s, h x) :=
      MeasureTheory.setAverage_sub hconst hclosed_s
    calc
      (⨍ x in s, h w - h x) =
          (⨍ x in s, (fun _ : ParabolicPoint => h w) x) -
            (⨍ x in s, h x) :=
        by simpa only [Pi.sub_apply] using hsub
      _ = h w - (⨍ x in s, h x) := by
        rw [MeasureTheory.setAverage_const hsPos.ne' hsTop.ne]
  have hmain : ‖h w‖ ≤ (⨍ x in s, ‖h w - h x‖) +
      (⨍ x in s, ‖h x‖) := by
    have havg_diff_norm : ‖h w - (⨍ x in s, h x)‖ ≤
        (⨍ x in s, ‖h w - h x‖) := by
      rw [← havgdiff]
      exact Integration.setAverage_norm_le volume s (fun x => h w - h x)
    have havg_norm : ‖⨍ x in s, h x‖ ≤ ⨍ x in s, ‖h x‖ :=
      Integration.setAverage_norm_le volume s h
    calc
      ‖h w‖ = ‖(h w - (⨍ x in s, h x)) + (⨍ x in s, h x)‖ := by
        congr 1
        abel
      _ ≤ ‖h w - (⨍ x in s, h x)‖ + ‖⨍ x in s, h x‖ :=
        norm_add_le _ _
      _ ≤ (⨍ x in s, ‖h w - h x‖) + (⨍ x in s, ‖h x‖) :=
        add_le_add havg_diff_norm havg_norm
  calc
    ‖h w‖ ≤ (⨍ x in s, ‖h w - h x‖) + (⨍ x in s, ‖h x‖) := hmain
    _ ≤ L * (2 * R) ^ γ + (⨍ x in s, ‖h x‖ ^ P) ^ (1 / P) :=
      add_le_add hfirst hsecond
    _ = (2 : ℝ) ^ γ * L * R ^ γ +
        (⨍ x in s, ‖h x‖ ^ P) ^ (1 / P) := by
      rw [Real.mul_rpow (by norm_num) hR.le]
      ring

/-- The same estimate with the local power datum supplied as a `MemLp`
membership on the closed ball. -/
theorem complex_holder_linf_on_memLp_ball
    {h : ParabolicPoint → ℂ} {z : ParabolicPoint} {R γ P L : ℝ}
    (hγ : 0 < γ) (hP : 1 ≤ P) (hR : 0 < R) (hL : 0 ≤ L)
    (hmem : MemLp h (ENNReal.ofReal P)
      (volume.restrict
        (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R)))
    (hholder : ∀ x y : ParabolicPoint,
      ‖h x - h y‖ ≤ L * parabolicDist x y ^ γ) :
    ∀ w ∈ Metric.ball z R,
      ‖h w‖ ≤ (2 : ℝ) ^ γ * L * R ^ γ +
        (⨍ x in Metric.ball z R, ‖h x‖ ^ P) ^ (1 / P) := by
  let _ : IsFiniteMeasure
      (volume.restrict
        (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact parabolicBall_closedBall_top hR⟩
  have hq : 1 ≤ ENNReal.ofReal P := ENNReal.one_le_ofReal.mpr hP
  have hclosed : IntegrableOn h
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R) volume := by
    change Integrable h (volume.restrict
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R))
    exact hmem.integrable hq
  have hclosedP : IntegrableOn (fun x => ‖h x‖ ^ P)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R) volume := by
    change Integrable (fun x => ‖h x‖ ^ P) (volume.restrict
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R))
    simpa only [ENNReal.toReal_ofReal (zero_le_one.trans hP)] using
      hmem.integrable_norm_rpow'
  exact complex_holder_linf_on_ball (h := h) (z := z) (R := R) (γ := γ)
    (P := P) (L := L) hγ hP hR hL hclosed hclosedP hholder


end CKN.Core.HeatPotential
