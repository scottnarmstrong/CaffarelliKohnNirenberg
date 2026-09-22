-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.SourceMorreyGradientNumerical
import CKN.Core.Endgame.ForceSlotNumericalData
import CKN.Core.Endgame.ForceSlotNumericalSupport
import CKN.Core.Endgame.Localization

/-!
# Numerical bound for the full force slot

The five localized source terms retain their individual numerical bounds.
The initial velocity bound controls the time and Laplacian cutoff terms,
whereas convection uses the improved velocity bound. The selected weak
pressure gradient is retained unchanged. All numerical parameters precede
the solution and cutoff in the source estimate.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The sum of the two cutoff terms, convection, force, and pressure bounds.
The radius is that of a cylinder containing the entire source carrier. -/
def forceSlotNumericalBound (q C R : ℝ) (KU KU25 KD KP Fnorm : ℝ≥0∞) : ℝ≥0∞ :=
  sourceRadiusFactor (min q (25 / 9)) (25 / 3) R * ENNReal.ofReal C *
      sourceUnitCylinderVolume ^ (1 / 2 : ℝ) * KU +
    sourceRadiusFactor (min q (25 / 9)) (25 / 3) R * ENNReal.ofReal C *
      sourceUnitCylinderVolume ^ (1 / 2 : ℝ) * KU +
    sourceRadiusFactor (min q (25 / 9)) (25 / 9) R * ENNReal.ofReal C * (3 * KU25 * KD) +
    sourceRadiusFactor (min q (25 / 9)) q R * ENNReal.ofReal C *
      sourceUnitCylinderVolume ^ (5 / 6 - 1 / q : ℝ) * Fnorm +
    ENNReal.ofReal C * KP

/-- Finite numerical input bounds give a finite force-slot bound. -/
theorem forceSlotNumericalBound_lt_top (q C R : ℝ) {KU KU25 KD KP Fnorm : ℝ≥0∞}
    (hq : 5 / 2 < q) (hR : 0 < R)
    (hKU : KU < ⊤) (hKU25 : KU25 < ⊤) (hKD : KD < ⊤)
    (hKP : KP < ⊤) (hF : Fnorm < ⊤) :
    forceSlotNumericalBound q C R KU KU25 KD KP Fnorm < ⊤ := by
  have hrad (τ : ℝ) : sourceRadiusFactor (min q (25 / 9)) τ R < ⊤ := by
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top)
  have hvol : sourceUnitCylinderVolume ≠ ⊤ := Integration.volume_parabolicCylinder_lt_top.ne
  have hhalf : sourceUnitCylinderVolume ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvol
  have hqP : (6 / 5 : ℝ) ≤ q := by linarith only [hq]
  have hexp : 0 ≤ (5 / 6 - 1 / q : ℝ) := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6 / 5) hqP
    norm_num at hi
    simpa only [one_div] using sub_nonneg.mpr hi
  have hforce : sourceUnitCylinderVolume ^ (5 / 6 - 1 / q : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hexp hvol
  have hradU := hrad (25 / 3)
  have hradN := hrad (25 / 9)
  have hradF := hrad q
  have hCfinite : ENNReal.ofReal C < ⊤ := ENNReal.ofReal_lt_top
  have hA := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hradU hCfinite) hhalf) hKU
  have hN := ENNReal.mul_lt_top (ENNReal.mul_lt_top hradN hCfinite)
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num : (3 : ℝ≥0∞) < ⊤) hKU25) hKD)
  have hF' := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hradF hCfinite) hforce) hF
  have hP := ENNReal.mul_lt_top hCfinite hKP
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hA, hA⟩, hN⟩, hF'⟩, hP⟩

private theorem source_sub_le {P θ : ℝ} (hP : 1 ≤ P)
    {a b : ParabolicPoint → ℝ} (ha : AEMeasurable a volume) (hb : AEMeasurable b volume) :
    morreyNorm P θ (fun w => a w - b w) ≤ morreyNorm P θ a + morreyNorm P θ b := by
  have h := morrey_norm_add_le (τ := θ) hP ha hb.neg
  have hn : morreyNorm P θ (fun w => -b w) = morreyNorm P θ b := by
    simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]
  change morreyNorm P θ (fun w => a w + -b w) ≤
    morreyNorm P θ a + morreyNorm P θ (fun w => -b w) at h
  rw [hn] at h
  simpa only [sub_eq_add_neg] using h

/-- The full, untruncated force slot has an explicit bound from the two
velocity norms, the gradient norm, the selected pressure-gradient norm,
and the original force norm. -/
theorem force_slot_numerical_bound_of_selected_gradient
    (q C R : ℝ) (KU KU25 KD KP Fnorm : ℝ≥0∞)
    (hq : 5 / 2 < q) (hR : 0 < R) (hC : 0 ≤ C)
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    {u f Dp : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hbox : localBox Ω I Ω' J) (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    (hcoeff : ∀ w : Vec3 × ℝ, |φ w| ≤ C ∧ |timePartial φ w| ≤ C ∧
      (∀ j, |spatialPartial φ j w| ≤ C) ∧
      |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C)
    (z : ParabolicPoint)
    (hcarrier : Metric.ball z (2 * R) ⊆ spaceTimeSet Ω I)
    (hsupp : tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z R)
    (hU : ∀ i, morreyNorm 3 (25 / 3)
      ((Metric.ball z R).indicator (fun w => u w i)) ≤ KU)
    (hU25 : ∀ i, morreyNorm 3 25
      ((Metric.ball z R).indicator (fun w => u w i)) ≤ KU25)
    (hD : ∀ i j, morreyNorm 2 (25 / 8)
      ((Metric.ball z R).indicator (fun w => Du w i j)) ≤ KD)
    (hP : ∀ i, morreyNorm (6 / 5) (min q (25 / 9))
      ((Metric.ball z R).indicator (fun w => Dp w i)) ≤ KP)
    (hDp : ∀ i, Integrable (fun w => Dp w i) (volume.restrict (spaceTimeSet Ω' J)))
    (hF : eLpNorm (fun w => vec3EuclideanNorm (f w)) (ENNReal.ofReal q)
      (volume.restrict (Metric.ball z R)) ≤ Fnorm) :
    ∀ i, morreyNorm (6 / 5) (min q (25 / 9))
      (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤
        forceSlotNumericalBound q C (2 * R) KU KU25 KD KP Fnorm := by
  have hlocal := hsol.2.2.2.2.2.1 _ _ (localBox_of_parabolic_ball hR hcarrier)
  have hball : Metric.ball z R =
      spaceTimeSet (vec3Ball z.1 R) (Ioo (z.2 - R ^ 2) (z.2 + R ^ 2)) :=
    metricBall_eq_parabolicBall z R
  have hu (i : Fin 3) : AEMeasurable (fun w => u w i) (volume.restrict (Metric.ball z R)) := by
    rw [hball]
    exact aemeasurable_pi_iff.mp hlocal.1.aemeasurable i
  have hd (i j : Fin 3) : AEMeasurable (fun w => Du w i j) (volume.restrict (Metric.ball z R)) := by
    rw [hball]
    exact aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hlocal.2.1.aemeasurable i) j
  have hf (i : Fin 3) : AEMeasurable (fun w => f w i) (volume.restrict (Metric.ball z R)) := by
    rw [hball]
    exact aemeasurable_pi_iff.mp hlocal.2.2.2.1.aemeasurable i
  have hUae (i : Fin 3) := (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr (hu i)
  have hDae (i j : Fin 3) := (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr (hd i j)
  have hFae (i : Fin 3) := (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr (hf i)
  have hzero (w : ParabolicPoint) (hw : w ∉ Metric.ball z R) :=
    force_slot_coefficients_zero hφ.1 (fun hm => hw (hsupp hm))
  have hQ := metricBall_subset_parabolicCylinder_doubled z hR
  have hR' : 0 < 2 * R := by positivity
  have hterms := force_slot_terms_aemeasurable hsol hφ hbox hφbox hDp
  intro i
  have hA := gradient_source_time_morrey_bound q C (2 * R) KU hq hR' hC
    (z₀ := (z.1, z.2 + R ^ 2)) i hQ (hUae i) (hU i)
    (fun w => (hcoeff (w.1, w.2)).2.1) (fun w hw => (hzero w hw).2.1)
  have hB := gradient_source_laplacian_morrey_bound q C (2 * R) KU hq hR' hC
    (z₀ := (z.1, z.2 + R ^ 2)) i hQ (hUae i) (hU i)
    (fun w => (hcoeff (w.1, w.2)).2.2.2) (fun w hw => (hzero w hw).2.2.2)
  have hN := gradient_source_convection_morrey_bound q C (2 * R) KU25 KD hq hR' hC
    (z₀ := (z.1, z.2 + R ^ 2)) i hQ hUae (hDae i) hU25 (hD i)
    (fun w => (hcoeff (w.1, w.2)).1) (fun w hw => (hzero w hw).1)
  have hFN := force_slot_force_component_norm_le q Fnorm (by linarith only [hq])
    Metric.isOpen_ball.measurableSet (Subset.refl _) i (hf i) hF
  have hForce := gradient_source_force_morrey_bound q C (2 * R) Fnorm hq hR' hC
    (z₀ := (z.1, z.2 + R ^ 2)) i hQ (hFae i) hFN
    (fun w => (hcoeff (w.1, w.2)).1) (fun w hw => (hzero w hw).1)
  have hPN : morreyNorm (6 / 5) (min ((1 / (25 : ℝ) + 8 / 25)⁻¹) q)
      ((Metric.ball z R).indicator (fun w => Dp w i)) ≤ KP := by
    norm_num only [show ((1 / (25 : ℝ) + 8 / 25)⁻¹) = 25 / 9 by norm_num, min_comm]
    exact hP i
  have hPressure := gradient_source_pressure_morrey_bound q 25 C KP hC i hPN
    (fun w => (hcoeff (w.1, w.2)).1) (fun w hw => (hzero w hw).1)
  norm_num only [show ((1 / (25 : ℝ) + 8 / 25)⁻¹) = 25 / 9 by norm_num, min_comm] at hPressure
  obtain ⟨hAm, hBm, hNm, hFm, hPm, _⟩ := hterms i
  have hAB := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6 / 5) hAm hBm).trans (add_le_add hA hB)
  have hABN := (source_sub_le (by norm_num : (1 : ℝ) ≤ 6 / 5) (hAm.add hBm) hNm).trans
    (add_le_add hAB hN)
  have hABNF := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6 / 5)
    ((hAm.add hBm).sub hNm) hFm).trans (add_le_add hABN hForce)
  exact (source_sub_le (by norm_num : (1 : ℝ) ≤ 6 / 5)
    (((hAm.add hBm).sub hNm).add hFm) hPm).trans (add_le_add hABNF hPressure)

end CKN.Core.Endgame
