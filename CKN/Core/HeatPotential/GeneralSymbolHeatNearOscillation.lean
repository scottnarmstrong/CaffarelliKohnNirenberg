-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbolHeatKernelSplitData

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic

/-- A bounded complex-valued function has bounded double-average oscillation. -/
theorem heat_near_pair_average_rpow_bound
    {E : Type*} [NormedAddCommGroup E]
    {h : ParabolicPoint → E} {B : Set ParabolicPoint} {p H : ℝ}
    (hp : 1 ≤ p) (hB : MeasurableSet B) (hBpos : 0 < volume B)
    (hBtop : volume B < ∞)
    (hAEM : AEStronglyMeasurable h (volume.restrict B))
    (hpoint : ∀ᵐ x ∂(volume.restrict B), ‖h x‖ ≤ H) (hH : 0 ≤ H) :
    (⨍ x in B, ⨍ y in B, ‖h x - h y‖ ^ p) ^ (1 / p) ≤ 2 * H := by
  let μ : Measure ParabolicPoint := volume.restrict B
  have hrestrict : (volume.restrict B).restrict B = volume.restrict B :=
    by
      rw [Measure.restrict_restrict hB]
      simp only [inter_self]
  let _ : IsFiniteMeasure μ := ⟨by simpa [μ] using hBtop⟩
  have hμpos : 0 < μ Set.univ := by simpa [μ] using hBpos
  have hμtop : μ Set.univ < ∞ := by finiteness
  have hpointμ : ∀ᵐ x ∂μ, ‖h x‖ ≤ H := by simpa [μ] using hpoint
  let q : ParabolicPoint × ParabolicPoint → ℝ :=
    fun xy => ‖h xy.1 - h xy.2‖ ^ p
  have hfst : AEStronglyMeasurable (fun xy : ParabolicPoint × ParabolicPoint => h xy.1)
      (μ.prod μ) := by
    exact hAEM.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hsnd : AEStronglyMeasurable (fun xy : ParabolicPoint × ParabolicPoint => h xy.2)
      (μ.prod μ) := by
    exact hAEM.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hqAEM : AEStronglyMeasurable q (μ.prod μ) := by
    dsimp [q]
    exact (continuous_id.rpow_const
      (fun _ => Or.inr (le_trans zero_le_one hp))).comp_aestronglyMeasurable
      (hfst.sub hsnd).norm
  have hpointFst : ∀ᵐ xy ∂(μ.prod μ), ‖h xy.1‖ ≤ H := by
    exact Measure.quasiMeasurePreserving_fst.ae hpointμ
  have hpointSnd : ∀ᵐ xy ∂(μ.prod μ), ‖h xy.2‖ ≤ H := by
    exact Measure.quasiMeasurePreserving_snd.ae hpointμ
  have hqbound : ∀ᵐ xy ∂(μ.prod μ), ‖q xy‖ ≤ (2 * H) ^ p := by
    filter_upwards [hpointFst, hpointSnd] with xy hxy₁ hxy₂
    have hdiff : ‖h xy.1 - h xy.2‖ ≤ 2 * H := by
      calc
        ‖h xy.1 - h xy.2‖ ≤ ‖h xy.1‖ + ‖h xy.2‖ := norm_sub_le _ _
        _ ≤ H + H := add_le_add hxy₁ hxy₂
        _ = 2 * H := by ring
    dsimp [q]
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hdiff (le_trans zero_le_one hp)
  have hqint : Integrable q (μ.prod μ) := by
    exact (MemLp.of_bound (p := (1 : ℝ≥0∞)) hqAEM ((2 * H) ^ p) hqbound).integrable
      (by norm_num)
  have hinnerAEM : AEStronglyMeasurable
      (fun x => ⨍ y, q (x, y) ∂μ) μ := by
    have hi := hqint.aestronglyMeasurable.integral_prod_right'
    convert hi.const_mul ((μ Set.univ).toReal⁻¹) using 1
    funext x
    rw [MeasureTheory.average_eq (μ := μ)]
    simp only [MeasureTheory.measureReal_def, smul_eq_mul]
  have hinnerBound : ∀ᵐ x ∂μ, (⨍ y, q (x, y) ∂μ) ≤ (2 * H) ^ p := by
    have hqprod : ∀ᵐ xy ∂(μ.prod μ), q xy ≤ (2 * H) ^ p := by
      filter_upwards [hqbound] with xy hxy
      exact le_trans (le_abs_self _) hxy
    have hqprodSlices : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
        q (x, y) ≤ (2 * H) ^ p := ae_ae_of_ae_prod hqprod
    filter_upwards [hqprodSlices, hqint.prod_right_ae] with x hx hqx
    have hmono := integral_mono_ae hqx (integrable_const _)
      (show ∀ᵐ y ∂μ, q (x, y) ≤ (2 * H) ^ p by exact hx)
    rw [integral_const] at hmono
    rw [MeasureTheory.average_eq]
    simp only [MeasureTheory.measureReal_def, smul_eq_mul]
    have hμr : 0 < (μ Set.univ).toReal := ENNReal.toReal_pos hμpos.ne' hμtop.ne
    calc
      (μ Set.univ).toReal⁻¹ * ∫ (x_1 : ParabolicPoint), q (x, x_1) ∂μ ≤
          (μ Set.univ).toReal⁻¹ * ((μ Set.univ).toReal * (2 * H) ^ p) := by
        gcongr
        exact hmono
      _ = (2 * H) ^ p := by field_simp
  have hinnerInt : Integrable (fun x => ⨍ y, q (x, y) ∂μ) μ := by
    apply Integrable.of_bound hinnerAEM ((2 * H) ^ p)
    filter_upwards [hinnerBound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (MeasureTheory.average_nonneg_of_ae (Filter.Eventually.of_forall fun y =>
        Real.rpow_nonneg (norm_nonneg _) _))]
    exact hx
  have houter : (⨍ x, ⨍ y, q (x, y) ∂μ ∂μ) ≤ (2 * H) ^ p := by
    have hmono := integral_mono_ae hinnerInt (integrable_const _)
      hinnerBound
    rw [MeasureTheory.average_eq]
    simp only [MeasureTheory.measureReal_def, smul_eq_mul]
    have hμr : 0 < (μ Set.univ).toReal := ENNReal.toReal_pos hμpos.ne' hμtop.ne
    calc
      (μ Set.univ).toReal⁻¹ * ∫ x, (⨍ y, q (x, y) ∂μ) ∂μ ≤
          (μ Set.univ).toReal⁻¹ * ((μ Set.univ).toReal * (2 * H) ^ p) := by
        gcongr
        simpa only [integral_const, smul_eq_mul, MeasureTheory.measureReal_def] using hmono
      _ = (2 * H) ^ p := by field_simp
  have hnonneg : 0 ≤ ⨍ x, ⨍ y, q (x, y) ∂μ ∂μ := by
    apply MeasureTheory.average_nonneg_of_ae
    filter_upwards [] with x
    exact MeasureTheory.average_nonneg_of_ae (Filter.Eventually.of_forall fun y =>
      Real.rpow_nonneg (norm_nonneg _) _)
  have hroot : 0 ≤ 1 / p := by positivity
  have hleft :
      (⨍ x, ⨍ y, q (x, y) ∂μ ∂μ) ^ (1 / p) ≤ ((2 * H) ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow hnonneg houter hroot
  have hp0 : p ≠ 0 := by linarith only [hp]
  have hright : ((2 * H) ^ p) ^ (1 / p) = 2 * H := by
    rw [← Real.rpow_mul (mul_nonneg (by norm_num) hH)]
    field_simp [hp0]
    simp
  simpa [q, μ, hrestrict] using hleft.trans_eq hright

end CKN.Core.HeatPotential
