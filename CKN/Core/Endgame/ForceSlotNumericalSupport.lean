-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.SourceMorreyGradient
import CKN.Core.Endgame.CutoffDerivatives
import CKN.Core.Endgame.OneSidedMeasurability

/-!
# Measurability and support of the full localized sources

The suitable solution supplies local measurability of the velocity, gradient,
and force. Local integrability of the selected pressure gradient suffices
for both full source slots to be globally measurable and compactly supported.
No numerical source bound is used in this step.
-/

open MeasureTheory Set
open scoped Topology BigOperators
open CKN.Foundation.Parabolic CKN.Core.Step3 CKN.Core.Step4

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- All localization coefficients vanish off the cutoff's topological support. -/
theorem force_slot_coefficients_zero {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {w : ParabolicPoint}
    (hw : (w.1, w.2) ∉ tsupport φ) :
    φ w = 0 ∧ timePartial φ w = 0 ∧ (∀ j, spatialPartial φ j w = 0) ∧
      spatialLaplacian (fun x => φ (x, w.2)) w.1 = 0 := by
  refine ⟨(show φ (w.1, w.2) = 0 from image_eq_zero_of_notMem_tsupport hw),
    timePartial_zero_of_not_mem_tsupport_public hφ hw,
    spatialPartial_zero_of_not_mem_tsupport_public hφ hw, ?_⟩
  change (∑ j : Fin 3, spatialSecondPartial φ j j w) = 0
  exact Finset.sum_eq_zero (fun j _ => spatialSecondPartial_zero_of_not_mem_tsupport_public hφ hw j j)

/-- The full localized force and derivative slots vanish outside the cutoff. -/
theorem force_slot_sources_zero {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (u f Dp : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    {w : ParabolicPoint} (hw : (w.1, w.2) ∉ tsupport φ) :
    localizedGradientSourceG φ u Du f Dp w = 0 ∧
      ∀ j, localizedGradientSourceH φ u j w = 0 := by
  obtain ⟨hv, ht, hx, hΔ⟩ := force_slot_coefficients_zero hφ hw
  constructor
  · funext i
    simp only [localizedGradientSourceG, localizedEquationG, hv, ht, hΔ,
      zero_mul, add_zero, sub_zero, Pi.zero_apply]
  · intro j
    simp only [localizedGradientSourceH, localizedEquationH, hx j, mul_zero, zero_smul]

/-- Each of the five force terms and every derivative term is measurable
using only local solution data and integrability of the pressure gradient. -/
theorem force_slot_terms_aemeasurable
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u f Dp : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hbox : localBox Ω I Ω' J) (hsupp : tsupport φ ⊆ Ω' ×ˢ J)
    (hDp : ∀ i, Integrable (fun w => Dp w i) (volume.restrict (spaceTimeSet Ω' J))) :
    ∀ i, AEMeasurable (fun w : ParabolicPoint => timePartial φ w * u w i) volume ∧
      AEMeasurable (fun w : ParabolicPoint =>
        spatialLaplacian (fun x => φ (x, w.2)) w.1 * u w i) volume ∧
      AEMeasurable (fun w => φ w * localizedConvection u Du w i) volume ∧
      AEMeasurable (fun w : ParabolicPoint => φ w * f w i) volume ∧
      AEMeasurable (fun w : ParabolicPoint => φ w * Dp w i) volume ∧
      ∀ j, AEMeasurable (fun w => localizedGradientSourceH φ u j w i) volume := by
  let S := spaceTimeSet Ω' J
  have hS : MeasurableSet S := hbox.1.measurableSet.prod hbox.2.2.2.1.measurableSet
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hu (i : Fin 3) : AEMeasurable (fun w => u w i) (volume.restrict S) :=
    aemeasurable_pi_iff.mp hdata.1.aemeasurable i
  have hDu (i j : Fin 3) : AEMeasurable (fun w => Du w i j) (volume.restrict S) :=
    aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hdata.2.1.aemeasurable i) j
  have hf (i : Fin 3) : AEMeasurable (fun w => f w i) (volume.restrict S) :=
    aemeasurable_pi_iff.mp hdata.2.2.2.1.aemeasurable i
  have hzero (w : ParabolicPoint) (hw : w ∉ S) :=
    force_slot_coefficients_zero hφ.1 (fun hm => hw (hsupp hm))
  have hv : AEMeasurable (φ : ParabolicPoint → ℝ) volume :=
    (hφ.1.continuous.comp continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have ht : AEMeasurable (fun w : ParabolicPoint => timePartial φ w) volume :=
    ((timePartial_contDiff_full hφ.1).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have hx (j : Fin 3) : AEMeasurable (fun w : ParabolicPoint => spatialPartial φ j w) volume :=
    ((spatialPartial_contDiff hφ.1 j).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have hΔ : AEMeasurable
      (fun w : ParabolicPoint => spatialLaplacian (fun x => φ (x, w.2)) w.1) volume := by
    have hc : Continuous
        (fun w : Vec3 × ℝ => spatialLaplacian (fun x => φ (x, w.2)) w.1) := by
      change Continuous (fun w : Vec3 × ℝ => ∑ j, spatialSecondPartial φ j j w)
      exact continuous_finsetSum _ (fun j _ => (spatialSecondPartial_contDiff_full hφ.1 j j).continuous)
    exact (hc.comp continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have hconv (i : Fin 3) : AEMeasurable (fun w => localizedConvection u Du w i)
      (volume.restrict S) := by
    have hterm (j : Fin 3) := (hu j).mul (hDu i j)
    simpa [localizedConvection, Fin.sum_univ_succ, Pi.add_def, Pi.mul_def] using
      (hterm 0).add ((hterm 1).add (hterm 2))
  intro i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact aemeasurable_mul_of_restrict_of_zero_outside hS ht (hu i)
      (fun w hw => (hzero w hw).2.1)
  · exact aemeasurable_mul_of_restrict_of_zero_outside hS hΔ (hu i)
      (fun w hw => (hzero w hw).2.2.2)
  · exact aemeasurable_mul_of_restrict_of_zero_outside hS hv (hconv i)
      (fun w hw => (hzero w hw).1)
  · exact aemeasurable_mul_of_restrict_of_zero_outside hS hv (hf i)
      (fun w hw => (hzero w hw).1)
  · exact aemeasurable_mul_of_restrict_of_zero_outside hS hv
      (hDp i).aestronglyMeasurable.aemeasurable (fun w hw => (hzero w hw).1)
  · intro j
    exact aemeasurable_mul_of_restrict_of_zero_outside hS ((hx j).const_mul (-2)) (hu i)
      (fun w hw => by rw [(hzero w hw).2.2.1 j, mul_zero])

/-- A locally integrable selected pressure gradient gives the measurable,
compactly supported sources required by the quantitative endgame. -/
theorem force_slot_sources_measurable_compact
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u f Dp : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hbox : localBox Ω I Ω' J) (hsupp : tsupport φ ⊆ Ω' ×ˢ J)
    (hDp : ∀ i, Integrable (fun w => Dp w i) (volume.restrict (spaceTimeSet Ω' J))) :
    (∀ i, AEMeasurable (fun w => localizedGradientSourceG φ u Du f Dp w i) volume) ∧
    (∀ j i, AEMeasurable (fun w => localizedGradientSourceH φ u j w i) volume) ∧
    (∀ i, HasCompactSupport (fun w => localizedGradientSourceG φ u Du f Dp w i)) ∧
    (∀ j i, HasCompactSupport (fun w => localizedGradientSourceH φ u j w i)) := by
  have hterms := force_slot_terms_aemeasurable hsol hφ hbox hsupp hDp
  have hG (i : Fin 3) : AEMeasurable
      (fun w => localizedGradientSourceG φ u Du f Dp w i) volume := by
    obtain ⟨hA, hB, hN, hF, hP, _hH⟩ := hterms i
    exact (((hA.add hB).sub hN).add hF).sub hP
  have hH (j i : Fin 3) : AEMeasurable
      (fun w => localizedGradientSourceH φ u j w i) volume :=
    (hterms i).2.2.2.2.2 j
  have hcompact {g : ParabolicPoint → ℝ}
      (hg : ∀ w, (w.1, w.2) ∉ tsupport φ → g w = 0) : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact
      (parabolicHomeomorph.isCompact_preimage.mpr hφ.2.1.isCompact)
    intro w hw
    by_contra hnot
    exact hw (hg w hnot)
  refine ⟨hG, hH, ?_, ?_⟩
  · intro i
    apply hcompact
    intro w hw
    exact congrFun (force_slot_sources_zero hφ.1 u f Dp Du hw).1 i
  · intro j i
    apply hcompact
    intro w hw
    exact congrFun ((force_slot_sources_zero hφ.1 u f Dp Du hw).2 j) i

end CKN.Core.Endgame
