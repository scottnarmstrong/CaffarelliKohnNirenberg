-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.Lin34Solution
import CKN.Core.Caccioppoli.LocalBox
import CKN.Setting.PressureGaugeSlices
import CKN.Setting.Energy.Calculus

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

/-! # Local space-time source for the integrated pressure estimate

This module obtains test-pairing integrability from the local force
integrability in the suitable weak-solution definition and proves the
integrated Lin estimate from local space-time divergence freedom.
-/

set_option autoImplicit false
noncomputable section

namespace CKN

private theorem pressure_force_pairing_integrable_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
      (tsupport ψ) volume := by
  classical
  rcases hsol with ⟨hΩ, hI, hIord, hq, hfLocal, hrest⟩
  rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
  let K : Set ParabolicPoint :=
    (fun z : Vec3 × ℝ => (z.1, z.2)) '' tsupport ψ
  have hKcompact : IsCompact K :=
    hψcompact.isCompact.image continuous_prod_to_parabolicPoint
  have hKcarrier : K ⊆ spaceTimeSet Ω I := by
    rintro z ⟨w, hw, rfl⟩
    exact hψsupport hw
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    caccioppoli_localBox_of_compact_subset hΩ hI hIord hKcompact hKcarrier
  have hlocalFinite : IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) := by
    let L : Set ParabolicPoint :=
      parabolicHomeomorph ⁻¹' (closure Ω' ×ˢ closure J)
    have hLfinite : volume L < ⊤ := by
      change (volume : Measure (Vec3 × ℝ)) (closure Ω' ×ˢ closure J) < ⊤
      exact (hbox.2.1.prod hbox.2.2.2.2.1).measure_lt_top
    have hsubset : spaceTimeSet Ω' J ⊆ L := by
      intro z hz
      change z.1 ∈ closure Ω' ∧ z.2 ∈ closure J
      exact ⟨subset_closure hz.1, subset_closure hz.2⟩
    exact isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono hsubset) hLfinite).ne
  let _ : IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) := hlocalFinite
  have hforce := hfLocal Ω' J hbox
  have hqone : 1 ≤ q := by linarith only [hq]
  have hforceInt (i : Fin 3) :
      Integrable (fun w : ParabolicPoint => f w i)
        (volume.restrict (spaceTimeSet Ω' J)) := by
    exact (hforce i).integrable (ENNReal.one_le_ofReal.mpr hqone)
  have hpartialContinuous (i : Fin 3) :
      Continuous (fun w : ParabolicPoint => spatialPartial ψ i w) := by
    have hc := (spatialPartial_contDiff hψdiff i).continuous.comp
      parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  choose Ki hKi using fun i : Fin 3 =>
    hψcompact.isCompact.exists_bound_of_continuousOn
      (spatialPartial_contDiff hψdiff i).continuous.continuousOn
  set Kd : ℝ := max 0 (Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩ Ki)
  have hKd : 0 ≤ Kd := le_max_left _ _
  have hpartialBound : ∀ i : Fin 3, ∀ w : ParabolicPoint,
      ‖spatialPartial ψ i w‖ ≤ Kd := by
    intro i w
    have heq : spatialPartial ψ i w =
        spatialPartial ψ i (parabolicHomeomorph w) := rfl
    rw [heq]
    by_cases hw : parabolicHomeomorph w ∈ tsupport ψ
    · exact (hKi i (parabolicHomeomorph w) hw).trans
        ((Finset.le_sup' Ki (Finset.mem_univ i)).trans (le_max_right _ _))
    · rw [spatialPartial_eq_zero_off_tsupport hw i]
      rw [norm_zero]
      exact hKd
  have hterm (i : Fin 3) :
      Integrable (fun w : ParabolicPoint => f w i * spatialPartial ψ i w)
        (volume.restrict (spaceTimeSet Ω' J)) := by
    have hpartialMeas : AEStronglyMeasurable (fun w : ParabolicPoint =>
        spatialPartial ψ i w) (volume.restrict (spaceTimeSet Ω' J)) :=
      (hpartialContinuous i).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
    have hm := (hforceInt i).mul_bdd hpartialMeas
      (Eventually.of_forall fun w => by
        simpa only [Real.norm_eq_abs] using hpartialBound i w)
    simpa only [mul_comm] using hm
  have hsum : Integrable
      (fun w : ParabolicPoint => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
      (volume.restrict (spaceTimeSet Ω' J)) :=
    integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun i _hi => hterm i)
  have hsupp : Function.support
      (fun w : ParabolicPoint => ∑ i : Fin 3, f w i * spatialPartial ψ i w) ⊆
        spaceTimeSet Ω' J := by
    intro w hw
    by_contra hnot
    have hnotψ : parabolicHomeomorph w ∉ tsupport ψ := by
      intro hψw
      apply hnot
      exact hKbox ⟨parabolicHomeomorph w, hψw, rfl⟩
    have hzero :
        (∑ i : Fin 3, f w i * spatialPartial ψ i w) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [show spatialPartial ψ i w =
        spatialPartial ψ i (parabolicHomeomorph w) from rfl,
        spatialPartial_eq_zero_off_tsupport hnotψ i, mul_zero]
    exact hw hzero
  have hglobal : Integrable
      (fun w : ParabolicPoint => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
      volume := (integrableOn_iff_integrable_of_support_subset hsupp).mp hsum
  simpa only [IntegrableOn] using hglobal.mono_measure Measure.restrict_le_self

/-- The integrated pressure estimate under local space-time divergence freedom
of the force, with its test-pairing integrability supplied by suitability. -/
theorem pressure_lin34_integrated_local_spacetime_source :
∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (_hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (_hρ : 0 < ρ) (_hr : 0 < r)
    (_hhalf : r ≤ ρ / 2)
    (_hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (_hdivf : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      (∫ w in spaceTimeSet Ω I, ∑ i : Fin 3, f w i * spatialPartial ψ i w) = 0),
pressureD p z r ≤ lin34AbsoluteConstant *
      ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
        (r / ρ) * pressureD p z ρ) := by
  intro Ω I q u Du p f hsol z ρ r hρ hr hhalf hsub hdivf
  have hsource : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
          (tsupport ψ) volume ∧
        ∫ w in spaceTimeSet Ω I,
          ∑ i : Fin 3, f w i * spatialPartial ψ i w = 0 := by
    intro ψ hψ
    exact ⟨pressure_force_pairing_integrable_of_sws hsol hψ, hdivf ψ hψ⟩
  exact ((CKN.Pressure.pressure_lin34_of_sws q hsol hρ hr hhalf hsub).1 hsource).2

end CKN
end
