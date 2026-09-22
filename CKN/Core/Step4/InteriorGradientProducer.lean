-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.InteriorGradientProducerTransport
import CKN.Core.Endgame.TheoremAClosersInstancesQ
import CKN.Core.Step4.PressureGradientOriginASlotFinal
import CKN.Core.Step4.PressureGradientOriginBSlotInstances

/-! # The quantitative pressure gradient on the two interior past collars

The cell and time-mass estimates of the pressure gradient are available at the
radius pairs `(11/16, 43/64)` and `(5/8, 19/32)`.  The causality step starts
from the smaller carrier `B_{5/8}`, so it needs the same estimate at the pairs
`(5/8, 19/32)` and `(9/16, 17/32)`.

A parabolic dilation about the space-time origin by `10/11`, respectively
`9/10`, carries the first pair onto a pair whose input radius is exactly the
required one and whose output radius is larger than the required one.  Since
the dilation factor is smaller than one, the dilated unit cylinder lies inside
the original one, so the cubic data hypothesis is available with the explicit
loss `μ⁻²`, and both velocity and gradient Morrey data transport with explicit
finite factors.  The selected pressure gradient of the dilated solution
transports back with the finite factor `μ^{5/κ - 3}`.

All of the constants are chosen from the force exponent, the data bound and
the two Morrey bounds alone, before any domain, any time interval and any
solution.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Endgame

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

/-- The common Calderón–Zygmund threshold of the cell and time-mass slots. -/
def interiorGradientThreshold (q : ℝ) : ℝ :=
  max 0 (max (originASlotCorrectionThreshold originASlotM2Threshold q)
    bslotThresholdB)

/-- The quantitative pressure-gradient estimate at the two established radius
pairs, in the existential form in which the localization steps consume it. -/
theorem exists_pressure_gradient_morrey_bound_on_fixed_collar
    (q τ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτu : τ ≤ 25)
    (hinst : (τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32))
    (hR₁ : 0 < R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 3 / 4) (hε : 0 ≤ ε)
    (hKU : KU < ⊤) (hKD : KD < ⊤) :
    ∃ KP : ℝ≥0∞, KP < ⊤ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i)
              (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
              ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i)) ≤
            KP) := by
  have hA : ∀ q', originASlotCorrectionThreshold originASlotM2Threshold q' ≤
      interiorGradientThreshold q' :=
    fun _ => (le_max_left _ _).trans (le_max_right _ _)
  have hB : ∀ q', bslotThresholdB ≤ interiorGradientThreshold q' :=
    fun _ => (le_max_right _ _).trans (le_max_right _ _)
  have h0 : ∀ q', (0 : ℝ) ≤ interiorGradientThreshold q' := fun _ => le_max_left _ _
  have hmain := theoremA_hGA_of_integral_slots_instances_q interiorGradientThreshold
    (fun q' τ' C R₀' R₁' ε' KU' KD' hq' hτ' hτu' hC hth =>
      theoremA_aSlot_integral_instances q' τ' C R₀' R₁' ε' KU' KD' hq' hτ' hτu' hC
        ((hA q').trans hth))
    (fun q' τ' C R₀' R₁' ε' KU' KD' hq' hτ' hτu' hC hth =>
      theoremA_bslot_integral_instances q' τ' C R₀' R₁' ε' KU' KD' hq' hτ' hτu' hC
        ((hB q').trans hth))
    q τ (interiorGradientThreshold q) R₀ R₁ ε KU KD hq hτ hτu (h0 q) le_rfl hinst
    hR₁ hR₁R₀ hR₀ hε hKU hKD
  exact ⟨_, hmain.1, fun {_ _ _ _ _ _} hsol hdom hU hD hsmall =>
    hmain.2 hsol hdom hU hD hsmall⟩

/-- The same estimate on a collar obtained from a established one by a parabolic
dilation about the space-time origin.  The dilation factor is at most one, so
no datum outside the original unit cylinder is used. -/
theorem exists_pressure_gradient_morrey_bound_of_dilation
    (q τ R₀ R₁ R₀' R₁' ε μ : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτu : τ ≤ 25)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hinst : (τ = 25 / 3 ∧ R₀' = 11 / 16 ∧ R₁' = 43 / 64) ∨
      (τ = 25 ∧ R₀' = 5 / 8 ∧ R₁' = 19 / 32))
    (hR₀ : R₀ = μ * R₀') (hR₁ : 0 < R₁) (hR₁le : R₁ ≤ μ * R₁')
    (hR₁' : 0 < R₁') (hR₁'R₀' : R₁' < R₀') (hR₀' : R₀' < 3 / 4) (hε : 0 ≤ ε)
    (hKU : KU < ⊤) (hKD : KD < ⊤) :
    ∃ KP : ℝ≥0∞, KP < ⊤ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i)
              (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
              ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i)) ≤
            KP) := by
  classical
  have hR₀'pos : (0 : ℝ) < R₀' := hR₁'.trans hR₁'R₀'
  have hτpos : (0 : ℝ) < τ := by linarith only [hτ]
  set KU' : ℝ≥0∞ :=
    ENNReal.ofReal |μ| * (ENNReal.ofReal μ ^ (-5 / τ : ℝ) * KU) with hKU'def
  set KD' : ℝ≥0∞ :=
    ENNReal.ofReal |μ ^ 2| *
      (ENNReal.ofReal μ ^ (-5 / (25 / 8 : ℝ) : ℝ) * KD) with hKD'def
  have hKU'top : KU' < ⊤ := force_slot_scaling_bound_lt_top μ μ τ hμ hKU
  have hKD'top : KD' < ⊤ :=
    force_slot_scaling_bound_lt_top μ (μ ^ 2) (25 / 8 : ℝ) hμ hKD
  have hε' : (0 : ℝ) ≤ μ⁻¹ ^ 2 * ε := by positivity
  obtain ⟨KP', hKP', hprod⟩ := exists_pressure_gradient_morrey_bound_on_fixed_collar
    q τ R₀' R₁' (μ⁻¹ ^ 2 * ε) KU' KD' hq hτ hτu hinst hR₁' hR₁'R₀' hR₀' hε'
    hKU'top hKD'top
  refine ⟨ENNReal.ofReal |μ⁻¹ ^ 2 * μ⁻¹| *
    (ENNReal.ofReal μ⁻¹ ^ (-5 / min ((1 / τ + 8 / 25)⁻¹) q : ℝ) * KP'),
    force_slot_scaling_bound_lt_top μ⁻¹ (μ⁻¹ ^ 2 * μ⁻¹)
      (min ((1 / τ + 8 / 25)⁻¹) q) (inv_pos.mpr hμ) hKP', ?_⟩
  intro Ω I u Du p f hsol hdom hU hD hsmall
  have hsol' := isSuitableWeakSolutionIntegrable_rescale hsol originPoint hμ
  have hdom' := interior_rescaled_domain hμ hμ1 hdom
  have hU' : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀').indicator
        (fun z => rescaleVelocity μ originPoint u z i)) ≤ KU' := by
    intro i
    exact rescaled_indicator_morrey_le (c := μ) (P := 3) (τ := τ) (R := R₀)
      (R' := R₀') hμ (by norm_num) (le_of_lt (mul_pos hμ hR₀'pos)) hR₀.ge
      (fun z => u z i) (hU i)
  have hD' : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀').indicator
        (fun z => rescaleGradient μ originPoint Du z i j)) ≤ KD' := by
    intro i j
    exact rescaled_indicator_morrey_le (c := μ ^ 2) (P := 2) (τ := (25 / 8 : ℝ))
      (R := R₀) (R' := R₀') hμ (by norm_num) (le_of_lt (mul_pos hμ hR₀'pos))
      hR₀.ge (fun z => Du z i j) (hD i j)
  have hsmall' := rescaled_unit_data_le (u := u) (f := f) (p := p) hμ hμ1 hq hsmall
  obtain ⟨Dn, hAE, hInt, hweak, hN⟩ := hprod hsol' hdom' hU' hD' hsmall'
  exact interior_gradient_transport hμ hR₁ hR₁le hsol.2.1.measurableSet p Dn
    hAE hInt hweak hN

/-- **The quantitative pressure gradient on the two interior past collars.**
For the force exponent, the cubic data bound and the two Morrey bounds, one
finite Morrey majorant of a selected weak spatial pressure gradient is chosen
before every domain, time interval and solution.  The two radius pairs are
those of the causality localization: `(5/8, 19/32)` at velocity exponent
`25/3`, and `(9/16, 17/32)` at velocity exponent `25`. -/
theorem exists_pressure_gradient_morrey_bound_on_past_collar
    (q τ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞) (hq : 5 / 2 < q)
    (hinst : (τ = 25 / 3 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32) ∨
      (τ = 25 ∧ R₀ = 9 / 16 ∧ R₁ = 17 / 32))
    (hε : 0 ≤ ε) (hKU : KU < ⊤) (hKD : KD < ⊤) :
    ∃ KP : ℝ≥0∞, KP < ⊤ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i)
              (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
              ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i)) ≤
            KP) := by
  rcases hinst with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact exists_pressure_gradient_morrey_bound_of_dilation q (25 / 3) (5 / 8)
      (19 / 32) (11 / 16) (43 / 64) ε (10 / 11) KU KD hq (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (Or.inl ⟨rfl, rfl, rfl⟩) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hKU hKD
  · exact exists_pressure_gradient_morrey_bound_of_dilation q 25 (9 / 16)
      (17 / 32) (5 / 8) (19 / 32) ε (9 / 10) KU KD hq (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (Or.inr ⟨rfl, rfl, rfl⟩) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hKU hKD

end CKN.Core.Step4
