-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.PressureGaugeSlices

/-!
# The pressure of a suitable weak solution is fixed only up to a function of time

This file proves the invariance stated in `rem:two-means` of `paper/ckn.tex`:
if `(u,p)` is a suitable weak solution with force `f` and `c ∈ L^{3/2}_loc(I)`,
then `(u, p + c)` is a suitable weak solution with the same force.  This is the
reason the pressure in the excess `eq:excess` is compared with a spatial mean at
each time: no statement about `p` alone can be invariant.

Only two clauses of `def:sws` see the gauge.  In the momentum equation the extra
term is `c(t) div φ`, which integrates to zero because the spatial integral of a
divergence vanishes on every time slice.  In the local energy inequality the
extra term is `2 c(t) u · ∇ψ`, which integrates to zero because the
divergence-free clause (S2) makes the spatial pairing of `u(·,t)` with
`∇ψ(·,t)` vanish for almost every time.  Both pairings are integrable by the
slice bound coming from the essential supremum of the slice energies.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- **`rem:two-means`, the pressure gauge.**  Adding a function of time in
`L^{3/2}` on every local time interval to the pressure of a suitable weak
solution again gives a suitable weak solution with the same velocity, gradient
and force. -/
theorem isSuitableWeakSolutionIntegrable_add_pressure_gauge
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (c : ℝ → ℝ)
    (hc : ∀ Ω' J, localBox Ω I Ω' J →
      MemLp c (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict J)) :
    IsSuitableWeakSolutionIntegrable Ω I q u Du (fun z => p z + c z.2) f := by
  classical
  obtain ⟨hΩ, hI, hIord, hq, hfloc, hmeas, hS2, hmom, hen⟩ := hsol
  refine ⟨hΩ, hI, hIord, hq, hfloc, ?_, hS2, ?_, ?_⟩
  · -- The measurability and integrability data.
    intro Ω' J hbox
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hmeas Ω' J hbox
    have hcbox := memLp_gauge_on_box hbox (hc Ω' J hbox)
    refine ⟨h1, h2, h3.add hcbox.aestronglyMeasurable, h4, h5, h6, ?_, h8, h9⟩
    exact h7.add hcbox
  · -- The momentum equation.
    intro φ hφ
    obtain ⟨hOldInt, hOldZero⟩ := hmom φ hφ
    obtain ⟨hcInt, hcZero⟩ := gauge_divergence_pairing hΩ hI hIord hc hφ
    set T : Set ParabolicPoint := tsupport (show ParabolicPoint → Vec3 from φ)
      with hTdef
    have hTeq : T = tsupport φ := tsupport_parabolic_eq φ
    have hcompsupp : ∀ i : Fin 3,
        tsupport (fun w => φ w i) ⊆ tsupport φ := by
      intro i
      refine tsupport_component_subset (V := Vec3) (ι := Fin 3) φ i ?_
      intro z hz
      rw [hz]
      rfl
    have hOldOff : ∀ z : ParabolicPoint, z ∉ T →
        (-∑ i, u z i * timePartial (fun w => φ w i) z
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f z i * φ z i) = 0 := by
      intro z hzT
      have hz : z ∉ tsupport φ := hTeq ▸ hzT
      have h1 : ∀ i : Fin 3, timePartial (fun w => φ w i) z = 0 := fun i =>
        timePartial_eq_zero_off_tsupport (ψ := fun w : Vec3 × ℝ => φ w i)
          (fun hmem => hz (hcompsupp i hmem))
      have h2 : ∀ i j : Fin 3, spatialPartial (fun w => φ w i) j z = 0 := fun i j =>
        spatialPartial_eq_zero_off_tsupport (ψ := fun w : Vec3 × ℝ => φ w i)
          (fun hmem => hz (hcompsupp i hmem)) j
      have h3 : ∀ i : Fin 3, φ z i = 0 := fun i =>
        image_eq_zero_of_notMem_tsupport (f := fun w => φ w i)
          fun hmem => hz (hcompsupp i hmem)
      simp [h1, h2, h3]
    have hOldSupp : Function.support
        (fun z => -∑ i, u z i * timePartial (fun w => φ w i) z
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f z i * φ z i) ⊆ T := by
      intro z hz
      by_contra hcon
      exact hz (hOldOff z hcon)
    have hOldFull := (integrableOn_iff_integrable_of_support_subset hOldSupp).mp hOldInt
    have hpt : ∀ z : ParabolicPoint,
        (-∑ i, u z i * timePartial (fun w => φ w i) z
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
            - (p z + c z.2) * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f z i * φ z i)
          = (-∑ i, u z i * timePartial (fun w => φ w i) z
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f z i * φ z i)
              - c z.2 * ∑ i, spatialPartial (fun w => φ w i) i z := by
      intro z
      ring
    refine ⟨?_, ?_⟩
    · refine (hOldInt.sub hcInt.integrableOn).congr ?_
      exact Filter.Eventually.of_forall fun z => (hpt z).symm
    · have hcoff : ∀ z : ParabolicPoint, z ∉ spaceTimeSet Ω I →
          c z.2 * ∑ i, spatialPartial (fun w => φ w i) i z = 0 := by
        intro z hz
        have hz' : z ∉ tsupport φ := fun hmem => hz (hφ.2.2 hmem)
        have h2 : ∀ i : Fin 3, spatialPartial (fun w => φ w i) i z = 0 := fun i =>
          spatialPartial_eq_zero_off_tsupport (ψ := fun w : Vec3 × ℝ => φ w i)
            (fun hmem => hz' (hcompsupp i hmem)) i
        simp [h2]
      have hcST : ∫ z in spaceTimeSet Ω I,
          c z.2 * ∑ i, spatialPartial (fun w => φ w i) i z = 0 := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hcoff]
        exact hcZero
      calc ∫ z in spaceTimeSet Ω I,
            (-∑ i, u z i * timePartial (fun w => φ w i) z
              - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
              + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
              - (p z + c z.2) * ∑ i, spatialPartial (fun w => φ w i) i z
              - ∑ i, f z i * φ z i)
          = ∫ z in spaceTimeSet Ω I,
              ((-∑ i, u z i * timePartial (fun w => φ w i) z
                - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
                + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
                - p z * ∑ i, spatialPartial (fun w => φ w i) i z
                - ∑ i, f z i * φ z i)
                - c z.2 * ∑ i, spatialPartial (fun w => φ w i) i z) :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ = (∫ z in spaceTimeSet Ω I,
              (-∑ i, u z i * timePartial (fun w => φ w i) z
                - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
                + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
                - p z * ∑ i, spatialPartial (fun w => φ w i) i z
                - ∑ i, f z i * φ z i))
            - ∫ z in spaceTimeSet Ω I,
                c z.2 * ∑ i, spatialPartial (fun w => φ w i) i z :=
            integral_sub hOldFull.integrableOn hcInt.integrableOn
        _ = 0 := by rw [hOldZero, hcST, sub_zero]
  · -- The local energy inequality.
    intro ψ hψ hψnn
    obtain ⟨hGradInt, hOldInt, hOldIneq⟩ := hen ψ hψ hψnn
    set T : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from ψ)
      with hTdef
    have hTeq : T = tsupport ψ := tsupport_parabolic_eq ψ
    obtain ⟨hcInt, hcZero⟩ := gauge_velocity_pairing hΩ hI hIord hc
      (fun Ω' J hbox => (hmeas Ω' J hbox).1)
      (fun Ω' J hbox => (hmeas Ω' J hbox).2.2.2.2.1) hS2 hψ
    have hOldOff : ∀ z : ParabolicPoint, z ∉ T →
        (vec3EuclideanNorm (u z) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + (2 * ∑ i, f z i * u z i) * ψ z) = 0 := by
      intro z hzT
      have hz : z ∉ tsupport ψ := hTeq ▸ hzT
      have h1 : timePartial ψ z = 0 := timePartial_eq_zero_off_tsupport hz
      have h2 : ∀ i : Fin 3, spatialSecondPartial ψ i i z = 0 := by
        intro i
        exact spatialPartial_eq_zero_off_tsupport
          (fun hmem => hz (tsupport_spatialPartial_subset i hmem)) i
      have h3 : ∀ i : Fin 3, spatialPartial ψ i z = 0 := fun i =>
        spatialPartial_eq_zero_off_tsupport hz i
      have h4 : ψ z = 0 :=
        image_eq_zero_of_notMem_tsupport (f := show ParabolicPoint → ℝ from ψ) hzT
      simp [h1, h2, h3, h4]
    have hOldSupp : Function.support
        (fun z => vec3EuclideanNorm (u z) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + (2 * ∑ i, f z i * u z i) * ψ z) ⊆ T := by
      intro z hz
      by_contra hcon
      exact hz (hOldOff z hcon)
    have hOldFull := (integrableOn_iff_integrable_of_support_subset hOldSupp).mp hOldInt
    have hpt : ∀ z : ParabolicPoint,
        (vec3EuclideanNorm (u z) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + (vec3EuclideanNorm (u z) ^ 2 + 2 * (p z + c z.2)) *
                ∑ i, u z i * spatialPartial ψ i z
            + (2 * ∑ i, f z i * u z i) * ψ z)
          = (vec3EuclideanNorm (u z) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + (2 * ∑ i, f z i * u z i) * ψ z)
              + 2 * (c z.2 * ∑ i, u z i * spatialPartial ψ i z) := by
      intro z
      ring
    have hcoff : ∀ z : ParabolicPoint, z ∉ spaceTimeSet Ω I →
        c z.2 * ∑ i, u z i * spatialPartial ψ i z = 0 := by
      intro z hz
      have hz' : z ∉ tsupport ψ := fun hmem => hz (hψ.2.2 hmem)
      have h3 : ∀ i : Fin 3, spatialPartial ψ i z = 0 := fun i =>
        spatialPartial_eq_zero_off_tsupport hz' i
      simp [h3]
    have hcST : ∫ z in spaceTimeSet Ω I,
        c z.2 * ∑ i, u z i * spatialPartial ψ i z = 0 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hcoff]
      exact hcZero
    refine ⟨hGradInt, ?_, ?_⟩
    · refine (hOldInt.add ((hcInt.const_mul (2 : ℝ)).integrableOn)).congr ?_
      exact Filter.Eventually.of_forall fun z => (hpt z).symm
    · have hsplit : ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z) ^ 2 *
                (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
              + (vec3EuclideanNorm (u z) ^ 2 + 2 * (p z + c z.2)) *
                  ∑ i, u z i * spatialPartial ψ i z
              + (2 * ∑ i, f z i * u z i) * ψ z)
            = ∫ z in spaceTimeSet Ω I,
                (vec3EuclideanNorm (u z) ^ 2 *
                  (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
                + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                    ∑ i, u z i * spatialPartial ψ i z
                + (2 * ∑ i, f z i * u z i) * ψ z) := by
        calc ∫ z in spaceTimeSet Ω I,
              (vec3EuclideanNorm (u z) ^ 2 *
                    (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
                  + (vec3EuclideanNorm (u z) ^ 2 + 2 * (p z + c z.2)) *
                      ∑ i, u z i * spatialPartial ψ i z
                  + (2 * ∑ i, f z i * u z i) * ψ z)
            = ∫ z in spaceTimeSet Ω I,
                ((vec3EuclideanNorm (u z) ^ 2 *
                    (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
                  + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                      ∑ i, u z i * spatialPartial ψ i z
                  + (2 * ∑ i, f z i * u z i) * ψ z)
                  + 2 * (c z.2 * ∑ i, u z i * spatialPartial ψ i z)) :=
              integral_congr_ae (Filter.Eventually.of_forall hpt)
          _ = (∫ z in spaceTimeSet Ω I,
                (vec3EuclideanNorm (u z) ^ 2 *
                    (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
                  + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                      ∑ i, u z i * spatialPartial ψ i z
                  + (2 * ∑ i, f z i * u z i) * ψ z))
              + ∫ z in spaceTimeSet Ω I,
                  2 * (c z.2 * ∑ i, u z i * spatialPartial ψ i z) :=
              integral_add hOldFull.integrableOn
                ((hcInt.const_mul (2 : ℝ)).integrableOn)
          _ = _ := by
              rw [integral_const_mul, hcST, mul_zero, add_zero]
      rw [hsplit]
      exact hOldIneq

end CKN
