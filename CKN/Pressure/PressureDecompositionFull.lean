-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.DecompositionGlobalDistribution
import CKN.Pressure.PressureDecompositionRiesz
import CKN.Pressure.ForceCancellationLocalSpacetime
import CKN.Pressure.PkBoundsUnconditionalCore

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
open CKN.Foundation.Euclidean

set_option autoImplicit false
noncomputable section

namespace CKN

/-- The full local pressure decomposition, including its distributional
Laplacian identity for arbitrary compactly supported spatial tests. -/
theorem pressure_decomposition_full_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    let η := mollifiedBallCutoff z.1 hρ
    let c := fun t j => average (volume.restrict (vec3Ball z.1 ρ))
      (fun y => u (y, t) j)
    (∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        (∫ x, η x * p (x, t) * spatialLaplacian ψ x) =
          (∫ x, ∑ i, ∑ j,
            η x * pressureUTensor u c (x, t) i j * mixedSecond ψ i j x) +
          (∫ x, ∑ i, ∑ j,
            mixedSecond η i j x * pressureUTensor u c (x, t) i j * ψ x) +
          (∫ x, ∑ i, ∑ j,
            pressureUTensor u c (x, t) i j * spatialDeriv η i x * spatialDeriv ψ j x) +
          (∫ x, ∑ i, ∑ j,
            pressureUTensor u c (x, t) i j * spatialDeriv η j x * spatialDeriv ψ i x) -
          (∫ x, p (x, t) * spatialLaplacian η x * ψ x) -
          2 * (∫ x, ∑ j, spatialDeriv η j x * p (x, t) * spatialDeriv ψ j x) -
          (∫ x, ∑ j, η x * f (x, t) j * spatialDeriv ψ j x) -
          (∫ x, ∑ j, spatialDeriv η j x * f (x, t) j * ψ x)) ∧
    (∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (pressureP1 η u c p f t =ᵐ[volume]
        pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
          (fun i j x => η x * pressureUTensor u c (x, t) i j)) ∧
      ((fun x => η x * p (x, t)) =ᵐ[volume]
        (fun x => pressureP1 η u c p f t x + pressureP2 η u c t x +
          pressureP3 η u c t x + pressureP4 η u c t x + pressureP5 η p t x +
          pressureP6 η p t x + pressureP7 η f t x + pressureP8 η f t x))) ∧
    ((∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w => ∑ i, f w i * spatialPartial ψ i w) (tsupport ψ) volume ∧
      ∫ w in spaceTimeSet Ω I, ∑ i, f w i * spatialPartial ψ i w = 0) →
      ∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        pressureP7 η f t + pressureP8 η f t =ᵐ[volume] 0) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun t j =>
    average (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := mollifiedBallCutoff_smooth z.1 hρ
  have hηc : HasCompactSupport η := mollifiedBallCutoff_hasCompactSupport z.1 hρ
  obtain ⟨_Ω', _J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport η ⊆ Ω :=
    (pressure_cutoff_support_subset_ball z.1 hρ).trans
      (fun x hx => hbox.2.2.1 (subset_closure (hball hx)))
  have htimeI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  constructor
  · intro ψ hψ hψc
    have hglobal := pressure_laplace_cutoff_identity_global_ae
      hsol hη hηc hηΩ (c := c) hψ hψc
    have hlocal := ae_restrict_of_ae_restrict_of_subset htimeI hglobal
    filter_upwards [hlocal] with t ht
    have hgradInt :
        (∫ x, spatialGradDot η ψ x * p (x, t)) =
          (∫ x, ∑ j, spatialDeriv η j x * p (x, t) * spatialDeriv ψ j x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [spatialGradDot, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hgradInt] at ht
    simpa only [η, c, mul_assoc, mul_left_comm, mul_comm] using ht
  · constructor
    · have hP1 := pressure_decomposition_first_term_riesz_of_sws hsol hρ hsub
      have hterms := pressure_decomposition_eight_terms_of_sws hsol hρ hsub
      filter_upwards [hP1, hterms] with t htP1 htTerms
      have hdecomp : (fun x => η x * p (x, t)) =ᵐ[volume]
          (fun x => pressureP1 η u c p f t x + pressureP2 η u c t x +
            pressureP3 η u c t x + pressureP4 η u c t x + pressureP5 η p t x +
            pressureP6 η p t x + pressureP7 η f t x + pressureP8 η f t x) := by
        filter_upwards [htP1, htTerms] with x hxP1 hxTerms
        change pressureP1 η u c p f t x =
          pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
            (fun i j y => η y * pressureUTensor u c (y, t) i j) x at hxP1
        change η x * p (x, t) =
          pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
              (fun i j y => η y * pressureUTensor u c (y, t) i j) x +
            pressureP2 η u c t x + pressureP3 η u c t x + pressureP4 η u c t x +
            pressureP5 η p t x + pressureP6 η p t x + pressureP7 η f t x +
            pressureP8 η f t x at hxTerms
        rw [← hxP1] at hxTerms
        exact hxTerms
      exact ⟨(by simpa only [η, c] using htP1),
        (by simpa only [η, c] using hdecomp)⟩
    · intro hdiv
      exact pressure_force_eq_zero_of_sws_localSpacetimeDivergenceFree
        hsol hρ hsub hdiv

end CKN

end
