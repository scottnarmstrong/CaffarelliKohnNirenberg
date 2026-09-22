-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbolCharacterizationAE
import CKN.Foundation.Heat.CausalDistribution

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

private lemma heatKernelPlus_measurable_characterization_final :
    Measurable (fun p : ParabolicPoint => (heatKernelPlus p : ℂ)) := by
  apply Complex.measurable_ofReal.comp
  unfold heatKernelPlus
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · unfold heatKernel
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    · fun_prop
    · exact measurable_const
  · exact measurable_const

private lemma heatKernelPlus_locallyIntegrable_complex_characterization_final :
    LocallyIntegrable (fun p : ParabolicPoint => (heatKernelPlus p : ℂ)) volume := by
  intro p
  rcases heatKernelPlus_locallyIntegrable p with ⟨U, hU, hInt⟩
  exact ⟨U, hU, hInt.ofReal⟩

private lemma multiplierKernel_locallyIntegrable_characterization_final
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    LocallyIntegrable (fun z : ParabolicPoint =>
      spatialMultiplierHeatKernel σ z.1 z.2) volume := by
  intro z
  rcases locallyIntegrable_spatialMultiplierHeatKernel hσ hhom
      (parabolicHomeomorph z) with ⟨U, hU, hInt⟩
  refine ⟨parabolicHomeomorph ⁻¹' U, ?_, ?_⟩
  · exact parabolicHomeomorph.continuous.continuousAt.preimage_mem_nhds hU
  · have hset : parabolicHomeomorph ⁻¹' U = U := by
      ext q
      rfl
    rw [hset]
    change IntegrableOn (fun z : Vec3 × ℝ =>
      spatialMultiplierHeatKernel σ z.1 z.2) U
      (volume : Measure (Vec3 × ℝ))
    exact hInt

private lemma multiplierKernel_measurable_characterization_final
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    Measurable (fun z : ParabolicPoint =>
      spatialMultiplierHeatKernel σ z.1 z.2) := by
  exact (measurable_spatialMultiplierHeatKernel hσ hhom).comp
    parabolicHomeomorph.measurable

private lemma test_function_hasCompactSupport_parabolic
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℂ)) :
    HasCompactSupport (fun w : ParabolicPoint => ψ (parabolicHomeomorph w)) := by
  exact ψ.hasCompactSupport.comp_homeomorph parabolicHomeomorph

private lemma test_function_continuous_parabolic
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℂ)) :
    Continuous (fun w : ParabolicPoint => ψ (parabolicHomeomorph w)) := by
  exact ψ.continuous.comp parabolicHomeomorph.continuous

private lemma potential_test_integrable_characterization_final
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) {g : ParabolicPoint → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℂ)) :
    Integrable (fun w : ParabolicPoint =>
      ψ (parabolicHomeomorph w) * (∫ v, k (pointSub w v) * (g v : ℂ))) volume := by
  have hpot := kernel_potential_locallyIntegrable_of_compact hk hkm hg hgc
  have hmul := hpot.integrable_smul_left_of_hasCompactSupport
    (test_function_continuous_parabolic ψ)
    (test_function_hasCompactSupport_parabolic ψ)
  simpa only [smul_eq_mul] using hmul

private lemma potential_test_pairing_characterization_final
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) {g : ParabolicPoint → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℂ)) :
    (∫ w : ParabolicPoint, ψ (parabolicHomeomorph w) *
        (∫ v, k (pointSub w v) * (g v : ℂ))) =
      ∫ v, (g v : ℂ) *
        (∫ w : ParabolicPoint, ψ (parabolicHomeomorph w) *
          k (pointSub w v)) := by
  exact kernel_testFunction_pairing_of_compact hk hkm hg hgc
    (test_function_continuous_parabolic ψ)
    (test_function_hasCompactSupport_parabolic ψ)

/-- The general-symbol heat potential has the a.e. slice characterization and
the compact-test distributional pairing from `eq:heat-potential`. -/
theorem heatPotentialCharacterization
    {K : ℕ} {P θ₀ θ₁ : ℝ} (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (σ : Fin K → Vec3 → ℂ) (hσ : ∀ k, ∀ n : ℕ, ContDiffOn ℝ (n : ℕ∞) (σ k) ({0}ᶜ : Set Vec3))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k))
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    (hFmeas : AEMeasurable F volume) (hGmeas : ∀ k, AEMeasurable (G k) volume)
    (hFmorrey : morreyNorm P θ₀ F < ∞)
    (hGmorrey : ∀ k, morreyNorm P θ₁ (G k) < ∞)
    (hFsupp : HasCompactSupport F) (hGsupp : ∀ k, HasCompactSupport (G k)) :
    ∃ hbar : ParabolicPoint → ℂ,
      LocallyIntegrable hbar volume ∧
      hbar =ᵐ[volume] multiplierHeatPotential σ F G ∧
      (∀ᵐ w ∂volume,
        Integrable (fun v => (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ)) volume ∧
        ∀ k, Integrable
          (fun v => spatialMultiplierHeatKernel (σ k) (pointSub w v).1
            (pointSub w v).2 * (G k v : ℂ)) volume) ∧
      (∀ᵐ w ∂volume,
        multiplierHeatPotential σ F G w =
          (∫ s : ℝ, spatialHeatConv (w.2 - s)
            (fun y : Vec3 => ((F (y, s) : ℝ) : ℂ)) w.1) +
            ∑ k, ∫ s : ℝ, spatialMultiplierApply (σ k)
              (spatialHeatConv (w.2 - s)
                (fun y : Vec3 => ((G k (y, s) : ℝ) : ℂ))) w.1) ∧
      ∀ ψ : 𝓓((⊤ : TopologicalSpace.Opens (Vec3 × ℝ)), ℂ),
        (∫ w, ψ w * hbar w) =
          (∫ v, (F v : ℂ) *
            (∫ w, ψ w * (heatKernelPlus (pointSub w v) : ℂ))) +
          ∑ k, ∫ v, (G k v : ℂ) *
            (∫ w, ψ w *
              spatialMultiplierHeatKernel (σ k) (pointSub w v).1
                (pointSub w v).2) := by
  have hsrc := multiplierHeatPotential_sources_integrable
    hP hPθ₀ hPθ₁ hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp
  have hlocal := locallyIntegrable_multiplierHeatPotential_of_morrey
    hP hPθ₀ hPθ₁ hσ hhom hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp
  have hslice := multiplierHeatPotential_slice_form_ae_of_morrey
    hP hPθ₀ hPθ₁ hσ hhom hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp
  let hbar : ParabolicPoint → ℂ := multiplierHeatPotential σ F G
  refine ⟨hbar, ?_, ?_, ?_, ?_, ?_⟩
  · exact hlocal
  · exact Filter.Eventually.of_forall (fun w => rfl)
  · have hFpair := kernel_pairings_ae_of_compact
      heatKernelPlus_locallyIntegrable_complex_characterization_final
      heatKernelPlus_measurable_characterization_final hsrc.1 hFsupp
    have hGpair : ∀ k, ∀ᵐ w ∂volume, Integrable
        (fun v : ParabolicPoint =>
          spatialMultiplierHeatKernel (σ k) (pointSub w v).1
            (pointSub w v).2 * (G k v : ℂ)) volume := by
      intro k
      exact kernel_pairings_ae_of_compact
        (multiplierKernel_locallyIntegrable_characterization_final
          (contDiffOn_infty.2 (hσ k)) (hhom k))
        (multiplierKernel_measurable_characterization_final
          (contDiffOn_infty.2 (hσ k)) (hhom k)) (hsrc.2 k) (hGsupp k)
    have hGall : ∀ᵐ w ∂volume, ∀ k, Integrable
        (fun v : ParabolicPoint =>
          spatialMultiplierHeatKernel (σ k) (pointSub w v).1
            (pointSub w v).2 * (G k v : ℂ)) volume := ae_all_iff.2 hGpair
    filter_upwards [hFpair, hGall] with w hwF hwG
    exact ⟨hwF, hwG⟩
  · exact hslice
  · intro ψ
    have hFpot := potential_test_integrable_characterization_final
      heatKernelPlus_locallyIntegrable_complex_characterization_final
      heatKernelPlus_measurable_characterization_final hsrc.1 hFsupp ψ
    have hGpot : ∀ k, Integrable (fun w : ParabolicPoint =>
        ψ (parabolicHomeomorph w) *
          (∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
            (pointSub w v).2 * (G k v : ℂ))) volume := by
      intro k
      exact potential_test_integrable_characterization_final
        (multiplierKernel_locallyIntegrable_characterization_final
          (contDiffOn_infty.2 (hσ k)) (hhom k))
        (multiplierKernel_measurable_characterization_final
          (contDiffOn_infty.2 (hσ k)) (hhom k)) (hsrc.2 k) (hGsupp k) ψ
    have hsumInt : Integrable (fun w : ParabolicPoint =>
        ∑ k, ψ (parabolicHomeomorph w) *
          (∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
            (pointSub w v).2 * (G k v : ℂ))) volume :=
      integrable_finsetSum (Finset.univ : Finset (Fin K))
        (fun k hk => hGpot k)
    have hFpair := potential_test_pairing_characterization_final
      heatKernelPlus_locallyIntegrable_complex_characterization_final
      heatKernelPlus_measurable_characterization_final hsrc.1 hFsupp ψ
    have hGpair : ∀ k, (∫ w : ParabolicPoint, ψ (parabolicHomeomorph w) *
        (∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
          (pointSub w v).2 * (G k v : ℂ))) =
        ∫ v, (G k v : ℂ) * (∫ w : ParabolicPoint,
          ψ (parabolicHomeomorph w) *
            spatialMultiplierHeatKernel (σ k) (pointSub w v).1
              (pointSub w v).2) := by
      intro k
      exact potential_test_pairing_characterization_final
        (multiplierKernel_locallyIntegrable_characterization_final
          (contDiffOn_infty.2 (hσ k)) (hhom k))
        (multiplierKernel_measurable_characterization_final
          (contDiffOn_infty.2 (hσ k)) (hhom k)) (hsrc.2 k) (hGsupp k) ψ
    change (∫ w : ParabolicPoint, ψ (parabolicHomeomorph w) * hbar w) =
      (∫ v : ParabolicPoint, (F v : ℂ) *
        (∫ w : ParabolicPoint, ψ (parabolicHomeomorph w) *
          (heatKernelPlus (pointSub w v) : ℂ))) +
        ∑ k, ∫ v : ParabolicPoint, (G k v : ℂ) *
          (∫ w : ParabolicPoint, ψ (parabolicHomeomorph w) *
            spatialMultiplierHeatKernel (σ k) (pointSub w v).1
              (pointSub w v).2)
    change (∫ w : ParabolicPoint, ψ (parabolicHomeomorph w) *
      ((∫ v, (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ)) +
        ∑ k, ∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
          (pointSub w v).2 * (G k v : ℂ))) = _
    simp_rw [mul_add, Finset.mul_sum]
    rw [integral_add hFpot hsumInt]
    rw [integral_finsetSum (Finset.univ : Finset (Fin K))
      (fun k hk => hGpot k)]
    rw [hFpair]
    have hsumPair :
        (∑ k, ∫ w : ParabolicPoint, ψ (parabolicHomeomorph w) *
          (∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
            (pointSub w v).2 * (G k v : ℂ))) =
        ∑ k, ∫ v, (G k v : ℂ) * (∫ w : ParabolicPoint,
          ψ (parabolicHomeomorph w) *
            spatialMultiplierHeatKernel (σ k) (pointSub w v).1
              (pointSub w v).2) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hGpair k
    rw [hsumPair]

end CKN.Core.HeatPotential
