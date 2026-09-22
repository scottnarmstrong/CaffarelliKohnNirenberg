-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbolCharacterization
import CKN.Core.HeatPotential.GeneralSymbolPairings
import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelLocalIntegrable

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

private lemma heatKernelPlus_measurable_characterization_ae :
    Measurable (fun p : ParabolicPoint => (heatKernelPlus p : ℂ)) := by
  apply Complex.measurable_ofReal.comp
  unfold heatKernelPlus
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · unfold heatKernel
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    · fun_prop
    · exact measurable_const
  · exact measurable_const

private lemma locallyIntegrable_spatialMultiplierHeatKernel_parabolic_characterization_ae
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

private lemma measurable_spatialMultiplierHeatKernel_parabolic_characterization_ae
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    Measurable (fun z : ParabolicPoint =>
      spatialMultiplierHeatKernel σ z.1 z.2) := by
  have h := measurable_spatialMultiplierHeatKernel hσ hhom
  exact h.comp parabolicHomeomorph.measurable

private lemma heatKernelPlus_locallyIntegrable_complex_characterization_ae :
    LocallyIntegrable (fun p : ParabolicPoint => (heatKernelPlus p : ℂ)) volume := by
  intro p
  rcases heatKernelPlus_locallyIntegrable p with ⟨U, hU, hInt⟩
  exact ⟨U, hU, hInt.ofReal⟩

/-- The Morrey source assumptions give the a.e. kernel-side slice representation.

The exceptional set is retained explicitly: compactly supported integrable sources
give the kernel pairings almost everywhere, which is the exact Fubini conclusion used
by the representation and does not silently strengthen the source hypotheses. -/
theorem multiplierHeatPotential_slice_form_ae_of_morrey
    {K : ℕ} {P θ₀ θ₁ : ℝ}
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    {σ : Fin K → Vec3 → ℂ}
    (hσ : ∀ k, ∀ n : ℕ,
      ContDiffOn ℝ (n : ℕ∞) (σ k) ({0}ᶜ : Set Vec3))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k))
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    (hFmeas : AEMeasurable F volume) (hGmeas : ∀ k, AEMeasurable (G k) volume)
    (hFmorrey : morreyNorm P θ₀ F < ∞)
    (hGmorrey : ∀ k, morreyNorm P θ₁ (G k) < ∞)
    (hFsupp : HasCompactSupport F) (hGsupp : ∀ k, HasCompactSupport (G k)) :
    ∀ᵐ w ∂volume,
      multiplierHeatPotential σ F G w =
        (∫ s : ℝ, spatialHeatConv (w.2 - s)
          (fun y : Vec3 => ((F (y, s) : ℝ) : ℂ)) w.1) +
          ∑ k, ∫ s : ℝ, spatialMultiplierApply (σ k)
            (spatialHeatConv (w.2 - s)
              (fun y : Vec3 => ((G k (y, s) : ℝ) : ℂ))) w.1 := by
  have hsrc := multiplierHeatPotential_sources_integrable
    hP hPθ₀ hPθ₁ hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp
  have hFpair := kernel_pairings_ae_of_compact
    heatKernelPlus_locallyIntegrable_complex_characterization_ae
    heatKernelPlus_measurable_characterization_ae hsrc.1 hFsupp
  have hGpair : ∀ k, ∀ᵐ w ∂volume,
      Integrable (fun v : ParabolicPoint =>
        spatialMultiplierHeatKernel (σ k) (pointSub w v).1
          (pointSub w v).2 * ((G k v : ℝ) : ℂ)) volume := by
    intro k
    exact kernel_pairings_ae_of_compact
      (locallyIntegrable_spatialMultiplierHeatKernel_parabolic_characterization_ae
        (contDiffOn_infty.2 (hσ k)) (hhom k))
      (measurable_spatialMultiplierHeatKernel_parabolic_characterization_ae
        (contDiffOn_infty.2 (hσ k)) (hhom k))
      (hsrc.2 k) (hGsupp k)
  have hGpairAll : ∀ᵐ w ∂volume, ∀ k, Integrable
      (fun v : ParabolicPoint =>
        spatialMultiplierHeatKernel (σ k) (pointSub w v).1
          (pointSub w v).2 * ((G k v : ℝ) : ℂ)) volume :=
    ae_all_iff.2 hGpair
  have hGslice := multiplierHeatPotential_source_slice_integrable
    hP hPθ₀ hPθ₁ hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp
  filter_upwards [hFpair, hGpairAll] with w hwF hwG
  exact multiplierHeatPotential_slice_form_of_pairings hσ hhom hGslice w hwF hwG

/-- The Morrey source assumptions make the kernel-side multiplier potential locally
integrable once the degree-one multiplier kernel bridge is available. -/
theorem locallyIntegrable_multiplierHeatPotential_of_morrey
    {K : ℕ} {P θ₀ θ₁ : ℝ}
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    {σ : Fin K → Vec3 → ℂ}
    (hσ : ∀ k, ∀ n : ℕ,
      ContDiffOn ℝ (n : ℕ∞) (σ k) ({0}ᶜ : Set Vec3))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k))
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    (hFmeas : AEMeasurable F volume) (hGmeas : ∀ k, AEMeasurable (G k) volume)
    (hFmorrey : morreyNorm P θ₀ F < ∞)
    (hGmorrey : ∀ k, morreyNorm P θ₁ (G k) < ∞)
    (hFsupp : HasCompactSupport F) (hGsupp : ∀ k, HasCompactSupport (G k)) :
    LocallyIntegrable (multiplierHeatPotential σ F G) volume := by
  have hsrc := multiplierHeatPotential_sources_integrable
    hP hPθ₀ hPθ₁ hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp
  have hF := kernel_potential_locallyIntegrable_of_compact
    heatKernelPlus_locallyIntegrable_complex_characterization_ae
    heatKernelPlus_measurable_characterization_ae hsrc.1 hFsupp
  have hG : ∀ k, LocallyIntegrable (fun w : ParabolicPoint =>
      ∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
        (pointSub w v).2 * (G k v : ℂ)) volume := by
    intro k
    exact kernel_potential_locallyIntegrable_of_compact
      (locallyIntegrable_spatialMultiplierHeatKernel_parabolic_characterization_ae
        (contDiffOn_infty.2 (hσ k)) (hhom k))
      (measurable_spatialMultiplierHeatKernel_parabolic_characterization_ae
        (contDiffOn_infty.2 (hσ k)) (hhom k))
      (hsrc.2 k) (hGsupp k)
  have hsum : LocallyIntegrable (fun w : ParabolicPoint =>
      ∑ k, ∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
        (pointSub w v).2 * (G k v : ℂ)) volume := by
    exact locallyIntegrable_finsetSum (Finset.univ : Finset (Fin K))
      (fun k hk => hG k)
  change LocallyIntegrable ((fun w : ParabolicPoint =>
      ∫ v, (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ)) +
      (fun w : ParabolicPoint =>
        ∑ k, ∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
          (pointSub w v).2 * (G k v : ℂ))) volume
  exact hF.add hsum

/-- A compactly supported test function may be moved across a kernel potential by
Fubini.  This is the test-transform identity used by the distributional clause. -/
theorem kernel_testFunction_pairing_of_compact
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) {g : ParabolicPoint → ℝ}
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    {ψ : ParabolicPoint → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) :
    (∫ w, ψ w * (∫ v, k (pointSub w v) * (g v : ℂ))) =
      ∫ v, (g v : ℂ) * (∫ w, ψ w * k (pointSub w v)) := by
  let K : Set ParabolicPoint := tsupport ψ
  have hK : IsCompact K := hψs.isCompact
  have hbase := kernel_product_integrableOn_of_compact hk hkm hg hgc hK
  obtain ⟨C, hC⟩ := hψc.bounded_above_of_compact_support hψs
  have hψae : AEStronglyMeasurable (fun z : ParabolicPoint × ParabolicPoint =>
      ψ z.1) (((volume : Measure ParabolicPoint).restrict K).prod
        (volume : Measure ParabolicPoint)) := by
    exact ((hψc.stronglyMeasurable_of_hasCompactSupport hψs).comp_measurable
      measurable_fst).aestronglyMeasurable
  have hprod : Integrable (fun z : ParabolicPoint × ParabolicPoint =>
      ψ z.1 * (k (pointSub z.1 z.2) * (g z.2 : ℂ)))
      (((volume : Measure ParabolicPoint).restrict K).prod
        (volume : Measure ParabolicPoint)) := by
    apply hbase.bdd_mul hψae
    filter_upwards [] with z
    exact hC z.1
  let f : ParabolicPoint × ParabolicPoint → ℂ := fun z =>
    ψ z.1 * (k (pointSub z.1 z.2) * (g z.2 : ℂ))
  have hfull : Integrable f ((volume : Measure ParabolicPoint).prod volume) := by
    apply (integrableOn_iff_integrable_of_support_subset (s := K ×ˢ Set.univ) ?_).mp
    · change IntegrableOn f (K ×ˢ Set.univ)
        ((volume : Measure ParabolicPoint).prod volume)
      rw [IntegrableOn, ← Measure.prod_restrict]
      simpa only [Measure.restrict_univ, f] using hprod
    · intro z hz
      have hzψ : ψ z.1 ≠ 0 := by
        intro hzψ
        apply hz
        simp only [f, hzψ, zero_mul]
      exact ⟨subset_tsupport (f := ψ) (Function.mem_support.mpr hzψ), mem_univ z.2⟩
  calc
    (∫ w, ψ w * (∫ v, k (pointSub w v) * (g v : ℂ))) =
        ∫ w, ∫ v, f (w, v) := by
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [f]
      rw [integral_const_mul]
    _ = ∫ z, f z := (integral_prod f hfull).symm
    _ = ∫ v, ∫ w, f (w, v) := integral_prod_symm f hfull
    _ = ∫ v, (g v : ℂ) * (∫ w, ψ w * k (pointSub w v)) := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [f]
      rw [show (fun w => ψ w * (k (pointSub w v) * (g v : ℂ))) =
          (fun w => (ψ w * k (pointSub w v)) * (g v : ℂ)) by
            funext w
            ring]
      rw [integral_mul_const]
      ring

end CKN.Core.HeatPotential
