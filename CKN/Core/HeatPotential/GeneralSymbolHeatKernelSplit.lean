-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbolCharacterizationFinal
import CKN.Core.HeatPotential.GeneralSymbolHeatKernelSplitData
import CKN.Foundation.Heat.CausalDistribution

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

private lemma heatKernelPlus_measurable_heat_split :
    Measurable (fun p : ParabolicPoint => (heatKernelPlus p : ℂ)) := by
  apply Complex.measurable_ofReal.comp
  unfold heatKernelPlus
  apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
  · unfold heatKernel
    apply Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    · fun_prop
    · exact measurable_const
  · exact measurable_const

private lemma heatKernelPlus_locallyIntegrable_heat_split :
    LocallyIntegrable (fun p : ParabolicPoint => (heatKernelPlus p : ℂ)) volume := by
  intro p
  rcases heatKernelPlus_locallyIntegrable p with ⟨U, hU, hInt⟩
  exact ⟨U, hU, hInt.ofReal⟩

private lemma multiplierKernel_locallyIntegrable_heat_split
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

private lemma multiplierKernel_measurable_heat_split
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    Measurable (fun z : ParabolicPoint =>
      spatialMultiplierHeatKernel σ z.1 z.2) := by
  exact (measurable_spatialMultiplierHeatKernel hσ hhom).comp
    parabolicHomeomorph.measurable

private lemma heat_split_source_integrability
    {K : ℕ} {P θ₀ θ₁ : ℝ} (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀)
    (hPθ₁ : P ≤ θ₁) {F : ParabolicPoint → ℝ}
    {G : Fin K → ParabolicPoint → ℝ}
    (hFmeas : AEMeasurable F volume) (hGmeas : ∀ k, AEMeasurable (G k) volume)
    (hFmorrey : morreyNorm P θ₀ F < ∞)
    (hGmorrey : ∀ k, morreyNorm P θ₁ (G k) < ∞)
    (hFsupp : HasCompactSupport F) (hGsupp : ∀ k, HasCompactSupport (G k)) :
    Integrable F volume ∧ ∀ k, Integrable (G k) volume :=
  multiplierHeatPotential_sources_integrable hP hPθ₀ hPθ₁ hFmeas hGmeas
    hFmorrey hGmorrey hFsupp hGsupp

private lemma heat_split_set_measurable {z : ParabolicPoint} {r : ℝ} :
    MeasurableSet (multiplierHeatNearSet z r) ∧
      ∀ j, MeasurableSet (multiplierHeatShellSet z r j) := by
  constructor
  · exact Metric.isOpen_ball.measurableSet
  · intro j
    exact Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet

private lemma heat_split_source_parts
    {K : ℕ} {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} {N : ℕ}
    (hFint : Integrable F volume) (hFsupp : HasCompactSupport F)
    (hGint : ∀ k, Integrable (G k) volume)
    (hGsupp : ∀ k, HasCompactSupport (G k))
    (hsets : MeasurableSet (multiplierHeatNearSet z r))
    (hshells : ∀ j, MeasurableSet (multiplierHeatShellSet z r j)) :
    Integrable ((multiplierHeatNearSet z r).indicator F) volume ∧
      HasCompactSupport ((multiplierHeatNearSet z r).indicator F) ∧
      (∀ j ∈ Finset.range N,
        Integrable ((multiplierHeatShellSet z r (j + 6)).indicator F) volume ∧
          HasCompactSupport ((multiplierHeatShellSet z r (j + 6)).indicator F)) ∧
      (∀ k, Integrable ((multiplierHeatNearSet z r).indicator (G k)) volume ∧
        HasCompactSupport ((multiplierHeatNearSet z r).indicator (G k)) ∧
        ∀ j ∈ Finset.range N,
          Integrable ((multiplierHeatShellSet z r (j + 6)).indicator (G k)) volume ∧
            HasCompactSupport ((multiplierHeatShellSet z r (j + 6)).indicator (G k))) := by
  have hnearF : Integrable ((multiplierHeatNearSet z r).indicator F) volume :=
    hFint.indicator hsets
  have hnearFc : HasCompactSupport ((multiplierHeatNearSet z r).indicator F) :=
    indicator_hasCompactSupport_of_hasCompactSupport hFsupp
  have hshellF : ∀ j ∈ Finset.range N,
      Integrable ((multiplierHeatShellSet z r (j + 6)).indicator F) volume ∧
        HasCompactSupport ((multiplierHeatShellSet z r (j + 6)).indicator F) := by
    intro j hj
    exact ⟨hFint.indicator (hshells (j + 6)),
      indicator_hasCompactSupport_of_hasCompactSupport hFsupp⟩
  refine ⟨hnearF, hnearFc, hshellF, ?_⟩
  intro k
  have hnearG : Integrable ((multiplierHeatNearSet z r).indicator (G k)) volume :=
    (hGint k).indicator hsets
  have hnearGc : HasCompactSupport ((multiplierHeatNearSet z r).indicator (G k)) :=
    indicator_hasCompactSupport_of_hasCompactSupport (hGsupp k)
  refine ⟨hnearG, hnearGc, ?_⟩
  intro j hj
  exact ⟨(hGint k).indicator (hshells (j + 6)),
    indicator_hasCompactSupport_of_hasCompactSupport (hGsupp k)⟩

private lemma heat_split_potential_ae
    {K : ℕ} {σ : Fin K → Vec3 → ℂ}
    (hσ : ∀ k, ∀ n : ℕ,
      ContDiffOn ℝ (n : ℕ∞) (σ k) ({0}ᶜ : Set Vec3))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k))
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} {N : ℕ}
    (hFsplit : F = (multiplierHeatNearSet z r).indicator F +
        Finset.sum (Finset.range N) (fun j =>
          (multiplierHeatShellSet z r (j + 6)).indicator F))
    (hGsplit : ∀ k, G k = (multiplierHeatNearSet z r).indicator (G k) +
        Finset.sum (Finset.range N) (fun j =>
          (multiplierHeatShellSet z r (j + 6)).indicator (G k)))
    (hFint : Integrable F volume) (hFsupp : HasCompactSupport F)
    (hGint : ∀ k, Integrable (G k) volume)
    (hGsupp : ∀ k, HasCompactSupport (G k)) :
    ∀ᵐ w ∂volume,
      multiplierHeatPotential σ F G w =
        multiplierHeatPotentialNear σ F G z r w +
          Finset.sum (Finset.range N) (fun j =>
            multiplierHeatPotentialShell σ F G z r (j + 6) w) := by
  have hsets := heat_split_set_measurable (z := z) (r := r)
  have hparts := heat_split_source_parts (N := N) hFint hFsupp hGint hGsupp
    hsets.1 hsets.2
  have hFpot := kernel_potential_split_ae
    heatKernelPlus_locallyIntegrable_heat_split
    heatKernelPlus_measurable_heat_split hFsplit
    hparts.1 hparts.2.1
    (fun j hj => (hparts.2.2.1 j hj).1)
    (fun j hj => (hparts.2.2.1 j hj).2)
  have hGpot : ∀ k, ∀ᵐ w ∂volume,
      (∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
          (pointSub w v).2 * (G k v : ℂ)) =
        (∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
          (pointSub w v).2 *
            (((multiplierHeatNearSet z r).indicator (G k) v : ℝ) : ℂ)) +
          Finset.sum (Finset.range N) (fun j =>
            ∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
              (pointSub w v).2 *
                ((((multiplierHeatShellSet z r (j + 6)).indicator (G k)) v : ℝ) : ℂ)) := by
    intro k
    exact kernel_potential_split_ae
      (multiplierKernel_locallyIntegrable_heat_split
        (contDiffOn_infty.2 (hσ k)) (hhom k))
      (multiplierKernel_measurable_heat_split
        (contDiffOn_infty.2 (hσ k)) (hhom k))
      (hGsplit k) (hparts.2.2.2 k |>.1) (hparts.2.2.2 k |>.2.1)
      (fun j hj => (hparts.2.2.2 k |>.2.2 j hj).1)
      (fun j hj => (hparts.2.2.2 k |>.2.2 j hj).2)
  filter_upwards [hFpot, ae_all_iff.2 hGpot] with w hwF hwG
  simp only [multiplierHeatPotential, multiplierHeatPotentialNear,
    multiplierHeatPotentialShell]
  rw [hwF]
  have hGsum :
      (∑ k, ∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
          (pointSub w v).2 * (G k v : ℂ)) =
        ∑ k, ((∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
          (pointSub w v).2 *
            (((multiplierHeatNearSet z r).indicator (G k) v : ℝ) : ℂ)) +
          Finset.sum (Finset.range N) (fun j =>
            ∫ v, spatialMultiplierHeatKernel (σ k) (pointSub w v).1
              (pointSub w v).2 *
                ((((multiplierHeatShellSet z r (j + 6)).indicator (G k)) v : ℝ) : ℂ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hwG k
  rw [hGsum]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  ac_rfl

/-- The compactly supported general-symbol potential has the finite near/shell
split required by `step:heat-kernel-split`, with one locally integrable
representative identified almost everywhere. -/
theorem heatKernelSplit
    {K : ℕ} {P θ₀ θ₁ : ℝ} (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (σ : Fin K → Vec3 → ℂ) (hσ : ∀ k, SmoothOffOrigin (σ k))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k))
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    (hFmeas : AEMeasurable F volume) (hGmeas : ∀ k, AEMeasurable (G k) volume)
    (hFmorrey : morreyNorm P θ₀ F < ∞)
    (hGmorrey : ∀ k, morreyNorm P θ₁ (G k) < ∞)
    (hFsupp : HasCompactSupport F) (hGsupp : ∀ k, HasCompactSupport (G k))
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    ∃ hbar : ParabolicPoint → ℂ, ∃ N : ℕ,
      LocallyIntegrable hbar volume ∧
      hbar =ᵐ[volume] multiplierHeatPotential σ F G ∧
      hbar =ᵐ[volume] fun w =>
        multiplierHeatPotentialNear σ F G z r w +
          Finset.sum (Finset.range N) (fun j =>
            multiplierHeatPotentialShell σ F G z r (j + 6) w) := by
  have hσ' : ∀ k, ∀ n : ℕ,
      ContDiffOn ℝ (n : ℕ∞) (σ k) ({0}ᶜ : Set Vec3) := by
    intro k n
    exact hσ k n
  have hlocal := locallyIntegrable_multiplierHeatPotential_of_morrey
    hP hPθ₀ hPθ₁ hσ' hhom hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp
  have hsrc := heat_split_source_integrability hP hPθ₀ hPθ₁ hFmeas hGmeas
    hFmorrey hGmorrey hFsupp hGsupp
  obtain ⟨N, hFsplit, hGsplit⟩ :=
    source_split_data_of_compact_support hr hFsupp hGsupp
  let hbar : ParabolicPoint → ℂ := multiplierHeatPotential σ F G
  refine ⟨hbar, N, ?_, ?_, ?_⟩
  · exact hlocal
  · exact Filter.Eventually.of_forall (fun w => rfl)
  · exact heat_split_potential_ae hσ' hhom hFsplit hGsplit hsrc.1 hFsupp hsrc.2 hGsupp

end CKN.Core.HeatPotential
