-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.Decomposition
import CKN.Pressure.DecompositionSWSBasic

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN

private theorem pressureAllSpace_support_spatialDeriv_subset {φ : Vec3 → ℝ} (i : Fin 3) :
    Function.support (spatialDeriv φ i) ⊆ tsupport φ := by
  intro x hx
  by_contra hxt
  exact hx (by simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt])

private theorem pressureAllSpace_ts_support_spatialDeriv_subset {φ : Vec3 → ℝ} (i : Fin 3) :
    tsupport (spatialDeriv φ i) ⊆ tsupport φ :=
  closure_minimal (pressureAllSpace_support_spatialDeriv_subset i) (isClosed_tsupport φ)

private theorem pressureAllSpace_support_mixedSecond_subset {φ : Vec3 → ℝ} (i j : Fin 3) :
    Function.support (mixedSecond φ i j) ⊆ tsupport φ :=
  (pressureAllSpace_support_spatialDeriv_subset (φ := spatialDeriv φ j) i).trans
    (pressureAllSpace_ts_support_spatialDeriv_subset j)

private theorem pressureAllSpace_ts_support_mixedSecond_subset {φ : Vec3 → ℝ}
    (i j : Fin 3) : tsupport (mixedSecond φ i j) ⊆ tsupport φ :=
  closure_minimal (pressureAllSpace_support_mixedSecond_subset i j) (isClosed_tsupport φ)

private theorem pressureAllSpace_ts_support_spatialLaplacian_subset {φ : Vec3 → ℝ} :
    tsupport (spatialLaplacian φ) ⊆ tsupport φ := by
  apply closure_minimal
  · intro x hx
    by_contra hxt
    have hsecond (i : Fin 3) : spatialDeriv (spatialDeriv φ i) i x = 0 := by
      have hnot : x ∉ tsupport (spatialDeriv φ i) := fun hi =>
        hxt (pressureAllSpace_ts_support_spatialDeriv_subset i hi)
      simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]
    apply hx
    simp only [spatialLaplacian]
    rw [Finset.sum_eq_zero fun i _ => hsecond i]
  · exact isClosed_tsupport φ

private theorem pressureAllSpace_hasCompactSupport_spatialDeriv {φ : Vec3 → ℝ}
    (hφc : HasCompactSupport φ) (i : Fin 3) : HasCompactSupport (spatialDeriv φ i) :=
  HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    (pressureAllSpace_support_spatialDeriv_subset i)

private theorem pressureAllSpace_hasCompactSupport_mixedSecond {φ : Vec3 → ℝ}
    (hφc : HasCompactSupport φ) (i j : Fin 3) :
    HasCompactSupport (mixedSecond φ i j) :=
  HasCompactSupport.of_support_subset_isCompact hφc.isCompact
    (pressureAllSpace_support_mixedSecond_subset i j)

private theorem pressureAllSpace_spatial_restrict_isFiniteMeasure {K : Set Vec3}
    (hK : IsCompact (closure K)) : IsFiniteMeasure (volume.restrict K) := by
  apply isFiniteMeasure_restrict.mpr
  exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
    hK.measure_lt_top).ne

theorem pressure_laplace_cutoff_identity_ae_all_tests
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∀ᵐ s ∂volume.restrict I, 
      ∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) =
        (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)
          ) + (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)
          ) + (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j *
              (spatialDeriv η i x * spatialDeriv ψ j x)
          ) + (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j *
              (spatialDeriv η j x * spatialDeriv ψ i x)
          ) - (∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x))
          - 2 * (∫ x in Ω, (spatialGradDot η ψ x) * p (x, s))
          - (∫ x in Ω, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x))
          - (∫ x in Ω, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)) := by
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * ψ x) := hη.mul hψ
  have hprodc : HasCompactSupport (fun x => η x * ψ x) :=
    hηc.mul_right (f' := ψ)
  have hprodΩ : tsupport (fun x => η x * ψ x) ⊆ Ω :=
    (tsupport_mul_subset_left (f := η) (g := ψ)).trans hηΩ
  have hbase := pressure_slice_identity_ae h hprod hprodc hprodΩ
  have hdiv : ∀ᵐ s ∂volume.restrict I, ∀ j : Fin 3,
      ∫ x in Ω, ∑ i, u (x, s) i *
        spatialDeriv (spatialDeriv (fun y => η y * ψ y) j) i x = 0 := by
    rw [ae_all_iff]
    intro j
    have hd := divfree_slice_weak_of_suitable h
      (spatialDeriv (fun y => η y * ψ y) j)
      (contDiff_spatialDeriv_smooth hprod j)
      (hprodc.fderiv_apply (𝕜 := ℝ) (basisVec j))
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hprodΩ)
    filter_upwards [hd] with s hs
    simpa only [spatialDeriv] using hs
  let ψ₀ : Vec3 → ℝ := fun _ => 0
  have hψ₀c : HasCompactSupport ψ₀ := by
    simp [HasCompactSupport, ψ₀]
  have hψ₀Ω : tsupport ψ₀ ⊆ Ω := by
    simp [ψ₀]
  obtain ⟨Ω', hΩ'open, hηΩ', _hψ₀Ω', hΩ'compact, hΩ'Ω, hLp⟩ :=
    decomposition_slice_integrability h hηc hηΩ hψ₀c hψ₀Ω
  set_option linter.style.haveILetI false in
    letI : IsFiniteMeasure (volume.restrict Ω') :=
      pressureAllSpace_spatial_restrict_isFiniteMeasure hΩ'compact
  filter_upwards [hbase, hdiv, hLp] with s hbase_s hdiv_s hLp_s
  have huComp (i : Fin 3) : MemLp (fun x : Vec3 => u (x, s) i) 2
      (volume.restrict Ω') :=
    hLp_s.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have huInt (i : Fin 3) : Integrable (fun x : Vec3 => u (x, s) i)
      (volume.restrict Ω') := huComp i |>.integrable (by norm_num)
  have hfInt (i : Fin 3) : Integrable (fun x : Vec3 => f (x, s) i)
      (volume.restrict Ω') := by
    apply hLp_s.2.2.mono
      ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        hLp_s.2.2.aestronglyMeasurable)
    filter_upwards [] with x
    change ‖f (x, s) i‖ ≤ ‖f (x, s)‖
    rw [Pi.norm_def]
    simpa only [coe_nnnorm] using
      (NNReal.coe_le_coe.mpr
        (Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
          (f := fun b => ‖f (x, s) b‖₊) (Finset.mem_univ i)))
  have hscalar {g : Vec3 → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
      (hgΩ : tsupport g ⊆ Ω') :
      IntegrableOn (fun x => p (x, s) * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have hgm : AEStronglyMeasurable g (volume.restrict Ω') :=
      hg.measurable.aestronglyMeasurable
    have h' := hLp_s.2.1.mul_bdd hgm
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
    have h'On : IntegrableOn (fun x => p (x, s) * g x) Ω' volume := h'
    have hfull : Integrable (fun x => p (x, s) * g x) volume :=
      h'On.integrable_of_forall_notMem_eq_zero (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hgΩ hm)), mul_zero])
    exact hfull.integrableOn
  have huScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :
      IntegrableOn (fun x => u (x, s) i * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have hgm : AEStronglyMeasurable g (volume.restrict Ω') :=
      hg.measurable.aestronglyMeasurable
    have h' := (huInt i).mul_bdd hgm
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
    have h'On : IntegrableOn (fun x => u (x, s) i * g x) Ω' volume := h'
    have hfull : Integrable (fun x => u (x, s) i * g x) volume :=
      h'On.integrable_of_forall_notMem_eq_zero (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hgΩ hm)), mul_zero])
    exact hfull.integrableOn
  have huuScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :
      IntegrableOn (fun x => u (x, s) i * u (x, s) j * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have hgm : AEStronglyMeasurable g (volume.restrict Ω') :=
      hg.measurable.aestronglyMeasurable
    have h' := ((huComp i).integrable_mul (huComp j)).mul_bdd hgm
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
    have h'On : IntegrableOn
        (fun x => u (x, s) i * u (x, s) j * g x) Ω' volume := by
      change Integrable (fun x => u (x, s) i * u (x, s) j * g x)
        (volume.restrict Ω')
      exact h'
    have hfull : Integrable
        (fun x => u (x, s) i * u (x, s) j * g x) volume :=
      h'On.integrable_of_forall_notMem_eq_zero (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hgΩ hm)), mul_zero])
    exact hfull.integrableOn
  have hfScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :
      IntegrableOn (fun x => f (x, s) i * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have hgm : AEStronglyMeasurable g (volume.restrict Ω') :=
      hg.measurable.aestronglyMeasurable
    have h' := (hfInt i).mul_bdd hgm
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
    have h'On : IntegrableOn (fun x => f (x, s) i * g x) Ω' volume := h'
    have hfull : Integrable (fun x => f (x, s) i * g x) volume :=
      h'On.integrable_of_forall_notMem_eq_zero (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hgΩ hm)), mul_zero])
    exact hfull.integrableOn
  have hUScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :
      IntegrableOn (fun x => pressureUTensor u c (x, s) i j * g x) Ω volume := by
    have hraw := huuScalar (i := i) (j := j) hg hgc hgΩ
    have hlin := huScalar (i := i) hg hgc hgΩ
    have hsum : IntegrableOn
        (fun x => -(u (x, s) i * u (x, s) j * g x) +
          c s j * (u (x, s) i * g x)) Ω volume :=
      hraw.neg.add (hlin.const_mul (c s j))
    exact hsum.congr (Filter.Eventually.of_forall fun x => by
      simp only [pressureUTensor]
      ring)
  have hprodΩ' : tsupport (fun x => η x * ψ x) ⊆ Ω' :=
    (tsupport_mul_subset_left (f := η) (g := ψ)).trans hηΩ'
  have hηd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) :=
    contDiff_spatialDeriv_smooth hη i
  have hψd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i) :=
    contDiff_spatialDeriv_smooth hψ i
  have hηm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) :=
    contDiff_mixedSecond_smooth hη i j
  have hψm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have hηdc (i : Fin 3) : HasCompactSupport (spatialDeriv η i) :=
    pressureAllSpace_hasCompactSupport_spatialDeriv hηc i
  have hψdc (i : Fin 3) : HasCompactSupport (spatialDeriv ψ i) :=
    pressureAllSpace_hasCompactSupport_spatialDeriv hψc i
  have hp0 : IntegrableOn (fun x => p (x, s) * (η x * spatialLaplacian ψ x)) Ω volume :=
    hscalar (hη.mul (contDiff_spatialLaplacian_smooth hψ)).continuous
      (hηc.mul_right (f' := spatialLaplacian ψ))
      ((tsupport_mul_subset_left (f := η) (g := spatialLaplacian ψ)).trans hηΩ')
  have hp1 : IntegrableOn (fun x => p (x, s) * (ψ x * spatialLaplacian η x)) Ω volume :=
    hscalar (hψ.mul (contDiff_spatialLaplacian_smooth hη)).continuous
      (hψc.mul_right (f' := spatialLaplacian η))
      ((tsupport_mul_subset_right (f := ψ) (g := spatialLaplacian η)).trans
        ((pressureAllSpace_ts_support_spatialLaplacian_subset (φ := η)).trans hηΩ'))
  have hpgrad (j : Fin 3) : IntegrableOn
      (fun x => p (x, s) * (spatialDeriv η j x * spatialDeriv ψ j x)) Ω volume :=
    hscalar ((hηd j).mul (hψd j)).continuous
      ((hηdc j).mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ j)).trans
        ((pressureAllSpace_ts_support_spatialDeriv_subset j).trans hηΩ'))
  have hUU (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      mixedSecond (fun y => η y * ψ y) i j x) Ω volume :=
    huuScalar (contDiff_mixedSecond_smooth hprod i j).continuous
      (pressureAllSpace_hasCompactSupport_mixedSecond hprodc i j)
      ((pressureAllSpace_ts_support_mixedSecond_subset i j).trans hprodΩ')
  have hUU0 (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      (η x * mixedSecond ψ i j x)) Ω volume :=
    huuScalar ((hη.mul (hψm i j)).continuous)
      (hηc.mul_right (f' := mixedSecond ψ i j))
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')
  have hUU1 (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      (mixedSecond η i j x * ψ x)) Ω volume :=
    huuScalar ((hηm i j).mul hψ).continuous
      (hψc.mul_left (f := mixedSecond η i j))
      ((tsupport_mul_subset_left (f := mixedSecond η i j) (g := ψ)).trans
        ((pressureAllSpace_ts_support_mixedSecond_subset i j).trans hηΩ'))
  have hUU2 (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      (spatialDeriv η j x * spatialDeriv ψ i x)) Ω volume :=
    huuScalar ((hηd j).mul (hψd i)).continuous
      ((hηdc j).mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ i)).trans
        ((pressureAllSpace_ts_support_spatialDeriv_subset j).trans hηΩ'))
  have hUU3 (i j : Fin 3) : IntegrableOn (fun x => u (x, s) i * u (x, s) j *
      (spatialDeriv η i x * spatialDeriv ψ j x)) Ω volume :=
    huuScalar ((hηd i).mul (hψd j)).continuous
      ((hηdc i).mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := spatialDeriv η i)
        (g := spatialDeriv ψ j)).trans
        ((pressureAllSpace_ts_support_spatialDeriv_subset i).trans hηΩ'))
  have hU0 (i j : Fin 3) : IntegrableOn
      (fun x => pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) Ω volume :=
    hUScalar ((hη.mul (hψm i j)).continuous)
      (hηc.mul_right (f' := mixedSecond ψ i j))
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')
  have hU1 (i j : Fin 3) : IntegrableOn (fun x => pressureUTensor u c (x, s) i j *
      (mixedSecond η i j x * ψ x)) Ω volume :=
    hUScalar ((hηm i j).mul hψ).continuous
      (hψc.mul_left (f := mixedSecond η i j))
      ((tsupport_mul_subset_left (f := mixedSecond η i j) (g := ψ)).trans
        ((pressureAllSpace_ts_support_mixedSecond_subset i j).trans hηΩ'))
  have hU2 (i j : Fin 3) : IntegrableOn (fun x => pressureUTensor u c (x, s) i j *
      (spatialDeriv η i x * spatialDeriv ψ j x)) Ω volume :=
    hUScalar ((hηd i).mul (hψd j)).continuous
      ((hηdc i).mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := spatialDeriv η i)
        (g := spatialDeriv ψ j)).trans
        ((pressureAllSpace_ts_support_spatialDeriv_subset i).trans hηΩ'))
  have hU3 (i j : Fin 3) : IntegrableOn (fun x => pressureUTensor u c (x, s) i j *
      (spatialDeriv η j x * spatialDeriv ψ i x)) Ω volume :=
    hUScalar ((hηd j).mul (hψd i)).continuous
      ((hηdc j).mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ i)).trans
        ((pressureAllSpace_ts_support_spatialDeriv_subset j).trans hηΩ'))
  have hf0 (i : Fin 3) : IntegrableOn
      (fun x => f (x, s) i * (η x * spatialDeriv ψ i x)) Ω volume :=
    hfScalar ((hη.mul (hψd i)).continuous)
      (hηc.mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηΩ')
  have hf1 (i : Fin 3) : IntegrableOn
      (fun x => f (x, s) i * (ψ x * spatialDeriv η i x)) Ω volume :=
    hfScalar ((hψ.mul (hηd i)).continuous)
      (hψc.mul_right (f' := spatialDeriv η i))
      ((tsupport_mul_subset_right (f := ψ) (g := spatialDeriv η i)).trans
        ((pressureAllSpace_ts_support_spatialDeriv_subset i).trans hηΩ'))
  have hfinite {g : Fin 3 → Vec3 → ℝ} (hg : ∀ i, IntegrableOn (g i) Ω volume) :
      IntegrableOn (fun x => ∑ i, g i x) Ω volume := by
    have hs := integrable_finsetSum' (Finset.univ : Finset (Fin 3)) (fun i _ => hg i)
    have heq : (fun x => ∑ i, g i x) = ∑ i, (fun x => g i x) := by
      funext x; simp only [Finset.sum_apply]
    change Integrable (fun x => ∑ i, g i x) (volume.restrict Ω)
    rw [heq]
    exact hs
  have hpgsum : IntegrableOn
      (fun x => ∑ j, p (x, s) * (spatialDeriv η j x * spatialDeriv ψ j x)) Ω volume :=
    hfinite (fun j => hpgrad j)
  have hUUprodSum : IntegrableOn (fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x) Ω volume :=
    hfinite (fun i => hfinite (fun j => hUU i j))
  have hUU0Sum : IntegrableOn (fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j * (η x * mixedSecond ψ i j x)) Ω volume :=
    hfinite (fun i => hfinite (fun j => hUU0 i j))
  have hUU1Sum : IntegrableOn (fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j * (mixedSecond η i j x * ψ x)) Ω volume :=
    hfinite (fun i => hfinite (fun j => hUU1 i j))
  have hUU2Sum : IntegrableOn (fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j * (spatialDeriv η j x * spatialDeriv ψ i x)) Ω volume :=
    hfinite (fun i => hfinite (fun j => hUU2 i j))
  have hUU3Sum : IntegrableOn (fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j * (spatialDeriv η i x * spatialDeriv ψ j x)) Ω volume :=
    hfinite (fun i => hfinite (fun j => hUU3 i j))
  have hU0Sum : IntegrableOn (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) Ω volume :=
    hfinite (fun i => hfinite (fun j => hU0 i j))
  have hU1Sum : IntegrableOn (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) Ω volume :=
    hfinite (fun i => hfinite (fun j => hU1 i j))
  have hU2Sum : IntegrableOn (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (spatialDeriv η i x * spatialDeriv ψ j x)) Ω volume :=
    hfinite (fun i => hfinite (fun j => hU2 i j))
  have hU3Sum : IntegrableOn (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (spatialDeriv η j x * spatialDeriv ψ i x)) Ω volume :=
    hfinite (fun i => hfinite (fun j => hU3 i j))
  have hf0Sum : IntegrableOn
      (fun x => ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) Ω volume :=
    hfinite (fun i => hf0 i)
  have hf1Sum : IntegrableOn
      (fun x => ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)) Ω volume :=
    hfinite (fun i => hf1 i)
  have hgradSum : IntegrableOn
      (fun x => p (x, s) * spatialGradDot η ψ x) Ω volume := by
    apply hpgsum.congr
    filter_upwards [] with x
    simp only [spatialGradDot]
    rw [Finset.mul_sum]
  have hLapExpand :
      (∫ x in Ω, p (x, s) * spatialLaplacian (fun y => η y * ψ y) x) =
        (∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x)) +
          2 * (∫ x in Ω, spatialGradDot η ψ x * p (x, s)) +
          ∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x) := by
    have hpt : ∀ x, p (x, s) * spatialLaplacian (fun y => η y * ψ y) x =
        p (x, s) * (η x * spatialLaplacian ψ x) +
          2 * (p (x, s) * spatialGradDot η ψ x) +
          p (x, s) * (ψ x * spatialLaplacian η x) := by
      intro x
      rw [congrFun (spatialLaplacian_mul_smooth hη hψ) x]
      ring
    calc
      (∫ x in Ω, p (x, s) * spatialLaplacian (fun y => η y * ψ y) x) =
          ∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) +
            2 * (p (x, s) * spatialGradDot η ψ x) +
            p (x, s) * (ψ x * spatialLaplacian η x) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ((∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x)) +
          ∫ x in Ω, 2 * (p (x, s) * spatialGradDot η ψ x)) +
          ∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x) := by
        calc
          (∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) +
              2 * (p (x, s) * spatialGradDot η ψ x) +
              p (x, s) * (ψ x * spatialLaplacian η x)) =
              (∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) +
                2 * (p (x, s) * spatialGradDot η ψ x)) +
                ∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x) := by
            simpa only [Pi.add_apply] using
              (integral_add (hp0.add (hgradSum.const_mul 2)) hp1)
          _ = ((∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x)) +
              ∫ x in Ω, 2 * (p (x, s) * spatialGradDot η ψ x)) +
              ∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x) := by
            rw [integral_add hp0 (hgradSum.const_mul 2)]
        
      _ = (∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x)) +
          2 * (∫ x in Ω, spatialGradDot η ψ x * p (x, s)) +
          ∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x) := by
        have hcomm : (∫ x in Ω, p (x, s) * spatialGradDot η ψ x) =
            ∫ x in Ω, spatialGradDot η ψ x * p (x, s) := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        rw [integral_const_mul, hcomm]
  have hConvExpand :
      (∫ x in Ω, ∑ i, ∑ j,
        u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x) =
        (∫ x in Ω, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j * (η x * mixedSecond ψ i j x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j * (mixedSecond η i j x * ψ x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j *
              (spatialDeriv η j x * spatialDeriv ψ i x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j *
              (spatialDeriv η i x * spatialDeriv ψ j x)) := by
    let A : Vec3 → ℝ := fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j * (η x * mixedSecond ψ i j x)
    let B : Vec3 → ℝ := fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j * (mixedSecond η i j x * ψ x)
    let C : Vec3 → ℝ := fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j *
        (spatialDeriv η j x * spatialDeriv ψ i x)
    let D : Vec3 → ℝ := fun x => ∑ i, ∑ j,
      u (x, s) i * u (x, s) j *
        (spatialDeriv η i x * spatialDeriv ψ j x)
    have hA : IntegrableOn A Ω volume := by
      simpa [A] using hUU0Sum
    have hB : IntegrableOn B Ω volume := by
      simpa [B] using hUU1Sum
    have hC : IntegrableOn C Ω volume := by
      simpa [C] using hUU2Sum
    have hD : IntegrableOn D Ω volume := by
      simpa [D] using hUU3Sum
    have hpt : ∀ x, (∑ i, ∑ j, u (x, s) i * u (x, s) j *
        mixedSecond (fun y => η y * ψ y) i j x) =
        A x + B x + C x + D x := by
      intro x
      simp only [A, B, C, D]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [spatialSecondDeriv_mul_smooth hη hψ i j x]
      ring
    calc
      (∫ x in Ω, ∑ i, ∑ j,
        u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x) =
          ∫ x in Ω, A x + B x + C x + D x := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ x in Ω, (A x + B x) + (C x + D x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x in Ω, A x + B x) + (∫ x in Ω, C x + D x) := by
        simpa only [Pi.add_apply] using
          (integral_add (hA.add hB) (hC.add hD))
      _ = ((∫ x in Ω, A x) + (∫ x in Ω, B x)) +
          ((∫ x in Ω, C x) + (∫ x in Ω, D x)) := by
        rw [integral_add hA hB]
        rw [integral_add hC hD]
      _ = (∫ x in Ω, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j * (η x * mixedSecond ψ i j x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j * (mixedSecond η i j x * ψ x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j *
              (spatialDeriv η j x * spatialDeriv ψ i x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j *
              (spatialDeriv η i x * spatialDeriv ψ j x)) := by
        simp only [A, B, C, D]
        ring
  have hForceExpand :
      (∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv (fun y => η y * ψ y) i x) =
        (∫ x in Ω, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) +
          ∫ x in Ω, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x) := by
    have hpt : ∀ x, (∑ i, f (x, s) i * spatialDeriv (fun y => η y * ψ y) i x) =
        (∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) +
          (∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)) := by
      intro x
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [spatialDeriv_mul (hη.differentiable (by simp) x)
        (hψ.differentiable (by simp) x) i]
      ring
    calc
      (∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv (fun y => η y * ψ y) i x) =
          ∫ x in Ω, (∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) +
            (∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ x in Ω, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) +
          ∫ x in Ω, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x) := by
        rw [integral_add hf0Sum hf1Sum]
  have hUProd (i j : Fin 3) : IntegrableOn
      (fun x => pressureUTensor u c (x, s) i j *
        mixedSecond (fun y => η y * ψ y) i j x)
      Ω volume :=
    hUScalar (contDiff_mixedSecond_smooth hprod i j).continuous
      (pressureAllSpace_hasCompactSupport_mixedSecond hprodc i j)
      ((pressureAllSpace_ts_support_mixedSecond_subset i j).trans hprodΩ')
  have hUProdSum : IntegrableOn
      (fun x => ∑ i, ∑ j,
        pressureUTensor u c (x, s) i j * mixedSecond (fun y => η y * ψ y) i j x)
      Ω volume :=
    hfinite (fun i => hfinite (fun j => hUProd i j))
  have huProd (i j : Fin 3) : IntegrableOn
      (fun x => u (x, s) i * mixedSecond (fun y => η y * ψ y) i j x)
      Ω volume :=
    huScalar (contDiff_mixedSecond_smooth hprod i j).continuous
      (pressureAllSpace_hasCompactSupport_mixedSecond hprodc i j)
      ((pressureAllSpace_ts_support_mixedSecond_subset i j).trans hprodΩ')
  have hCorrInner (j : Fin 3) : IntegrableOn (fun x => c s j * ∑ i,
      u (x, s) i * mixedSecond (fun y => η y * ψ y) i j x) Ω volume :=
    (hfinite (fun i => huProd i j)).const_mul (c s j)
  have hdivProd (j : Fin 3) : ∫ x in Ω, ∑ i, u (x, s) i * mixedSecond (fun y => η y * ψ y) i j x = 0 := by
    simpa only [mixedSecond] using hdiv_s j
  have hCorrZero :
      ∫ x in Ω, ∑ j, c s j * ∑ i, u (x, s) i *
        mixedSecond (fun y => η y * ψ y) i j x = 0 := by
    calc
      (∫ x in Ω, ∑ j, c s j * ∑ i, u (x, s) i *
          mixedSecond (fun y => η y * ψ y) i j x) =
          ∑ j, ∫ x in Ω, c s j * ∑ i, u (x, s) i *
            mixedSecond (fun y => η y * ψ y) i j x := by
        simpa using integral_finsetSum (μ := volume.restrict Ω)
          (Finset.univ : Finset (Fin 3)) (fun j _ => hCorrInner j)
      _ = ∑ j, c s j * (∫ x in Ω, ∑ i, u (x, s) i *
          mixedSecond (fun y => η y * ψ y) i j x) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hdivProd j]
        simp
  have hBalance :
      (∫ x in Ω, ∑ i, ∑ j,
        pressureUTensor u c (x, s) i j * mixedSecond (fun y => η y * ψ y) i j x) +
          ∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x = 0 := by
    have hpoint : ∀ x, (∑ i, ∑ j,
        pressureUTensor u c (x, s) i j * mixedSecond (fun y => η y * ψ y) i j x) +
          (∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x) =
        ∑ j, c s j * ∑ i, u (x, s) i *
          mixedSecond (fun y => η y * ψ y) i j x := by
      intro x
      calc
        (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            mixedSecond (fun y => η y * ψ y) i j x) +
            (∑ i, ∑ j, u (x, s) i * u (x, s) j *
              mixedSecond (fun y => η y * ψ y) i j x) =
            ∑ i, ∑ j, ((pressureUTensor u c (x, s) i j *
              mixedSecond (fun y => η y * ψ y) i j x) +
              (u (x, s) i * u (x, s) j *
                mixedSecond (fun y => η y * ψ y) i j x)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.sum_add_distrib]
        _ = ∑ i, ∑ j, c s j * (u (x, s) i *
            mixedSecond (fun y => η y * ψ y) i j x) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          simp only [pressureUTensor]
          ring
        _ = ∑ j, ∑ i, c s j * (u (x, s) i *
            mixedSecond (fun y => η y * ψ y) i j x) := by
          rw [Finset.sum_comm]
        _ = ∑ j, c s j * ∑ i, u (x, s) i *
            mixedSecond (fun y => η y * ψ y) i j x := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.mul_sum]
    calc
      (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j * mixedSecond (fun y => η y * ψ y) i j x) +
          ∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x =
          ∫ x in Ω, (∑ i, ∑ j,
            pressureUTensor u c (x, s) i j * mixedSecond (fun y => η y * ψ y) i j x) +
            (∑ i, ∑ j,
              u (x, s) i * u (x, s) j * mixedSecond (fun y => η y * ψ y) i j x) := by
        simpa only [Pi.add_apply] using
          (integral_add hUProdSum hUUprodSum).symm
      _ = ∫ x in Ω, ∑ j, c s j * ∑ i, u (x, s) i *
          mixedSecond (fun y => η y * ψ y) i j x :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = 0 := hCorrZero
  have hUExpand :
      (∫ x in Ω, ∑ i, ∑ j,
        pressureUTensor u c (x, s) i j * mixedSecond (fun y => η y * ψ y) i j x) =
        (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j *
              (spatialDeriv η j x * spatialDeriv ψ i x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j *
              (spatialDeriv η i x * spatialDeriv ψ j x)) := by
    have hpt : ∀ x : Vec3, (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        mixedSecond (fun y => η y * ψ y) i j x) =
        (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (η x * mixedSecond ψ i j x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (mixedSecond η i j x * ψ x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η i x * spatialDeriv ψ j x)) := by
      intro x
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [spatialSecondDeriv_mul_smooth hη hψ i j x]
      ring
    calc
      (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          mixedSecond (fun y => η y * ψ y) i j x) =
          ∫ x in Ω, (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (η x * mixedSecond ψ i j x)) +
            (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
              (mixedSecond η i j x * ψ x)) +
            (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
              (spatialDeriv η j x * spatialDeriv ψ i x)) +
            (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
              (spatialDeriv η i x * spatialDeriv ψ j x)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ x in Ω, ((∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (η x * mixedSecond ψ i j x)) +
            (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
              (mixedSecond η i j x * ψ x))) +
            ((∑ i, ∑ j, pressureUTensor u c (x, s) i j *
              (spatialDeriv η j x * spatialDeriv ψ i x)) +
            (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
              (spatialDeriv η i x * spatialDeriv ψ j x))) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x in Ω, (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (η x * mixedSecond ψ i j x)) +
          (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (mixedSecond η i j x * ψ x))) +
          (∫ x in Ω, (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) +
            (∑ i, ∑ j, pressureUTensor u c (x, s) i j *
              (spatialDeriv η i x * spatialDeriv ψ j x))) := by
        simpa only [Pi.add_apply] using
          (integral_add (hU0Sum.add hU1Sum) (hU3Sum.add hU2Sum))
      _ = ((∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (η x * mixedSecond ψ i j x)) +
          (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (mixedSecond η i j x * ψ x))) +
          ((∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) +
          (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η i x * spatialDeriv ψ j x))) := by
        rw [integral_add hU0Sum hU1Sum]
        rw [integral_add hU3Sum hU2Sum]
      _ = (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
          (η x * mixedSecond ψ i j x)) +
          (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (mixedSecond η i j x * ψ x)) +
          (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) +
          (∫ x in Ω, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
            (spatialDeriv η i x * spatialDeriv ψ j x)) := by
        ring
  linarith only [hbase_s, hLapExpand, hConvExpand, hForceExpand, hBalance, hUExpand]

end CKN

end
