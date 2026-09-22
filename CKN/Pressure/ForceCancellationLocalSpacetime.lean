-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.ForceCancellationUnconditional
import CKN.Setting.DivergenceFreeSlice

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN

private theorem mollifiedBallCutoff_smoothCompactTest_local {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) : SmoothCompactTest (mollifiedBallCutoff x₀ hρ) := by
  refine ⟨fun n => ?_, mollifiedBallCutoff_hasCompactSupport x₀ hρ⟩
  exact (mollifiedBallCutoff_smooth x₀ hρ).of_le (by simp)

private lemma smoothCompactTest_contDiff_local
    {ψ : Vec3 → ℝ} (hψ : SmoothCompactTest ψ) :
    ContDiff ℝ (⊤ : ℕ∞) ψ :=
  (contDiff_infty).2 hψ.1

private lemma smoothCompactTest_deriv_integrable_local
    {g ψ : Vec3 → ℝ} (hg : Integrable g volume)
    (hψ : SmoothCompactTest ψ) (i : Fin 3) :
    Integrable (fun x => g x * spatialDeriv ψ i x) volume := by
  have hψtop := smoothCompactTest_contDiff_local hψ
  have hψd := contDiff_spatialDeriv_smooth hψtop i
  have hψdc : HasCompactSupport (spatialDeriv ψ i) :=
    hψ.2.fderiv_apply (𝕜 := ℝ) (basisVec i)
  obtain ⟨C, hC⟩ := hψdc.exists_bound_of_continuous hψd.continuous
  exact hg.mul_bdd hψd.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hC x)

private lemma smoothCompactTest_mul_local
    {η ψ : Vec3 → ℝ} (hη : SmoothCompactTest η) (hψ : SmoothCompactTest ψ) :
    SmoothCompactTest (fun x => η x * ψ x) := by
  have hηtop := smoothCompactTest_contDiff_local hη
  have hψtop := smoothCompactTest_contDiff_local hψ
  refine ⟨fun n => ?_, hη.2.mul_right (f' := ψ)⟩
  exact (hηtop.mul hψtop).of_le (by simp)

private theorem force_source_integrable_local
    {f : ParabolicPoint → Vec3} {s : ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) {V : Set Vec3}
    (hfs : Integrable (fun x : Vec3 => f (x, s)) (volume.restrict V))
    (hηV : tsupport (mollifiedBallCutoff x₀ hρ) ⊆ V) :
    (∀ j, Integrable
        (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) volume ∧
      HasCompactSupport
        (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j)) ∧
    (∀ j, Integrable
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) volume ∧
      HasCompactSupport
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)) := by
  have hηmeasV : AEStronglyMeasurable (mollifiedBallCutoff x₀ hρ)
      (volume.restrict V) :=
    ((mollifiedBallCutoff_smooth x₀ hρ).continuous.aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hsourceInt (j : Fin 3) :
      Integrable
        (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j) volume := by
    have hfc : AEStronglyMeasurable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) :=
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        hfs.aestronglyMeasurable
    have hfcint : Integrable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).integrable_comp hfs
    have hmul := hfcint.mul_bdd hηmeasV
      (Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using
          (abs_le.mpr ⟨by linarith only
            [mollifiedBallCutoff_nonneg x₀ hρ y],
            mollifiedBallCutoff_le_one x₀ hρ y⟩)))
    exact decomposition_full_of_on_sws
      (show IntegrableOn
          (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) V volume by
        simpa only [IntegrableOn, mul_comm] using hmul)
      ((tsupport_mul_subset_left (f := mollifiedBallCutoff x₀ hρ)
        (g := fun y => f (y, s) j)).trans hηV)
  have hsourceSupp (j : Fin 3) : HasCompactSupport
      (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) := by
    exact (mollifiedBallCutoff_hasCompactSupport x₀ hρ).mul_right
  have hderivC (j : Fin 3) : HasCompactSupport
      (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) :=
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ).fderiv_apply
      (𝕜 := ℝ) (basisVec j)
  have hderivV (j : Fin 3) :
      tsupport (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) ⊆ V := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηV
  have hderivInt (j : Fin 3) :
      Integrable
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) volume := by
    have hηd := contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth x₀ hρ) j
    have hηdV : AEStronglyMeasurable
        (spatialDeriv (mollifiedBallCutoff x₀ hρ) j)
        (volume.restrict V) := by
      have hηdmeas : AEStronglyMeasurable
          (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) volume :=
        hηd.continuous.aestronglyMeasurable
      exact hηdmeas.mono_measure Measure.restrict_le_self
    have hfc : Integrable (fun y : Vec3 => f (y, s) j)
        (volume.restrict V) := by
      simpa only [ContinuousLinearMap.proj_apply] using
        (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).integrable_comp hfs
    have hmul := hfc.mul_bdd hηdV
      (Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using
          pressure_cutoff_spatialDeriv_bound x₀ hρ y j))
    exact decomposition_full_of_on_sws
      (show IntegrableOn
          (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) V volume by
        simpa only [IntegrableOn] using
          (hmul.congr (Eventually.of_forall (fun y => by ring))))
      ((tsupport_mul_subset_left
        (f := spatialDeriv (mollifiedBallCutoff x₀ hρ) j)
        (g := fun y => f (y, s) j)).trans (hderivV j))
  have hderivSupp (j : Fin 3) : HasCompactSupport
      (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) := by
    exact (hderivC j).mul_right
  constructor
  · intro j
    exact ⟨hsourceInt j, hsourceSupp j⟩
  · intro j
    exact ⟨hderivInt j, hderivSupp j⟩

private theorem pressure_force_pairing_zero_of_localized_divergence
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : SmoothCompactTest η)
    (hdiv : ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
      ∫ x, ∑ i : Fin 3, f (x, s) i * spatialDeriv (fun y => η y * ψ y) i x = 0)
    (hInt7 : ∀ j, Integrable
      (fun y => η y * f (y, s) j) volume)
    (hSupp7 : ∀ j, HasCompactSupport
      (fun y => η y * f (y, s) j))
    (hInt8 : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp8 : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j)) :
    ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
      ∫ x, (pressureP7 η f s x + pressureP8 η f s x) * spatialLaplacian ψ x = 0 := by
  intro ψ hψ
  have hηtop := smoothCompactTest_contDiff_local hη
  have hψtop := smoothCompactTest_contDiff_local hψ
  have hηψ := smoothCompactTest_mul_local hη hψ
  have hdivηψ := hdiv ψ hψ
  have hterm7 (j : Fin 3) : Integrable
      (fun x => η x * f (x, s) j * spatialDeriv ψ j x) volume := by
    exact smoothCompactTest_deriv_integrable_local (hInt7 j) hψ j
  have hterm8 (j : Fin 3) : Integrable
      (fun x => spatialDeriv η j x * f (x, s) j * ψ x) volume := by
    have hψc : HasCompactSupport ψ := hψ.2
    have hψbound := hψc.exists_bound_of_continuous hψtop.continuous
    obtain ⟨C, hC⟩ := hψbound
    exact (hInt8 j).mul_bdd hψtop.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x)
  have hsum7 : Integrable
      (fun x => ∑ j : Fin 3, η x * f (x, s) j * spatialDeriv ψ j x) volume := by
    exact integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _hj => hterm7 j)
  have hsum8 : Integrable
      (fun x => ∑ j : Fin 3, spatialDeriv η j x * f (x, s) j * ψ x) volume := by
    exact integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _hj => hterm8 j)
  have hdiv' : ∫ x, (∑ j : Fin 3,
      η x * f (x, s) j * spatialDeriv ψ j x) +
        (∑ j : Fin 3, spatialDeriv η j x * f (x, s) j * ψ x) = 0 := by
    calc
      _ = ∫ x, ∑ i : Fin 3, f (x, s) i *
          spatialDeriv (fun y => η y * ψ y) i x := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [show (∑ i : Fin 3, f (x, s) i *
            spatialDeriv (fun y => η y * ψ y) i x) =
          ∑ i : Fin 3, (η x * f (x, s) i * spatialDeriv ψ i x +
            spatialDeriv η i x * f (x, s) i * ψ x) by
          apply Finset.sum_congr rfl
          intro i hi
          rw [spatialDeriv_mul
            (hηtop.differentiable (by simp) x)
            (hψtop.differentiable (by simp) x) i]
          ring]
        rw [← Finset.sum_add_distrib]
      _ = 0 := hdivηψ
  have hdiv'' : (∫ x, ∑ j : Fin 3,
      η x * f (x, s) j * spatialDeriv ψ j x) +
      (∫ x, ∑ j : Fin 3,
        spatialDeriv η j x * f (x, s) j * ψ x) = 0 := by
    calc
      _ = ∫ x, (∑ j : Fin 3,
          η x * f (x, s) j * spatialDeriv ψ j x) +
          (∑ j : Fin 3,
            spatialDeriv η j x * f (x, s) j * ψ x) :=
        (integral_add hsum7 hsum8).symm
      _ = 0 := hdiv'
  have hdivsum : (∑ j : Fin 3, ∫ x,
      η x * f (x, s) j * spatialDeriv ψ j x) +
      (∑ j : Fin 3, ∫ x,
        spatialDeriv η j x * f (x, s) j * ψ x) = 0 := by
    rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))] at hdiv''
    · rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))] at hdiv''
      · exact hdiv''
      · intro j hj
        exact hterm8 j
    · intro j hj
      exact hterm7 j
  have hP7 := pressureP7_distributional_pairing hInt7 hSupp7 hψtop hψ.2
  have hP8 := pressureP8_distributional_pairing hInt8 hSupp8 hψtop hψ.2
  calc
    ∫ x, (pressureP7 η f s x + pressureP8 η f s x) *
        spatialLaplacian ψ x =
      (∫ x, pressureP7 η f s x * spatialLaplacian ψ x) +
        ∫ x, pressureP8 η f s x * spatialLaplacian ψ x := by
      rw [show (fun x => (pressureP7 η f s x + pressureP8 η f s x) *
          spatialLaplacian ψ x) =
        (fun x => pressureP7 η f s x * spatialLaplacian ψ x +
          pressureP8 η f s x * spatialLaplacian ψ x) by
          funext x
          ring]
      have hP7Int : Integrable (fun x => pressureP7 η f s x *
          spatialLaplacian ψ x) volume := by
        have hlocal := pressureP7_locallyIntegrable hInt7 hSupp7
        simpa only [smul_eq_mul, mul_comm] using
          hlocal.integrable_smul_right_of_hasCompactSupport
            (contDiff_spatialLaplacian_smooth hψtop).continuous
            (decomposition_laplacian_hasCompactSupport_sws hψ.2)
      have hP8Int : Integrable (fun x => pressureP8 η f s x *
          spatialLaplacian ψ x) volume := by
        have hlocal := pressureP8_locallyIntegrable hInt8 hSupp8
        simpa only [smul_eq_mul, mul_comm] using
          hlocal.integrable_smul_right_of_hasCompactSupport
            (contDiff_spatialLaplacian_smooth hψtop).continuous
            (decomposition_laplacian_hasCompactSupport_sws hψ.2)
      exact integral_add hP7Int hP8Int
    _ = 0 := by
      rw [hP7, hP8]
      linarith only [hdivsum]

private theorem pressure_force_eq_zero_of_localized_divergence
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : SmoothCompactTest η)
    (hdiv : ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
      ∫ x, ∑ i : Fin 3, f (x, s) i * spatialDeriv (fun y => η y * ψ y) i x = 0)
    (hInt7 : ∀ j, Integrable
      (fun y => η y * f (y, s) j) volume)
    (hSupp7 : ∀ j, HasCompactSupport
      (fun y => η y * f (y, s) j))
    (hInt8 : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp8 : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j))
    (hmem : ∀ R : ℝ, 0 < R →
      MemLp (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2)) (volume.restrict (euclideanBall (0 : Vec3) R)))
    (hgrowth : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      lpNorm (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2)) (volume.restrict (euclideanBall (0 : Vec3) R)) ≤
          C * (1 + R)) :
    pressureP7 η f s + pressureP8 η f s =ᵐ[volume] 0 := by
  have hweak : CKN.Foundation.Heat.WeaklyHarmonicOn Set.univ
      (pressureP7 η f s + pressureP8 η f s) := by
    intro ψ hψ hψc hψU
    have htest : SmoothCompactTest ψ := by
      refine ⟨fun n => ?_, hψc⟩
      exact hψ.of_le (by simp)
    have hzero := pressure_force_pairing_zero_of_localized_divergence
      hη hdiv hInt7 hSupp7 hInt8 hSupp8 ψ htest
    simpa only [Measure.restrict_univ, Set.mem_univ, true_and, Pi.add_apply] using hzero
  obtain ⟨C, hC, hgrowth'⟩ := hgrowth
  exact CKN.Foundation.Heat.weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth
    hC hmem hweak hgrowth'

/-- Local spacetime solenoidality on the domain cancels the force potentials on
almost every time slice of an admissible pressure cylinder. -/
theorem pressure_force_eq_zero_of_sws_localSpacetimeDivergenceFree
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
        (tsupport ψ) volume ∧
      ∫ w in spaceTimeSet Ω I, ∑ i : Fin 3, f w i * spatialPartial ψ i w = 0) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s =ᵐ[volume] 0 := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  have hηc : HasCompactSupport η := mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηtest : SmoothCompactTest η := by
    exact mollifiedBallCutoff_smoothCompactTest_local (x₀ := z.1) hρ
  have hηsupport : tsupport η ⊆ vec3Ball z.1 ρ :=
    pressure_cutoff_support_subset_ball z.1 hρ
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport η ⊆ Ω := by
    exact hηsupport.trans (fun x hx => hbox.2.2.1 (subset_closure (hball hx)))
  obtain ⟨V, hVopen, hηV, _hVmeas, _hVcompact, hVΩ, hslice⟩ :=
    decomposition_slice_integrability hsol hηc hηΩ hηc hηΩ
  have hTsubI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hsliceT : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      Integrable (fun x : Vec3 => f (x, s)) (volume.restrict V) := by
    exact (ae_restrict_of_ae_restrict_of_subset hTsubI hslice).mono
      (fun s hs => hs.2.2)
  have hloc : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ i : Fin 3, LocallyIntegrableOn (fun x : Vec3 => f (x, s) i) V volume := by
    filter_upwards [hsliceT] with s hs i
    exact IntegrableOn.locallyIntegrableOn
      ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integrable_comp hs)
  have hsliceΩ := divfree_slice_weak (u := f) hdiv hsol.2.1
  have hsliceV : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        ∫ x in V, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
    intro ψ hψ hψc hψV
    have hψΩ := hψV.trans (subset_closure.trans hVΩ)
    have hΩzero := ae_restrict_of_ae_restrict_of_subset hTsubI
      (hsliceΩ ψ hψ hψc hψΩ)
    filter_upwards [hΩzero] with s hs
    have hzero : ∀ x ∉ V,
        ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
      intro x hx
      apply Finset.sum_eq_zero
      intro i hi
      have hderiv : (fderiv ℝ ψ x) (basisVec i) = 0 := by
        rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun hm => hx (hψV hm))]
        rfl
      simp [hderiv]
    have hΩV : V ⊆ Ω := subset_closure.trans hVΩ
    have hΩset : ∫ x in Ω, ∑ i : Fin 3, f (x, s) i *
        (fderiv ℝ ψ x) (basisVec i) = ∫ x,
          ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
        hzero x (fun hv => hx (hΩV hv)))
    have hVset : ∫ x in V, ∑ i : Fin 3, f (x, s) i *
        (fderiv ℝ ψ x) (basisVec i) = ∫ x,
          ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    rw [hΩset] at hs
    rw [hVset]
    exact hs
  have hVdiv := ae_slice_divergence_zero_of_forall_test hVopen hloc hsliceV
  have hdivη : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
        ∫ x, ∑ i : Fin 3, f (x, s) i *
          spatialDeriv (fun y => η y * ψ y) i x = 0 := by
    filter_upwards [hVdiv] with s hs ψ hψ
    have hηtop := smoothCompactTest_contDiff_local hηtest
    have hψtop := smoothCompactTest_contDiff_local hψ
    have hφη : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => η y * ψ y) := hηtop.mul hψtop
    have hφηc : HasCompactSupport (fun y : Vec3 => η y * ψ y) := hηc.mul_right
    have hφηV : tsupport (fun y : Vec3 => η y * ψ y) ⊆ V :=
      (tsupport_mul_subset_left (f := η) (g := ψ)).trans hηV
    have hVzero := hs (fun y => η y * ψ y) hφη hφηc hφηV
    have hzero : ∀ x ∉ V,
        ∑ i : Fin 3, f (x, s) i *
          spatialDeriv (fun y : Vec3 => η y * ψ y) i x = 0 := by
      have hderivSubset (i : Fin 3) :
          tsupport (spatialDeriv (fun y : Vec3 => η y * ψ y) i) ⊆ V :=
        (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hφηV
      intro x hx
      apply Finset.sum_eq_zero
      intro i hi
      have hderiv : x ∉ tsupport
          (spatialDeriv (fun y : Vec3 => η y * ψ y) i) := by
        intro hm
        exact hx (hderivSubset i hm)
      rw [image_eq_zero_of_notMem_tsupport hderiv]
      simp
    calc
      _ = ∫ x in V, ∑ i : Fin 3, f (x, s) i *
          spatialDeriv (fun y : Vec3 => η y * ψ y) i x := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
      _ = 0 := hVzero
  have hproducer := pressure_force_memLp_and_lpNorm_growth_ae_of_sws
    hsol hρ hsub
  let C : ℝ → ℝ := fun s =>
    CKN.Foundation.Euclidean.pressureP7GrowthConstant η f s
        (vec3EuclideanNorm z.1 + ρ) +
      CKN.Foundation.Euclidean.pressureP8GrowthConstant η f s
        (vec3EuclideanNorm z.1 + ρ)
  have hmem : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ R : ℝ, 0 < R →
        MemLp (pressureP7 η f s + pressureP8 η f s)
          (ENNReal.ofReal (3 / 2)) (volume.restrict (euclideanBall (0 : Vec3) R)) :=
    hproducer.mono fun s hs => hs.1
  have hgrowth : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      0 ≤ C s ∧ ∀ R : ℝ, 0 < R →
        lpNorm (pressureP7 η f s + pressureP8 η f s)
          (ENNReal.ofReal (3 / 2)) (volume.restrict (euclideanBall (0 : Vec3) R)) ≤
            C s * (1 + R) := by
    filter_upwards [hproducer] with s hs
    exact ⟨by simpa [C] using hs.2.1, by simpa [C] using hs.2.2⟩
  filter_upwards [hdivη, hmem, hgrowth, hsliceT] with s hsdiv hsmem hsgrowth hs
  have hsource := force_source_integrable_local hρ hs hηV
  exact pressure_force_eq_zero_of_localized_divergence
    hηtest hsdiv
    (fun j => (hsource.1 j).1) (fun j => (hsource.1 j).2)
    (fun j => (hsource.2 j).1) (fun j => (hsource.2 j).2)
    hsmem ⟨C s, hsgrowth.1, hsgrowth.2⟩

end CKN
