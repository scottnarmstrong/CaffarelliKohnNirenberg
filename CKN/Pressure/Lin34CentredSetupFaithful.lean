-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.Lin34SliceCore
import CKN.Pressure.DeltaPCentred
import CKN.Pressure.ForceCancellationLocalSpacetime
import CKN.Pressure.HarmonicRemainderForceTerms
import CKN.Pressure.SliceIntegrability
import CKN.Pressure.PkBoundsCylinder

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
open CKN.Foundation.Euclidean

set_option autoImplicit false
noncomputable section

namespace CKN

private theorem lin34Setup_smoothCompactTest {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) : SmoothCompactTest (mollifiedBallCutoff x₀ hρ) := by
  refine ⟨fun n => ?_, mollifiedBallCutoff_hasCompactSupport x₀ hρ⟩
  exact (mollifiedBallCutoff_smooth x₀ hρ).of_le (by simp)

private theorem lin34Setup_smoothCompactTest_contDiff {ψ : Vec3 → ℝ}
    (hψ : SmoothCompactTest ψ) : ContDiff ℝ (⊤ : ℕ∞) ψ :=
  (contDiff_infty).2 hψ.1

private theorem lin34Setup_smoothCompactTest_mul {η ψ : Vec3 → ℝ}
    (hη : SmoothCompactTest η) (hψ : SmoothCompactTest ψ) :
    SmoothCompactTest (fun x => η x * ψ x) := by
  have hηtop := lin34Setup_smoothCompactTest_contDiff hη
  have hψtop := lin34Setup_smoothCompactTest_contDiff hψ
  refine ⟨fun n => ?_, hη.2.mul_right (f' := ψ)⟩
  exact (hηtop.mul hψtop).of_le (by simp)

private theorem lin34Setup_deriv_integrable {g ψ : Vec3 → ℝ}
    (hg : Integrable g volume) (hψ : SmoothCompactTest ψ) (i : Fin 3) :
    Integrable (fun x => g x * spatialDeriv ψ i x) volume := by
  have hψtop := lin34Setup_smoothCompactTest_contDiff hψ
  have hψd := contDiff_spatialDeriv_smooth hψtop i
  have hψdc : HasCompactSupport (spatialDeriv ψ i) :=
    hψ.2.fderiv_apply (𝕜 := ℝ) (basisVec i)
  obtain ⟨C, hC⟩ := hψdc.exists_bound_of_continuous hψd.continuous
  exact hg.mul_bdd hψd.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hC x)

private theorem lin34Setup_force_pairing_zero
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : SmoothCompactTest η)
    (hdiv : ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
      ∫ x, ∑ i : Fin 3, f (x, s) i *
        spatialDeriv (fun y => η y * ψ y) i x = 0)
    (hInt7 : ∀ j, Integrable (fun y => η y * f (y, s) j) volume)
    (hSupp7 : ∀ j, HasCompactSupport (fun y => η y * f (y, s) j))
    (hInt8 : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp8 : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j)) :
    ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
      ∫ x, (pressureP7 η f s x + pressureP8 η f s x) *
        spatialLaplacian ψ x = 0 := by
  intro ψ hψ
  have hηtop := lin34Setup_smoothCompactTest_contDiff hη
  have hψtop := lin34Setup_smoothCompactTest_contDiff hψ
  have hηψ := lin34Setup_smoothCompactTest_mul hη hψ
  have hdivηψ := hdiv ψ hψ
  have hterm7 (j : Fin 3) : Integrable
      (fun x => η x * f (x, s) j * spatialDeriv ψ j x) volume :=
    lin34Setup_deriv_integrable (hInt7 j) hψ j
  have hterm8 (j : Fin 3) : Integrable
      (fun x => spatialDeriv η j x * f (x, s) j * ψ x) volume := by
    have hψbound := hψ.2.exists_bound_of_continuous hψtop.continuous
    obtain ⟨C, hC⟩ := hψbound
    exact (hInt8 j).mul_bdd hψtop.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x)
  have hsum7 : Integrable
      (fun x => ∑ j : Fin 3, η x * f (x, s) j * spatialDeriv ψ j x) volume :=
    integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _hj => hterm7 j)
  have hsum8 : Integrable
      (fun x => ∑ j : Fin 3, spatialDeriv η j x * f (x, s) j * ψ x) volume :=
    integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
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

private theorem lin34Setup_force_eq_zero_of_localized_divergence
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : SmoothCompactTest η)
    (hdiv : ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
      ∫ x, ∑ i : Fin 3, f (x, s) i *
        spatialDeriv (fun y => η y * ψ y) i x = 0)
    (hInt7 : ∀ j, Integrable (fun y => η y * f (y, s) j) volume)
    (hSupp7 : ∀ j, HasCompactSupport (fun y => η y * f (y, s) j))
    (hInt8 : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp8 : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j))
    (hmem : ∀ R : ℝ, 0 < R →
      MemLp (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) R)))
    (hgrowth : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      lpNorm (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R)) :
    pressureP7 η f s + pressureP8 η f s =ᵐ[volume] 0 := by
  have hweak : WeaklyHarmonicOn Set.univ (pressureP7 η f s + pressureP8 η f s) := by
    intro ψ hψ hψc hψU
    have htest : SmoothCompactTest ψ := by
      refine ⟨fun n => ?_, hψc⟩
      exact hψ.of_le (by simp)
    have hzero := lin34Setup_force_pairing_zero hη hdiv hInt7 hSupp7 hInt8 hSupp8
      ψ htest
    simpa only [Measure.restrict_univ, Set.mem_univ, true_and, Pi.add_apply] using hzero
  obtain ⟨C, hC, hgrowth'⟩ := hgrowth
  exact weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth hC hmem hweak hgrowth'

private theorem lin34Setup_force_integrable
    {f : ParabolicPoint → Vec3} {s : ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) {V : Set Vec3}
    (hfs : Integrable (fun x : Vec3 => f (x, s)) (volume.restrict V))
    (hηV : tsupport (mollifiedBallCutoff x₀ hρ) ⊆ V) :
    (∀ j, Integrable
        (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) volume ∧
      HasCompactSupport
        (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j)) ∧
    (∀ j, Integrable
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
          volume ∧
      HasCompactSupport
        (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)) := by
  have hηmeasV : AEStronglyMeasurable (mollifiedBallCutoff x₀ hρ)
      (volume.restrict V) :=
    ((mollifiedBallCutoff_smooth x₀ hρ).continuous.aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hsourceInt (j : Fin 3) : Integrable
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
      (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) :=
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ).mul_right
  have hderivC (j : Fin 3) : HasCompactSupport
      (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) :=
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ).fderiv_apply
      (𝕜 := ℝ) (basisVec j)
  have hderivV (j : Fin 3) :
      tsupport (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) ⊆ V :=
    (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηV
  have hderivInt (j : Fin 3) : Integrable
      (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
        volume := by
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
          (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y *
            f (y, s) j) V volume by
        simpa only [IntegrableOn] using
          (hmul.congr (Eventually.of_forall (fun y => by ring))))
      ((tsupport_mul_subset_left
        (f := spatialDeriv (mollifiedBallCutoff x₀ hρ) j)
        (g := fun y => f (y, s) j)).trans (hderivV j))
  have hderivSupp (j : Fin 3) : HasCompactSupport
      (fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) :=
    (hderivC j).mul_right
  exact ⟨fun j => ⟨hsourceInt j, hsourceSupp j⟩,
    fun j => ⟨hderivInt j, hderivSupp j⟩⟩

private theorem lin34Setup_force_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ω →
        ∫ x in Ω, ∑ j : Fin 3, f (x, s) j * spatialDeriv ψ j x = 0) →
      ∀ᵐ x ∂volume, lin34ForcePart f z.1 ρ hρ s x = 0 := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  have hηc : HasCompactSupport η := mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηtest : SmoothCompactTest η := lin34Setup_smoothCompactTest hρ
  have hηsupport : tsupport η ⊆ vec3Ball z.1 ρ :=
    pressure_cutoff_support_subset_ball z.1 hρ
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport η ⊆ Ω := by
    exact hηsupport.trans (fun x hx => hbox.2.2.1 (subset_closure (hball hx)))
  obtain ⟨V, _hVopen, hηV, _hVmeas, _hVcompact, hVΩ, hslice⟩ :=
    decomposition_slice_integrability hsol hηc hηΩ hηc hηΩ
  have hTsubI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hsliceT : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      Integrable (fun x : Vec3 => f (x, s)) (volume.restrict V) := by
    exact (ae_restrict_of_ae_restrict_of_subset hTsubI hslice).mono
      (fun s hs => hs.2.2)
  have hproducer := pressure_force_memLp_and_lpNorm_growth_ae_of_sws hsol hρ hsub
  filter_upwards [hproducer, hsliceT] with s hpforce hfs
  intro hdivlocal
  have hsource := lin34Setup_force_integrable hρ hfs hηV
  have hdivη : ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
      ∫ x, ∑ i : Fin 3, f (x, s) i *
        spatialDeriv (fun y => η y * ψ y) i x = 0 := by
    intro ψ hψ
    have htest := lin34Setup_smoothCompactTest_mul hηtest hψ
    have htestΩ : tsupport (fun y => η y * ψ y) ⊆ Ω :=
      (tsupport_mul_subset_left (f := η) (g := ψ)).trans hηΩ
    have hΩzero := hdivlocal (fun y => η y * ψ y)
      (lin34Setup_smoothCompactTest_contDiff htest) htest.2 htestΩ
    have hzero : ∀ x ∉ Ω,
        ∑ i : Fin 3, f (x, s) i *
          spatialDeriv (fun y => η y * ψ y) i x = 0 := by
      intro x hx
      apply Finset.sum_eq_zero
      intro i hi
      have hderiv : x ∉ tsupport
          (spatialDeriv (fun y => η y * ψ y) i) := by
        intro hm
        exact hx ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans htestΩ hm)
      rw [image_eq_zero_of_notMem_tsupport hderiv]
      simp
    have hset : ∫ x in Ω, ∑ i : Fin 3, f (x, s) i *
        spatialDeriv (fun y => η y * ψ y) i x =
      ∫ x, ∑ i : Fin 3, f (x, s) i *
        spatialDeriv (fun y => η y * ψ y) i x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    rw [hset] at hΩzero
    exact hΩzero
  have hmem : ∀ R : ℝ, 0 < R →
      MemLp (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) R)) := by
    simpa only [η] using hpforce.1
  have hgrowth : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      lpNorm (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R) := by
    refine ⟨pressureP7GrowthConstant η f s (vec3EuclideanNorm z.1 + ρ) +
      pressureP8GrowthConstant η f s (vec3EuclideanNorm z.1 + ρ), ?_, ?_⟩
    · simpa only [η] using hpforce.2.1
    · intro R hR
      simpa only [η] using hpforce.2.2 R hR
  have hzero := lin34Setup_force_eq_zero_of_localized_divergence hηtest hdivη
    (fun j => (hsource.1 j).1) (fun j => (hsource.1 j).2)
    (fun j => (hsource.2 j).1) (fun j => (hsource.2 j).2) hmem hgrowth
  filter_upwards [hzero] with x hx
  simpa only [lin34ForcePart, η, Pi.add_apply, Pi.zero_apply] using hx

private theorem lin34Setup_ball_eq_euclideanBall {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private theorem lin34Setup_tensorNorm_identity
    (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ s : ℝ)
    (x : Vec3) :
    Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      pressureUHat u (fun t j => ⨍ y in vec3Ball x₀ ρ, u (y, t) j)
        (x, s) i j ^ 2) =
      vec3EuclideanNorm (u (x, s) -
        (fun j => ⨍ y in vec3Ball x₀ ρ, u (y, s) j)) ^ (2 : ℕ) := by
  have hid := lin34_pressureUTensorNorm_centred u x₀ ρ s x
  have hmean : meanFreeVec u x₀ ρ s x =
      u (x, s) - (fun j => ⨍ y in vec3Ball x₀ ρ, u (y, s) j) := by
    funext j
    rfl
  rw [← hmean]
  simpa [pressureUTensorNorm, pressureUHat, pressureUTensor,
    lin34CentredVelocity, meanFreeVec, meanFreeComponent] using hid

private theorem lin34Setup_tensor_eLpNorm_identity
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ s : ℝ}
    (hu : AEStronglyMeasurable (fun x : Vec3 => u (x, s))
      (volume.restrict (vec3Ball x₀ ρ))) :
    eLpNorm (fun x => Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      pressureUHat u (fun t j => ⨍ y in vec3Ball x₀ ρ, u (y, t) j)
        (x, s) i j ^ 2)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ)) =
    eLpNorm (fun x => vec3EuclideanNorm (u (x, s) -
      (fun j => ⨍ y in vec3Ball x₀ ρ, u (y, s) j))) 3
      (volume.restrict (vec3Ball x₀ ρ)) ^ (2 : ℕ) := by
  let g : Vec3 → ℝ := fun x => vec3EuclideanNorm
    (u (x, s) - fun j => ⨍ y in vec3Ball x₀ ρ, u (y, s) j)
  have hgmeas : AEStronglyMeasurable g
      (volume.restrict (vec3Ball x₀ ρ)) := by
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      (hu.sub aestronglyMeasurable_const)
  have hpow := eLpNorm_norm_rpow g hgmeas (p := ENNReal.ofReal (3 / 2 : ℝ))
    (q := (2 : ℝ)) (by norm_num)
  have hcast : ENNReal.ofReal (3 / 2 : ℝ) * ENNReal.ofReal (2 : ℝ) =
      (3 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    norm_num
  have hnorm : (fun x : Vec3 => ‖g x‖ ^ (2 : ℝ)) = fun x => g x ^ (2 : ℕ) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact Real.rpow_natCast _ 2
  calc
    _ = eLpNorm (fun x => g x ^ (2 : ℕ))
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (vec3Ball x₀ ρ)) := by
      apply eLpNorm_congr_ae
      filter_upwards [] with x
      rw [lin34Setup_tensorNorm_identity u x₀ ρ s x]
    _ = eLpNorm (fun x => ‖g x‖ ^ (2 : ℝ))
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (vec3Ball x₀ ρ)) := by rw [hnorm]
    _ = eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ) * ENNReal.ofReal (2 : ℝ))
          (volume.restrict (vec3Ball x₀ ρ)) ^ (2 : ℝ) := hpow
    _ = eLpNorm g 3 (volume.restrict (vec3Ball x₀ ρ)) ^ (2 : ℝ) := by
      rw [hcast]
    _ = eLpNorm g 3 (volume.restrict (vec3Ball x₀ ρ)) ^ (2 : ℕ) :=
      ENNReal.rpow_natCast _ 2

/-- The four setup statements for the doubly centred pressure decomposition of
`prop:lin34`: the tensor bounds, the decomposition on the inner ball, and the
conditional cancellation of the force group. -/
theorem lin34_centred_setup
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) (ρ : ℝ) (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    let c := fun s : ℝ => fun j : Fin 3 => ⨍ y in vec3Ball z.1 ρ, u (y,s) j
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ x : Vec3, Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
        pressureUHat u c (x,s) i j ^ 2) ≤ vec3EuclideanNorm (u (x,s) - c s) ^ 2) ∧
      eLpNorm (fun x => Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
        pressureUHat u c (x,s) i j ^ 2)) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball z.1 ρ)) ≤
          eLpNorm (fun x => vec3EuclideanNorm (u (x,s) - c s)) 3
            (volume.restrict (vec3Ball z.1 ρ)) ^ (2 : ℕ) ∧
      (∀ᵐ x ∂volume.restrict (vec3Ball z.1 (13 * ρ / 20)),
        p (x,s) = lin34CentredP1 u p f z.1 ρ hρ s x +
          lin34CentredRemainder u p z.1 ρ hρ s x +
          lin34ForcePart f z.1 ρ hρ s x) ∧
      ((∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ Ω → ∫ x in Ω, ∑ j : Fin 3,
            f (x,s) j * spatialDeriv ψ j x = 0) →
        ∀ᵐ x ∂volume, lin34ForcePart f z.1 ρ hρ s x = 0) := by
  dsimp only
  have hforce := lin34Setup_force_ae_of_sws hsol hρ hsub
  have hslice : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      AEStronglyMeasurable (fun x : Vec3 => u (x, s))
        (volume.restrict (vec3Ball z.1 ρ)) := by
    obtain ⟨Ω', J, hbox, hball', htime'⟩ := pressure_box_geometry hsol hρ hsub
    have hJ := slice_memLp_ae_of_sws hsol hbox
    exact (ae_restrict_of_ae_restrict_of_subset htime' hJ).mono fun s hs =>
      (hs.1.mono_measure (Measure.restrict_mono_set volume hball')).aestronglyMeasurable
  have hdecomposition' : ∀ᵐ s ∂volume.restrict
      (Ioc (z.2 - ρ ^ 2) z.2),
      (fun x : Vec3 => p (x, s)) =ᵐ[volume.restrict
        (vec3Ball z.1 (13 * ρ / 20))]
        (lin34CentredP1 u p f z.1 ρ hρ s +
          lin34CentredRemainder u p z.1 ρ hρ s + lin34ForcePart f z.1 ρ hρ s) := by
    have htime' : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I := by
      obtain ⟨Ω', J, hbox, hball', htime'⟩ := pressure_box_geometry hsol hρ hsub
      exact htime'.trans (subset_closure.trans hbox.2.2.2.2.2)
    filter_upwards [] with s
    have hdecomposition := lin34_centred_decomposition_on_inner
      (u := u) (p := p) (f := f) (x₀ := z.1) (ρ := ρ) (s := s) hρ
    rw [lin34Setup_ball_eq_euclideanBall (by positivity : 0 < 13 * ρ / 20)] at hdecomposition
    exact hdecomposition
  filter_upwards [hforce, hdecomposition', hslice] with s hforce_s hdecomposition_s hslice_s
  have htensor := lin34Setup_tensorNorm_identity u z.1 ρ s
  refine ⟨?_, ?_, ?_, hforce_s⟩
  · intro x
    rw [htensor x]
  · exact le_of_eq (lin34Setup_tensor_eLpNorm_identity hslice_s)
  · exact hdecomposition_s

end CKN
