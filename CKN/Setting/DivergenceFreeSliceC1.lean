-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.DivergenceFreeSlice
import CKN.Foundation.Measure.SliceDistribution
import CKN.Foundation.Measure.SliceDistributionMollifyBounds
import CKN.Foundation.Sobolev.Mollify.Basic
import CKN.Foundation.Sobolev.WeakDerivative
import CKN.Foundation.Parabolic.Topology
import CKN.Foundation.Parabolic.BallBasics
import CKN.Statements.SpaceTimeTestFunction
import CKN.Setting.Energy.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A common exceptional set for C¹ divergence tests

The space-time divergence identity first gives a common almost-everywhere slice
identity for smooth tests. Local integrability of the slices then extends that
identity by spatial mollification to every compactly supported C¹ test in an
interior ball, outside one exceptional time set.
-/

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators Topology Convolution
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

private theorem tsupport_parabolic_eq (f : ParabolicPoint → ℝ) :
    tsupport f = parabolicHomeomorph ⁻¹' tsupport
      (fun z : Vec3 × ℝ => f z) := by
  have hsupp : Function.support f = parabolicHomeomorph ⁻¹' Function.support
      (fun z : Vec3 × ℝ => f z) := by
    ext z
    rw [Set.mem_preimage, Function.mem_support, Function.mem_support]
    exact Iff.rfl
  rw [tsupport, tsupport, hsupp, ← parabolicHomeomorph.preimage_closure]

private theorem divergence_test_integrableOn_support
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3}
    (hu : LocallyIntegrableOn u (spaceTimeSet Ω I) volume)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    IntegrableOn (fun z : ParabolicPoint =>
      ∑ i : Fin 3, u z i * spatialPartial ψ i z)
      (tsupport (fun z : ParabolicPoint => ψ (parabolicHomeomorph z))) volume := by
  let Ψ : ParabolicPoint → ℝ := fun z => ψ (parabolicHomeomorph z)
  have hts : tsupport Ψ = parabolicHomeomorph ⁻¹' tsupport ψ := by
    have hψfun : (fun z : Vec3 × ℝ => Ψ z) = ψ := by
      funext z
      rcases z with ⟨x, t⟩
      rfl
    simpa only [hψfun] using tsupport_parabolic_eq Ψ
  have hKcompact : IsCompact (tsupport Ψ) := by
    rw [hts]
    exact parabolicHomeomorph.isCompact_preimage.mpr hψ.2.1.isCompact
  have hKsub : tsupport Ψ ⊆ spaceTimeSet Ω I := by
    rw [hts]
    exact hψ.2.2
  have huK : IntegrableOn u (tsupport Ψ) volume :=
    hu.integrableOn_compact_subset hKsub hKcompact
  have huK' : Integrable u (volume.restrict (tsupport Ψ)) := huK
  have hterm (i : Fin 3) :
      IntegrableOn (fun z : ParabolicPoint => u z i * spatialPartial ψ i z)
        (tsupport Ψ) volume := by
    have hcoord : IntegrableOn (fun z : ParabolicPoint => u z i)
        (tsupport Ψ) volume :=
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integrable_comp huK'
    have hderiv : Continuous (fun z : ParabolicPoint => spatialPartial ψ i z) :=
      (spatialPartial_contDiff hψ.1 i).continuous.comp
        parabolicHomeomorph.continuous
    exact hcoord.mul_continuousOn hderiv.continuousOn hKcompact
  rw [MeasureTheory.IntegrableOn]
  simpa [Ψ, parabolicHomeomorph] using
    MeasureTheory.integrable_finsetSum Finset.univ (fun i hi => hterm i)

private theorem ae_slice_locallyIntegrableOn_ball_of_localIntegrability
    {Ω : Set Vec3} {I : Set ℝ} (hI : IsOpen I)
    {u : ParabolicPoint → Vec3}
    (hu : LocallyIntegrableOn u (spaceTimeSet Ω I) volume)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hB : closure (vec3Ball x₀ ρ) ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I,
      IntegrableOn (fun x : Vec3 => u (x, s))
        (closure (vec3Ball x₀ ρ)) volume ∧
      ∀ i : Fin 3,
        LocallyIntegrableOn (fun x : Vec3 => u (x, s) i)
          (vec3Ball x₀ ρ) volume := by
  let ι := {p : ℝ × ℝ // 0 < p.2 ∧ Metric.closedBall p.1 p.2 ⊆ I}
  let V : ι → Set ℝ := fun p => Metric.ball p.1.1 p.1.2
  have hVopen (p : ι) : IsOpen (V p) := Metric.isOpen_ball
  have hVunion : (⋃ p : ι, V p) = I := by
    ext s
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp⟩
      exact p.2.2 (Metric.ball_subset_closedBall hp)
    · intro hs
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hI s hs
      let p : ι := ⟨(s, ε / 2), ⟨by positivity,
        (closedBall_subset_ball (by linarith only [hε])).trans hεsub⟩⟩
      refine ⟨p, ?_⟩
      exact mem_ball_self (by positivity)
  obtain ⟨S, hScount, hSunion⟩ :=
    TopologicalSpace.isOpen_iUnion_countable V hVopen
  set_option linter.style.haveILetI false in
    letI : Countable S := hScount.to_subtype
  have hGoodAll : ∀ᵐ s ∂volume, ∀ p : S,
      s ∈ Metric.closedBall p.1.1.1 p.1.1.2 →
        IntegrableOn (fun x : Vec3 => u (x, s)) (closure (vec3Ball x₀ ρ)) volume := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    let T : Set ℝ := Metric.closedBall p.1.1.1 p.1.1.2
    have hTcompact : IsCompact T := isCompact_closedBall _ _
    have hTsub : T ⊆ I := p.1.2.2
    have hKcompact : IsCompact (parabolicHomeomorph ⁻¹'
        (closure (vec3Ball x₀ ρ) ×ˢ T)) :=
      parabolicHomeomorph.isCompact_preimage.mpr
        ((isCompact_closure_vec3Ball hρ).prod hTcompact)
    have hKsub : parabolicHomeomorph ⁻¹'
        (closure (vec3Ball x₀ ρ) ×ˢ T) ⊆ spaceTimeSet Ω I := by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      exact ⟨hB hx, hTsub ht⟩
    have hInt := hu.integrableOn_compact_subset hKsub hKcompact
    have hpre : parabolicHomeomorph ⁻¹'
        (closure (vec3Ball x₀ ρ) ×ˢ T) = closure (vec3Ball x₀ ρ) ×ˢ T := by
      ext ⟨x, t⟩
      rfl
    rw [hpre] at hInt
    change IntegrableOn (fun z : Vec3 × ℝ => u ((z.1, z.2) : ParabolicPoint))
      (closure (vec3Ball x₀ ρ) ×ˢ T) (volume : Measure (Vec3 × ℝ)) at hInt
    have hIntProd : Integrable
        (fun z : Vec3 × ℝ => u ((z.1, z.2) : ParabolicPoint))
        ((volume.restrict (closure (vec3Ball x₀ ρ))).prod (volume.restrict T)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
      exact hInt
    have hSliceT : ∀ᵐ s ∂volume.restrict T,
        IntegrableOn (fun x : Vec3 => u (x, s)) (closure (vec3Ball x₀ ρ)) volume := by
      filter_upwards [hIntProd.prod_left_ae] with s hs
      exact hs
    have hSliceGlobal : ∀ᵐ s ∂volume,
        s ∈ T → IntegrableOn (fun x : Vec3 => u (x, s))
          (closure (vec3Ball x₀ ρ)) volume :=
      (ae_restrict_iff' hTcompact.measurableSet).mp hSliceT
    filter_upwards [hSliceGlobal] with s hs hmem
    exact hs hmem
  have hGlobal : ∀ᵐ s ∂volume,
      s ∈ I → IntegrableOn (fun x : Vec3 => u (x, s))
        (closure (vec3Ball x₀ ρ)) volume := by
    filter_upwards [hGoodAll] with s hs hmem
    have hsCover : s ∈ ⋃ p ∈ S, V p := by
      rw [hSunion, hVunion]
      exact hmem
    simp only [Set.mem_iUnion] at hsCover
    obtain ⟨p, hpS, hpV⟩ := hsCover
    have hpClosed : s ∈ Metric.closedBall p.1.1 p.1.2 :=
      Metric.ball_subset_closedBall hpV
    exact hs ⟨p, hpS⟩ hpClosed
  have hIntI : ∀ᵐ s ∂volume.restrict I,
      IntegrableOn (fun x : Vec3 => u (x, s))
        (closure (vec3Ball x₀ ρ)) volume :=
    (ae_restrict_iff' hI.measurableSet).mpr hGlobal
  filter_upwards [hIntI] with s hs
  refine ⟨hs, ?_⟩
  intro i
  have hVec : Integrable (fun x : Vec3 => u (x, s))
      (volume.restrict (closure (vec3Ball x₀ ρ))) := hs
  have hCoord : IntegrableOn (fun x : Vec3 => u (x, s) i)
      (closure (vec3Ball x₀ ρ)) volume := by
    exact (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integrable_comp hVec
  exact hCoord.locallyIntegrableOn.mono_set subset_closure

private theorem mollified_test_tsupport_subset_ball
    {x₀ : Vec3} {ρ δ : ℝ} {E : Set Vec3} {ψ : Vec3 → ℝ}
    (hE : IsCompact E)
    (hδsub : Metric.cthickening δ E ⊆ vec3Ball x₀ ρ)
    (hψE : tsupport ψ ⊆ E) {ε : ℝ} (hε : 0 < ε)
    (hεle : ε ≤ δ) :
    tsupport (mollify ψ ε hε) ⊆ vec3Ball x₀ ρ := by
  have hsupp : Function.support (mollify ψ ε hε) ⊆ Metric.cthickening δ E := by
    exact (support_mollify_subset hε).trans
      ((Metric.cthickening_subset_of_subset ε hψE).trans
        (Metric.cthickening_mono hεle E))
  change closure (Function.support (mollify ψ ε hε)) ⊆ vec3Ball x₀ ρ
  exact (closure_minimal hsupp hE.cthickening.isClosed).trans hδsub

private theorem fderiv_mollify_c1
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    {ε : ℝ} (hε : 0 < ε) (x : Vec3) (i : Fin 3) :
    (fderiv ℝ (mollify ψ ε hε) x) (basisVec i) =
      mollify (fun y => (fderiv ℝ ψ y) (basisVec i)) ε hε x := by
  have hfd := hψc.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) (mollifier_locallyIntegrable hε) hψ x
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hfd.fderiv
  rw [convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (mollifier_locallyIntegrable hε) (hψc.fderiv ℝ)
    (hψ.continuous_fderiv (by norm_num)) x (basisVec i)] at h
  simpa [mollify] using h

private theorem fderiv_eq_zero_of_not_mem_tsupport
    {ψ : Vec3 → ℝ} {x : Vec3} (hx : x ∉ tsupport ψ) :
    fderiv ℝ ψ x = 0 := by
  have hev : ψ =ᶠ[𝓝 x] (fun _ : Vec3 => (0 : ℝ)) :=
    Filter.eventually_of_mem ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hx)
      (fun y hy => by
        by_contra hne
        exact hy (subset_tsupport ψ (Function.mem_support.mpr hne)))
  rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_const_apply]

private theorem c1_divergence_zero_of_smooth_tests
    {x₀ : Vec3} {ρ : ℝ} {E : Set Vec3} {g : Vec3 → Vec3}
    (hE : IsCompact E) (hEB : E ⊆ vec3Ball x₀ ρ)
    (hg : IntegrableOn g (closure (vec3Ball x₀ ρ)) volume)
    (hsmooth : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ vec3Ball x₀ ρ →
      ∫ x in vec3Ball x₀ ρ, ∑ i : Fin 3,
        g x i * (fderiv ℝ φ x) (basisVec i) = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψE : tsupport ψ ⊆ E) :
    ∫ x in vec3Ball x₀ ρ, ∑ i : Fin 3,
      g x i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
  obtain ⟨δ, hδpos, hδsub⟩ :=
    hE.exists_cthickening_subset_open (isOpen_vec3Ball x₀ ρ) hEB
  let φ : ℕ → Vec3 → ℝ := fun n =>
    mollify ψ (sliceRadius n) (sliceRadius_pos n)
  have hφsmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (φ n) := by
    exact mollify_contDiff (sliceRadius_pos n)
      (hψ.continuous.locallyIntegrable)
  have hφcompact (n : ℕ) : HasCompactSupport (φ n) := by
    simpa [φ, mollify] using
      (mollifier_hasCompactSupport (sliceRadius_pos n)).convolution
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψc
  have hsmall : ∀ᶠ n in atTop, sliceRadius n ≤ δ := by
    filter_upwards [tendsto_sliceRadius_atTop.eventually (gt_mem_nhds hδpos)]
      with n hn
    exact le_of_lt hn
  have hφsupport (n : ℕ) (hn : sliceRadius n ≤ δ) :
      tsupport (φ n) ⊆ vec3Ball x₀ ρ := by
    exact mollified_test_tsupport_subset_ball hE hδsub hψE
      (sliceRadius_pos n) hn
  have hzero : ∀ᶠ n in atTop,
      ∫ x in vec3Ball x₀ ρ, ∑ i : Fin 3,
        g x i * (fderiv ℝ (φ n) x) (basisVec i) = 0 := by
    filter_upwards [hsmall] with n hn
    exact hsmooth (φ n) (hφsmooth n) (hφcompact n) (hφsupport n hn)
  let D : Fin 3 → Vec3 → ℝ := fun i x => (fderiv ℝ ψ x) (basisVec i)
  let Dn : Fin 3 → ℕ → Vec3 → ℝ := fun i n x =>
    (fderiv ℝ (φ n) x) (basisVec i)
  have hDcont (i : Fin 3) : Continuous (D i) := by
    exact (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDcompact (i : Fin 3) : HasCompactSupport (D i) := by
    simpa [D] using hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hDlimit (i : Fin 3) (x : Vec3) :
      Tendsto (fun n => Dn i n x) atTop (nhds (D i x)) := by
    have hm := mollify_tendsto_of_continuous tendsto_sliceRadius_atTop
      sliceRadius_pos (hDcont i) x
    refine hm.congr' ?_
    filter_upwards with n
    exact (fderiv_mollify_c1 hψ hψc (sliceRadius_pos n) x i).symm
  have hDbound (i : Fin 3) : ∃ M : ℝ, ∀ x, |D i x| ≤ M := by
    obtain ⟨M, hM⟩ := (hDcompact i).exists_bound_of_continuous (hDcont i)
    refine ⟨M, fun x => ?_⟩
    simpa [Real.norm_eq_abs] using hM x
  let M : Fin 3 → ℝ := fun i => Classical.choose (hDbound i)
  have hM (i : Fin 3) (x : Vec3) : |D i x| ≤ M i :=
    Classical.choose_spec (hDbound i) x
  have hDnabs (i : Fin 3) (n : ℕ) (x : Vec3) : |Dn i n x| ≤ M i := by
    rw [show Dn i n x = mollify (D i) (sliceRadius n) (sliceRadius_pos n) x by
      simpa [Dn, D, φ] using fderiv_mollify_c1 hψ hψc
        (sliceRadius_pos n) x i]
    exact abs_mollify_le (hDcont i) (hM i) (sliceRadius_pos n) x
  have hgBall : Integrable g (volume.restrict (vec3Ball x₀ ρ)) := by
    have hgClosed : Integrable g (volume.restrict (closure (vec3Ball x₀ ρ))) := hg
    exact hgClosed.mono_measure
      (Measure.restrict_mono_set volume subset_closure)
  have hgi (i : Fin 3) :
      Integrable (fun x : Vec3 => g x i) (volume.restrict (vec3Ball x₀ ρ)) := by
    exact (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integrable_comp hgBall
  have happrox (i : Fin 3) (n : ℕ) :
      Integrable (fun x : Vec3 => g x i * Dn i n x)
        (volume.restrict (vec3Ball x₀ ρ)) := by
    have hDnmeas : AEStronglyMeasurable (Dn i n)
        (volume.restrict (vec3Ball x₀ ρ)) := by
      exact ((hφsmooth n).continuous_fderiv (by norm_num)).clm_apply
        continuous_const |>.aestronglyMeasurable
    have hDnBound : ∀ᵐ x ∂volume.restrict (vec3Ball x₀ ρ),
        ‖Dn i n x‖ ≤ M i := by
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hDnabs i n x
    exact (hgi i).mul_bdd hDnmeas hDnBound
  have hdom (i : Fin 3) (n : ℕ) :
      ∀ᵐ x ∂volume.restrict (vec3Ball x₀ ρ),
        ‖g x i * Dn i n x‖ ≤ M i * ‖g x i‖ := by
    filter_upwards with x
    rw [norm_mul]
    calc
      ‖g x i‖ * ‖Dn i n x‖ ≤ ‖g x i‖ * M i :=
        mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hDnabs i n x)
          (norm_nonneg _)
      _ = M i * ‖g x i‖ := by ring
  have hlim (i : Fin 3) : Tendsto
      (fun n => ∫ x in vec3Ball x₀ ρ, g x i * Dn i n x)
      atTop (nhds (∫ x in vec3Ball x₀ ρ, g x i * D i x)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => M i * ‖g x i‖)
      (fun n => (happrox i n).aestronglyMeasurable)
      ((hgi i).norm.const_mul (M i))
      (fun n => hdom i n)
      (Filter.Eventually.of_forall fun x =>
        Filter.Tendsto.const_mul (g x i) (hDlimit i x))
  have hlimsum : Tendsto
      (fun n => ∑ i : Fin 3, ∫ x in vec3Ball x₀ ρ, g x i * Dn i n x)
      atTop (nhds (∑ i : Fin 3, ∫ x in vec3Ball x₀ ρ, g x i * D i x)) :=
    tendsto_finsetSum _ fun i _ => hlim i
  have hzeroSum : ∀ᶠ n in atTop,
      ∑ i : Fin 3, ∫ x in vec3Ball x₀ ρ, g x i * Dn i n x = 0 := by
    filter_upwards [hzero] with n hn
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => happrox i n)] at hn
    exact hn
  have hlimit : ∑ i : Fin 3, ∫ x in vec3Ball x₀ ρ, g x i * D i x = 0 := by
    apply tendsto_nhds_unique hlimsum
    exact tendsto_const_nhds.congr'
      (hzeroSum.mono fun n hn => hn.symm)
  have htargetInt (i : Fin 3) :
      Integrable (fun x : Vec3 => g x i * D i x)
        (volume.restrict (vec3Ball x₀ ρ)) := by
    exact (hgi i).mul_bdd (hDcont i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hM i x)
  calc
    ∫ x in vec3Ball x₀ ρ, ∑ i : Fin 3, g x i * (fderiv ℝ ψ x) (basisVec i) =
        ∑ i : Fin 3, ∫ x in vec3Ball x₀ ρ, g x i * D i x := by
          rw [MeasureTheory.integral_finsetSum Finset.univ
            (fun i _ => htargetInt i)]
    _ = 0 := hlimit

/-- One exceptional time set suffices for every compactly supported (C^1)
spatial test contained in a compact subset of an interior ball, when the
space-time field is distributionally divergence free and locally integrable. -/
theorem divergence_free_common_null_set
    (Ω : Set Vec3) (I : Set ℝ) (hΩ : IsOpen Ω) (hI : IsOpen I)
    (u : ParabolicPoint → Vec3)
    (hu : LocallyIntegrableOn u (spaceTimeSet Ω I) volume)
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      ∫ z in spaceTimeSet Ω I, ∑ i : Fin 3,
        u z i * spatialPartial ψ i z = 0)
    (x₀ : Vec3) (ρ : ℝ) (hρ : 0 < ρ)
    (hB : closure (vec3Ball x₀ ρ) ⊆ Ω)
    (J : Set ℝ) (hJ : OrdConnected J) (hJI : closure J ⊆ I)
    (E : Set Vec3) (hE : IsCompact E) (hEB : E ⊆ vec3Ball x₀ ρ) :
    ∃ N : Set ℝ, N ⊆ J ∧ volume N = 0 ∧
      ∀ s ∈ J \ N, ∀ ψ : Vec3 → ℝ, ContDiff ℝ 1 ψ → tsupport ψ ⊆ E →
        ∫ x in vec3Ball x₀ ρ, ∑ i : Fin 3,
          u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
  have _hSpaceTimeOpen : IsOpen (spaceTimeSet Ω I) :=
    isOpen_spaceTimeSet Ω I hΩ hI
  have hS2 : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z : ParabolicPoint =>
        ∑ i : Fin 3, u z i * spatialPartial ψ i z) (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i : Fin 3,
        u z i * spatialPartial ψ i z = 0 := by
    intro ψ hψ
    exact ⟨divergence_test_integrableOn_support hu hψ, hdiv ψ hψ⟩
  have hslice := divfree_slice_weak hS2 hI
  have hsliceBall : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ vec3Ball x₀ ρ →
      ∀ᵐ s ∂volume.restrict I,
        ∫ x in vec3Ball x₀ ρ, ∑ i : Fin 3,
          u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
    intro ψ hψ hψc hψB
    have hψΩ : tsupport ψ ⊆ Ω := hψB.trans (subset_closure.trans hB)
    have hsmooth := hslice ψ hψ hψc hψΩ
    filter_upwards [hsmooth] with s hs
    have hzeroB (x : Vec3) (hx : x ∉ vec3Ball x₀ ρ) :
        ∑ i : Fin 3, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [fderiv_eq_zero_of_not_mem_tsupport (fun h => hx (hψB h))]
      simp
    have hBfull : ∫ x in vec3Ball x₀ ρ, ∑ i : Fin 3,
        u (x, s) i * (fderiv ℝ ψ x) (basisVec i) ∂volume =
        ∫ x, ∑ i : Fin 3,
          u (x, s) i * (fderiv ℝ ψ x) (basisVec i) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzeroB
    have hΩfull : ∫ x in Ω, ∑ i : Fin 3,
        u (x, s) i * (fderiv ℝ ψ x) (basisVec i) ∂volume =
        ∫ x, ∑ i : Fin 3,
          u (x, s) i * (fderiv ℝ ψ x) (basisVec i) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (by
      intro x hxΩ
      exact hzeroB x (fun hxB => hxΩ (hB (subset_closure hxB))))
    calc
      ∫ x in vec3Ball x₀ ρ, ∑ i : Fin 3,
          u (x, s) i * (fderiv ℝ ψ x) (basisVec i) =
        ∫ x, ∑ i : Fin 3,
          u (x, s) i * (fderiv ℝ ψ x) (basisVec i) := hBfull
      _ = ∫ x in Ω, ∑ i : Fin 3,
          u (x, s) i * (fderiv ℝ ψ x) (basisVec i) := hΩfull.symm
      _ = 0 := hs
  have hloc := ae_slice_locallyIntegrableOn_ball_of_localIntegrability
    hI hu hρ hB
  have hSliceAll := ae_slice_divergence_zero_of_forall_test
    (isOpen_vec3Ball x₀ ρ) (hloc.mono fun s h => h.2) hsliceBall
  let SmoothGood : ℝ → Prop := fun s => ∀ ψ : Vec3 → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ vec3Ball x₀ ρ →
    ∫ x in vec3Ball x₀ ρ, ∑ i : Fin 3,
      u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0
  let Good : ℝ → Prop := fun s =>
    IntegrableOn (fun x : Vec3 => u (x, s))
      (closure (vec3Ball x₀ ρ)) volume ∧ SmoothGood s
  have hAll : ∀ᵐ s ∂volume.restrict I, Good s := by
    filter_upwards [hSliceAll, hloc] with s hs hlocal
    exact ⟨hlocal.1, hs⟩
  have hAllGlobal : ∀ᵐ s ∂volume, s ∈ I → Good s :=
    (ae_restrict_iff' hI.measurableSet).mp hAll
  have hJgood : ∀ᵐ s ∂volume.restrict J, Good s := by
    apply (ae_restrict_iff' hJ.measurableSet).mpr
    filter_upwards [hAllGlobal] with s hs hsJ
    exact hs (hJI (subset_closure hsJ))
  have hJgoodGlobal : ∀ᵐ s ∂volume, s ∈ J → Good s :=
    (ae_restrict_iff' hJ.measurableSet).mp hJgood
  let N : Set ℝ := {s | s ∈ J ∧ ¬ Good s}
  have hNnull : volume N = 0 := by
    have hbad : volume {s | ¬ (s ∈ J → Good s)} = 0 := ae_iff.mp hJgoodGlobal
    simpa only [N, not_imp] using hbad
  refine ⟨N, ?_, hNnull, ?_⟩
  · rintro s ⟨hsJ, _⟩
    exact hsJ
  · intro s hs ψ hψ hψE
    have hsJ : s ∈ J := hs.1
    have hsN : s ∉ N := hs.2
    have hGood : Good s := by
      by_contra hnot
      exact hsN ⟨hsJ, hnot⟩
    have hψc : HasCompactSupport ψ := by
      change IsCompact (tsupport ψ)
      exact hE.of_isClosed_subset (isClosed_tsupport ψ) hψE
    exact c1_divergence_zero_of_smooth_tests hE hEB hGood.1
      (fun φ hφ hφc hφB => hGood.2 φ hφ hφc hφB)
      hψ hψc hψE

end CKN

end
