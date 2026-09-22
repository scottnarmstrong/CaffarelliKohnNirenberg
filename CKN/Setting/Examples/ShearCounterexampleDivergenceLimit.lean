-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Examples.ShearCounterexampleMomentumLimit
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Distributional divergence identities for the rough parabolic shear. -/

set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped ENNReal Topology
namespace CKN


private def finiteShearDivergenceResidual (N : ℕ) (ψ : Vec3 × ℝ → ℝ)
    (z : Vec3 × ℝ) : ℝ :=
  shearFullScalarPartial N z * spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z

def shearDivergenceResidual (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  shearFullScalar z * spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z

private theorem finiteShearDivergenceResidual_continuous (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Continuous (finiteShearDivergenceResidual N ψ) := by
  have hW : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => shearFullScalarPartial N z) :=
    shearFullScalarPartial_contDiff N
  have hD : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z) :=
    spatialPartial_contDiff hψ 2
  unfold finiteShearDivergenceResidual
  exact (hW.mul hD).continuous

private theorem scalarTestSpace_zero_of_not_tsupport
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) :
    spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z = 0 := by
  have hEq : spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z =
      fderiv ℝ ψ z (basisVec (2 : Fin 3), (0 : ℝ)) :=
    spatialPartial_eq_joint_fderiv hψ z 2
  let D : Vec3 × ℝ → ℝ := fun w => fderiv ℝ ψ w (basisVec (2 : Fin 3), (0 : ℝ))
  have hD : D z = 0 := by
    by_contra hne
    have hsupp : z ∈ Function.support D := Function.mem_support.mpr hne
    have hmem : z ∈ tsupport D := subset_tsupport D hsupp
    have hsub : tsupport D ⊆ tsupport ψ :=
      tsupport_fderiv_apply_subset ℝ (basisVec (2 : Fin 3), (0 : ℝ))
    exact hz (hsub hmem)
  rw [hEq]
  simpa [D] using hD

private theorem shearCounterexample_divergence_finite (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ z : Vec3 × ℝ,
      ∑ i : Fin 3, shearCounterexampleVelocityPartial N z i *
        spatialPartial (show ParabolicPoint → ℝ from ψ) i z ∂volume = 0 := by
  let W : Vec3 × ℝ → ℝ := fun z => shearFullScalarPartial N z
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := shearFullScalarPartial_contDiff N
  have hIBP := integral_mul_spatialPartial_eq_neg_spatialPartial_mul hW hψ hψc 2
  have hzero (z : Vec3 × ℝ) :
      spatialPartial (show ParabolicPoint → ℝ from W) 2 z = 0 := by
    simpa [W] using
      shearFullScalarPartial_gradient_zero N (parabolicHomeomorph.symm z)
  have hsum (z : Vec3 × ℝ) :
      (∑ i : Fin 3, shearCounterexampleVelocityPartial N z i *
        spatialPartial (show ParabolicPoint → ℝ from ψ) i z) =
      W z * spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z := by
    simp [W, shearCounterexampleVelocityPartial]
  calc
    _ = ∫ z : Vec3 × ℝ,
        W z * spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hsum z
    _ = -∫ z : Vec3 × ℝ,
        spatialPartial (show ParabolicPoint → ℝ from W) 2 z * ψ z ∂volume := hIBP
    _ = 0 := by
      have hz : (fun z : Vec3 × ℝ =>
          spatialPartial (show ParabolicPoint → ℝ from W) 2 z * ψ z) = fun _ => 0 := by
        funext z
        rw [hzero z]
        simp
      rw [hz, integral_zero]
      simp

private def shearDivergenceMajorant (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  |shearFullScalar z| *
    |spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z|

private theorem shearDivergenceMajorant_integrable {Ω' : Set Vec3} {J : Set ℝ}
    [IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J))]
    [hOpen : OpensMeasurableSpace (Vec3 × ℝ)]
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (shearDivergenceMajorant ψ)
      (volume.restrict (spaceTimeSet Ω' J)) := by
  let μ := volume.restrict (spaceTimeSet Ω' J)
  let D : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := spatialPartial_contDiff hψ 2
  have hDsupp : HasCompactSupport D := spatialPartial_hasCompactSupport hψ hψc 2
  have hDtop : MemLp D ⊤ μ := by
    exact @Continuous.memLp_top_of_hasCompactSupport ℝ _ (Vec3 × ℝ) _ _ hOpen D
      hD.continuous hDsupp μ
  have hW3 : MemLp shearFullScalar 3 μ :=
    shearFullScalar_memLp_on_localBox shearReducedBumpSeries_memLp_three hbox
  have hW2 : MemLp shearFullScalar 2 μ := hW3.mono_exponent (by norm_num)
  have hprod : Integrable (fun z => |shearFullScalar z| * |D z|) μ := by
    apply MemLp.integrable (q := 2) (by norm_num)
    exact hW2.abs.mul hDtop.abs
  change Integrable (fun z => |shearFullScalar z| * |D z|) μ
  exact hprod

private theorem finiteShearDivergenceResidual_bound_ae {Ω' : Set Vec3} {J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ) :
    ∀ N, ∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω' J)),
      ‖finiteShearDivergenceResidual N ψ z‖ ≤ shearDivergenceMajorant ψ z := by
  have hW0 : ∀ᵐ z ∂volume, 0 ≤ shearFullScalar z := by
    filter_upwards [shearFullScalarPartial_le_ae 0] with z hz
    exact le_trans (shearCounterexampleVelocityPartial_nonneg 0 z) hz
  have hW0μ := ae_restrict_of_ae (s := spaceTimeSet Ω' J) hW0
  intro N
  have hWle := ae_restrict_of_ae (s := spaceTimeSet Ω' J)
    (shearFullScalarPartial_le_ae N)
  filter_upwards [hW0μ, hWle] with z hW0z hWlez
  have hWN : 0 ≤ shearFullScalarPartial N z :=
    shearCounterexampleVelocityPartial_nonneg N z
  have hWabs : |shearFullScalarPartial N z| ≤ |shearFullScalar z| := by
    rw [abs_of_nonneg hWN, abs_of_nonneg hW0z]
    exact hWlez
  simp only [finiteShearDivergenceResidual, shearDivergenceMajorant, Real.norm_eq_abs,
    abs_mul]
  exact mul_le_mul_of_nonneg_right hWabs (abs_nonneg _)

private theorem finiteShearDivergenceResidual_tendsto_ae
    (ψ : Vec3 × ℝ → ℝ) :
    ∀ᵐ z : ParabolicPoint ∂volume,
      Tendsto (fun N => finiteShearDivergenceResidual N ψ z) atTop
        (𝓝 (shearDivergenceResidual ψ z)) := by
  filter_upwards [shearFullScalarPartial_tendsto_ae] with z hW
  have hD : Tendsto (fun _ : ℕ =>
      spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z) atTop
      (𝓝 (spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z)) :=
    tendsto_const_nhds
  have hmul := hW.mul hD
  simpa [finiteShearDivergenceResidual, shearDivergenceResidual] using hmul

private theorem finiteShearDivergenceResidual_tsupport_subset (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    tsupport (finiteShearDivergenceResidual N ψ) ⊆ tsupport ψ := by
  have hsupp : Function.support (finiteShearDivergenceResidual N ψ) ⊆ tsupport ψ := by
    intro z hz
    by_contra hnot
    have hD : spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z = 0 :=
      scalarTestSpace_zero_of_not_tsupport ψ hψ hnot
    exact (Function.mem_support.mp hz) (by simp [finiteShearDivergenceResidual, hD])
  change closure (Function.support (finiteShearDivergenceResidual N ψ)) ⊆ tsupport ψ
  exact closure_minimal hsupp (isClosed_tsupport ψ)

theorem shearDivergenceResidual_tsupport_subset
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    tsupport (shearDivergenceResidual ψ) ⊆ tsupport ψ := by
  have hsupp : Function.support (shearDivergenceResidual ψ) ⊆ tsupport ψ := by
    intro z hz
    by_contra hnot
    have hD : spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z = 0 :=
      scalarTestSpace_zero_of_not_tsupport ψ hψ hnot
    exact (Function.mem_support.mp hz) (by simp [shearDivergenceResidual, hD])
  change closure (Function.support (shearDivergenceResidual ψ)) ⊆ tsupport ψ
  exact closure_minimal hsupp (isClosed_tsupport ψ)

private theorem divergence_setIntegral_eq_integral_of_support_subset
    {S : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}
    (hS : MeasurableSet S) (hsupp : Function.support f ⊆ S) :
    ∫ z in S, f z ∂volume = ∫ z, f z ∂volume := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ S
  · simp [hz]
  · have hfz : f z = 0 := by
      by_contra hne
      exact hz (hsupp (Function.mem_support.mpr hne))
    simp [hz, hfz]

private theorem finiteShearDivergenceResidual_integral_zero (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ z : Vec3 × ℝ, finiteShearDivergenceResidual N ψ z ∂volume = 0 := by
  have hfinite := shearCounterexample_divergence_finite N ψ hψ hψc
  rw [← hfinite]
  apply integral_congr_ae
  filter_upwards [] with z
  simp [finiteShearDivergenceResidual, shearCounterexampleVelocityPartial]

private theorem shearDivergenceResidual_integrable_on_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    [IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J))]
    [hOpen : OpensMeasurableSpace (Vec3 × ℝ)]
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (shearDivergenceResidual ψ)
      (volume.restrict (spaceTimeSet Ω' J)) := by
  let μ := volume.restrict (spaceTimeSet Ω' J)
  let D : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := spatialPartial_contDiff hψ 2
  have hDsupp : HasCompactSupport D := spatialPartial_hasCompactSupport hψ hψc 2
  have hDtop : MemLp D ⊤ μ := by
    exact @Continuous.memLp_top_of_hasCompactSupport ℝ _ (Vec3 × ℝ) _ _ hOpen D
      hD.continuous hDsupp μ
  have hW3 : MemLp shearFullScalar 3 μ :=
    shearFullScalar_memLp_on_localBox shearReducedBumpSeries_memLp_three hbox
  have hW2 : MemLp shearFullScalar 2 μ := hW3.mono_exponent (by norm_num)
  have hprod : MemLp (fun z => shearFullScalar z * D z) 2 μ := hW2.mul hDtop
  have hInt := hprod.integrable (q := 2) (by norm_num)
  change Integrable (fun z => shearFullScalar z * D z) μ
  exact hInt

theorem shearDivergenceResidual_integral_zero_of_local_support
    {Ω' : Set Vec3} {J : Set ℝ}
    [hOpen : OpensMeasurableSpace (Vec3 × ℝ)]
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (hS : MeasurableSet (spaceTimeSet Ω' J))
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψsub : tsupport ψ ⊆ spaceTimeSet Ω' J) :
    Integrable (shearDivergenceResidual ψ)
        (volume.restrict (spaceTimeSet Ω' J)) ∧
      ∫ z : Vec3 × ℝ, shearDivergenceResidual ψ z ∂volume = 0 := by
  let S : Set (Vec3 × ℝ) := Ω' ×ˢ J
  let μ : Measure (Vec3 × ℝ) := volume.restrict S
  have hSprod : MeasurableSet S := by
    change MeasurableSet (spaceTimeSet Ω' J)
    exact hS
  have hψsub' : tsupport ψ ⊆ S := by simpa [S, spaceTimeSet] using hψsub
  have hMajorant : Integrable (shearDivergenceMajorant ψ) μ := by
    let hμ : IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) :=
      shear_localBox_volume_restrict_finite hbox
    exact @shearDivergenceMajorant_integrable Ω' J hμ hOpen hbox ψ hψ hψc
  have hDom := finiteShearDivergenceResidual_bound_ae (Ω' := Ω') (J := J) ψ
  have hLim0 := finiteShearDivergenceResidual_tendsto_ae ψ
  have hLimμ : ∀ᵐ z ∂μ,
      Tendsto (fun N => finiteShearDivergenceResidual N ψ z) atTop
        (𝓝 (shearDivergenceResidual ψ z)) := by
    change ∀ᵐ z : Vec3 × ℝ ∂volume.restrict S,
      Tendsto (fun N => finiteShearDivergenceResidual N ψ z) atTop
        (𝓝 (shearDivergenceResidual ψ z))
    exact ae_restrict_of_ae hLim0
  have hDCT : Tendsto
      (fun N => ∫ z : Vec3 × ℝ, finiteShearDivergenceResidual N ψ z ∂μ)
      atTop (𝓝 (∫ z : Vec3 × ℝ, shearDivergenceResidual ψ z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (bound := shearDivergenceMajorant ψ)
    · intro N
      exact (finiteShearDivergenceResidual_continuous N ψ hψ).measurable.aestronglyMeasurable
    · exact hMajorant
    · exact hDom
    · exact hLimμ
  have hInt : Integrable (shearDivergenceResidual ψ) μ := by
    let hμ : IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) :=
      shear_localBox_volume_restrict_finite hbox
    exact @shearDivergenceResidual_integrable_on_localBox Ω' J hμ hOpen hbox ψ hψ hψc
  have hfinite (N : ℕ) :
      ∫ z : Vec3 × ℝ, finiteShearDivergenceResidual N ψ z ∂μ = 0 := by
    change ∫ z : Vec3 × ℝ in S, finiteShearDivergenceResidual N ψ z ∂volume = 0
    rw [divergence_setIntegral_eq_integral_of_support_subset hSprod
      ((subset_tsupport (finiteShearDivergenceResidual N ψ)).trans
        ((finiteShearDivergenceResidual_tsupport_subset N ψ hψ).trans hψsub'))]
    exact finiteShearDivergenceResidual_integral_zero N ψ hψ hψc
  have hzero : Tendsto
      (fun N => ∫ z : Vec3 × ℝ, finiteShearDivergenceResidual N ψ z ∂μ)
      atTop (𝓝 0) := by
    have heq : (fun N => ∫ z : Vec3 × ℝ,
        finiteShearDivergenceResidual N ψ z ∂μ) = fun _ => 0 := by
      funext N
      exact hfinite N
    rw [heq]
    exact tendsto_const_nhds
  have hint := tendsto_nhds_unique hzero hDCT
  have hμzero : ∫ z : Vec3 × ℝ, shearDivergenceResidual ψ z ∂μ = 0 := by
    simpa using hint.symm
  have hset := divergence_setIntegral_eq_integral_of_support_subset hSprod
    ((subset_tsupport (shearDivergenceResidual ψ)).trans
      ((shearDivergenceResidual_tsupport_subset ψ hψ).trans hψsub'))
  have hInt' : Integrable (shearDivergenceResidual ψ) μ := hInt
  change Integrable (shearDivergenceResidual ψ) μ at hInt'
  refine ⟨hInt', ?_⟩
  have hμzero' : ∫ z : Vec3 × ℝ in S, shearDivergenceResidual ψ z ∂volume = 0 := by
    change ∫ z : Vec3 × ℝ, shearDivergenceResidual ψ z ∂μ = 0 at hμzero
    exact hμzero
  exact hset.symm.trans hμzero'

end CKN
