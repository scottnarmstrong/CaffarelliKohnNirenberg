-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Examples.ShearCounterexample.MomentumMajorant
import CKN.Setting.Examples.ShearCounterexample.FiniteMomentumIntegral
import CKN.Setting.Examples.ShearCounterexample.SeriesApprox
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Distributional momentum identities for the rough parabolic shear. -/

set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped Topology
namespace CKN

private def finiteMomentumResidual (N : ℕ) (φ : Vec3 × ℝ → Vec3)
    (z : Vec3 × ℝ) : ℝ :=
  -(shearFullScalarPartial N z * timePartial (fun w => φ w 2) z)
    - shearFullScalarPartial N z ^ 2 * spatialPartial (fun w => φ w 2) 2 z
    + shearFullGradientPartial 0 N z * spatialPartial (fun w => φ w 2) 0 z
    + shearFullGradientPartial 1 N z * spatialPartial (fun w => φ w 2) 1 z
    - shearFullForcePartial N z * φ z 2

def fullMomentumResidual (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : ℝ :=
  -(shearFullScalar z * timePartial (fun w => φ w 2) z)
    - shearFullScalar z ^ 2 * spatialPartial (fun w => φ w 2) 2 z
    + shearFullGradient 0 z * spatialPartial (fun w => φ w 2) 0 z
    + shearFullGradient 1 z * spatialPartial (fun w => φ w 2) 1 z
    - shearFullForceScalar z * φ z 2

private theorem finiteMomentumResidual_continuous (N : ℕ)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (finiteMomentumResidual N φ) := by
  unfold finiteMomentumResidual
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => φ z 2) :=
    component_contDiff hφ 2
  have hPT : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial (fun w => φ w 2) z) :=
    timePartial_contDiff hP
  have hP0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => φ w 2) 0 z) :=
    spatialPartial_contDiff hP 0
  have hP1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => φ w 2) 1 z) :=
    spatialPartial_contDiff hP 1
  have hP2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => φ w 2) 2 z) :=
    spatialPartial_contDiff hP 2
  have hW : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => shearFullScalarPartial N z) :=
    shearFullScalarPartial_contDiff N
  have hG0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => shearFullGradientPartial 0 N z) :=
    shearFullGradientPartial_contDiff N 0
  have hG1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => shearFullGradientPartial 1 N z) :=
    shearFullGradientPartial_contDiff N 1
  have hF : Continuous (fun z : Vec3 × ℝ => shearFullForcePartial N z) := by
    have hh : Continuous (fun z : Vec3 × ℝ =>
        shearFullForcePartial N (parabolicHomeomorph.symm z)) :=
      (shearFullForcePartial_continuous N).comp parabolicHomeomorph.continuous_invFun
    have heq : (fun z : Vec3 × ℝ => shearFullForcePartial N z) =
        fun z => shearFullForcePartial N (parabolicHomeomorph.symm z) := by
      funext z
      cases z
      rfl
    rw [heq]
    exact hh
  fun_prop

private theorem finiteMomentumResidual_measurable (N : ℕ)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    [OpensMeasurableSpace (Vec3 × ℝ)] :
    Measurable (finiteMomentumResidual N φ) :=
  (finiteMomentumResidual_continuous N φ hφ).measurable

private theorem fullMomentumResidual_measurable (φ : Vec3 × ℝ → Vec3)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Measurable (fullMomentumResidual φ) := by
  unfold fullMomentumResidual
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => φ z 2) :=
    component_contDiff hφ 2
  have hPm : Measurable (fun z : Vec3 × ℝ => φ z 2) := hP.continuous.measurable
  have hPT : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial (fun w => φ w 2) z) :=
    timePartial_contDiff hP
  have hP0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => φ w 2) 0 z) :=
    spatialPartial_contDiff hP 0
  have hP1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => φ w 2) 1 z) :=
    spatialPartial_contDiff hP 1
  have hP2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => φ w 2) 2 z) :=
    spatialPartial_contDiff hP 2
  have hPTm : Measurable (fun z : Vec3 × ℝ =>
      timePartial (fun w => φ w 2) z) := hPT.continuous.measurable
  have hP0m : Measurable (fun z : Vec3 × ℝ =>
      spatialPartial (fun w => φ w 2) 0 z) := hP0.continuous.measurable
  have hP1m : Measurable (fun z : Vec3 × ℝ =>
      spatialPartial (fun w => φ w 2) 1 z) := hP1.continuous.measurable
  have hP2m : Measurable (fun z : Vec3 × ℝ =>
      spatialPartial (fun w => φ w 2) 2 z) := hP2.continuous.measurable
  have hWm : Measurable (fun z : Vec3 × ℝ => shearFullScalar z) := by
    change Measurable shearFullScalar
    exact shearFullScalar_measurable
  have hG0m : Measurable (fun z : Vec3 × ℝ => shearFullGradient 0 z) := by
    change Measurable (shearFullGradient 0)
    exact shearFullGradient_measurable 0
  have hG1m : Measurable (fun z : Vec3 × ℝ => shearFullGradient 1 z) := by
    change Measurable (shearFullGradient 1)
    exact shearFullGradient_measurable 1
  have hFm : Measurable (fun z : Vec3 × ℝ => shearFullForceScalar z) := by
    change Measurable shearFullForceScalar
    exact shearFullForceScalar_measurable
  have hPmeas : Measurable (fun z : Vec3 × ℝ => φ z 2) := hPm
  fun_prop

private theorem momentumTestComponent_zero_of_not_tsupport
    (φ : Vec3 × ℝ → Vec3) {z : Vec3 × ℝ} (hz : z ∉ tsupport φ) :
    φ z 2 = 0 := by
  by_contra hne
  have hvec : φ z ≠ 0 := by
    intro hz0
    apply hne
    rw [hz0]
    simp
  exact hz (subset_tsupport φ (Function.mem_support.mpr hvec))

private theorem momentumTestTime_zero_of_not_tsupport
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport φ) :
    timePartial (fun w => φ w 2) z = 0 := by
  let P : Vec3 × ℝ → ℝ := fun w => φ w 2
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := component_contDiff hφ 2
  have hcomp : tsupport P ⊆ tsupport φ := by
    change tsupport ((fun v : Vec3 => v 2) ∘ φ) ⊆ tsupport φ
    exact tsupport_comp_subset (g := fun v : Vec3 => v 2) (by simp) φ
  have hEq : timePartial P z = fderiv ℝ P z ((0 : Vec3), (1 : ℝ)) := by
    exact timePartial_eq_joint_fderiv hP z
  have hder : fderiv ℝ P z ((0 : Vec3), (1 : ℝ)) = 0 := by
    by_contra hne
    let D : Vec3 × ℝ → ℝ := fun w => fderiv ℝ P w ((0 : Vec3), (1 : ℝ))
    have hne' : D z ≠ 0 := by simpa [D] using hne
    have hsupp : z ∈ Function.support D := Function.mem_support.mpr hne'
    have hmem : z ∈ tsupport D := subset_tsupport D hsupp
    have hsub := (tsupport_fderiv_apply_subset ℝ ((0 : Vec3), (1 : ℝ))).trans hcomp
    exact hz (hsub hmem)
  change timePartial P z = 0
  rw [hEq, hder]

private theorem momentumTestSpace_zero_of_not_tsupport
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin 3)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport φ) :
    spatialPartial (fun w => φ w 2) i z = 0 := by
  let P : Vec3 × ℝ → ℝ := fun w => φ w 2
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := component_contDiff hφ 2
  have hcomp : tsupport P ⊆ tsupport φ :=
    tsupport_comp_subset (g := fun v : Vec3 => v 2) (by simp) φ
  have hEq : spatialPartial P i z = fderiv ℝ P z (basisVec i, (0 : ℝ)) := by
    exact spatialPartial_eq_joint_fderiv hP z i
  have hder : fderiv ℝ P z (basisVec i, (0 : ℝ)) = 0 := by
    by_contra hne
    let D : Vec3 × ℝ → ℝ := fun w => fderiv ℝ P w (basisVec i, (0 : ℝ))
    have hne' : D z ≠ 0 := by simpa [D] using hne
    have hsupp : z ∈ Function.support D := Function.mem_support.mpr hne'
    have hmem : z ∈ tsupport D := subset_tsupport D hsupp
    have hsub := (tsupport_fderiv_apply_subset ℝ (basisVec i, (0 : ℝ))).trans hcomp
    exact hz (hsub hmem)
  change spatialPartial P i z = 0
  rw [hEq, hder]

private theorem finiteMomentumResidual_eq_zero_of_not_tsupport (N : ℕ)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport φ) :
    finiteMomentumResidual N φ z = 0 := by
  simp [finiteMomentumResidual, momentumTestComponent_zero_of_not_tsupport φ hz,
    momentumTestTime_zero_of_not_tsupport φ hφ hz,
    momentumTestSpace_zero_of_not_tsupport φ hφ 0 hz,
    momentumTestSpace_zero_of_not_tsupport φ hφ 1 hz,
    momentumTestSpace_zero_of_not_tsupport φ hφ 2 hz]

private theorem fullMomentumResidual_eq_zero_of_not_tsupport
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport φ) :
    fullMomentumResidual φ z = 0 := by
  simp [fullMomentumResidual, momentumTestComponent_zero_of_not_tsupport φ hz,
    momentumTestTime_zero_of_not_tsupport φ hφ hz,
    momentumTestSpace_zero_of_not_tsupport φ hφ 0 hz,
    momentumTestSpace_zero_of_not_tsupport φ hφ 1 hz,
    momentumTestSpace_zero_of_not_tsupport φ hφ 2 hz]

private theorem finiteMomentumResidual_tsupport_subset (N : ℕ)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    tsupport (finiteMomentumResidual N φ) ⊆ tsupport φ := by
  have hsupp : Function.support (finiteMomentumResidual N φ) ⊆ tsupport φ := by
    intro z hz
    by_contra hzφ
    exact (Function.mem_support.mp hz)
      (finiteMomentumResidual_eq_zero_of_not_tsupport N φ hφ hzφ)
  change closure (Function.support (finiteMomentumResidual N φ)) ⊆ tsupport φ
  exact closure_minimal hsupp (isClosed_tsupport φ)

theorem fullMomentumResidual_tsupport_subset
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    tsupport (fullMomentumResidual φ) ⊆ tsupport φ := by
  have hsupp : Function.support (fullMomentumResidual φ) ⊆ tsupport φ := by
    intro z hz
    by_contra hzφ
    exact (Function.mem_support.mp hz)
      (fullMomentumResidual_eq_zero_of_not_tsupport φ hφ hzφ)
  change closure (Function.support (fullMomentumResidual φ)) ⊆ tsupport φ
  exact closure_minimal hsupp (isClosed_tsupport φ)

private theorem setIntegral_eq_integral_of_support_subset
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

private theorem finiteMomentumResidual_integral_zero (N : ℕ)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    ∫ z : Vec3 × ℝ, finiteMomentumResidual N φ z ∂volume = 0 := by
  have hfinite := shearCounterexample_momentum_finite N φ hφ hφc
  rw [← hfinite]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [shearFiniteMomentumResidual_simplify N φ z]
  simp [finiteMomentumResidual, shearCounterexampleDuPartial, Fin.sum_univ_succ]
  ring

private theorem abs_five_add_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  calc
    |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
    _ ≤ (|a + b + c| + |d|) + |e| := by gcongr; exact abs_add_le _ _
    _ ≤ (|a + b| + |c| + |d|) + |e| := by gcongr; exact abs_add_le _ _
    _ ≤ (|a| + |b| + |c| + |d|) + |e| := by gcongr; exact abs_add_le _ _

private theorem finiteMomentumResidual_bound_ae
    {Ω' : Set Vec3} {J : Set ℝ} (φ : Vec3 × ℝ → Vec3) :
    ∀ N, ∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω' J)),
      ‖finiteMomentumResidual N φ z‖ ≤ shearMomentumMajorant φ z := by
  let μ := volume.restrict (spaceTimeSet Ω' J)
  have hW0 : ∀ᵐ z ∂volume, 0 ≤ shearFullScalar z := by
    filter_upwards [shearFullScalarPartial_le_ae 0] with z hz
    have hpart := shearCounterexampleVelocityPartial_nonneg 0 z
    exact le_trans hpart hz
  have hW0μ := ae_restrict_of_ae (s := spaceTimeSet Ω' J) hW0
  intro N
  have hWle := ae_restrict_of_ae (s := spaceTimeSet Ω' J)
    (shearFullScalarPartial_le_ae N)
  filter_upwards [hW0μ, hWle] with z hW0z hWlez
  have hWN : 0 ≤ shearFullScalarPartial N z :=
    shearCounterexampleVelocityPartial_nonneg N z
  have hW : 0 ≤ shearFullScalar z := hW0z
  have hWabs : |shearFullScalarPartial N z| ≤ |shearFullScalar z| := by
    rw [abs_of_nonneg hWN, abs_of_nonneg hW]
    exact hWlez
  have hWsq : |shearFullScalarPartial N z| ^ 2 ≤ |shearFullScalar z| ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 hWabs
  have hG0 := shearFullGradientPartial_abs_le 0 N z
  have hG1 := shearFullGradientPartial_abs_le 1 N z
  have hF := shearFullForcePartial_abs_le N z
  let P : Vec3 × ℝ → ℝ := fun w => φ w 2
  let PT : Vec3 × ℝ → ℝ := fun w => timePartial (fun v => φ v 2) w
  let P0 : Vec3 × ℝ → ℝ := fun w => spatialPartial (fun v => φ v 2) 0 w
  let P1 : Vec3 × ℝ → ℝ := fun w => spatialPartial (fun v => φ v 2) 1 w
  let P2 : Vec3 × ℝ → ℝ := fun w => spatialPartial (fun v => φ v 2) 2 w
  let A := -(shearFullScalarPartial N z * PT z)
  let B := -(shearFullScalarPartial N z ^ 2 * P2 z)
  let C := shearFullGradientPartial 0 N z * P0 z
  let D := shearFullGradientPartial 1 N z * P1 z
  let E := -(shearFullForcePartial N z * P z)
  have hA : |A| ≤ |shearFullScalar z| * |PT z| := by
    dsimp [A]
    rw [abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_right hWabs (abs_nonneg _)
  have hB : |B| ≤ |shearFullScalar z| ^ 2 * |P2 z| := by
    dsimp [B]
    rw [abs_neg, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right hWsq (abs_nonneg _)
  have hC : |C| ≤ |shearFullGradient 0 z| * |P0 z| := by
    dsimp [C]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hG0 (abs_nonneg _)
  have hD : |D| ≤ |shearFullGradient 1 z| * |P1 z| := by
    dsimp [D]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hG1 (abs_nonneg _)
  have hE : |E| ≤ |shearFullForceScalar z| * |P z| := by
    dsimp [E]
    rw [abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_right hF (abs_nonneg _)
  have hsum := abs_five_add_le A B C D E
  change |A + B + C + D + E| ≤ _ at hsum
  change ‖finiteMomentumResidual N φ z‖ ≤ _
  rw [Real.norm_eq_abs]
  have hres : finiteMomentumResidual N φ z = A + B + C + D + E := by
    dsimp [finiteMomentumResidual, A, B, C, D, E, P, PT, P0, P1, P2]
    ring
  rw [hres]
  calc
    |A + B + C + D + E| ≤ |A| + |B| + |C| + |D| + |E| := hsum
    _ ≤ |shearFullScalar z| * |PT z| +
        |shearFullScalar z| ^ 2 * |P2 z| +
        |shearFullGradient 0 z| * |P0 z| +
        |shearFullGradient 1 z| * |P1 z| +
        |shearFullForceScalar z| * |P z| := by
      gcongr
    _ = shearMomentumMajorant φ z := by rfl

private theorem finiteMomentumResidual_tendsto_ae
    (φ : Vec3 × ℝ → Vec3) :
    ∀ᵐ z : ParabolicPoint ∂volume,
      Tendsto (fun N => finiteMomentumResidual N φ z) atTop
        (𝓝 (fullMomentumResidual φ z)) := by
  filter_upwards [shearFullScalarPartial_tendsto_ae,
    shearFullGradientPartial_tendsto_ae 0,
    shearFullGradientPartial_tendsto_ae 1,
    shearFullForcePartial_tendsto_ae] with z hW hG0 hG1 hF
  let PT := timePartial (fun w => φ w 2) z
  let P0 := spatialPartial (fun w => φ w 2) 0 z
  let P1 := spatialPartial (fun w => φ w 2) 1 z
  let P2 := spatialPartial (fun w => φ w 2) 2 z
  let P := φ z 2
  have hA : Tendsto (fun N => -(shearFullScalarPartial N z * PT)) atTop
      (𝓝 (-(shearFullScalar z * PT))) :=
    (hW.mul tendsto_const_nhds).neg
  have hB : Tendsto (fun N => -(shearFullScalarPartial N z ^ 2 * P2)) atTop
      (𝓝 (-(shearFullScalar z ^ 2 * P2))) :=
    ((hW.pow 2).mul tendsto_const_nhds).neg
  have hC : Tendsto (fun N => shearFullGradientPartial 0 N z * P0) atTop
      (𝓝 (shearFullGradient 0 z * P0)) := hG0.mul tendsto_const_nhds
  have hD : Tendsto (fun N => shearFullGradientPartial 1 N z * P1) atTop
      (𝓝 (shearFullGradient 1 z * P1)) := hG1.mul tendsto_const_nhds
  have hE : Tendsto (fun N => -(shearFullForcePartial N z * P)) atTop
      (𝓝 (-(shearFullForceScalar z * P))) :=
    (hF.mul tendsto_const_nhds).neg
  have hsum := (((hA.add hB).add hC).add hD).add hE
  simpa [finiteMomentumResidual, fullMomentumResidual, PT, P0, P1, P2, P,
    sub_eq_add_neg, add_assoc] using hsum

set_option linter.style.haveILetI false in
theorem fullMomentumResidual_integral_zero_of_local_support
    {Ω' : Set Vec3} {J : Set ℝ}
    [hOpen : OpensMeasurableSpace (Vec3 × ℝ)]
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (hS : MeasurableSet (spaceTimeSet Ω' J))
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ)
    (hφsub : tsupport φ ⊆ spaceTimeSet Ω' J) :
    ∫ z : Vec3 × ℝ, fullMomentumResidual φ z ∂volume = 0 := by
  letI : OpensMeasurableSpace (Vec3 × ℝ) := hOpen
  let S : Set (Vec3 × ℝ) := Ω' ×ˢ J
  let μ : Measure (Vec3 × ℝ) := volume.restrict S
  have hSprod : MeasurableSet S := by
    change MeasurableSet (spaceTimeSet Ω' J)
    exact hS
  have hφsub' : tsupport φ ⊆ S := by
    simpa [S, spaceTimeSet] using hφsub
  have hMajorant : Integrable (shearMomentumMajorant φ) μ := by
    exact shearMomentumMajorant_integrable_on_localBox hbox φ hφ hφc
  have hDom := finiteMomentumResidual_bound_ae (Ω' := Ω') (J := J) φ
  have hLim0 := finiteMomentumResidual_tendsto_ae φ
  have hLimμ : ∀ᵐ z ∂μ,
      Tendsto (fun N => finiteMomentumResidual N φ z) atTop
        (𝓝 (fullMomentumResidual φ z)) := by
    change ∀ᵐ z : Vec3 × ℝ ∂volume.restrict S,
      Tendsto (fun N => finiteMomentumResidual N φ z) atTop
        (𝓝 (fullMomentumResidual φ z))
    exact ae_restrict_of_ae hLim0
  have hDCT : Tendsto
      (fun N => ∫ z : Vec3 × ℝ, finiteMomentumResidual N φ z ∂μ)
      atTop (𝓝 (∫ z : Vec3 × ℝ, fullMomentumResidual φ z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (bound := shearMomentumMajorant φ)
    · intro N
      exact (finiteMomentumResidual_measurable N φ hφ).aestronglyMeasurable
    · exact hMajorant
    · exact hDom
    · exact hLimμ
  have hfinite (N : ℕ) :
      ∫ z : Vec3 × ℝ, finiteMomentumResidual N φ z ∂μ = 0 := by
    change ∫ z : Vec3 × ℝ in S, finiteMomentumResidual N φ z ∂volume = 0
    rw [setIntegral_eq_integral_of_support_subset hSprod
      ((subset_tsupport (finiteMomentumResidual N φ)).trans
        ((finiteMomentumResidual_tsupport_subset N φ hφ).trans hφsub'))]
    exact finiteMomentumResidual_integral_zero N φ hφ hφc
  have hzero : Tendsto
      (fun N => ∫ z : Vec3 × ℝ, finiteMomentumResidual N φ z ∂μ)
      atTop (𝓝 0) := by
    have heq : (fun N => ∫ z : Vec3 × ℝ,
        finiteMomentumResidual N φ z ∂μ) = fun _ => 0 := by
      funext N
      exact hfinite N
    rw [heq]
    exact tendsto_const_nhds
  have hint := tendsto_nhds_unique hzero hDCT
  have hfull_zero : ∫ z : Vec3 × ℝ, fullMomentumResidual φ z ∂μ = 0 := by
    simpa using hint.symm
  have hset := setIntegral_eq_integral_of_support_subset hSprod
    ((subset_tsupport (fullMomentumResidual φ)).trans
      ((fullMomentumResidual_tsupport_subset φ hφ).trans hφsub'))
  change ∫ z : Vec3 × ℝ in S, fullMomentumResidual φ z ∂volume = 0 at hfull_zero
  exact hset.symm.trans hfull_zero

set_option linter.style.haveILetI false in
theorem fullMomentumResidual_integrable_on_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    [hOpen : OpensMeasurableSpace (Vec3 × ℝ)]
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
      Integrable (fullMomentumResidual φ)
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hOpen_nonempty : Nonempty (OpensMeasurableSpace (Vec3 × ℝ)) := ⟨hOpen⟩
  cases hOpen_nonempty
  have hMajorant := shearMomentumMajorant_integrable_on_localBox hbox φ hφ hφc
  have hBound : ∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω' J)),
      ‖fullMomentumResidual φ z‖ ≤ shearMomentumMajorant φ z := by
    filter_upwards [] with z
    let P : Vec3 × ℝ → ℝ := fun w => φ w 2
    let PT : Vec3 × ℝ → ℝ := fun w => timePartial (fun v => φ v 2) w
    let P0 : Vec3 × ℝ → ℝ := fun w => spatialPartial (fun v => φ v 2) 0 w
    let P1 : Vec3 × ℝ → ℝ := fun w => spatialPartial (fun v => φ v 2) 1 w
    let P2 : Vec3 × ℝ → ℝ := fun w => spatialPartial (fun v => φ v 2) 2 w
    let A := -(shearFullScalar z * PT z)
    let B := -(shearFullScalar z ^ 2 * P2 z)
    let C := shearFullGradient 0 z * P0 z
    let D := shearFullGradient 1 z * P1 z
    let E := -(shearFullForceScalar z * P z)
    have hsum := abs_five_add_le A B C D E
    change |A + B + C + D + E| ≤ _ at hsum
    change ‖fullMomentumResidual φ z‖ ≤ _
    rw [Real.norm_eq_abs]
    have hres : fullMomentumResidual φ z = A + B + C + D + E := by
      dsimp [fullMomentumResidual, A, B, C, D, E, P, PT, P0, P1, P2]
      ring
    rw [hres]
    calc
      |A + B + C + D + E| ≤ |A| + |B| + |C| + |D| + |E| := hsum
      _ = |shearFullScalar z| * |PT z| +
          |shearFullScalar z| ^ 2 * |P2 z| +
          |shearFullGradient 0 z| * |P0 z| +
          |shearFullGradient 1 z| * |P1 z| +
          |shearFullForceScalar z| * |P z| := by
        simp only [A, B, C, D, E, abs_neg, abs_mul, abs_pow]
      _ = shearMomentumMajorant φ z := by rfl
  exact hMajorant.mono'
    (fullMomentumResidual_measurable φ hφ).aestronglyMeasurable hBound

end CKN
