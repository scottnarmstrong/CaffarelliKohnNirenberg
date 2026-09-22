-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.ReducedSpatialFinite
import CKN.Setting.Examples.ShearCounterexample.SliceFullWeak
import CKN.Setting.Examples.ShearCounterexample.FactorDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smoothness of finite shear approximations. -/

namespace CKN
open CKN.Foundation.Parabolic

theorem shearReducedBumpTerm_contDiff_full (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (shearReducedBumpTerm n) := by
  unfold shearReducedBumpTerm
  simpa [shearBumpField, smul_eq_mul] using
    (shearScaleBump_smooth_of_pos (shearScale_pos n)).const_smul (shearWeight n)

theorem shearReducedBumpPartial_contDiff (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (shearReducedBumpPartial N) := by
  unfold shearReducedBumpPartial
  apply ContDiff.sum
  intro n hn
  exact shearReducedBumpTerm_contDiff_full n

theorem shearFullScalarPartial_contDiff (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => shearFullScalarPartial N z) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun z : Vec3 × ℝ =>
      shearReducedBumpPartial N ((fun i : Fin 2 => z.1 i.castSucc), z.2))
  have hview : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => ((fun i : Fin 2 => z.1 i.castSucc), z.2)) := by
    fun_prop
  exact shearReducedBumpPartial_contDiff N |>.comp hview

private theorem shearSpatialProjection_basisVec (j : Fin 3) :
    shearSpatialProjectionDerivative (basisVec j) =
      if j = 0 then basisVec 0 else if j = 1 then basisVec 1 else 0 := by
  fin_cases j <;>
    ext i <;>
    fin_cases i <;>
    simp [shearSpatialProjectionDerivative, basisVec,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]

theorem shearFullScalarPartial_spatialPartial (N : ℕ)
    (z : Vec3 × ℝ) (j : Fin 3) :
    spatialPartial (show ParabolicPoint → ℝ from shearFullScalarPartial N) j z =
      if j = 0 then shearFullGradientPartial 0 N z else
        if j = 1 then shearFullGradientPartial 1 N z else 0 := by
  change fderiv ℝ (fun x : Vec3 => shearFullScalarPartial N (x, z.2))
      z.1 (basisVec j) = _
  let F : Vec2 → ℝ := fun y => shearReducedBumpPartial N (y, z.2)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    dsimp [F]
    exact shearReducedBumpPartial_contDiff N |>.comp (by fun_prop)
  have hFd : DifferentiableAt ℝ F (shearSpatialProjection z.1) :=
    (hF.differentiable (by simp)).differentiableAt
  have hcomp := hFd.hasFDerivAt.comp z.1
    (shearSpatialProjection_hasFDerivAt z.1)
  have hfun : (fun x : Vec3 => shearFullScalarPartial N (x, z.2)) =
      F ∘ shearSpatialProjection := by
    funext x
    rfl
  have hval : fderiv ℝ (fun x : Vec3 => shearFullScalarPartial N (x, z.2))
      z.1 (basisVec j) =
      fderiv ℝ F (shearSpatialProjection z.1)
        (shearSpatialProjectionDerivative (basisVec j)) := by
    rw [hfun, hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
  rw [hval, shearSpatialProjection_basisVec]
  by_cases h0 : j = 0
  · subst j
    change fderiv ℝ (fun y : Vec2 => shearReducedBumpPartial N (y, z.2))
        (shearSpatialProjection z.1) (basisVec 0) =
      shearReducedGradientPartial 0 N (shearSpatialProjection z.1, z.2)
    exact shearReducedBumpPartial_fderiv_apply N z.2 0 (shearSpatialProjection z.1)
  · by_cases h1 : j = 1
    · subst j
      change fderiv ℝ (fun y : Vec2 => shearReducedBumpPartial N (y, z.2))
          (shearSpatialProjection z.1) (basisVec 1) =
        shearReducedGradientPartial 1 N (shearSpatialProjection z.1, z.2)
      exact shearReducedBumpPartial_fderiv_apply N z.2 1 (shearSpatialProjection z.1)
    · simp [h0, h1]

end CKN
