-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.SliceDerivative
import CKN.Foundation.Sobolev.WeakDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # Weak spatial derivative identities for shear slices. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

def shearSpatialProjection (x : Vec3) : Vec2 := fun i => x i.castSucc

def shearSpatialProjectionDerivative : Vec3 →L[ℝ] Vec2 :=
  ContinuousLinearMap.pi (fun i : Fin 2 => ContinuousLinearMap.proj (i.castSucc))

theorem shearSpatialProjection_hasFDerivAt (x : Vec3) :
    HasFDerivAt shearSpatialProjection shearSpatialProjectionDerivative x := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact hasFDerivAt_apply (𝕜 := ℝ) (i.castSucc) x

theorem shearFullSlice_fderiv_eq_Du {t : ℝ} (ht : t ≠ 0)
    (x : Vec3) (j : Fin 3) :
    fderiv ℝ (fun y : Vec3 => shearCounterexampleVelocity ((y, t) : ParabolicPoint) 2) x
        (basisVec j) = shearCounterexampleDu ((x, t) : ParabolicPoint) 2 j := by
  let F : Vec2 → ℝ := fun y => shearReducedBumpSeries (y, t)
  let P : Vec3 → Vec2 := shearSpatialProjection
  have hFcont : ContDiff ℝ (⊤ : ℕ∞) F := by
    exact shearFullSlice_smooth_of_time_nezero ht
  have hFd : DifferentiableAt ℝ F (P x) :=
    (hFcont.differentiable (by simp)).differentiableAt
  have hcomp := hFd.hasFDerivAt.comp x (shearSpatialProjection_hasFDerivAt x)
  change fderiv ℝ (F ∘ P) x (basisVec j) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  fin_cases j
  · change (fderiv ℝ F (P x)) (shearSpatialProjectionDerivative (basisVec 0)) = _
    have hp : shearSpatialProjectionDerivative (basisVec 0) = basisVec 0 := by
      ext i
      fin_cases i <;>
        simp [shearSpatialProjectionDerivative, basisVec,
          ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    rw [hp]
    have hf := shearReducedSlice_deriv_eq_gradient ht (P x) 0
    change (fderiv ℝ F (P x)) (basisVec 0) = shearReducedGradientSeries 0 (P x, t)
    exact hf
  · change (fderiv ℝ F (P x)) (shearSpatialProjectionDerivative (basisVec 1)) = _
    have hp : shearSpatialProjectionDerivative (basisVec 1) = basisVec 1 := by
      ext i
      fin_cases i <;>
        simp [shearSpatialProjectionDerivative, basisVec,
          ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    rw [hp]
    have hf := shearReducedSlice_deriv_eq_gradient ht (P x) 1
    change (fderiv ℝ F (P x)) (basisVec 1) = shearReducedGradientSeries 1 (P x, t)
    exact hf
  · change (fderiv ℝ F (P x)) (shearSpatialProjectionDerivative (basisVec 2)) = _
    have hp : shearSpatialProjectionDerivative (basisVec 2) = 0 := by
      ext i
      fin_cases i <;>
        simp [shearSpatialProjectionDerivative, basisVec,
          ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    rw [hp]
    simp [P, shearCounterexampleDu]

theorem shearCounterexampleSlice_hasWeakGradient_of_time_nezero {t : ℝ} (ht : t ≠ 0) :
    ∀ i : Fin 3,
      HasWeakGradientOn Set.univ
        (fun x : Vec3 => shearCounterexampleVelocity (x, t) i)
        (fun x j => shearCounterexampleDu (x, t) i j) := by
  intro i
  fin_cases i
  · have h := HasWeakGradientOn.of_contDiff (U := (Set.univ : Set Vec3))
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec3 => (0 : ℝ)))
    simpa [shearCounterexampleVelocity, shearCounterexampleDu] using h
  · have h := HasWeakGradientOn.of_contDiff (U := (Set.univ : Set Vec3))
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec3 => (0 : ℝ)))
    simpa [shearCounterexampleVelocity, shearCounterexampleDu] using h
  · have hcont : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => shearCounterexampleVelocity ((x, t) : ParabolicPoint) 2) := by
      have hred : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Vec2 => shearReducedBumpSeries (y, t)) :=
        shearFullSlice_smooth_of_time_nezero ht
      have hproj : ContDiff ℝ (⊤ : ℕ∞) shearSpatialProjection := by
        fun_prop [shearSpatialProjection]
      change ContDiff ℝ (⊤ : ℕ∞)
        ((fun y : Vec2 => shearReducedBumpSeries (y, t)) ∘ shearSpatialProjection)
      exact hred.comp hproj
    have hweak := HasWeakGradientOn.of_contDiff
      (U := (Set.univ : Set Vec3)) (hcont.of_le (by simp))
    have heq : (fun x j => (fderiv ℝ
        (fun y : Vec3 => shearCounterexampleVelocity ((y, t) : ParabolicPoint) 2) x)
        (basisVec j)) =
        (fun x j => shearCounterexampleDu ((x, t) : ParabolicPoint) 2 j) := by
      funext x j
      exact shearFullSlice_fderiv_eq_Du ht x j
    simpa [heq] using hweak

theorem shearCounterexampleSlice_hasWeakGradientOn_of_time_nezero
    {Ω' : Set Vec3} (hΩ' : IsOpen Ω') (t : ℝ) (ht : t ≠ 0) :
    ∀ i : Fin 3,
      HasWeakGradientOn Ω'
        (fun x : Vec3 => shearCounterexampleVelocity (x, t) i)
        (fun x j => shearCounterexampleDu (x, t) i j) := by
  intro i
  exact HasWeakGradientOn.restrict hΩ' (Set.subset_univ Ω')
    (shearCounterexampleSlice_hasWeakGradient_of_time_nezero ht i)

end CKN
