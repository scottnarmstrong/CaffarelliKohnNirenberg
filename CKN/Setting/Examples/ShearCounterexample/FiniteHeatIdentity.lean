-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Examples.ShearCounterexample.ReducedFiniteDerivatives
import CKN.Setting.Examples.ShearCounterexample.FactorDerivative
import CKN.Statements.SpatialSecondPartial

/-! # Finite-scale heat identities for the shear profile. -/

set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Finset
namespace CKN

theorem shearReducedGradientPartial_contDiff (N : ℕ) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec 2 × ℝ => shearReducedGradientPartial i N z) := by
  unfold shearReducedGradientPartial
  apply ContDiff.sum
  intro n hn
  exact shearReducedGradientTerm_contDiff_full i n

theorem shearReducedBumpPartial_timeDerivative (N : ℕ) (x : Vec 2) (t : ℝ) :
    fderiv ℝ (fun s : ℝ => shearReducedBumpPartial N (x, s)) t 1 =
      ∑ n ∈ Finset.range N,
        shearWeight n * shearTimeFirstField (shearScale n) (x, t) := by
  have hfun : (fun s : ℝ => shearReducedBumpPartial N (x, s)) =
      fun s => ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, s) := by
    rfl
  have hcurve (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => shearReducedBumpTerm n (x, s)) := by
    have hembed : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (x, s)) := by fun_prop
    exact (shearReducedBumpTerm_contDiff_full n).comp hembed
  have hderiv : HasFDerivAt
      (fun s : ℝ => ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, s))
      (∑ n ∈ Finset.range N,
        fderiv ℝ (fun s : ℝ => shearReducedBumpTerm n (x, s)) t) t := by
    rw [show (fun s : ℝ => ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, s)) =
        ∑ n ∈ Finset.range N, fun s => shearReducedBumpTerm n (x, s) by
      funext s
      simp]
    apply HasFDerivAt.sum
    intro n hn
    have hd : DifferentiableAt ℝ (fun s : ℝ => shearReducedBumpTerm n (x, s)) t :=
      ((hcurve n).differentiable (by simp)).differentiableAt
    exact hd.hasFDerivAt
  rw [hfun, hderiv.fderiv]
  rw [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact shearReducedBumpTerm_timeDerivative n x t

theorem shearReducedGradientPartial_spatialDerivative (N : ℕ) (i : Fin 2)
    (x : Vec 2) (t : ℝ) :
    fderiv ℝ (fun y : Vec 2 => shearReducedGradientPartial i N (y, t)) x
        (basisVec i) =
      ∑ n ∈ Finset.range N,
        shearWeight n * shearSpatialSecondField (shearScale n) i (x, t) := by
  have hcurve (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => shearReducedGradientTerm i n (y, t)) := by
    have hembed : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (y, t)) := by fun_prop
    exact (shearReducedGradientTerm_contDiff_full i n).comp hembed
  have hderiv : HasFDerivAt
      (fun y : Vec 2 => ∑ n ∈ Finset.range N, shearReducedGradientTerm i n (y, t))
      (∑ n ∈ Finset.range N,
        fderiv ℝ (fun y : Vec 2 => shearReducedGradientTerm i n (y, t)) x) x := by
    rw [show (fun y : Vec 2 => ∑ n ∈ Finset.range N,
        shearReducedGradientTerm i n (y, t)) =
        ∑ n ∈ Finset.range N, fun y => shearReducedGradientTerm i n (y, t) by
      funext y
      simp]
    apply HasFDerivAt.sum
    intro n hn
    have hd : DifferentiableAt ℝ
        (fun y : Vec 2 => shearReducedGradientTerm i n (y, t)) x :=
      ((hcurve n).differentiable (by simp)).differentiableAt
    exact hd.hasFDerivAt
  change fderiv ℝ
    (fun y : Vec 2 => ∑ n ∈ Finset.range N, shearReducedGradientTerm i n (y, t))
    x (basisVec i) = _
  rw [hderiv.fderiv]
  rw [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact shearReducedGradientTerm_spatialDerivative i n x t

theorem shearReducedBumpPartial_laplacian (N : ℕ) (z : Vec 2 × ℝ) :
    (∑ i : Fin 2,
      fderiv ℝ (fun x : Vec 2 =>
        fderiv ℝ (fun y : Vec 2 => shearReducedBumpPartial N (y, z.2)) x
          (basisVec i)) z.1 (basisVec i)) =
      (∑ n ∈ Finset.range N,
        shearWeight n * shearSpatialSecondField (shearScale n) 0 z) +
      (∑ n ∈ Finset.range N,
        shearWeight n * shearSpatialSecondField (shearScale n) 1 z) := by
  have hspace (i : Fin 2) :
      fderiv ℝ (fun x : Vec 2 =>
        fderiv ℝ (fun y : Vec 2 => shearReducedBumpPartial N (y, z.2)) x
          (basisVec i)) z.1 (basisVec i) =
        ∑ n ∈ Finset.range N,
          shearWeight n * shearSpatialSecondField (shearScale n) i z := by
    have hfirst : (fun x : Vec 2 =>
        fderiv ℝ (fun y : Vec 2 => shearReducedBumpPartial N (y, z.2)) x
          (basisVec i)) =
        fun x => shearReducedGradientPartial i N (x, z.2) := by
      funext x
      exact shearReducedBumpPartial_fderiv_apply N z.2 i x
    rw [hfirst]
    exact shearReducedGradientPartial_spatialDerivative N i z.1 z.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rw [hspace 0, hspace (Fin.succ 0)]
  rw [show Fin.succ (0 : Fin 1) = (1 : Fin 2) by rfl]

theorem shearReducedBumpPartial_heat_identity (N : ℕ) (z : Vec 2 × ℝ) :
    fderiv ℝ (fun t : ℝ => shearReducedBumpPartial N (z.1, t)) z.2 1 -
      ∑ i : Fin 2,
        fderiv ℝ (fun x : Vec 2 =>
          fderiv ℝ (fun y : Vec 2 => shearReducedBumpPartial N (y, z.2)) x
            (basisVec i)) z.1 (basisVec i) =
      shearReducedForcePartial N z := by
  have ht := shearReducedBumpPartial_timeDerivative N z.1 z.2
  rw [ht, shearReducedBumpPartial_laplacian N z]
  have hsumForce :
      (∑ n ∈ Finset.range N,
        shearWeight n * shearTimeFirstField (shearScale n) (z.1, z.2)) -
        ((∑ n ∈ Finset.range N,
          shearWeight n * shearSpatialSecondField (shearScale n) 0 (z.1, z.2)) +
         (∑ n ∈ Finset.range N,
          shearWeight n * shearSpatialSecondField (shearScale n) 1 (z.1, z.2))) =
      ∑ n ∈ Finset.range N, shearWeight n *
        (shearTimeFirstField (shearScale n) (z.1, z.2) -
          shearSpatialSecondField (shearScale n) 0 (z.1, z.2) -
          shearSpatialSecondField (shearScale n) 1 (z.1, z.2)) := by
    symm
    calc
      _ = ∑ n ∈ Finset.range N,
          (shearWeight n * shearTimeFirstField (shearScale n) (z.1, z.2) -
            (shearWeight n * shearSpatialSecondField (shearScale n) 0 (z.1, z.2) +
             shearWeight n * shearSpatialSecondField (shearScale n) 1 (z.1, z.2))) := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = (∑ n ∈ Finset.range N,
          shearWeight n * shearTimeFirstField (shearScale n) (z.1, z.2)) -
          ∑ n ∈ Finset.range N,
            (shearWeight n * shearSpatialSecondField (shearScale n) 0 (z.1, z.2) +
             shearWeight n * shearSpatialSecondField (shearScale n) 1 (z.1, z.2)) :=
        by rw [Finset.sum_sub_distrib]
      _ = _ := by rw [Finset.sum_add_distrib]
  simpa [shearReducedForcePartial, shearReducedForceTerm,
    shearReducedForceCore, smul_eq_mul] using hsumForce

theorem shearFullGradientPartial_contDiff (N : ℕ) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => shearFullGradientPartial i N z) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun z : Vec3 × ℝ =>
      shearReducedGradientPartial i N ((fun j : Fin 2 => z.1 j.castSucc), z.2))
  have hred := shearReducedGradientPartial_contDiff N i
  exact hred.comp (by fun_prop)


theorem shearFullGradientPartial_spatialPartial (N : ℕ) (i : Fin 2)
    (z : Vec3 × ℝ) :
    spatialPartial (show ParabolicPoint → ℝ from shearFullGradientPartial i N)
        i.castSucc z =
      ∑ n ∈ Finset.range N,
        shearWeight n * shearSpatialSecondField (shearScale n) i
          (shearReducedView z) := by
  change fderiv ℝ (fun x : Vec3 => shearFullGradientPartial i N (x, z.2))
      z.1 (basisVec i.castSucc) = _
  let F : Vec2 → ℝ := fun y => shearReducedGradientPartial i N (y, z.2)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    dsimp [F]
    have hred := shearReducedGradientPartial_contDiff N i
    have hembed : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec2 => (y, z.2)) := by fun_prop
    exact hred.comp hembed
  have hFd : DifferentiableAt ℝ F (shearSpatialProjection z.1) :=
    (hF.differentiable (by simp)).differentiableAt
  have hcomp := hFd.hasFDerivAt.comp z.1
    (shearSpatialProjection_hasFDerivAt z.1)
  have hfun : (fun x : Vec3 => shearFullGradientPartial i N (x, z.2)) =
      F ∘ shearSpatialProjection := by
    funext x
    rfl
  have hval : fderiv ℝ (fun x : Vec3 => shearFullGradientPartial i N (x, z.2))
      z.1 (basisVec i.castSucc) =
      fderiv ℝ F (shearSpatialProjection z.1)
        (shearSpatialProjectionDerivative (basisVec i.castSucc)) := by
    rw [hfun, hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
  have hproj : shearSpatialProjectionDerivative (basisVec i.castSucc) = basisVec i := by
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [shearSpatialProjectionDerivative, basisVec,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
  rw [hval, hproj]
  change fderiv ℝ (fun y : Vec2 => shearReducedGradientPartial i N (y, z.2))
      (shearSpatialProjection z.1) (basisVec i) = _
  exact shearReducedGradientPartial_spatialDerivative N i
    (shearSpatialProjection z.1) z.2

theorem shearFullScalarPartial_heat_identity (N : ℕ) (z : ParabolicPoint) :
    timePartial (show ParabolicPoint → ℝ from shearFullScalarPartial N) z -
      ∑ i : Fin 3, spatialSecondPartial
        (show ParabolicPoint → ℝ from shearFullScalarPartial N) i i z =
      shearFullForcePartial N z := by
  have ht : timePartial (show ParabolicPoint → ℝ from shearFullScalarPartial N) z =
      fderiv ℝ (fun t : ℝ =>
        shearReducedBumpPartial N ((fun i : Fin 2 => z.1 i.castSucc), t)) z.2 1 := by
    rfl
  have hs0 : spatialSecondPartial
      (show ParabolicPoint → ℝ from shearFullScalarPartial N) 0 0 z =
      spatialPartial (show ParabolicPoint → ℝ from shearFullGradientPartial 0 N) 0 z := by
    unfold spatialSecondPartial
    congr 1
    funext w
    exact shearFullScalarPartial_spatialPartial N w 0
  have hs1 : spatialSecondPartial
      (show ParabolicPoint → ℝ from shearFullScalarPartial N) 1 1 z =
      spatialPartial (show ParabolicPoint → ℝ from shearFullGradientPartial 1 N) 1 z := by
    unfold spatialSecondPartial
    congr 1
    funext w
    exact shearFullScalarPartial_spatialPartial N w 1
  have hs2 : spatialSecondPartial
      (show ParabolicPoint → ℝ from shearFullScalarPartial N) 2 2 z = 0 := by
    unfold spatialSecondPartial
    have hz : (fun w : ParabolicPoint =>
        spatialPartial (show ParabolicPoint → ℝ from shearFullScalarPartial N) 2 w) =
          fun _ => 0 := by
      funext w
      have h := shearFullScalarPartial_spatialPartial N w 2
      simpa using h
    rw [hz]
    simp [spatialPartial]
  have hs1' : spatialSecondPartial
      (show ParabolicPoint → ℝ from shearFullScalarPartial N)
      (Fin.succ 0) (Fin.succ 0) z =
      spatialPartial (show ParabolicPoint → ℝ from shearFullGradientPartial 1 N) 1 z := by
    simpa using hs1
  have hs2' : spatialSecondPartial
      (show ParabolicPoint → ℝ from shearFullScalarPartial N)
      (Fin.succ (Fin.succ 0)) (Fin.succ (Fin.succ 0)) z = 0 := by
    simpa using hs2
  have hlap : (∑ i : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from shearFullScalarPartial N) i i z) =
      spatialPartial (show ParabolicPoint → ℝ from shearFullGradientPartial 0 N) 0 z +
      spatialPartial (show ParabolicPoint → ℝ from shearFullGradientPartial 1 N) 1 z := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rw [hs0, hs1', hs2']
    simp
  rw [ht, hlap]
  have hgrad0 := shearFullGradientPartial_spatialPartial N 0 z
  have hgrad1 := shearFullGradientPartial_spatialPartial N 1 z
  have hgrad0' : spatialPartial
      (show ParabolicPoint → ℝ from shearFullGradientPartial 0 N) 0 z =
      ∑ n ∈ Finset.range N,
        shearWeight n * shearSpatialSecondField (shearScale n) 0 (shearReducedView z) := by
    simpa using hgrad0
  have hgrad1' : spatialPartial
      (show ParabolicPoint → ℝ from shearFullGradientPartial 1 N) 1 z =
      ∑ n ∈ Finset.range N,
        shearWeight n * shearSpatialSecondField (shearScale n) 1 (shearReducedView z) := by
    simpa using hgrad1
  rw [hgrad0', hgrad1']
  have hred := shearReducedBumpPartial_heat_identity N (shearReducedView z)
  have hredLap := shearReducedBumpPartial_laplacian N (shearReducedView z)
  rw [hredLap] at hred
  simpa [shearReducedView, shearFullForcePartial] using hred

end CKN
