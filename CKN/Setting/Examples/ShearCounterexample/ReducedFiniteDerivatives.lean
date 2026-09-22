-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Examples.ShearCounterexample.FiniteSmooth
import CKN.Setting.Examples.ShearCounterexample.SmoothSecondDerivative
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Finite derivative estimates for the reduced shear series. -/

set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic
namespace CKN

theorem shearReducedGradientTerm_contDiff_full (i : Fin 2) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (shearReducedGradientTerm i n) := by
  let r := shearScale n
  let a : Vec 2 × ℝ := (basisVec i, 0)
  let F : ((Vec 2 × ℝ) × (Vec 2 × ℝ)) → ℝ := fun p =>
    fderiv ℝ (shearScaleBump r) p.1 p.2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    exact (shearScaleBump_smooth_of_pos (shearScale_pos n)).contDiff_fderiv_apply
      (by simp)
  have hH : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec 2 × ℝ => fderiv ℝ (shearScaleBump r) z a) := by
    change ContDiff ℝ (⊤ : ℕ∞) (F ∘ fun z => (z, a))
    exact hF.comp (by fun_prop)
  have hdir (z : Vec 2 × ℝ) :
      shearSpatialFirstField r i z = fderiv ℝ (shearScaleBump r) z a := by
    change iteratedFDeriv ℝ 1 (shearScaleBump r) z
        (fun _ : Fin 1 => (basisVec i, (0 : ℝ))) = _
    rw [iteratedFDeriv_one_apply]
  have heq : shearReducedGradientTerm i n =
      fun z => shearWeight n * fderiv ℝ (shearScaleBump r) z a := by
    funext z
    change shearWeight n * shearSpatialFirstField r i z =
      shearWeight n * fderiv ℝ (shearScaleBump r) z a
    exact congrArg (fun q : ℝ => shearWeight n * q) (hdir z)
  rw [heq]
  simpa only [smul_eq_mul] using hH.const_smul (shearWeight n)

theorem shearReducedBumpTerm_timeDerivative (n : ℕ) (x : Vec 2) (t : ℝ) :
    fderiv ℝ (fun s : ℝ => shearReducedBumpTerm n (x, s)) t 1 =
      shearWeight n * shearTimeFirstField (shearScale n) (x, t) := by
  let r := shearScale n
  let G : ℝ → Vec 2 × ℝ := fun s => (x, s)
  have hG : HasFDerivAt G
      ((0 : ℝ →L[ℝ] Vec 2).prod (ContinuousLinearMap.id ℝ ℝ)) t := by
    exact (hasFDerivAt_const (𝕜 := ℝ) x t).prodMk (hasFDerivAt_id t)
  have hF : HasFDerivAt (shearScaleBump r)
      (fderiv ℝ (shearScaleBump r) (x, t)) (x, t) :=
    ((shearScaleBump_smooth_of_pos (shearScale_pos n)).differentiable (by simp)
      (x, t)).hasFDerivAt
  have hc := (hF.const_smul (shearWeight n)).comp t hG
  change fderiv ℝ (fun s : ℝ => shearWeight n • shearScaleBump r (x, s)) t 1 = _
  have hfun : (fun s : ℝ => shearWeight n • shearScaleBump r (x, s)) =
      (shearWeight n • shearScaleBump r) ∘ G := rfl
  rw [hfun, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply]
  change shearWeight n *
      fderiv ℝ (shearScaleBump r) (x, t) (0, 1) = _
  have hdir : fderiv ℝ (shearScaleBump r) (x, t) (0, 1) =
      shearTimeFirstField r (x, t) := by
    change fderiv ℝ (shearScaleBump r) (x, t) (0, 1) =
      iteratedFDeriv ℝ 1 (shearScaleBump r) (x, t)
        (fun _ : Fin 1 => ((0 : Vec 2), (1 : ℝ)))
    rw [iteratedFDeriv_one_apply]
  rw [hdir]

theorem shearReducedGradientTerm_spatialDerivative (i : Fin 2) (n : ℕ)
    (x : Vec 2) (t : ℝ) :
    fderiv ℝ (fun y : Vec 2 => shearReducedGradientTerm i n (y, t)) x
        (basisVec i) =
      shearWeight n * shearSpatialSecondField (shearScale n) i (x, t) := by
  let r := shearScale n
  let a : Vec 2 × ℝ := (basisVec i, 0)
  let G : Vec 2 → Vec 2 × ℝ := fun y => (y, t)
  let H : Vec 2 × ℝ → ℝ := fun z => fderiv ℝ (shearScaleBump r) z a
  have hG : HasFDerivAt G
      ((ContinuousLinearMap.id ℝ (Vec 2)).prod (0 : Vec 2 →L[ℝ] ℝ)) x := by
    exact (hasFDerivAt_id x).prodMk (hasFDerivAt_const (𝕜 := ℝ) t x)
  have hHdiff : DifferentiableAt ℝ H (x, t) := by
    have hD : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Vec 2 × ℝ) × (Vec 2 × ℝ) =>
          fderiv ℝ (shearScaleBump r) p.1 p.2) :=
      (shearScaleBump_smooth_of_pos (shearScale_pos n)).contDiff_fderiv_apply
        (by simp)
    have hcont : ContDiff ℝ (⊤ : ℕ∞) H := by
      change ContDiff ℝ (⊤ : ℕ∞)
        ((fun p : (Vec 2 × ℝ) × (Vec 2 × ℝ) =>
          fderiv ℝ (shearScaleBump r) p.1 p.2) ∘ fun z => (z, a))
      exact hD.comp (by fun_prop)
    exact hcont.differentiable (by simp) (x, t)
  have hcomp := hHdiff.hasFDerivAt.comp x hG
  have hfirst : (fun y : Vec 2 => shearSpatialFirstField r i (y, t)) = H ∘ G := by
    funext y
    change iteratedFDeriv ℝ 1 (shearScaleBump r) (y, t)
        (fun _ : Fin 1 => (basisVec i, (0 : ℝ))) =
      fderiv ℝ (shearScaleBump r) (y, t) a
    rw [iteratedFDeriv_one_apply]
  have hweighted : (fun y : Vec 2 => shearReducedGradientTerm i n (y, t)) =
      shearWeight n • (H ∘ G) := by
    funext y
    change shearWeight n * shearSpatialFirstField r i (y, t) =
      shearWeight n * H (G y)
    exact congrArg (fun q : ℝ => shearWeight n * q) (congrFun hfirst y)
  have hsecond := fderiv_directional_fderiv_eq_iteratedFDeriv_two
    (f := shearScaleBump r)
    (shearScaleBump_smooth_of_pos (shearScale_pos n)) (x, t) a a
  have hsecond' : fderiv ℝ H (x, t) (basisVec i, 0) =
      shearSpatialSecondField r i (x, t) := by
    change fderiv ℝ (fun z => fderiv ℝ (shearScaleBump r) z a) (x, t) a =
      iteratedFDeriv ℝ 2 (shearScaleBump r) (x, t)
        (fun _ : Fin 2 => a)
    rw [hsecond]
    rfl
  have hcw := hcomp.const_smul (shearWeight n)
  rw [hweighted, hcw.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply]
  change shearWeight n * fderiv ℝ H (x, t) (basisVec i, 0) = _
  rw [hsecond']

end CKN
