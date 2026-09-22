-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.SeriesApprox

/-! # Reduced spatial finite-scale estimates. -/

namespace CKN

theorem shearReducedBumpPartial_fderiv_apply (N : ℕ) (t : ℝ)
    (i : Fin 2) (x : Vec 2) :
    fderiv ℝ (fun y : Vec 2 => shearReducedBumpPartial N (y, t)) x
        (basisVec i) = shearReducedGradientPartial i N (x, t) := by
  have hderiv : HasFDerivAt
      (fun y : Vec 2 => ∑ n ∈ Finset.range N, shearReducedBumpTerm n (y, t))
      (∑ n ∈ Finset.range N,
        fderiv ℝ (fun y : Vec 2 => shearReducedBumpTerm n (y, t)) x) x := by
    rw [show (fun y : Vec 2 =>
        ∑ n ∈ Finset.range N, shearReducedBumpTerm n (y, t)) =
      ∑ n ∈ Finset.range N, fun y => shearReducedBumpTerm n (y, t) by
        funext y
        simp]
    apply HasFDerivAt.sum
    intro n hn
    exact (shearReducedSliceTerm_contDiff n t).differentiable (by simp) x |>.hasFDerivAt
  change fderiv ℝ
    (fun y : Vec 2 => ∑ n ∈ Finset.range N, shearReducedBumpTerm n (y, t)) x
      (basisVec i) = _
  rw [hderiv.fderiv]
  rw [sum_apply]
  unfold shearReducedGradientPartial
  apply Finset.sum_congr rfl
  intro n hn
  exact shearReducedSliceTerm_fderiv_apply n t i x

end CKN
