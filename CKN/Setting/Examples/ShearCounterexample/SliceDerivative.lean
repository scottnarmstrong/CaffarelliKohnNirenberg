-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.SliceFinite

/-! # Derivative bounds for finite shear slices. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory Filter
namespace CKN

private theorem shearReducedBumpSeries_eq_sum_of_N {t : ℝ} (_ : t ≠ 0)
    (N : ℕ) (hN : ∀ n, N ≤ n → 2 * shearScale n ^ 2 < |t|) :
    ∀ x : Vec 2,
      shearReducedBumpSeries (x, t) =
        ∑ n ∈ Finset.range N, shearReducedBumpTerm n (x, t) := by
  intro x
  unfold shearReducedBumpSeries
  apply tsum_eq_sum
  intro n hn
  have hnN : N ≤ n := by
    have hnot : ¬ n < N := by simpa using hn
    exact not_lt.mp hnot
  exact shearReducedBumpTerm_zero_of_time_large (hN n hnN)

private theorem shearReducedGradientSeries_eq_sum_of_N {t : ℝ}
    (N : ℕ) (hN : ∀ n, N ≤ n → 2 * shearScale n ^ 2 < |t|)
    (i : Fin 2) :
    ∀ x : Vec 2,
      shearReducedGradientSeries i (x, t) =
        ∑ n ∈ Finset.range N, shearReducedGradientTerm i n (x, t) := by
  intro x
  unfold shearReducedGradientSeries
  apply tsum_eq_sum
  intro n hn
  have hnN : N ≤ n := by
    have hnot : ¬ n < N := by simpa using hn
    exact not_lt.mp hnot
  exact shearReducedGradientTerm_zero_of_time_large (i := i) (hN n hnN)

theorem shearReducedSlice_deriv_eq_gradient {t : ℝ} (ht : t ≠ 0)
    (x : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun y : Vec 2 => shearReducedBumpSeries (y, t)) x (basisVec i) =
      shearReducedGradientSeries i (x, t) := by
  obtain ⟨N, hN⟩ := exists_shearScale_sq_lt_abs_time ht
  have hfun : (fun y : Vec 2 => shearReducedBumpSeries (y, t)) =
      fun y => ∑ n ∈ Finset.range N, shearReducedBumpTerm n (y, t) := by
    funext y
    exact shearReducedBumpSeries_eq_sum_of_N ht N hN y
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
  rw [hfun, hderiv.fderiv]
  simp only [sum_apply]
  rw [shearReducedGradientSeries_eq_sum_of_N N hN i x]
  apply Finset.sum_congr rfl
  intro n hn
  exact shearReducedSliceTerm_fderiv_apply n t i x

end CKN
