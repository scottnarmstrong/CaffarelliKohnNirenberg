-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! # Local constancy and derivative identities for the shear profile. -/
open Filter
open scoped Topology
set_option autoImplicit false
noncomputable section

namespace CKN

theorem iteratedFDeriv_eq_zero_on_open_const
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (c : ℝ)
    (hconst : ∀ y ∈ U, f y = c) {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℝ 1 f x = 0 ∧ iteratedFDeriv ℝ 2 f x = 0 := by
  have hD1 : ∀ y ∈ U, iteratedFDeriv ℝ 1 f y = 0 := by
    intro y hy
    have hnear : f =ᶠ[𝓝 y] fun _ : E => c := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hconst z hz
    have hderiv : HasFDerivAt f (0 : E →L[ℝ] ℝ) y :=
      hnear.hasFDerivAt_iff.mpr (hasFDerivAt_const c y)
    ext m
    rw [iteratedFDeriv_one_apply, hderiv.fderiv]
    simp
  have hD1x := hD1 x hx
  refine ⟨hD1x, ?_⟩
  have hnearD : (fun y => iteratedFDeriv ℝ 1 f y) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hD1 y hy
  have hderivD : HasFDerivAt (fun y => iteratedFDeriv ℝ 1 f y)
      (0 : E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) x := by
    exact hnearD.hasFDerivAt_iff.mpr
      (hasFDerivAt_const
        (0 : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) x)
  ext m
  rw [iteratedFDeriv_succ_apply_left, hderivD.fderiv]
  simp

end CKN
