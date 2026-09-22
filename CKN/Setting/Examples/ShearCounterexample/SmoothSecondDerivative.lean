-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Second derivative identities for smooth shear factors. -/

namespace CKN

theorem fderiv_directional_fderiv_eq_iteratedFDeriv_two
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (z a b : E) :
    fderiv ℝ (fun y => fderiv ℝ f y a) z b =
      iteratedFDeriv ℝ 2 f z (Fin.cons b (fun _ : Fin 1 => a)) := by
  have hfun : (fun y : E =>
      iteratedFDeriv ℝ 1 f y (fun _ : Fin 1 => a)) =
      fun y => fderiv ℝ f y a := by
    funext y
    rw [iteratedFDeriv_one_apply]
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) z :=
    (hf.differentiable_iteratedFDeriv (by simp)).differentiableAt
  let m : Fin 2 → E := Fin.cons b (fun _ : Fin 1 => a)
  have h := hdiff.iteratedFDeriv_succ_apply_left'
    (m := m)
  have hm0 : m 0 = b := by simp [m]
  have htail : Fin.tail m = (fun _ : Fin 1 => a) := by
    simp [m]
  rw [htail, hm0] at h
  rw [hfun] at h
  simpa [m] using h.symm

end CKN
