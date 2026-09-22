-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Finiteness
import CKN.Core.Caccioppoli.Finiteness

/-! # Combined monotonicity of the five scale quantities

For a suitable weak solution, all five radius comparisons hold together on
an admissible cylinder. The pressure comparison uses the squared quantity;
the required finiteness of the integrals follows from suitability.
-/

open Set
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-- The five inequalities of `lem:monotonicity`, including the squared
pressure inequality, with every finiteness premise supplied by suitability. -/
theorem scale_quantities_mono_radius_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    alpha u z r ≤ (ρ / r) ^ (1 / 2 : ℝ) * alpha u z ρ ∧
    beta u Du z r ≤ (ρ / r) ^ (1 / 2 : ℝ) * beta u Du z ρ ∧
    gamma u z r ≤ (ρ / r) ^ (2 / 3 : ℝ) * gamma u z ρ ∧
    delta p z r ^ 2 ≤ (ρ / r) ^ (4 / 3 : ℝ) * delta p z ρ ^ 2 ∧
    lambda q f z r ≤ (r / ρ) ^ (3 - 5 / q) * lambda q f z ρ := by
  have hρ : 0 < ρ := hr.trans_le hrρ
  exact ⟨alpha_mono_radius_of_sws hsol z hr hrρ hsub,
    beta_mono_radius_of_sws hsol z hr hrρ hsub,
    gamma_mono_radius u z hr hrρ (caccioppoli_velocity_integral_ne_top hsol hρ hsub),
    delta_sq_mono_radius_of_sws hsol z hr hrρ hsub,
    lambda_mono_radius_of_sws hsol z hr hrρ hsub⟩

end CKN
