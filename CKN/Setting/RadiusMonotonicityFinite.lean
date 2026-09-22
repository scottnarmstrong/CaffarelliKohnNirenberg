-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.CombinedMonotonicity

open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-- The five radius comparisons for finite-valued scale quantities on a
compactly contained outer cylinder. -/
theorem scale_quantities_mono_radius_compact_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    alpha u z r ≤ (ρ / r) ^ (1 / 2 : ℝ) * alpha u z ρ ∧
    beta u Du z r ≤ (ρ / r) ^ (1 / 2 : ℝ) * beta u Du z ρ ∧
    gamma u z r ≤ (ρ / r) ^ (2 / 3 : ℝ) * gamma u z ρ ∧
    delta p z r ^ 2 ≤ (ρ / r) ^ (4 / 3 : ℝ) * delta p z ρ ^ 2 ∧
    lambda q f z r ≤ (r / ρ) ^ (3 - 5 / q) * lambda q f z ρ := by
  exact scale_quantities_mono_radius_of_sws hsol z hr hrρ.le hsub

end CKN
