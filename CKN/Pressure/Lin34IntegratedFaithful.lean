-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.Lin34IntegratedLocalSource

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-- The integrated solenoidal estimate of `prop:lin34`, with the local
space-time divergence condition on the force and the common absolute
constant used by the proposition's two solenoidal clauses. -/
theorem pressure_lin34_integrated_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hdivf : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      (∫ w in spaceTimeSet Ω I, ∑ i : Fin 3, f w i * spatialPartial ψ i w) = 0) :
    pressureD p z r ≤ lin34AbsoluteConstant *
      ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
        (r / ρ) * pressureD p z ρ) := by
  exact pressure_lin34_integrated_local_spacetime_source
    hsol hρ hr hhalf hsub hdivf

end CKN

end
