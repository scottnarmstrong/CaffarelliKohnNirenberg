-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.ForceCancellationSolenoidalDisplay

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

namespace StepDecompSolenoidal

/-- The scalar-test solenoidal pressure cancellation in the step-facing namespace. -/
theorem pressure_force_cancellation_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
        (tsupport ψ) volume ∧
      ∫ w in spaceTimeSet Ω I, ∑ i : Fin 3, f w i * spatialPartial ψ i w = 0) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s =ᵐ[volume] 0 := by
  exact CKN.pressure_force_cancellation_of_sws hsol hρ hsub hdiv

end StepDecompSolenoidal

end CKN
