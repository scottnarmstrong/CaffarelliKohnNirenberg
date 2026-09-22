-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.CZHarmonicCorollaryFaithful
import CKN.Pressure.ForceCancellationSolenoidalDisplay

/-!
# Local-force cancellation in the Calderón–Zygmund pressure corollary

The Calderón–Zygmund and harmonic conclusions are inherited from the full
corollary. The force cancellation uses only the local spacetime divergence
identity on compactly supported tests in the solution domain.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN

/-- The Calderón–Zygmund/harmonic corollary with force cancellation under the
local spacetime distributional divergence condition. -/
theorem czHarmonic_corollary_local_of_sws :
    ∀ k : ℕ, ∃ C₁₆ : ℝ, 0 ≤ C₁₆ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ},
          (hρ : 0 < ρ) →
          closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
          let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
          let c : ℝ → Vec3 := fun t j =>
            average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)
          (∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
            (∀ x ∈ euclideanBall z.1 (13 * ρ / 20),
              p (x, s) = czPressurePart η u c p f s x +
                harmonicPressurePart η u c p s x + forcePressurePart η f s x) ∧
            czPressurePart η u c p f s =ᵐ[volume] czPressureRieszPart η u c s ∧
            WeaklyHarmonicOn (euclideanBall z.1 (13 * ρ / 20))
              (harmonicPressurePart η u c p s) ∧
            ∀ x ∈ vec3Ball z.1 (ρ / 2),
              ‖iteratedFDeriv ℝ k (harmonicPressurePart η u c p s) x‖ ≤
                C₁₆ * ρ ^ (-(2 + k : ℝ)) *
                  (alpha u z ρ ^ 2 +
                    lpNorm (fun y : Vec3 => p (y, s))
                      (ENNReal.ofReal (3 / 2 : ℝ))
                      (volume.restrict (vec3Ball z.1 ρ)))) ∧
          ((∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
            IntegrableOn (fun w => ∑ i, f w i * spatialPartial ψ i w)
              (tsupport ψ) volume ∧
            ∫ w in spaceTimeSet Ω I, ∑ i, f w i * spatialPartial ψ i w = 0) →
            ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
              forcePressurePart η f s =ᵐ[volume] 0) := by
  intro k
  obtain ⟨C₁₆, hC₁₆, hcor⟩ := czHarmonic_corollary_of_sws k
  refine ⟨C₁₆, hC₁₆, ?_⟩
  intro Ω I q u Du p f hsol z ρ hρ hsub
  dsimp only
  have hbase := hcor hsol hρ hsub
  refine ⟨hbase.1, ?_⟩
  intro hdiv
  simpa only [forcePressurePart] using
    pressure_force_cancellation_of_sws hsol hρ hsub hdiv

end CKN

end
