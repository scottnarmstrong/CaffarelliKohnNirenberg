-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.Identification

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false

noncomputable section

namespace CKN

/-- A whole-space distributional identity is the form consumed by the
    Liouville identification. Unlike the local slice export, this identity
    quantifies over every compactly supported smooth test. -/
theorem pressureP1_eq_of_wholeSpace_identity_and_linear_growth
    {p₁ Tg : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hP1 : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume →
      ∫ x, p₁ x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hT : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => Tg x * spatialLaplacian ψ x) volume →
      ∫ x, Tg x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hP1Int : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume)
    (hTInt : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => Tg x * spatialLaplacian ψ x) volume)
    (hmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp (p₁ - Tg) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hgrowth : ∀ ρ : ℝ, 0 < ρ →
      lpNorm (p₁ - Tg) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ)) :
    p₁ =ᵐ[volume] Tg := by
  apply pressureP1_eq_of_distributional_identity_and_linear_growth hC
  · intro ψ hψ hψc _hψU hInt
    exact hP1 ψ hψ hψc hInt
  · intro ψ hψ hψc _hψU hInt
    exact hT ψ hψ hψc hInt
  · intro ψ hψ hψc _hψU
    exact hP1Int ψ hψ hψc
  · intro ψ hψ hψc _hψU
    exact hTInt ψ hψ hψc
  · exact hmem
  · exact hgrowth

end CKN
