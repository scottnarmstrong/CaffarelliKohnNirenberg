-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.InteriorSupDisplay

open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false

namespace CKN.Foundation.Heat

/-- The weakly harmonic supremum estimate on the three-quarter ball. -/
theorem weak_harmonic_interior_sup_three_quarters :
    ∃ C₁₇ : ℝ, ∀ (h : Vec3 → ℝ) (x₀ : Vec3) (ρ : ℝ), 0 < ρ →
      MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) →
      WeaklyHarmonicOn (euclideanBall x₀ ρ) h →
      eLpNorm h ⊤ (volume.restrict (euclideanBall x₀ (3 * ρ / 4))) ≤
        ENNReal.ofReal (C₁₇ * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) :=
  CKN.Foundation.Heat.weak_harmonic_interior_sup

end CKN.Foundation.Heat
