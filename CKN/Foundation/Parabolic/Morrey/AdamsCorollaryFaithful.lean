-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.AdamsFiniteDisplay

open MeasureTheory
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- Paper label `cor:adams`: the potential map has a finite exponent-dependent
coefficient, and its extended potential is finite almost everywhere.
The Lean statement uses the cylinder seminorm `morreyNorm` and the
sum-gauge kernel `√|t-s| + |x-y|₂`.  The paper uses the ball Morrey norm
and the maximum-gauge kernel.  The norm comparison in `eq:morrey-cyl` and
the bounds `d_par ≤ parabolicRho₂ ≤ 2 * d_par` relate these conventions;
they need not have identical numerical constants. -/
theorem parabolic_adams_corollary_faithful (P τ β : ℝ)
    (hP : 1 < P) (hPτ : P ≤ τ) (hβ : 0 < β) (hβτ : β * τ < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ParabolicPoint → ℝ, Measurable f →
      morreyNorm P τ f < ⊤ →
        (∀ᵐ z ∂volume, parabolicRieszPotential β f z < ⊤) ∧
        morreyNorm (P / (1 - β * τ / 5)) (τ / (1 - β * τ / 5))
          (fun z => (parabolicRieszPotential β f z).toReal) ≤
            ENNReal.ofReal C * morreyNorm P τ f := by
  exact parabolic_adams_finite P τ β hP hPτ hβ hβτ

end CKN.Foundation.Parabolic.Morrey

end
