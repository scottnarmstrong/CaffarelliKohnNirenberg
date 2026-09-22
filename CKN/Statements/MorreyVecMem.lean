-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Basic

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false

namespace CKN

/-- Componentwise parabolic Morrey membership used by paper label `def:parabolic-morrey`. -/
def morreyVecMem (P τ : ℝ) (S : Set ParabolicPoint)
    (u : ParabolicPoint → Vec3) : Prop :=
  ∀ i : Fin 3,
    morreyBallNorm P τ (S.indicator (fun z => u z i)) < ∞

end CKN
