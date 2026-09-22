-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.ScalingQuantitiesFullOnCylinder

/-!
# Scale-quantity identities at the paper's cylinder hypothesis

This module exposes the scale-quantity identities with containment of the open
rescaled cylinder, matching Lemma `lem:scaling-quantities`.
-/

open CKN.Foundation.Parabolic Set

namespace CKN

/-- All scale-quantity and auxiliary excess identities under containment of
the open rescaled cylinder. -/
theorem scaling_quantities_paper :
∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (_hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (μ : ℝ) (_hμ : 0 < μ) (z₀ ζ : ParabolicPoint) (r κ : ℝ) (_hr : 0 < r)
    (__hdom : parabolicCylinder
      (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)).1
      (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)).2 (μ*r) ⊆ spaceTimeSet Ω I),
    let z := parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)
    alpha (rescaleVelocity μ z₀ u) ζ r = alpha u z (μ*r) ∧
    beta (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du) ζ r = beta u Du z (μ*r) ∧
    gamma (rescaleVelocity μ z₀ u) ζ r = gamma u z (μ*r) ∧
    delta (rescalePressure μ z₀ p) ζ r = delta p z (μ*r) ∧
    lambda q (rescaleForce μ z₀ f) ζ r = lambda q f z (μ*r) ∧
    theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du) (rescalePressure μ z₀ p) ζ r =
      theta κ u Du p z (μ*r) ∧
    tsaiVelocityExcess (rescaleVelocity μ z₀ u) ζ r = tsaiVelocityExcess u z (μ*r) ∧
    tsaiPressureExcess (rescalePressure μ z₀ p) ζ r = tsaiPressureExcess p z (μ*r) ∧
    tsaiPhi (rescaleVelocity μ z₀ u) (rescalePressure μ z₀ p) ζ r = tsaiPhi u p z (μ*r) ∧
    tsaiPsi (rescaleVelocity μ z₀ u) ζ r = tsaiPsi u z (μ*r) := by
  exact @scaling_quantities_full_on_cylinder_source

end CKN
