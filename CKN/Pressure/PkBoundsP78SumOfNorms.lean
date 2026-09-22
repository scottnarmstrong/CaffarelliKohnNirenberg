-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.PkBoundsUnconditionalP8
import CKN.Pressure.PkBoundsP7SolutionBound
import CKN.Pressure.Lin34SliceForceCylinder
import CKN.Foundation.Harmonic.InteriorEstimatesBasic

/-!
# The force group bound as a sum of norms

Parts (d) and (e) of `lem:pk-bounds` in `paper/ckn.tex` bound the normalised
`L^{3/2}` masses of `p₇` and of `p₈` separately.  Adding them gives
`eq:p78-bound`, the bound on the **sum of the two norms** — not merely on the
norm of the sum — with the constant `C₁₃(q)` of that lemma, which is the sum of
the two individual constants.
-/

open MeasureTheory Set

open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

/-- **`eq:p78-bound`.**  For `0 < r ≤ ρ/2` and a suitable weak solution, the sum
of the normalised `L^{3/2}` norms of `p₇` and `p₈` over `Q_r(z₀)` is at most
`C₁₃(q) · (r/ρ) · λ(z₀, ρ)`. -/
theorem pressureP78_sum_of_norms_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (eLpNorm' (fun w : ParabolicPoint =>
              pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r)) +
          eLpNorm' (fun w : ParabolicPoint =>
              pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r))) ≤
      ENNReal.ofReal (lin34ForceCylinderConstant q * (r / ρ) * lambda q f z ρ) := by
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have h7 := pressureP7_bound hsol hρ hr hhalf hsub
  have h8 := pressureP8_bound hsol hρ hr hhalf hsub
  have hlam : 0 ≤ lambda q f z ρ := by
    unfold lambda
    positivity
  have hratio : 0 ≤ r / ρ := by positivity
  have hX : 0 ≤ r / ρ * lambda q f z ρ := mul_nonneg hratio hlam
  have hC7 : 0 ≤ (pressureP7SolutionConstant q).toReal := ENNReal.toReal_nonneg
  have hC8 : 0 ≤ pressureP13Constant q := by
    unfold pressureP13Constant
    have := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
    positivity
  have h7' : pressureP7SolutionConstant q *
      ENNReal.ofReal (r / ρ * lambda q f z ρ) =
      ENNReal.ofReal ((pressureP7SolutionConstant q).toReal *
        (r / ρ * lambda q f z ρ)) := by
    rw [ENNReal.ofReal_mul hC7,
      ENNReal.ofReal_toReal (pressureP7SolutionConstant_ne_top hq)]
  rw [mul_add]
  refine (add_le_add h7 h8).trans ?_
  rw [h7', ← ENNReal.ofReal_add (mul_nonneg hC7 hX)
    (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold lin34ForceCylinderConstant
  ring_nf
  exact le_rfl

end CKN
