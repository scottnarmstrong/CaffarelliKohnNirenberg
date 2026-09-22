-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SliceNormBoundsPaperVelocity
import CKN.Setting.SliceNormBoundsPaperGradient
import CKN.Setting.SliceNormBoundsPaperPressure
import CKN.Setting.SliceNormBoundsPaperForce

open MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped ENNReal

set_option autoImplicit false

namespace CKN

/-- Paper equation `eq:slice-norm-bounds`: the four slice norm bounds assembled into
one display. Each conjunct is the corresponding lemma from
`SliceNormBoundsPaperVelocity`, `SliceNormBoundsPaperGradient`,
`SliceNormBoundsPaperPressure`, and `SliceNormBoundsPaperForce`. -/
theorem spatialSliceNorms_timeNorm_display
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    essSup (fun s : ℝ => velocitySpatialSliceNorm u z.1 ρ s)
        (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
        ENNReal.ofReal (Real.sqrt ρ * alpha u z ρ) ∧
      (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, gradientSpatialSliceNorm Du z.1 ρ s ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt ρ * beta u Du z ρ) ∧
      (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2,
        pressureSpatialSliceNorm p z.1 ρ s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) =
        ENNReal.ofReal (ρ ^ (4 / 3 : ℝ) * delta p z ρ ^ 2) ∧
      (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, forceSpatialSliceNorm f z.1 ρ q s ^ q) ^ (1 / q : ℝ) =
        ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ) :=
  ⟨velocitySpatialSliceNorm_essSup_eq_alpha hsol z hρ hsub,
   gradientSpatialSliceNorm_timeNorm_eq_beta hsol z hρ hsub,
   pressureSpatialSliceNorm_timeNorm_eq_delta_sq hsol z hρ hsub,
   forceSpatialSliceNorm_timeNorm_eq_lambda hsol z hρ hsub⟩

end CKN
