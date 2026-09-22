-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SpatialSliceNormIdentifyVelocity
import CKN.Setting.SpatialSliceNormIdentifyGradient
import CKN.Setting.SpatialSliceNormIdentifyPressure
import CKN.Setting.SpatialSliceNormIdentifyForce

open MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped ENNReal
set_option autoImplicit false

noncomputable section

namespace CKN

/-- Paper equation `eq:slice-norms` in `paper/ckn.tex`: the four spatial slice norms
are, almost everywhere in time on `J_ρ`, the explicit real integrals that the scale
quantities are built from. -/
theorem spatialSliceNorms_identify_display
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      velocitySpatialSliceNorm u z.1 ρ s =
        ENNReal.ofReal
          ((∫ y in vec3Ball z.1 ρ,
            vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) ∧
        gradientSpatialSliceNorm Du z.1 ρ s =
          ENNReal.ofReal ((∫ y in vec3Ball z.1 ρ,
            spatialGradientSq u Du (y, s)) ^ (1 / 2 : ℝ)) ∧
        pressureSpatialSliceNorm p z.1 ρ s =
          ENNReal.ofReal ((∫ y in vec3Ball z.1 ρ,
            |p (y, s)| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) ∧
        forceSpatialSliceNorm f z.1 ρ q s =
          ENNReal.ofReal
            ((∫ y in vec3Ball z.1 ρ,
              vec3EuclideanNorm (f (y, s)) ^ q) ^ (1 / q : ℝ)) := by
  have hv := velocitySpatialSliceNorm_eq_ofReal_ae hsol z hρ hsub
  have hg := gradientSpatialSliceNorm_eq_ofReal_ae hsol z hρ hsub
  have hp := pressureSpatialSliceNorm_eq_ofReal_ae hsol z hρ hsub
  have hf := forceSpatialSliceNorm_eq_ofReal_ae hsol z hρ hsub
  filter_upwards [hv, hg, hp, hf] with s hv' hg' hp' hf'
  exact ⟨hv', hg', hp', hf'⟩

end CKN
