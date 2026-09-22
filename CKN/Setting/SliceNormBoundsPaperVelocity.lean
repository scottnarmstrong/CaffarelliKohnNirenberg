-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SpatialSliceNormIdentifyVelocity
import CKN.Setting.SliceTimeNormVelocityEq

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
set_option autoImplicit false
namespace CKN

/-- Paper equation `eq:slice-norm-bounds`, velocity line in the
`velocitySpatialSliceNorm` notation: the essential supremum of the
spatial-slice norm of `u` over the cylinder equals `ρ^(1/2) * α(z,ρ)`. -/
theorem velocitySpatialSliceNorm_essSup_eq_alpha
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    essSup (fun s : ℝ => velocitySpatialSliceNorm u z.1 ρ s)
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
      ENNReal.ofReal (Real.sqrt ρ * alpha u z ρ) := by
  have h_ae_eq := velocitySpatialSliceNorm_eq_ofReal_ae hsol z hρ hsub
  have h_essSup_eq : essSup (fun s : ℝ => velocitySpatialSliceNorm u z.1 ρ s)
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
      essSup (fun s : ℝ => ENNReal.ofReal
        ((∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) :=
    essSup_congr_ae h_ae_eq
  rw [h_essSup_eq]
  exact velocitySliceTimeEssSup_eq_alpha hsol z hρ hsub

end CKN
