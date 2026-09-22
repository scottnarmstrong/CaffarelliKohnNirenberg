-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SpatialSliceNormIdentifyPressure
import CKN.Setting.SliceTimeNormPressure

open MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped ENNReal
set_option autoImplicit false
namespace CKN

/-!
# Pressure slice norm bounds: the full equality

Paper equation `eq:slice-norm-bounds`, pressure line: the $L^{3/2}(J_\rho)$
time norm of the $L^{3/2}(B_\rho)$ pressure slice norm equals $\\rho^{4/3}\\delta(\\rho)^2$.
-/

/-- Paper equation `eq:slice-norm-bounds`, pressure line:
$\|\|\|p\|\|_{L^{3/2}(J_\rho)} = \\rho^{4/3}\\delta(\\rho)^2$
where $\|\|\|p\|\|_{L^{3/2}(J_\rho)}$ is the $L^{3/2}(J_\rho)$ time norm of the
$L^{3/2}(B_\rho)$ pressure spatial slice norm. -/
theorem pressureSpatialSliceNorm_timeNorm_eq_delta_sq
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2,
      pressureSpatialSliceNorm p z.1 ρ s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) =
      ENNReal.ofReal (ρ ^ (4 / 3 : ℝ) * delta p z ρ ^ 2) := by
  let G : ℝ → ℝ := fun s =>
    (∫ y in vec3Ball z.1 ρ, |p (y, s)| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)
  have hG_nonneg (s : ℝ) : 0 ≤ G s := by
    dsimp [G]
    refine Real.rpow_nonneg (setIntegral_nonneg (vec3Ball_measurable z.1 ρ) ?_) _
    intro y hy
    exact Real.rpow_nonneg (abs_nonneg _) _
  have h_ae_eq : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureSpatialSliceNorm p z.1 ρ s = ENNReal.ofReal (G s) :=
    pressureSpatialSliceNorm_eq_ofReal_ae hsol z hρ hsub
  have h_ofReal_pow (s : ℝ) : (ENNReal.ofReal (G s)) ^ (3 / 2 : ℝ) =
      ENNReal.ofReal ((G s) ^ (3 / 2 : ℝ)) :=
    ENNReal.ofReal_rpow_of_nonneg (hG_nonneg s) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have h_enorm_pow (s : ℝ) : ‖G s‖ₑ ^ (3 / 2 : ℝ) = ENNReal.ofReal ((G s) ^ (3 / 2 : ℝ)) := by
    rw [Real.enorm_eq_ofReal (hG_nonneg s), h_ofReal_pow s]
  have h1 : (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, pressureSpatialSliceNorm p z.1 ρ s ^ (3 / 2 : ℝ)) =
      (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, (ENNReal.ofReal (G s)) ^ (3 / 2 : ℝ)) := by
    apply lintegral_congr_ae
    filter_upwards [h_ae_eq] with s hs
    simp [hs]
  have h2 : (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, (ENNReal.ofReal (G s)) ^ (3 / 2 : ℝ)) =
      (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, ENNReal.ofReal ((G s) ^ (3 / 2 : ℝ))) := by
    apply lintegral_congr_ae
    filter_upwards [] with s
    rw [h_ofReal_pow s]
  have h3 : (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, ENNReal.ofReal ((G s) ^ (3 / 2 : ℝ))) =
      (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, ‖G s‖ₑ ^ (3 / 2 : ℝ)) := by
    apply lintegral_congr_ae
    filter_upwards [] with s
    rw [h_enorm_pow s]
  have h_exp_eq : (2 / 3 : ℝ) = (1 : ℝ) / (3 / 2 : ℝ) := by norm_num
  have h4 : (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) =
      eLpNorm' G (3 / 2 : ℝ) (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
    rw [eLpNorm'_eq_lintegral_enorm, h_exp_eq]
  rw [h1, h2, h3, h4]
  exact pressureSliceTimeNorm_eq_delta_sq hsol z hρ hsub

end CKN
