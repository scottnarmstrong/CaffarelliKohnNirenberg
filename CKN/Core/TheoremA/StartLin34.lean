-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.TheoremA.StartCZ
import CKN.Pressure.Lin34SliceIntegrated

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-!
# Theorem A start with the Lin 3.4 estimate discharged

`thmA_start_of_CZ` consumes the integrated oscillation display `eq:lin35-force`
of `prop:lin34` as a named hypothesis.  That display is proved in
`pressure_lin34_force_lambda_of_sws` from a single analytic input, the
Calderón--Zygmund bound `ext:CZ` for the centred leading pressure term `p₁` of
`prop:pressure-decomposition` on almost every time slice.  This file performs
the substitution, so that the start of Theorem A rests on `ext:CZ` alone.
-/

/-- Theorem A start with the oscillation display of `prop:lin34` discharged.
The only remaining named analytic input is the slicewise Calderón--Zygmund
bound `ext:CZ` for the centred leading pressure term, quantified over the
solution data, the centre and the scale. -/
theorem thmA_start_of_lin34_cz
    (q C₁₁ C₂₇ C₂₈ : ℝ)
    (hq : 5 / 2 < q) (hC₁₁ : 0 ≤ C₁₁)
    (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hCZ_p1 : ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          MemLp (lin34CentredP1 u p f z.1 ρ hρ s)
              (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
            lpNorm (lin34CentredP1 u p f z.1 ρ hρ s)
                (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
              C₁₁ * lin34VelocitySlice u z ρ s ^ (2 / 3 : ℝ)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
      (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
      ∀ z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0,
        theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ / 4) ≤
            iterationEta C₂₇ ∧
          lambda q f z (iterationKappa C₂₇ / 4) ≤
            iterationLambda₀ C₂₇ C₂₈ := by
  have hforce : 0 ≤ lin34ForceConstant (lin34ForceExponent C₁₁) :=
    le_trans (lin34PointwiseConstant_nonneg hC₁₁)
      (lin34_pointwiseConstant_le_forceConstant hC₁₁)
  have hcyl : 0 ≤ lin34ForceCylinderConstant q ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (lin34ForceCylinderConstant_nonneg q hq) _
  have hC₁₃ : 0 ≤ lin34SolutionForceExponent C₁₁ q := by
    unfold lin34SolutionForceExponent
    exact Real.rpow_nonneg (mul_nonneg hforce (by linarith only [hcyl])) _
  refine thmA_start_of_CZ q (lin34SolutionForceExponent C₁₁ q) C₂₇ C₂₈ hq hC₁₃
    hC₂₇ hC₂₈ ?_
  intro Ω I u Du p f hsol z r ρ hρ hr hhalf hsub
  exact pressure_lin34_force_lambda_of_sws C₁₁ hC₁₁ hsol hρ hr hhalf hsub
    (hCZ_p1 hsol hρ hsub)

end CKN
