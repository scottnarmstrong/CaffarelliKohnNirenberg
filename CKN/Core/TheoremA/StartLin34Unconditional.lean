-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.TheoremA.StartLin34
import CKN.Pressure.Lin34CentredCZResidual
import CKN.Pressure.Lin34CentredResidual

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

/-!
# Theorem A start with the pressure oscillation assembled

Composing `thmA_start_of_lin34_cz` with `lin34_hCZ_p1_of_residual_ae_of_sws`
removes both the integrated oscillation display `eq:lin35-force` of
`prop:lin34` and the Calderón--Zygmund bound `ext:CZ` from the hypotheses of the
start of Theorem A.  What remains is the decay input of the Liouville step of
`ext:newtonian`: on almost every time slice the difference between the centred
first potential `p₁` of `prop:pressure-decomposition` and the indexed
second-order Riesz extension of its source is `L^{3/2}` on every ball about the
origin, with local norm growing at most linearly in the radius.

Everything else — the singular-integral estimate, the source estimate for the
centred tensor `eq:Uhat`, the whole-space distributional identity for the
centred potential, the decomposition, and the scale iteration — is discharged.
-/

/-- Theorem A start from the residual decay of the centred first pressure
potential alone.  The constant of `ext:CZ` is `lin34CZConstant`. -/
theorem thmA_start_of_centred_residual
    (q C₂₇ C₂₈ : ℝ)
    (hq : 5 / 2 < q) (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hresidual : ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∃ C : ℝ, 0 ≤ C ∧
          (∀ R : ℝ, 0 < R →
            MemLp (fun x => lin34CentredP1 u p f z.1 ρ hρ s x -
              pressureSecondExtensionOperator rieszSecondL2Input
                rieszSecondL2_weak_type (lin34CentredSource u z.1 hρ s) x)
              (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
          (∀ R : ℝ, 0 < R →
            lpNorm (fun x => lin34CentredP1 u p f z.1 ρ hρ s x -
              pressureSecondExtensionOperator rieszSecondL2Input
                rieszSecondL2_weak_type (lin34CentredSource u z.1 hρ s) x)
              (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R))) :
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
  refine thmA_start_of_lin34_cz q lin34CZConstant C₂₇ C₂₈ hq
    lin34CZConstant_nonneg hC₂₇ hC₂₈ ?_
  intro Ω I u Du p f hsol z ρ hρ hsub
  exact lin34_hCZ_p1_of_residual_ae_of_sws hsol hρ hsub (hresidual hsol hρ hsub)

/-- **Theorem A start with the pressure oscillation fully discharged.**  The
residual decay input is supplied by
`lin34_centred_residual_local_growth_ae_of_sws`, so no analytic hypothesis about
the pressure remains: the start of Theorem A holds for every suitable weak
solution with force exponent `q > 5/2`. -/
theorem thmA_start_unconditional
    (q C₂₇ C₂₈ : ℝ)
    (hq : 5 / 2 < q) (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈) :
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
  refine thmA_start_of_centred_residual q C₂₇ C₂₈ hq hC₂₇ hC₂₈ ?_
  intro Ω I u Du p f hsol z ρ hρ hsub
  exact lin34_centred_residual_local_growth_ae_of_sws hsol hρ hsub

end CKN
