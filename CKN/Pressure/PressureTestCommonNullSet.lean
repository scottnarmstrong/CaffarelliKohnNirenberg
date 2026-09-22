-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.DeltaPCentredMeanFreeAllTests

/-! # A common exceptional set for pressure tests on a cylinder

The spatial pressure identity is restricted to the open cylinder time window
before the test function is selected, retaining the original solution fields.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN

/-- The centred pressure equation holds simultaneously for every compact smooth
test on the ball, outside one null set in the open cylinder time window. -/
theorem pressure_delta_p_common_null_set
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z₀.1 z₀.2 ρ) ⊆ spaceTimeSet Ω I)
    : ∀ᵐ s ∂volume.restrict (Ioo (z₀.2 - ρ ^ 2) z₀.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ vec3Ball z₀.1 ρ →
      (∫ y in vec3Ball z₀.1 ρ, p (y,s) * spatialLaplacian ψ y) =
        (∫ y in vec3Ball z₀.1 ρ, ∑ i : Fin 3, ∑ j : Fin 3,
          (-u (y,s) i * (u (y,s) j - ⨍ w in vec3Ball z₀.1 ρ, u (w,s) j)) *
            mixedSecond ψ i j y) -
        ∫ y in vec3Ball z₀.1 ρ, ∑ i : Fin 3, f (y,s) i * spatialDeriv ψ i y := by
  have ht : z₀.2 ∈ Ioc (z₀.2 - ρ ^ 2) z₀.2 :=
    ⟨sub_lt_self _ (sq_pos_of_pos hρ), le_rfl⟩
  have hball : closure (vec3Ball z₀.1 ρ) ⊆ Ω := by
    intro x hx
    have hmem : (x, z₀.2) ∈ closure (parabolicCylinder z₀.1 z₀.2 ρ) := by
      rw [closure_parabolicCylinder hρ]
      rw [closure_vec3Ball hρ] at hx
      exact ⟨hx, ht.1.le, ht.2⟩
    exact (hsub hmem).1
  have htime : Ioo (z₀.2 - ρ ^ 2) z₀.2 ⊆ I := by
    intro s hs
    have hx : z₀.1 ∈ vec3Ball z₀.1 ρ := by
      change vec3EuclideanNorm (z₀.1 - z₀.1) < ρ
      simpa only [sub_self, vec3EuclideanNorm_zero] using hρ
    have hmem : (z₀.1, s) ∈ parabolicCylinder z₀.1 z₀.2 ρ :=
      ⟨hx, hs.1, hs.2.le⟩
    exact (hsub (subset_closure hmem)).2
  have h := pressure_delta_p_meanFree_ae_forall_of_sws hsol hρ hball
  filter_upwards [ae_mono (Measure.restrict_mono htime le_rfl) h] with s hs
  intro ψ hψ hψc hψB
  simpa only [utensor, meanFreeComponent] using hs ψ hψ hψc hψB


end CKN
