-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.LpExtensionExterior
import CKN.Foundation.Euclidean.LpExtensionCZ
import CKN.Pressure.IdentificationExtensionUnconditional

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Euclidean

open CKN
open CKN.Foundation.Heat

/- The three exterior results have a common consumer shape.  Keeping this
   adapter here leaves the owner interfaces unchanged while making the
   separation and support hypotheses explicit at each use. -/
theorem rieszSecondP1ExtensionOperator_exterior_consumer
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Vec3 → ℝ} (hG : MemLp G (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : HasCompactSupport G) {A U : Set Vec3} (hU : IsOpen U)
    (hGA : ∀ y ∉ A, G y = 0) (hAb : Bornology.IsBounded A) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A,
      δ ≤ vec3EuclideanNorm (x - y)) :
    rieszSecondP1ExtensionOperator hL2 hWeak11 G =ᵐ[volume.restrict U]
      (fun x => ∫ y,
        (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * G y) := by
  exact rieszSecondP1ExtensionOperator_agrees_exterior hL2 hWeak11 hG hGc
    hU hGA hAb hδ hsep

theorem rieszSecondGradientExtensionOperator_exterior_consumer
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Vec3 → ℝ} (hG : MemLp G (ENNReal.ofReal ((6 : ℝ) / 5)) volume)
    (hGc : HasCompactSupport G) {A U : Set Vec3} (hU : IsOpen U)
    (hGA : ∀ y ∉ A, G y = 0) (hAb : Bornology.IsBounded A) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A,
      δ ≤ vec3EuclideanNorm (x - y)) :
    rieszSecondGradientExtensionOperator hL2 hWeak11 G =ᵐ[volume.restrict U]
      (fun x => ∫ y,
        (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * G y) := by
  exact rieszSecondGradientExtensionOperator_agrees_exterior hL2 hWeak11 hG hGc
    hU hGA hAb hδ hsep

theorem pressureSecondExtensionOperator_exterior_consumer
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j, ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j)) {A U : Set Vec3} (hU : IsOpen U)
    (hGA : ∀ i j y, y ∉ A → G i j y = 0)
    (hAb : Bornology.IsBounded A) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A,
      δ ≤ vec3EuclideanNorm (x - y)) :
    pressureSecondExtensionOperator hL2 hWeak11 G =ᵐ[volume.restrict U]
      (fun x => ∑ i, ∑ j, ∫ y,
        (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * G i j y) := by
  exact pressureSecondExtensionOperator_agrees_exterior hL2 hWeak11 hG hGc
    hU hGA hAb hδ hsep

/- This is the exact composition used by the global CZ consumer once the
   whole-space identification has supplied the a.e. extension equality. -/
theorem hCZ_p1_unconditional_of_extension_identification
    (C_CZ C₁₁ E : ℝ) (_ : 0 ≤ C_CZ)
    (hoperator : czP1OperatorConstant ≤ C_CZ)
    (hconst : C_CZ ≤ C₁₁) (hE : 0 ≤ E)
    {p₁ : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j))
    (hsource : (∑ i, ∑ j, lpNorm (G i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ≤ E ^ (2 / 3 : ℝ))
    (hident : p₁ =ᵐ[volume] pressureSecondExtensionOperator
      rieszSecondL2Input rieszSecondL2_weak_type G) :
    lpNorm p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      C₁₁ * E ^ (2 / 3 : ℝ) := by
  have hident' : p₁ =ᵐ[volume]
      rieszSecondP1ExtensionTensorOperator
        rieszSecondL2Input rieszSecondL2_weak_type G := by
    simpa only [pressureSecondExtensionOperator] using hident
  have hp := pressure_lpNorm_le_of_rieszSecond_p1_tensor_extension
    (hL2 := fun i j => rieszSecondL2Input i j)
    (hWeak11 := fun i j => rieszSecondL2_weak_type i j)
    hG hGc hident' hsource hoperator hE
  exact hp.trans (mul_le_mul_of_nonneg_right hconst
    (Real.rpow_nonneg hE _))

/- K's whole-space identity supplies the identification input; the exterior
   formula is intentionally not used to turn that global statement into a
   pointwise singular-integral formula. -/
theorem hCZ_p1_unconditional_of_whole_space_extension
    (C_CZ C₁₁ E C : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hoperator : czP1OperatorConstant ≤ C_CZ)
    (hconst : C_CZ ≤ C₁₁) (hE : 0 ≤ E) (hC : 0 ≤ C)
    {p₁ : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j))
    (hsource : (∑ i, ∑ j, lpNorm (G i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ≤ E ^ (2 / 3 : ℝ))
    (hP1 : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume →
      ∫ x, p₁ x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hP1Int : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume)
    (hmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp (fun x => p₁ x - pressureSecondExtensionOperator
        rieszSecondL2Input rieszSecondL2_weak_type G x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hgrowth : ∀ ρ : ℝ, 0 < ρ →
      lpNorm (fun x => p₁ x - pressureSecondExtensionOperator
        rieszSecondL2Input rieszSecondL2_weak_type G x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ)) :
    lpNorm p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      C₁₁ * E ^ (2 / 3 : ℝ) := by
  have hident := pressureP1_hident_of_pressureSecondExtension_unconditional
    hC hG hP1 hP1Int hmem hgrowth
  exact hCZ_p1_unconditional_of_extension_identification C_CZ C₁₁ E
    hC_CZ hoperator hconst hE hG hGc hsource hident

/- The extension bound and the source norm control produce the two residual
   growth premises once a global MemLp witness for p₁ is available. -/
theorem hCZ_p1_unconditional_of_global_p1_memLp
    (C_CZ C₁₁ E : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hoperator : czP1OperatorConstant ≤ C_CZ)
    (hconst : C_CZ ≤ C₁₁) (hE : 0 ≤ E)
    {p₁ : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j))
    (hsource : (∑ i, ∑ j, lpNorm (G i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ≤ E ^ (2 / 3 : ℝ))
    (hp₁ : MemLp p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hP1 : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume →
      ∫ x, p₁ x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hP1Int : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume) :
    lpNorm p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      C₁₁ * E ^ (2 / 3 : ℝ) := by
  have hres := pressureSecondExtension_residual_local_growth_of_source_bound
    hG hGc hsource hE hp₁
  have hC : 0 ≤ lpNorm p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume +
      czP1OperatorConstant * E ^ (2 / 3 : ℝ) := by
    have hcz : 0 ≤ czP1OperatorConstant := by
      unfold czP1OperatorConstant czP1Constant
      positivity
    exact add_nonneg lpNorm_nonneg
      (mul_nonneg hcz (Real.rpow_nonneg hE _))
  exact hCZ_p1_unconditional C_CZ C₁₁ E
    (lpNorm p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume +
      czP1OperatorConstant * E ^ (2 / 3 : ℝ))
    hC_CZ hoperator hconst hE hC hG hGc hsource hP1 hP1Int hres.1 hres.2

end CKN.Foundation.Euclidean
