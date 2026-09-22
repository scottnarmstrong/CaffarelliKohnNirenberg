-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.InteriorBasic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Basic

/-!
# The Laplacian of a radial profile

This module records the coordinate identity used to study radial Newtonian potentials away from
their pole.
-/

open Set Filter
open scoped Topology
open CKN.Foundation.Parabolic CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Harmonic

private lemma hasFDerivAt_q (z : Vec3) :
    HasFDerivAt q
      (∑ i : Fin 3, (2 * z i) •
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
  have hfun : q = ∑ i : Fin 3, (fun y : Vec3 => y i * y i) := by
    funext y
    simp [q, pow_two]
  have hsum : HasFDerivAt
      (∑ i : Fin 3, (fun y : Vec3 => y i * y i))
      (∑ i : Fin 3, (2 * z i) •
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
    apply HasFDerivAt.sum
    intro i _hi
    have hprod := (hasFDerivAt_apply (𝕜 := ℝ) i z).mul
      (hasFDerivAt_apply (𝕜 := ℝ) i z)
    convert hprod using 1
    ext v
    simp [smul_eq_mul]
    ring_nf
  rw [hfun]
  exact hsum

private lemma spatialDeriv_comp_q_on_positive {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) {z : Vec3}
    (hz : 0 < q z) (i : Fin 3) :
    CKN.spatialDeriv (φ ∘ q) i z = 2 * z i * deriv φ (q z) := by
  have hφz : ContDiffAt ℝ 1 φ (q z) :=
    hφ.contDiffAt (Ioi_mem_nhds hz)
  have houter : HasFDerivAt φ
      ((deriv φ (q z)) • (1 : ℝ →L[ℝ] ℝ)) (q z) := by
    convert (hφz.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt using 1
    ext
    simp [smul_apply, ContinuousLinearMap.toSpanSingleton_apply]
  have hcomp := houter.comp z (hasFDerivAt_q z)
  change (fderiv ℝ (φ ∘ q) z) (CKN.basisVec i) = _
  rw [hcomp.fderiv]
  simp [smul_apply, CKN.basisVec_apply]
  ring

private lemma hasDerivAt_sq (r : ℝ) :
    HasDerivAt (fun x : ℝ => x * x) (2 * r) r := by
  convert (hasDerivAt_id r).mul (hasDerivAt_id r) using 1
  · rfl
  · simp only [id_eq]
    ring

/-- First derivative of a radial profile written in squared-radius coordinates. -/
theorem radialProfile_deriv {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0))
    {r : ℝ} (hr : 0 < r) :
    deriv (φ ∘ fun x : ℝ => x * x) r = 2 * r * deriv φ (r ^ 2) := by
  have hφr : ContDiffAt ℝ 1 φ (r * r) :=
    (hφ.of_le (by norm_num)).contDiffAt (Ioi_mem_nhds (by positivity))
  have hchain := HasDerivAt.comp (x := r) (h := fun x : ℝ => x * x)
    (hφr.differentiableAt (by norm_num)).hasDerivAt (hasDerivAt_sq r)
  rw [hchain.deriv]
  simp only [pow_two]
  ring

/-- Second derivative of a radial profile written in squared-radius coordinates. -/
theorem radialProfile_secondDeriv {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0)) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (φ ∘ fun x : ℝ => x * x)) r =
      2 * deriv φ (r ^ 2) + 4 * r ^ 2 * deriv (deriv φ) (r ^ 2) := by
  have hφ' : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) :=
    hφ.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hφ'r : ContDiffAt ℝ 1 (deriv φ) (r * r) :=
    hφ'.contDiffAt (Ioi_mem_nhds (by positivity))
  have hcomp := HasDerivAt.comp (x := r) (h := fun x : ℝ => x * x)
    (hφ'r.differentiableAt (by norm_num)).hasDerivAt (hasDerivAt_sq r)
  have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 r := by
    convert HasDerivAt.const_mul 2 (hasDerivAt_id r) using 1
    · funext x
      simp
    · ring
  have hprod := hlin.mul hcomp
  have hderiv1 : deriv (φ ∘ fun x : ℝ => x * x) =ᶠ[𝓝 r]
      (fun x => 2 * x * deriv φ (x ^ 2)) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    simpa only [pow_two] using radialProfile_deriv hφ hx
  have hderiv1' : deriv (φ ∘ fun x : ℝ => x * x) =ᶠ[𝓝 r]
      (fun x => (2 * x) * deriv φ (x * x)) := by
    simpa only [pow_two] using hderiv1
  have hderiv2 := hprod.congr_of_eventuallyEq hderiv1'
  rw [hderiv2.deriv]
  simp only [Function.comp_apply, pow_two]
  ring

/-- The three-dimensional Laplacian of a function of the squared radius. -/
theorem spatialLaplacian_comp_q_formula {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0)) {z : Vec3}
    (hz : 0 < q z) :
    CKN.spatialLaplacian (φ ∘ q) z =
      4 * q z * deriv (deriv φ) (q z) + 6 * deriv φ (q z) := by
  have hφ' : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) :=
    hφ.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hφ1 : ContDiffOn ℝ 1 φ (Set.Ioi 0) := hφ.of_le (by norm_num)
  have hqcont : Continuous q := by
    unfold q
    fun_prop
  have hs : q ⁻¹' Set.Ioi (0 : ℝ) ∈ 𝓝 z :=
    (isOpen_Ioi.preimage hqcont).mem_nhds hz
  have hsecond : ∀ i : Fin 3,
      CKN.spatialDeriv (CKN.spatialDeriv (φ ∘ q) i) i z =
        4 * (z i)^2 * deriv (deriv φ) (q z) +
          2 * deriv φ (q z) := by
    intro i
    have hφ'z : ContDiffAt ℝ 1 (deriv φ) (q z) :=
      hφ'.contDiffAt (Ioi_mem_nhds hz)
    have houter : HasFDerivAt (deriv φ)
        ((deriv (deriv φ) (q z)) • (1 : ℝ →L[ℝ] ℝ)) (q z) := by
      convert (hφ'z.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt using 1
      ext
      simp [smul_apply, ContinuousLinearMap.toSpanSingleton_apply]
    have hcomp := houter.comp z (hasFDerivAt_q z)
    have hcoord : HasFDerivAt (fun y : Vec3 => 2 * y i)
        (2 • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
      convert (hasFDerivAt_apply (𝕜 := ℝ) i z).const_mul 2 using 1
      ext v
      simp [smul_eq_mul]
    have hprod := hcoord.mul hcomp
    have heq : (fun y : Vec3 => CKN.spatialDeriv (φ ∘ q) i y) =ᶠ[𝓝 z]
        (fun y => (2 * y i) * deriv φ (q y)) := by
      filter_upwards [hs] with y hy
      rw [spatialDeriv_comp_q_on_positive hφ1 (by simpa using hy) i]
    have hderiv := hprod.congr_of_eventuallyEq heq
    have hpartial := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
      hderiv.fderiv
    change (fderiv ℝ (fun y => CKN.spatialDeriv (φ ∘ q) i y) z)
      (CKN.basisVec i) = _
    rw [hpartial]
    simp [smul_apply, CKN.basisVec_apply]
    ring
  rw [CKN.spatialLaplacian]
  rw [Finset.sum_congr rfl (by intro i hi; exact hsecond i)]
  simp [q, Fin.sum_univ_three]
  ring

end CKN.Foundation.Harmonic
