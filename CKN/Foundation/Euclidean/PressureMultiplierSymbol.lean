-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.DegreeOneSymbol
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The symbol of the pressure multiplier

The manuscript's pressure-multiplier discussion writes the localized
pressure gradient through the vector Fourier multipliers
`T_{jl} = -∇ ∂_j ∂_l Δ⁻¹` and prints for them the symbol
`ς_{jl}(ξ) = i ξ ξ_j ξ_l / |ξ|²`, homogeneous of degree one.  With the
normalization fixed in the same lemma, `∂_j ↦ i ξ_j` and `Δ⁻¹ ↦ -|ξ|⁻²`, the
symbol of `T_{jl}` is `-i ξ ξ_j ξ_l / |ξ|²`, so the printed formula is the
symbol of `-T_{jl} = ∇ ∂_j ∂_l Δ⁻¹`; the kernel `K_i = -∂_i ∂_j ∂_l N` recorded
for `T_{jl}` in the same section gives the same answer.  Erratum for the
source: the printed `ς_{jl}` should carry a minus sign.

This file defines the `m`-th component of the symbol exactly as printed, which
is the sign that matches the explicit kernel `subordinatedKernel` of
`CKN/Foundation/Heat/Subordination.lean`, and certifies that it belongs to the
symbol class of External Input `ext:heat-kernel`: smooth away from the origin
and homogeneous of degree one.  A consumer that needs the symbol of `T_{jl}`
itself takes the negation, which lies in the same class.
-/

open scoped BigOperators
open Set

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- The `m`-th component `i ξ_m ξ_j ξ_l / |ξ|²` of the symbol printed for the
pressure multiplier in the manuscript's pressure-multiplier discussion.  It is the symbol of
`-T_{jl} = ∇ ∂_j ∂_l Δ⁻¹`; the symbol of `T_{jl}` itself is its negation, which
lies in the same class.  At the origin the quotient is the Lean junk value `0`,
which is the value forced by degree-one homogeneity and does not affect any
integral against it. -/
def pressureMultiplierSymbol (j l m : Fin 3) (ξ : Vec3) : ℂ :=
  Complex.I * ((ξ m * ξ j * ξ l / vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)

private theorem sq_norm_eq_sum (ξ : Vec3) :
    vec3EuclideanNorm ξ ^ 2 = ∑ i, ξ i ^ 2 := by
  unfold vec3EuclideanNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- The symbol `ς_{jl}` in the manuscript's pressure-multiplier discussion is homogeneous of
degree one. -/
theorem pressureMultiplierSymbol_isDegreeOneHomogeneous (j l m : Fin 3) :
    IsDegreeOneHomogeneous (pressureMultiplierSymbol j l m) := by
  intro a ha ξ
  unfold pressureMultiplierSymbol
  have hcomp : ∀ i : Fin 3, (a • ξ) i = a * ξ i := fun i => rfl
  have hden : vec3EuclideanNorm (a • ξ) ^ 2 = a ^ 2 * vec3EuclideanNorm ξ ^ 2 := by
    rw [vec3EuclideanNorm_smul, abs_of_pos ha, mul_pow]
  have hnum : (a • ξ) m * (a • ξ) j * (a • ξ) l = a ^ 2 * (a * (ξ m * ξ j * ξ l)) := by
    rw [hcomp, hcomp, hcomp]; ring
  have hane : (a : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  have hratio : (a • ξ) m * (a • ξ) j * (a • ξ) l / vec3EuclideanNorm (a • ξ) ^ 2 =
      a * (ξ m * ξ j * ξ l / vec3EuclideanNorm ξ ^ 2) := by
    rw [hnum, hden, mul_div_mul_left _ _ hane, mul_div_assoc]
  rw [hratio]
  push_cast
  ring

/-- The symbol `ς_{jl}` in the manuscript's pressure-multiplier discussion is smooth away
from the origin, as the symbol class of External Input `ext:heat-kernel`
requires. -/
theorem pressureMultiplierSymbol_contDiffOn (j l m : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (pressureMultiplierSymbol j l m) ({0}ᶜ : Set Vec3) := by
  have hnum : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec3 => ξ m * ξ j * ξ l) :=
    (((contDiff_apply ℝ ℝ m).mul (contDiff_apply ℝ ℝ j)).mul (contDiff_apply ℝ ℝ l))
  have hden : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Vec3 => vec3EuclideanNorm ξ ^ 2) := by
    have hrw : (fun ξ : Vec3 => vec3EuclideanNorm ξ ^ 2) = fun ξ : Vec3 => ∑ i, ξ i ^ 2 := by
      funext ξ; exact sq_norm_eq_sum ξ
    rw [hrw]
    exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2
  have hne : ∀ ξ ∈ ({0}ᶜ : Set Vec3), vec3EuclideanNorm ξ ^ 2 ≠ 0 := by
    intro ξ hξ
    rw [sq_norm_eq_sum]
    intro hsum
    apply hξ
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Finset.univ) => sq_nonneg (ξ k))).1 hsum i (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hi
  have hdiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun ξ : Vec3 => ξ m * ξ j * ξ l / vec3EuclideanNorm ξ ^ 2) ({0}ᶜ : Set Vec3) :=
    (hnum.contDiffOn).div (hden.contDiffOn) hne
  have hcast : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun ξ : Vec3 => ((ξ m * ξ j * ξ l / vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))
      ({0}ᶜ : Set Vec3) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hdiv)
  exact contDiffOn_const.mul hcast

end CKN.Foundation.Euclidean
