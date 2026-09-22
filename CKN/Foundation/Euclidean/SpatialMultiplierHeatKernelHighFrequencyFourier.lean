-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelL1
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier bounds for the damped high-frequency symbol
-/

open scoped BigOperators FourierTransform
open MeasureTheory

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat VectorFourier

/-- Integration by parts gives a uniform Fourier bound for a damped cutoff symbol. -/
theorem exists_uniform_fourierIntegral_highDampedFrequency
    {τ : Vec3 → ℂ} (d : ℕ) (hd : d ≤ 3)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ w : Vec3,
      vec3EuclideanNorm w = 1 →
      ‖fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂
        (highDampedFrequencyFunction τ t) w‖ ≤ C := by
  obtain ⟨C, hC, hL1⟩ :=
    exists_uniform_integral_iteratedFDeriv_highDampedFrequency d hd hτ hhom
  let n := d + 4
  refine ⟨C, hC, ?_⟩
  intro t ht ht1 w hw
  have hn : n ≤ 7 := by dsimp [n]; omega
  have hf : ContDiff ℝ (n : ℕ∞) (highDampedFrequencyFunction τ t) :=
    (highDampedFrequencyFunction_contDiff hτ t).of_le (by exact_mod_cast le_top)
  have h'f : ∀ k : ℕ, k ≤ n →
      Integrable (iteratedFDeriv ℝ k (highDampedFrequencyFunction τ t)) volume := by
    intro k hk
    exact integrable_iteratedFDeriv_highDampedFrequency d k (by omega) hτ hhom t ht
  have hwNorm : ‖w‖ ≤ 1 := (norm_le_vec3EuclideanNorm w).trans_eq hw
  have hparts := norm_fourierIntegral_by_iteratedFDeriv
    frequencyFourierBilinear (highDampedFrequencyFunction τ t) n
    frequencyFourierBilinear_symm hf h'f w w hwNorm
  have hsum : (∑ j : Fin 3, w j * w j : ℝ) = 1 := by
    have hsum' : (∑ j : Fin 3, w j * w j : ℝ) = ∑ j : Fin 3, w j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum', ← vec3EuclideanNorm_sq, hw]
    norm_num
  have hLval : frequencyFourierBilinear w w = -((2 * Real.pi)⁻¹) := by
    rw [frequencyFourierBilinear_apply, hsum]
    ring
  have habs : |frequencyFourierBilinear w w| = (2 * Real.pi)⁻¹ := by
    rw [hLval, abs_neg, abs_of_pos (inv_pos.mpr (by positivity))]
  have hcoef : (2 * Real.pi) ^ n *
      |frequencyFourierBilinear w w| ^ n = 1 := by
    rw [habs, ← mul_pow]
    rw [mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    norm_num
  have hpoint :
      ‖fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂
        (highDampedFrequencyFunction τ t) w‖ ≤
        ∫ ξ : Vec3,
          ‖iteratedFDeriv ℝ n (highDampedFrequencyFunction τ t) ξ‖ := by
    calc
      ‖fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂
          (highDampedFrequencyFunction τ t) w‖ =
          ((2 * Real.pi) ^ n *
            |frequencyFourierBilinear w w| ^ n) *
              ‖fourierIntegral 𝐞 volume frequencyFourierBilinear.toLinearMap₁₂
                (highDampedFrequencyFunction τ t) w‖ := by rw [hcoef]; ring
      _ ≤ ∫ ξ : Vec3,
          ‖iteratedFDeriv ℝ n (highDampedFrequencyFunction τ t) ξ‖ := hparts
  exact hpoint.trans (by simpa [n] using (hL1 t ht ht1).2)

end CKN.Foundation.Euclidean
