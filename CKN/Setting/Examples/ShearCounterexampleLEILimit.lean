-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.Examples.ShearCounterexample.LEIHelpers
import CKN.Setting.Examples.ShearCounterexampleDivergenceLimit
import CKN.Setting.Examples.ShearCounterexampleMomentumLimit
import CKN.Setting.Examples.ShearCounterexampleSupportBridge
import CKN.Statements.SpaceTimeTestFunction
import CKN.Foundation.Parabolic.Integration.Average
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Local energy identities for the rough parabolic shear. -/

set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped ENNReal Topology
namespace CKN

private theorem shearFullScalar_nonneg_ae :
    ∀ᵐ z : ParabolicPoint ∂volume, 0 ≤ shearFullScalar z := by
  filter_upwards [shearFullScalarPartial_le_ae 0] with z h0
  have hpartial : shearFullScalarPartial 0 z = 0 := by
    simp [shearFullScalarPartial, shearReducedBumpPartial]
  rw [hpartial] at h0
  exact h0

private theorem lei_test_heat_zero_outside {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) :
    timePartial (show ParabolicPoint → ℝ from ψ) z +
      ∑ i : Fin 3, spatialSecondPartial
        (show ParabolicPoint → ℝ from ψ) i i z = 0 := by
  have ht := lei_timePartial_zero_of_not_tsupport hψ hz
  have hsum : ∑ i : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from ψ) i i z = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact lei_spatialSecond_zero_of_not_tsupport hψ i hz
  rw [ht, hsum]
  ring

private theorem lei_test_divergence_zero_outside {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) :
    ∑ i : Fin 3, shearCounterexampleVelocity z i *
      spatialPartial (show ParabolicPoint → ℝ from ψ) i z = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [lei_spatialPartial_zero_of_not_tsupport hψ i hz]
  simp

private theorem lei_test_divergence_zero_outside_partial {N : ℕ}
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) :
    ∑ i : Fin 3, shearCounterexampleVelocityPartial N z i *
      spatialPartial (show ParabolicPoint → ℝ from ψ) i z = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [lei_spatialPartial_zero_of_not_tsupport hψ i hz]
  simp

private theorem shearLEILeft_zero_of_not_tsupport (ψ : Vec3 × ℝ → ℝ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) : shearLEILeft ψ z = 0 := by
  have hψz : ψ z = 0 := lei_zero_of_not_tsupport hz
  simp [shearLEILeft, hψz]

private theorem shearLEIRight_zero_of_not_tsupport (ψ : Vec3 × ℝ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) : shearLEIRight ψ z = 0 := by
  have hψz : ψ z = 0 := lei_zero_of_not_tsupport hz
  have hheat := lei_test_heat_zero_outside hψ hz
  have hdiv := lei_test_divergence_zero_outside hψ hz
  simp [shearLEIRight, hψz, hheat, hdiv]

private theorem shearLEILeftPartial_zero_of_not_tsupport (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) : shearLEILeftPartial N ψ z = 0 := by
  have hψz : ψ z = 0 := lei_zero_of_not_tsupport hz
  simp [shearLEILeftPartial, hψz]

private theorem shearLEIRightPartial_zero_of_not_tsupport (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) :
    shearLEIRightPartial N ψ z = 0 := by
  have hψz : ψ z = 0 := lei_zero_of_not_tsupport hz
  have hheat := lei_test_heat_zero_outside hψ hz
  have hdiv := lei_test_divergence_zero_outside_partial (N := N) hψ hz
  simp [shearLEIRightPartial, hψz, hheat, hdiv]

private theorem lei_tsupport_subset_test {ψ : Vec3 × ℝ → ℝ}
    {g : Vec3 × ℝ → ℝ} (hzero : ∀ z, z ∉ tsupport ψ → g z = 0) :
    tsupport g ⊆ tsupport ψ := by
  have hsupp : Function.support g ⊆ tsupport ψ := by
    intro z hz
    by_contra hnot
    exact (Function.mem_support.mp hz) (hzero z hnot)
  change closure (Function.support g) ⊆ tsupport ψ
  exact closure_minimal hsupp (isClosed_tsupport ψ)

private theorem lei_left_tsupport_subset_test (ψ : Vec3 × ℝ → ℝ) :
    tsupport (shearLEILeft ψ) ⊆ tsupport ψ :=
  lei_tsupport_subset_test (fun (z : Vec3 × ℝ) hz =>
    shearLEILeft_zero_of_not_tsupport ψ (z := z) hz)

private theorem lei_right_tsupport_subset_test (ψ : Vec3 × ℝ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    tsupport (shearLEIRight ψ) ⊆ tsupport ψ :=
  lei_tsupport_subset_test (fun (z : Vec3 × ℝ) hz =>
    shearLEIRight_zero_of_not_tsupport ψ hψ (z := z) hz)

private theorem lei_left_partial_tsupport_subset_test (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) :
    tsupport (shearLEILeftPartial N ψ) ⊆ tsupport ψ :=
  lei_tsupport_subset_test (fun (z : Vec3 × ℝ) hz =>
    shearLEILeftPartial_zero_of_not_tsupport N ψ (z := z) hz)

private theorem lei_right_partial_tsupport_subset_test (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    tsupport (shearLEIRightPartial N ψ) ⊆ tsupport ψ :=
  lei_tsupport_subset_test (fun (z : Vec3 × ℝ) hz =>
    shearLEIRightPartial_zero_of_not_tsupport N ψ hψ (z := z) hz)

private theorem lei_left_partial_tendsto_ae (ψ : Vec3 × ℝ → ℝ) :
    ∀ᵐ z : ParabolicPoint ∂volume,
      Tendsto (fun N => shearLEILeftPartial N ψ z) atTop
        (𝓝 (shearLEILeft ψ z)) := by
  filter_upwards [shearFullGradientPartial_tendsto_ae 0,
    shearFullGradientPartial_tendsto_ae 1] with z hG0 hG1
  have hsum := (hG0.pow 2).add (hG1.pow 2)
  have hmul := hsum.mul_const (ψ z)
  have hseq : (fun N => shearLEILeftPartial N ψ (show Vec3 × ℝ from z)) =
      fun N => ((shearFullGradientPartial 0 N z) ^ 2 +
        (shearFullGradientPartial 1 N z) ^ 2) * ψ z := by
    funext N
    exact lei_left_partial_scalar_simplify N ψ (show Vec3 × ℝ from z)
  have hlim : shearLEILeft ψ (show Vec3 × ℝ from z) =
      ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) * ψ z :=
    lei_left_scalar_simplify ψ (show Vec3 × ℝ from z)
  rw [hseq, hlim]
  exact hmul

private theorem lei_right_partial_tendsto_ae (ψ : Vec3 × ℝ → ℝ) :
    ∀ᵐ z : ParabolicPoint ∂volume,
      Tendsto (fun N => shearLEIRightPartial N ψ z) atTop
        (𝓝 (shearLEIRight ψ z)) := by
  filter_upwards [shearFullScalarPartial_tendsto_ae,
    shearFullForcePartial_tendsto_ae] with z hW hF
  let heat : ℝ := timePartial (show ParabolicPoint → ℝ from ψ) z +
    ∑ i : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from ψ) i i z
  let ψ2 : ℝ := spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z
  have hA : Tendsto (fun N => shearFullScalarPartial N z ^ 2 * heat) atTop
      (𝓝 (shearFullScalar z ^ 2 * heat)) := (hW.pow 2).mul_const heat
  have hB : Tendsto (fun N => shearFullScalarPartial N z ^ 3 * ψ2) atTop
      (𝓝 (shearFullScalar z ^ 3 * ψ2)) := (hW.pow 3).mul_const ψ2
  have hF' : Tendsto (fun N => (2 : ℝ) * shearFullForcePartial N z) atTop
      (𝓝 (2 * shearFullForceScalar z)) := tendsto_const_nhds.mul hF
  have hC : Tendsto (fun N =>
      2 * shearFullForcePartial N z * shearFullScalarPartial N z * ψ z) atTop
      (𝓝 (2 * shearFullForceScalar z * shearFullScalar z * ψ z)) := by
    have hmul := (hF'.mul hW).mul_const (ψ z)
    simpa [mul_assoc] using hmul
  have hsum := (hA.add hB).add hC
  have hseq : (fun N => shearLEIRightPartial N ψ (show Vec3 × ℝ from z)) =
      fun N => shearFullScalarPartial N z ^ 2 * heat +
        shearFullScalarPartial N z ^ 3 * ψ2 +
        2 * shearFullForcePartial N z * shearFullScalarPartial N z * ψ z := by
    funext N
    simpa [heat, ψ2] using
      (lei_rhs_partial_scalar_simplify N ψ (show Vec3 × ℝ from z))
  have hlim : shearLEIRight ψ (show Vec3 × ℝ from z) =
      shearFullScalar z ^ 2 * heat + shearFullScalar z ^ 3 * ψ2 +
        2 * shearFullForceScalar z * shearFullScalar z * ψ z := by
    simpa [heat, ψ2] using lei_rhs_scalar_simplify ψ (show Vec3 × ℝ from z)
  rw [hseq, hlim]
  exact hsum

private theorem shearLEILeftPartial_norm_le (N : ℕ) (ψ : Vec3 × ℝ → ℝ)
    (hψnonneg : ∀ z, 0 ≤ ψ z) (z : Vec3 × ℝ) :
    ‖shearLEILeftPartial N ψ z‖ ≤ shearLEIMajorant ψ z := by
  have henergy : spatialGradientSq (shearCounterexampleVelocityPartial N)
      (shearCounterexampleDuPartial N) z ≤
      spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z :=
    shearCounterexampleDuPartial_energy_le N z
  have henergyN : 0 ≤ spatialGradientSq (shearCounterexampleVelocityPartial N)
      (shearCounterexampleDuPartial N) z := by
    simp [spatialGradientSq]
    positivity
  have hψ := hψnonneg z
  have henergyS :
      (shearFullGradientPartial 0 N z) ^ 2 +
        (shearFullGradientPartial 1 N z) ^ 2 ≤
      (shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2 := by
    rw [← shearCounterexampleDuPartial_energy_eq N (show ParabolicPoint from z),
      ← shearCounterexampleDu_energy_eq (show ParabolicPoint from z)]
    exact henergy
  rw [Real.norm_eq_abs, lei_left_partial_scalar_simplify]
  rw [abs_of_nonneg (mul_nonneg
    (add_nonneg (sq_nonneg (shearFullGradientPartial 0 N z))
      (sq_nonneg (shearFullGradientPartial 1 N z))) hψ)]
  dsimp [shearLEIMajorant]
  rw [abs_of_nonneg hψ]
  calc
    _ ≤ ((shearFullGradient 0 z) ^ 2 +
        (shearFullGradient 1 z) ^ 2) * ψ z :=
      mul_le_mul_of_nonneg_right henergyS hψ
    _ ≤ ((shearFullGradient 0 z) ^ 2 +
        (shearFullGradient 1 z) ^ 2) * ψ z +
        |shearFullScalar z| ^ 2 *
          |timePartial ψ z +
            ∑ i : Fin 3, spatialSecondPartial ψ i i z| +
        |shearFullScalar z| ^ 3 *
          |spatialPartial ψ 2 z| +
        2 * |shearFullForceScalar z| * |shearFullScalar z| * ψ z := by
      calc
        _ ≤ ((shearFullGradient 0 z) ^ 2 +
            (shearFullGradient 1 z) ^ 2) * ψ z +
            |shearFullScalar z| ^ 2 *
              |timePartial ψ z +
                ∑ i : Fin 3, spatialSecondPartial ψ i i z| :=
          le_add_of_nonneg_right (by positivity)
        _ ≤ ((shearFullGradient 0 z) ^ 2 +
            (shearFullGradient 1 z) ^ 2) * ψ z +
            |shearFullScalar z| ^ 2 *
              |timePartial ψ z +
                ∑ i : Fin 3, spatialSecondPartial ψ i i z| +
            |shearFullScalar z| ^ 3 *
              |spatialPartial ψ 2 z| :=
          le_add_of_nonneg_right (by positivity)
        _ ≤ ((shearFullGradient 0 z) ^ 2 +
            (shearFullGradient 1 z) ^ 2) * ψ z +
            |shearFullScalar z| ^ 2 *
              |timePartial ψ z +
                ∑ i : Fin 3, spatialSecondPartial ψ i i z| +
            |shearFullScalar z| ^ 3 *
              |spatialPartial ψ 2 z| +
            2 * |shearFullForceScalar z| * |shearFullScalar z| * ψ z :=
          le_add_of_nonneg_right (by positivity)

private theorem shearLEIRightPartial_norm_le_ae (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) :
    ∀ᵐ z : Vec3 × ℝ ∂volume,
      ‖shearLEIRightPartial N ψ z‖ ≤ shearLEIMajorant ψ z := by
  have hWnonneg := shearFullScalar_nonneg_ae
  have hWNle := shearFullScalarPartial_le_ae N
  have hFbound : ∀ᵐ z : ParabolicPoint ∂volume,
      |shearFullForcePartial N z| ≤ |shearFullForceScalar z| :=
    Filter.Eventually.of_forall (shearFullForcePartial_abs_le N)
  filter_upwards [hWnonneg, hWNle, hFbound] with z hW0 hWNle hFabs
  change |shearFullForcePartial N z| ≤ |shearFullForceScalar z| at hFabs
  let W : ℝ := shearFullScalar z
  let WN : ℝ := shearFullScalarPartial N z
  let F : ℝ := shearFullForceScalar z
  let FN : ℝ := shearFullForcePartial N z
  let H : ℝ := timePartial (show ParabolicPoint → ℝ from ψ) z +
    ∑ i : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from ψ) i i z
  let ψ2 : ℝ := spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z
  have hWN0 : 0 ≤ WN := by
    exact shearCounterexampleVelocityPartial_nonneg N z
  have hWNle' : WN ≤ W := hWNle
  have hW0' : 0 ≤ W := hW0
  have hWN2 : WN ^ 2 ≤ W ^ 2 := by
    nlinarith only [hWN0, hWNle', hW0']
  have hWN3 : WN ^ 3 ≤ W ^ 3 := by
    calc
      WN ^ 3 = WN ^ 2 * WN := by ring
      _ ≤ W ^ 2 * W := mul_le_mul hWN2 hWNle' hWN0 (sq_nonneg W)
      _ = W ^ 3 := by ring
  have hterm1 : |WN ^ 2 * H| ≤ |W| ^ 2 * |H| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg WN), abs_of_nonneg hW0']
    exact mul_le_mul_of_nonneg_right hWN2 (abs_nonneg H)
  have hterm2 : |WN ^ 3 * ψ2| ≤ |W| ^ 3 * |ψ2| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hWN0 3), abs_of_nonneg hW0']
    exact mul_le_mul_of_nonneg_right hWN3 (abs_nonneg ψ2)
  have hterm3 : |2 * FN * WN * ψ z| ≤ 2 * |F| * |W| * |ψ z| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
      abs_of_nonneg hWN0, abs_of_nonneg hW0']
    calc
      2 * |FN| * WN * |ψ z| ≤ 2 * |F| * WN * |ψ z| := by gcongr
      _ ≤ 2 * |F| * W * |ψ z| := by gcongr
  have htri : |WN ^ 2 * H + WN ^ 3 * ψ2 + 2 * FN * WN * ψ z| ≤
      |WN ^ 2 * H| + |WN ^ 3 * ψ2| + |2 * FN * WN * ψ z| := by
    calc
      _ ≤ |WN ^ 2 * H + WN ^ 3 * ψ2| + |2 * FN * WN * ψ z| := abs_add_le _ _
      _ ≤ |WN ^ 2 * H| + |WN ^ 3 * ψ2| + |2 * FN * WN * ψ z| := by
        gcongr
        exact abs_add_le _ _
  rw [Real.norm_eq_abs,
    lei_rhs_partial_scalar_simplify N ψ (show Vec3 × ℝ from z)]
  change |WN ^ 2 * H + WN ^ 3 * ψ2 +
      2 * FN * WN * ψ z| ≤
    ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) * |ψ z| +
      |W| ^ 2 * |H| + |W| ^ 3 * |ψ2| +
      2 * |F| * |W| * |ψ z|
  calc
    |WN ^ 2 * H + WN ^ 3 * ψ2 + 2 * FN * WN * ψ z|
      ≤ |WN ^ 2 * H| + |WN ^ 3 * ψ2| + |2 * FN * WN * ψ z| := htri
    _ ≤ |shearFullScalar z| ^ 2 *
        |H| + |W| ^ 3 * |ψ2| + 2 * |F| * |W| * |ψ z| := by
        exact add_le_add (add_le_add hterm1 hterm2) hterm3
    _ ≤ ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) * |ψ z| +
        |W| ^ 2 * |H| + |W| ^ 3 * |ψ2| + 2 * |F| * |W| * |ψ z| := by
      have hgrad : 0 ≤ ((shearFullGradient 0 z) ^ 2 +
          (shearFullGradient 1 z) ^ 2) * |ψ z| := by positivity
      linarith only [hgrad]
    _ = shearLEIMajorant ψ z := by rfl

private theorem lei_testHeat_contDiff {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      timePartial (show ParabolicPoint → ℝ from ψ) z + ∑ i : Fin 3,
        spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z) := by
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ∑ i : Fin 3,
      spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z) := by
    apply ContDiff.sum (s := Finset.univ)
    intro i hi
    exact spatialPartial_contDiff (spatialPartial_contDiff hψ i) i
  exact (timePartial_contDiff hψ).add hsum

private theorem shearLEILeftPartial_continuous (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Continuous (shearLEILeftPartial N ψ) := by
  have hEq : shearLEILeftPartial N ψ = fun z =>
      ((shearFullGradientPartial 0 N z) ^ 2 +
        (shearFullGradientPartial 1 N z) ^ 2) * ψ z := by
    funext z
    exact lei_left_partial_scalar_simplify N ψ z
  rw [hEq]
  exact ((shearFullGradientPartial_contDiff N 0).continuous.pow 2).add
    ((shearFullGradientPartial_contDiff N 1).continuous.pow 2) |>.mul hψ.continuous

private theorem shearLEIRightPartial_continuous (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Continuous (shearLEIRightPartial N ψ) := by
  let heat : Vec3 × ℝ → ℝ := fun z =>
    timePartial (show ParabolicPoint → ℝ from ψ) z + ∑ i : Fin 3,
      spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z
  let ψ2 : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z
  have hEq : shearLEIRightPartial N ψ = fun z =>
      shearFullScalarPartial N z ^ 2 * heat z +
        shearFullScalarPartial N z ^ 3 * ψ2 z +
        2 * shearFullForcePartial N z * shearFullScalarPartial N z * ψ z := by
    funext z
    simpa [heat, ψ2] using lei_rhs_partial_scalar_simplify N ψ z
  have hWprod : Continuous (fun z : Vec3 × ℝ => shearFullScalarPartial N z) :=
    (shearFullScalarPartial_contDiff N).continuous
  have hheat : Continuous heat := (lei_testHeat_contDiff hψ).continuous
  have hψ2 : Continuous ψ2 := (spatialPartial_contDiff hψ 2).continuous
  have hFpar : Continuous (shearFullForcePartial N) :=
    shearFullForcePartial_continuous N
  have hF : Continuous (fun z : Vec3 × ℝ => shearFullForcePartial N z) := by
    change Continuous ((show ParabolicPoint → ℝ from shearFullForcePartial N) ∘
      parabolicHomeomorph.symm)
    exact hFpar.comp parabolicHomeomorph.symm.continuous
  rw [hEq]
  change Continuous (fun z : Vec3 × ℝ =>
    shearFullScalarPartial N z ^ 2 * heat z +
      shearFullScalarPartial N z ^ 3 * ψ2 z +
      2 * shearFullForcePartial N z * shearFullScalarPartial N z * ψ z)
  exact (((hWprod.pow 2).mul hheat).add ((hWprod.pow 3).mul hψ2)).add
    (((((continuous_const : Continuous
      (fun _ : Vec3 × ℝ => (2 : ℝ))).mul hF).mul hWprod).mul hψ.continuous))

private theorem shearLEI_partial_integral_identity (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    2 * ∫ z : Vec3 × ℝ, shearLEILeftPartial N ψ z ∂volume =
      ∫ z : Vec3 × ℝ, shearLEIRightPartial N ψ z ∂volume := by
  have hfinite := shearCounterexample_finite_energy_identity N ψ hψ hψc
  have hPoint : (fun z : Vec3 × ℝ =>
      (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
        (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
          shearCounterexampleVelocityPartial N z 2 * spatialPartial ψ 2 z +
        2 * (∑ i : Fin 3,
      shearCounterexampleForcePartial N z i *
            shearCounterexampleVelocityPartial N z i) * ψ z) =
      shearLEIRightPartial N ψ := by
    funext z
    simp [shearLEIRightPartial, shearCounterexampleVelocityPartial,
      shearCounterexampleForcePartial, Fin.sum_univ_succ]
    ring
  have hLeft : (fun z : Vec3 × ℝ =>
      spatialGradientSq (shearCounterexampleVelocityPartial N)
        (shearCounterexampleDuPartial N) z * ψ z) = shearLEILeftPartial N ψ := by
    rfl
  rw [hLeft] at hfinite
  have hRight := congrArg (fun g : (Vec3 × ℝ → ℝ) => ∫ z, g z ∂volume) hPoint
  rw [hRight] at hfinite
  exact hfinite

theorem shearCounterexample_energy_identity_on_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (hS : MeasurableSet (spaceTimeSet Ω' J))
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψnonneg : ∀ z, 0 ≤ ψ z)
    (hψsub : tsupport ψ ⊆ spaceTimeSet Ω' J) :
    2 * ∫ z in (spaceTimeSet Ω' J : Set (Vec3 × ℝ)),
        shearLEILeft ψ z ∂(volume : Measure (Vec3 × ℝ)) =
      ∫ z in (spaceTimeSet Ω' J : Set (Vec3 × ℝ)),
        shearLEIRight ψ z ∂(volume : Measure (Vec3 × ℝ)) := by
  let S : Set (Vec3 × ℝ) := spaceTimeSet Ω' J
  let μ : Measure (Vec3 × ℝ) := volume.restrict S
  have hMajorant : Integrable (shearLEIMajorant ψ) μ := by
    exact shearLEIMajorant_integrable_on_localBox hbox ψ hψ hψc
  have hDomLeft : ∀ N, ∀ᵐ z ∂μ,
      ‖shearLEILeftPartial N ψ z‖ ≤ shearLEIMajorant ψ z := by
    intro N
    change ∀ᵐ z : Vec3 × ℝ ∂volume.restrict S, _
    exact ae_restrict_of_ae
      (Filter.Eventually.of_forall (shearLEILeftPartial_norm_le N ψ hψnonneg))
  have hDomRight : ∀ N, ∀ᵐ z ∂μ,
      ‖shearLEIRightPartial N ψ z‖ ≤ shearLEIMajorant ψ z := by
    intro N
    change ∀ᵐ z : Vec3 × ℝ ∂volume.restrict S, _
    exact ae_restrict_of_ae (shearLEIRightPartial_norm_le_ae N ψ)
  have hLimLeft0 := lei_left_partial_tendsto_ae ψ
  have hLimRight0 := lei_right_partial_tendsto_ae ψ
  have hLimLeft : ∀ᵐ z ∂μ,
      Tendsto (fun N => shearLEILeftPartial N ψ z) atTop
        (𝓝 (shearLEILeft ψ z)) := by
    change ∀ᵐ z : Vec3 × ℝ ∂volume.restrict S, _
    exact ae_restrict_of_ae hLimLeft0
  have hLimRight : ∀ᵐ z ∂μ,
      Tendsto (fun N => shearLEIRightPartial N ψ z) atTop
        (𝓝 (shearLEIRight ψ z)) := by
    change ∀ᵐ z : Vec3 × ℝ ∂volume.restrict S, _
    exact ae_restrict_of_ae hLimRight0
  have hDCTLeft : Tendsto
      (fun N => ∫ z : Vec3 × ℝ, shearLEILeftPartial N ψ z ∂μ)
      atTop (𝓝 (∫ z : Vec3 × ℝ, shearLEILeft ψ z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (bound := shearLEIMajorant ψ)
    · intro N
      exact (shearLEILeftPartial_continuous N ψ hψ).measurable.aestronglyMeasurable
    · exact hMajorant
    · exact hDomLeft
    · exact hLimLeft
  have hDCTRight : Tendsto
      (fun N => ∫ z : Vec3 × ℝ, shearLEIRightPartial N ψ z ∂μ)
      atTop (𝓝 (∫ z : Vec3 × ℝ, shearLEIRight ψ z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (bound := shearLEIMajorant ψ)
    · intro N
      exact (shearLEIRightPartial_continuous N ψ hψ).measurable.aestronglyMeasurable
    · exact hMajorant
    · exact hDomRight
    · exact hLimRight
  have hLbox (N : ℕ) :
      ∫ z : Vec3 × ℝ, shearLEILeftPartial N ψ z ∂μ =
        ∫ z : Vec3 × ℝ, shearLEILeftPartial N ψ z ∂volume := by
    change ∫ z in S, shearLEILeftPartial N ψ z ∂volume = _
    exact setIntegral_eq_integral_of_tsupport_subset hS
      ((lei_left_partial_tsupport_subset_test N ψ).trans hψsub)
  have hRbox (N : ℕ) :
      ∫ z : Vec3 × ℝ, shearLEIRightPartial N ψ z ∂μ =
        ∫ z : Vec3 × ℝ, shearLEIRightPartial N ψ z ∂volume := by
    change ∫ z in S, shearLEIRightPartial N ψ z ∂volume = _
    exact setIntegral_eq_integral_of_tsupport_subset hS
      ((lei_right_partial_tsupport_subset_test N ψ hψ).trans hψsub)
  have hfinite (N : ℕ) :
      2 * ∫ z : Vec3 × ℝ, shearLEILeftPartial N ψ z ∂μ =
        ∫ z : Vec3 × ℝ, shearLEIRightPartial N ψ z ∂μ := by
    calc
      2 * ∫ z : Vec3 × ℝ, shearLEILeftPartial N ψ z ∂μ =
          2 * ∫ z : Vec3 × ℝ, shearLEILeftPartial N ψ z ∂volume := by
        rw [hLbox]
      _ = ∫ z : Vec3 × ℝ, shearLEIRightPartial N ψ z ∂volume :=
        shearLEI_partial_integral_identity N ψ hψ hψc
      _ = ∫ z : Vec3 × ℝ, shearLEIRightPartial N ψ z ∂μ := by
        rw [hRbox]
  have hseq :
      (fun N => 2 * ∫ z : Vec3 × ℝ, shearLEILeftPartial N ψ z ∂μ) =
        fun N => ∫ z : Vec3 × ℝ, shearLEIRightPartial N ψ z ∂μ := by
    funext N
    exact hfinite N
  have h2lim : Tendsto
      (fun N => 2 * ∫ z : Vec3 × ℝ, shearLEILeftPartial N ψ z ∂μ)
      atTop (𝓝 (2 * ∫ z : Vec3 × ℝ, shearLEILeft ψ z ∂μ)) := by
    simpa using tendsto_const_nhds.mul hDCTLeft
  rw [hseq] at h2lim
  have hlim := tendsto_nhds_unique h2lim hDCTRight
  simpa [CKN.Foundation.Parabolic.ParabolicPoint, S, μ] using hlim

theorem shearCounterexample_energy_identity_on_localBox_parabolic
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (hS : MeasurableSet (spaceTimeSet Ω' J))
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψnonneg : ∀ z, 0 ≤ ψ z)
    (hψsub : tsupport ψ ⊆ spaceTimeSet Ω' J) :
    2 * ∫ z in spaceTimeSet Ω' J, shearLEILeft ψ z
        ∂(volume : Measure ParabolicPoint) =
      ∫ z in spaceTimeSet Ω' J, shearLEIRight ψ z
        ∂(volume : Measure ParabolicPoint) := by
  rw [show (volume : Measure ParabolicPoint) = (volume : Measure (Vec3 × ℝ)) by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]]
  exact shearCounterexample_energy_identity_on_localBox hbox hS ψ hψ hψc
    hψnonneg hψsub

private theorem shearLEILeft_norm_le (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) :
    ‖shearLEILeft ψ z‖ ≤ shearLEIMajorant ψ z := by
  rw [Real.norm_eq_abs, lei_left_scalar_simplify]
  have hgrad : 0 ≤ (shearFullGradient 0 z) ^ 2 +
      (shearFullGradient 1 z) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [abs_mul, abs_of_nonneg hgrad]
  dsimp [shearLEIMajorant]
  calc
    _ ≤ ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) *
        |ψ z| + |shearFullScalar z| ^ 2 *
          |timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z| :=
      le_add_of_nonneg_right (by positivity)
    _ ≤ ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) *
        |ψ z| + |shearFullScalar z| ^ 2 *
          |timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z| +
        |shearFullScalar z| ^ 3 * |spatialPartial ψ 2 z| :=
      le_add_of_nonneg_right (by positivity)
    _ ≤ ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) *
        |ψ z| + |shearFullScalar z| ^ 2 *
          |timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z| +
        |shearFullScalar z| ^ 3 * |spatialPartial ψ 2 z| +
        2 * |shearFullForceScalar z| * |shearFullScalar z| * |ψ z| :=
      le_add_of_nonneg_right (by positivity)

private theorem shearLEIRight_norm_le_ae (ψ : Vec3 × ℝ → ℝ) :
    ∀ᵐ z : Vec3 × ℝ ∂volume,
      ‖shearLEIRight ψ z‖ ≤ shearLEIMajorant ψ z := by
  filter_upwards [shearFullScalar_nonneg_ae] with z hW0
  let W := shearFullScalar z
  let F := shearFullForceScalar z
  let H := timePartial (show ParabolicPoint → ℝ from ψ) z +
    ∑ i : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from ψ) i i z
  let ψ2 := spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z
  have hW : 0 ≤ W := hW0
  have htermA : |W ^ 2 * H| = |W| ^ 2 * |H| := by rw [abs_mul, abs_pow]
  have htermB : |W ^ 3 * ψ2| = |W| ^ 3 * |ψ2| := by rw [abs_mul, abs_pow]
  have htermC : |2 * F * W * ψ z| = 2 * |F| * |W| * |ψ z| := by
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  rw [Real.norm_eq_abs, lei_rhs_scalar_simplify ψ (show Vec3 × ℝ from z)]
  change |W ^ 2 * H + W ^ 3 * ψ2 + 2 * F * W * ψ z| ≤ _
  calc
    |W ^ 2 * H + W ^ 3 * ψ2 + 2 * F * W * ψ z|
        ≤ |W ^ 2 * H| + |W ^ 3 * ψ2| + |2 * F * W * ψ z| := by
          calc
            _ ≤ |W ^ 2 * H + W ^ 3 * ψ2| + |2 * F * W * ψ z| := abs_add_le _ _
            _ ≤ |W ^ 2 * H| + |W ^ 3 * ψ2| + |2 * F * W * ψ z| := by
              gcongr
              exact abs_add_le _ _
    _ = |W| ^ 2 * |H| + |W| ^ 3 * |ψ2| +
        2 * |F| * |W| * |ψ z| := by rw [htermA, htermB, htermC]
    _ ≤ ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) *
          |ψ z| + |W| ^ 2 * |H| + |W| ^ 3 * |ψ2| +
          2 * |F| * |W| * |ψ z| := by
      have hgrad : 0 ≤ ((shearFullGradient 0 z) ^ 2 +
          (shearFullGradient 1 z) ^ 2) * |ψ z| := by positivity
      linarith only [hgrad]
    _ = shearLEIMajorant ψ z := by
      dsimp [shearLEIMajorant, W, F, H, ψ2]

private theorem shearLEILeft_measurable (ψ : Vec3 × ℝ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : Measurable (shearLEILeft ψ) := by
  have hEq : shearLEILeft ψ = fun z =>
      ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) * ψ z := by
    funext z
    exact lei_left_scalar_simplify ψ z
  rw [hEq]
  exact ((shearFullGradient_measurable 0).pow_const 2).add
    ((shearFullGradient_measurable 1).pow_const 2) |>.mul hψ.continuous.measurable

private theorem shearLEIRight_measurable (ψ : Vec3 × ℝ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : Measurable (shearLEIRight ψ) := by
  let heat : Vec3 × ℝ → ℝ := fun z =>
    timePartial (show ParabolicPoint → ℝ from ψ) z + ∑ i : Fin 3,
      spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z
  let ψ2 : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z
  have hEq : shearLEIRight ψ = fun z =>
      shearFullScalar z ^ 2 * heat z + shearFullScalar z ^ 3 * ψ2 z +
        2 * shearFullForceScalar z * shearFullScalar z * ψ z := by
    funext z
    simpa [heat, ψ2] using lei_rhs_scalar_simplify ψ z
  have hheat : Measurable heat := (lei_testHeat_contDiff hψ).continuous.measurable
  have hψ2 : Measurable ψ2 := (spatialPartial_contDiff hψ 2).continuous.measurable
  rw [hEq]
  exact (((shearFullScalar_measurable.pow_const 2).mul hheat).add
    ((shearFullScalar_measurable.pow_const 3).mul hψ2)).add
      (((continuous_const.measurable.mul shearFullForceScalar_measurable).mul
        shearFullScalar_measurable).mul hψ.continuous.measurable)

private theorem shearLEI_integrableOn_of_compact_test
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψsub : @tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd ψ ⊆
      spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1)) :
    IntegrableOn (shearLEILeft ψ) (tsupport ψ) volume ∧
      IntegrableOn (shearLEIRight ψ) (tsupport ψ) volume := by
  have hK : IsCompact (tsupport ψ) := hψc
  have hKsub : tsupport ψ ⊆ vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 1 := by
    simpa [spaceTimeSet] using hψsub
  obtain ⟨Ω', J, hbox, hKbox, _hSmeas⟩ :=
    shear_localBox_of_compact_tsupport hK hKsub
  have hψsub' : tsupport ψ ⊆ spaceTimeSet Ω' J := by
    simpa [spaceTimeSet] using hKbox
  have hMajorant : Integrable (shearLEIMajorant ψ)
      (volume.restrict (spaceTimeSet Ω' J)) :=
    shearLEIMajorant_integrable_on_localBox hbox ψ hψ hψc
  have hμmono : volume.restrict (tsupport ψ) ≤
      volume.restrict (spaceTimeSet Ω' J) :=
    Measure.restrict_mono hψsub' le_rfl
  have hLeftDom : ∀ᵐ z ∂(volume.restrict (tsupport ψ)),
      ‖shearLEILeft ψ z‖ ≤ shearLEIMajorant ψ z := by
    exact ae_restrict_of_ae (Filter.Eventually.of_forall
      (shearLEILeft_norm_le ψ))
  have hRightDom : ∀ᵐ z ∂(volume.restrict (tsupport ψ)),
      ‖shearLEIRight ψ z‖ ≤ shearLEIMajorant ψ z :=
    ae_restrict_of_ae (shearLEIRight_norm_le_ae ψ)
  have hMajorantK := hMajorant.mono_measure hμmono
  have hLeft := hMajorantK.mono'
    ((shearLEILeft_measurable ψ hψ).aestronglyMeasurable) hLeftDom
  have hRight := hMajorantK.mono'
    ((shearLEIRight_measurable ψ hψ).aestronglyMeasurable) hRightDom
  exact ⟨hLeft, hRight⟩

theorem shearCounterexample_localEnergyClause_product
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψnonneg : ∀ z, 0 ≤ ψ z)
    (hψsub : @tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd ψ ⊆
      spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1)) :
    IntegrableOn (fun z : Vec3 × ℝ =>
      spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z * ψ z)
      (@tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd ψ)
        (volume : Measure (Vec3 × ℝ)) ∧
    IntegrableOn (fun z : Vec3 × ℝ =>
      (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
        ((vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 +
          2 * shearCounterexamplePressure z) *
          ∑ i : Fin 3, shearCounterexampleVelocity z i * spatialPartial ψ i z +
        2 * (∑ i : Fin 3, shearCounterexampleForce z i *
          shearCounterexampleVelocity z i) * ψ z)
      (@tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd ψ)
        (volume : Measure (Vec3 × ℝ)) ∧
    2 * ∫ z in (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1) : Set (Vec3 × ℝ)),
        spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z * ψ z
          ∂(volume : Measure (Vec3 × ℝ)) =
      ∫ z in (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1) : Set (Vec3 × ℝ)),
        (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
          ((vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 +
            2 * shearCounterexamplePressure z) *
            ∑ i : Fin 3, shearCounterexampleVelocity z i * spatialPartial ψ i z +
          2 * (∑ i : Fin 3, shearCounterexampleForce z i *
            shearCounterexampleVelocity z i) * ψ z
          ∂(volume : Measure (Vec3 × ℝ)) := by
  have hIntegrable := shearLEI_integrableOn_of_compact_test ψ hψ hψc hψsub
  have hK : IsCompact (@tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd ψ) := hψc
  have hKsub : @tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd ψ ⊆
      vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 1 := by
    simpa [spaceTimeSet] using hψsub
  obtain ⟨Ω', J, hbox, hKbox, hSmeas⟩ :=
    shear_localBox_of_compact_tsupport hK hKsub
  have hψsubLocal : @tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd ψ ⊆
      spaceTimeSet Ω' J := by
    simpa [spaceTimeSet] using hKbox
  have hlocalIdentity := shearCounterexample_energy_identity_on_localBox_parabolic
    hbox hSmeas ψ hψ hψc hψnonneg hψsubLocal
  have hGlobalMeas : MeasurableSet
      (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1)) := by
    change MeasurableSet (vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 1)
    exact (vec3Ball_measurable (0 : Vec3) 1).prod measurableSet_Ioo
  have hLocalLeft :
      ∫ z in (spaceTimeSet Ω' J : Set (Vec3 × ℝ)), shearLEILeft ψ z
          ∂(volume : Measure (Vec3 × ℝ)) =
        ∫ z : Vec3 × ℝ, shearLEILeft ψ z ∂volume :=
    setIntegral_eq_integral_of_tsupport_subset hSmeas
      ((lei_left_tsupport_subset_test ψ).trans hψsubLocal)
  have hLocalRight :
      ∫ z in (spaceTimeSet Ω' J : Set (Vec3 × ℝ)), shearLEIRight ψ z
          ∂(volume : Measure (Vec3 × ℝ)) =
        ∫ z : Vec3 × ℝ, shearLEIRight ψ z ∂volume :=
    setIntegral_eq_integral_of_tsupport_subset hSmeas
      ((lei_right_tsupport_subset_test ψ hψ).trans hψsubLocal)
  have hGlobalLeft :
      ∫ z in (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1) : Set (Vec3 × ℝ)),
          shearLEILeft ψ z ∂(volume : Measure (Vec3 × ℝ)) =
        ∫ z : Vec3 × ℝ, shearLEILeft ψ z ∂volume :=
    setIntegral_eq_integral_of_tsupport_subset hGlobalMeas
      ((lei_left_tsupport_subset_test ψ).trans hψsub)
  have hGlobalRight :
      ∫ z in (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1) : Set (Vec3 × ℝ)),
          shearLEIRight ψ z ∂(volume : Measure (Vec3 × ℝ)) =
        ∫ z : Vec3 × ℝ, shearLEIRight ψ z ∂volume :=
    setIntegral_eq_integral_of_tsupport_subset hGlobalMeas
      ((lei_right_tsupport_subset_test ψ hψ).trans hψsub)
  have hIdentity :
      2 * ∫ z in (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1) : Set (Vec3 × ℝ)),
          shearLEILeft ψ z ∂(volume : Measure (Vec3 × ℝ)) =
        ∫ z in (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1) : Set (Vec3 × ℝ)),
          shearLEIRight ψ z ∂(volume : Measure (Vec3 × ℝ)) := by
    calc
      _ = 2 * ∫ z : Vec3 × ℝ, shearLEILeft ψ z ∂volume := by rw [hGlobalLeft]
      _ = 2 * ∫ z in (spaceTimeSet Ω' J : Set (Vec3 × ℝ)), shearLEILeft ψ z
            ∂(volume : Measure (Vec3 × ℝ)) := by rw [hLocalLeft]
      _ = ∫ z in (spaceTimeSet Ω' J : Set (Vec3 × ℝ)), shearLEIRight ψ z
            ∂(volume : Measure (Vec3 × ℝ)) :=
          shearCounterexample_energy_identity_on_localBox hbox hSmeas ψ hψ hψc
            hψnonneg hψsubLocal
      _ = ∫ z : Vec3 × ℝ, shearLEIRight ψ z ∂volume := hLocalRight
      _ = ∫ z in (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1) : Set (Vec3 × ℝ)),
            shearLEIRight ψ z ∂(volume : Measure (Vec3 × ℝ)) := by rw [← hGlobalRight]
  have hRaw : (fun z : Vec3 × ℝ =>
      (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
        ((vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 +
          2 * shearCounterexamplePressure z) *
          ∑ i : Fin 3, shearCounterexampleVelocity z i * spatialPartial ψ i z +
        2 * (∑ i : Fin 3, shearCounterexampleForce z i *
          shearCounterexampleVelocity z i) * ψ z) = shearLEIRight ψ := by
    funext z
    simp [shearLEIRight, shearCounterexamplePressure]
  refine ⟨hIntegrable.1, ?_, ?_⟩
  · rw [hRaw]
    exact hIntegrable.2
  · rw [hRaw]
    exact hIdentity

theorem shearCounterexample_localEnergyClause
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψnonneg : ∀ z, 0 ≤ ψ z)
    (hψsub : @tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd ψ ⊆
      spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1)) :
    IntegrableOn (fun z : ParabolicPoint =>
      spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z * ψ z)
      (@tsupport ParabolicPoint ℝ Real.instZero
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (show ParabolicPoint → ℝ from ψ))
        (volume : Measure ParabolicPoint) ∧
    IntegrableOn (fun z : ParabolicPoint =>
      (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
        ((vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 +
          2 * shearCounterexamplePressure z) *
          ∑ i : Fin 3, shearCounterexampleVelocity z i * spatialPartial ψ i z +
        2 * (∑ i : Fin 3, shearCounterexampleForce z i *
          shearCounterexampleVelocity z i) * ψ z)
      (@tsupport ParabolicPoint ℝ Real.instZero
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (show ParabolicPoint → ℝ from ψ))
        (volume : Measure ParabolicPoint) ∧
    2 * ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1),
        spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z * ψ z ≤
      ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1),
        (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
          ((vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 +
            2 * shearCounterexamplePressure z) *
            ∑ i : Fin 3, shearCounterexampleVelocity z i * spatialPartial ψ i z +
          2 * (∑ i : Fin 3, shearCounterexampleForce z i *
            shearCounterexampleVelocity z i) * ψ z := by
  have h := shearCounterexample_localEnergyClause_product ψ hψ hψc hψnonneg hψsub
  have hts := tsupport_parabolic_eq_product_test ψ
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact h.1
  · rw [hts, CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact h.2.1
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  exact le_of_eq h.2.2

end CKN
