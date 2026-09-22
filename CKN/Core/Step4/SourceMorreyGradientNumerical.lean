-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.SourceMorreyGradient
import CKN.Core.Step4.SourceMorreyData
import CKN.Core.Endgame.CutoffMorrey
import CKN.Core.Endgame.SourceComponents
import CKN.Foundation.Parabolic.Morrey.Minkowski

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Endgame

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-! # Numerical bounds for the gradient-slot source

The carrier is allowed to be any measurable set contained in a parabolic
cylinder.  This keeps the radius factors visible while allowing the local
cutoff and the selected pressure gradient to use different carriers.
-/

def sourceUnitCylinderVolume : ℝ≥0∞ :=
  volume (parabolicCylinder (0 : Vec3) 0 1)

def sourceRadiusFactor (θ τ R : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal R) ^ (5 * (1 / θ - 1 / τ))

private theorem source_zero_outside_cylinder
    {Q : Set ParabolicPoint} {z₀ : ParabolicPoint} {R : ℝ}
    (hQ : Q ⊆ parabolicCylinder z₀.1 z₀.2 R) {f : ParabolicPoint → ℝ}
    (hzero : ∀ z ∉ Q, f z = 0) :
    ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, f z = 0 := by
  intro z hz
  by_cases hzQ : z ∈ Q
  · exact False.elim (hz (hQ hzQ))
  · exact hzero z hzQ

private theorem source_lower_radius_bound
    {P θ θ₀ R : ℝ} {Q : Set ParabolicPoint} {z₀ : ParabolicPoint}
    {f : ParabolicPoint → ℝ} {K : ℝ≥0∞}
    (hP : 1 ≤ P) (hPθ : P ≤ θ) (hθθ₀ : θ ≤ θ₀) (hR : 0 < R)
    (hQ : Q ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hzero : ∀ z ∉ Q, f z = 0)
    (hN : morreyNorm P θ₀ f ≤ K) :
    morreyNorm P θ f ≤ sourceRadiusFactor θ θ₀ R * K := by
  have hzero' := source_zero_outside_cylinder hQ hzero
  have hlow := morreyNorm_lower_morrey_exponent (p := P) (q := θ₀)
    (q' := θ) hP (hPθ.trans hθθ₀) hPθ hθθ₀ hR hzero'
  exact hlow.trans (mul_le_mul_of_nonneg_left hN bot_le)

private theorem source_lower_integrability_bound
    {P P₀ θ : ℝ} {Q : Set ParabolicPoint} {f : ParabolicPoint → ℝ}
    {K : ℝ≥0∞} (hP : 1 ≤ P) (hPP₀ : P ≤ P₀) (hP₀θ : P₀ ≤ θ)
    (hf : AEMeasurable (Q.indicator f) volume)
    (hN : morreyNorm P₀ θ (Q.indicator f) ≤ K) :
    morreyNorm P θ (Q.indicator f) ≤
      sourceUnitCylinderVolume ^ (1 / P - 1 / P₀) * K := by
  have hlow := morreyNorm_lower_integrability (p' := P) (p := P₀)
    (q := θ) hP hPP₀ hP₀θ hf
  exact hlow.trans (mul_le_mul_of_nonneg_left hN bot_le)

private theorem gradient_source_bounded_multiplier_morrey_bound
    (q C₁₀ R : ℝ) (KU : ℝ≥0∞) (hq : 5 / 2 < q) (hR : 0 < R)
    (hC : 0 ≤ C₁₀) {z₀ : ParabolicPoint} {Q : Set ParabolicPoint}
    {a : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3} (i : Fin 3)
    (hQ : Q ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hUae : AEMeasurable (Q.indicator (fun z => u z i)) volume)
    (hU : morreyNorm 3 (25 / 3 : ℝ)
      (Q.indicator (fun z => u z i)) ≤ KU)
    (hbound : ∀ z, |a z| ≤ C₁₀)
    (hzero : ∀ z ∉ Q, a z = 0) :
    morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => a z * u z i) ≤
      sourceRadiusFactor (min q (25 / 9 : ℝ)) (25 / 3) R *
        ENNReal.ofReal C₁₀ * sourceUnitCylinderVolume ^ (1 / 2 : ℝ) * KU := by
  have hθ : (6 / 5 : ℝ) ≤ min q (25 / 9 : ℝ) :=
    le_min (by linarith only [hq]) (by norm_num)
  have hθupper : min q (25 / 9 : ℝ) ≤ (25 / 3 : ℝ) := by
    exact (min_le_right q (25 / 9)).trans (by norm_num)
  have hlow := source_lower_integrability_bound
    (Q := Q) (f := fun z => u z i) (K := KU)
    (P := (6 / 5 : ℝ)) (P₀ := 3) (θ := (25 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hUae hU
  have hlow'' : morreyNorm (6 / 5) (25 / 3)
      (Q.indicator (fun z => u z i)) ≤
      sourceUnitCylinderVolume ^ (1 / 2 : ℝ) * KU := by
    convert hlow using 1
    norm_num
  have hlow' := source_lower_radius_bound (Q := Q) (z₀ := z₀)
    (f := Q.indicator (fun z => u z i))
    (K := sourceUnitCylinderVolume ^ (1 / 2 : ℝ) * KU)
    (P := (6 / 5 : ℝ)) (θ := min q (25 / 9 : ℝ)) (θ₀ := 25 / 3)
    (by norm_num) hθ hθupper hR hQ
    (fun z hz => indicator_of_notMem hz _) hlow''
  have hmul := morrey_norm_mul_le_indicator (6 / 5)
    (min q (25 / 9)) C₁₀ (by norm_num) hC Q
    (fun z => a z) (fun z => u z i) hbound hzero
  have hmul' : morreyNorm (6 / 5) (min q (25 / 9))
      (fun z => a z * u z i) ≤
      ENNReal.ofReal C₁₀ *
        (sourceRadiusFactor (min q (25 / 9)) (25 / 3) R *
          (sourceUnitCylinderVolume ^ (1 / 2 : ℝ) * KU)) :=
    hmul.trans (mul_le_mul_of_nonneg_left hlow' (by positivity))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul'

/-- The time-cutoff term, with the radius and unit-cylinder factors exposed. -/
theorem gradient_source_time_morrey_bound
    (q C₁₀ R : ℝ) (KU : ℝ≥0∞) (hq : 5 / 2 < q) (hR : 0 < R)
    (hC : 0 ≤ C₁₀) {z₀ : ParabolicPoint} {Q : Set ParabolicPoint}
    {φ : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3} (i : Fin 3)
    (hQ : Q ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hUae : AEMeasurable (Q.indicator (fun z => u z i)) volume)
    (hU : morreyNorm 3 (25 / 3 : ℝ)
      (Q.indicator (fun z => u z i)) ≤ KU)
    (hbound : ∀ z, |timePartial φ z| ≤ C₁₀)
    (hzero : ∀ z ∉ Q, timePartial φ z = 0) :
    morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => timePartial φ z * u z i) ≤
      sourceRadiusFactor (min q (25 / 9 : ℝ)) (25 / 3) R *
        ENNReal.ofReal C₁₀ * sourceUnitCylinderVolume ^ (1 / 2 : ℝ) * KU := by
  exact gradient_source_bounded_multiplier_morrey_bound q C₁₀ R KU hq hR hC
    (z₀ := z₀) (Q := Q) (a := fun z => timePartial φ z) (u := u) i hQ
    hUae hU hbound hzero

/-- The spatial-Laplacian cutoff term has the same numerical bound as the
time-cutoff term. -/
theorem gradient_source_laplacian_morrey_bound
    (q C₁₀ R : ℝ) (KU : ℝ≥0∞) (hq : 5 / 2 < q) (hR : 0 < R)
    (hC : 0 ≤ C₁₀) {z₀ : ParabolicPoint} {Q : Set ParabolicPoint}
    {φ : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3} (i : Fin 3)
    (hQ : Q ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hUae : AEMeasurable (Q.indicator (fun z => u z i)) volume)
    (hU : morreyNorm 3 (25 / 3 : ℝ)
      (Q.indicator (fun z => u z i)) ≤ KU)
    (hbound : ∀ z : ParabolicPoint,
      |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C₁₀)
    (hzero : ∀ z : ParabolicPoint, z ∉ Q →
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0) :
    morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) ≤
      sourceRadiusFactor (min q (25 / 9 : ℝ)) (25 / 3) R *
        ENNReal.ofReal C₁₀ * sourceUnitCylinderVolume ^ (1 / 2 : ℝ) * KU := by
  exact gradient_source_bounded_multiplier_morrey_bound q C₁₀ R KU hq hR hC
    (z₀ := z₀) (Q := Q)
    (a := fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1) (u := u)
    i hQ hUae hU hbound hzero

private theorem gradient_source_product_sum_bound
    {Q : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {i : Fin 3}
    {KU KD : ℝ≥0∞} (hUae : ∀ j, AEMeasurable
      (Q.indicator (fun z => u z j)) volume)
    (hDae : ∀ j, AEMeasurable
      (Q.indicator (fun z => Du z i j)) volume)
    (hU : ∀ j, morreyNorm 3 25
      (Q.indicator (fun z => u z j)) ≤ KU)
    (hD : ∀ j, morreyNorm 2 (25 / 8 : ℝ)
      (Q.indicator (fun z => Du z i j)) ≤ KD) :
    AEMeasurable (fun z => ∑ j : Fin 3,
      Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) volume ∧
    morreyNorm (6 / 5 : ℝ) (25 / 9 : ℝ)
      (fun z => ∑ j : Fin 3,
        Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) ≤
      3 * KU * KD := by
  let b : Fin 3 → ParabolicPoint → ℝ := fun j z =>
    Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z
  have hbe : ∀ j, AEMeasurable (b j) volume := fun j =>
    (hUae j).mul (hDae j)
  have hb : AEMeasurable (fun z => ∑ j : Fin 3, b j z) volume := by
    simpa [Fin.sum_univ_succ, Pi.add_def] using
      (hbe 0).add ((hbe 1).add (hbe 2))
  have hbn : ∀ j, morreyNorm (6 / 5) (25 / 9) (b j) ≤ KU * KD := by
    intro j
    have hprod := morreyNorm_holder (p := (6 / 5 : ℝ))
      (p₁ := 3) (p₂ := 2) (q := (25 / 9 : ℝ))
      (q₁ := 25) (q₂ := (25 / 8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hUae j) (hDae j)
    exact hprod.trans (mul_le_mul (hU j) (hD j) (by positivity) (by positivity))
  have h12 := (morrey_norm_add_le (τ := (25 / 9 : ℝ)) (by norm_num)
    (hbe 1) (hbe 2)).trans (add_le_add (hbn 1) (hbn 2))
  have hall := (morrey_norm_add_le (τ := (25 / 9 : ℝ)) (by norm_num)
    (hbe 0) ((hbe 1).add (hbe 2))).trans (add_le_add (hbn 0) h12)
  have hthree : KU * KD + (KU * KD + KU * KD) = 3 * KU * KD := by ring
  refine ⟨?_, ?_⟩
  · simpa [b, Fin.sum_univ_succ, Pi.add_def] using hb
  · simpa [b, Fin.sum_univ_succ, Pi.add_def, hthree] using hall

/-- The convection term is controlled by the bootstrapped velocity bound and
first-gradient bound, with the radius loss for lowering its Morrey exponent. -/
theorem gradient_source_convection_morrey_bound
    (q C₁₀ R : ℝ) (KU25 KD : ℝ≥0∞) (hq : 5 / 2 < q) (hR : 0 < R)
    (hC : 0 ≤ C₁₀) {z₀ : ParabolicPoint} {Q : Set ParabolicPoint}
    {φ : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} (i : Fin 3)
    (hQ : Q ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hUae : ∀ j, AEMeasurable (Q.indicator (fun z => u z j)) volume)
    (hDae : ∀ j, AEMeasurable
      (Q.indicator (fun z => Du z i j)) volume)
    (hU : ∀ j, morreyNorm 3 25
      (Q.indicator (fun z => u z j)) ≤ KU25)
    (hD : ∀ j, morreyNorm 2 (25 / 8 : ℝ)
      (Q.indicator (fun z => Du z i j)) ≤ KD)
    (hbound : ∀ z, |φ z| ≤ C₁₀) (hzero : ∀ z ∉ Q, φ z = 0) :
    morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => φ z * localizedConvection u Du z i) ≤
      sourceRadiusFactor (min q (25 / 9 : ℝ)) (25 / 9) R *
        ENNReal.ofReal C₁₀ * (3 * KU25 * KD) := by
  have hθ : (6 / 5 : ℝ) ≤ min q (25 / 9 : ℝ) :=
    le_min (by linarith only [hq]) (by norm_num)
  have hsum := gradient_source_product_sum_bound hUae hDae hU hD
  have hsum' : morreyNorm (6 / 5) (min q (25 / 9))
      (fun z => ∑ j : Fin 3,
        Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) ≤
      sourceRadiusFactor (min q (25 / 9)) (25 / 9) R *
        (3 * KU25 * KD) := source_lower_radius_bound (Q := Q) (z₀ := z₀)
    (f := fun z => ∑ j : Fin 3,
      Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z)
    (K := 3 * KU25 * KD) (P := (6 / 5 : ℝ))
    (θ := min q (25 / 9 : ℝ)) (θ₀ := 25 / 9) (by norm_num) hθ
    (min_le_right q (25 / 9)) hR hQ (by
      intro z hz
      by_cases hzQ : z ∈ Q
      · exact False.elim (hz hzQ)
      · simp only [indicator_of_notMem hzQ, zero_mul, Finset.sum_const_zero]) hsum.2
  have heq : (fun z => φ z * localizedConvection u Du z i) =
      (fun z => φ z * ∑ j : Fin 3,
        Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) := by
    funext z
    by_cases hzQ : z ∈ Q
    · simp only [indicator_of_mem hzQ, localizedConvection]
    · simp only [hzero z hzQ, zero_mul]
  rw [heq]
  have hmono : morreyNorm (6 / 5) (min q (25 / 9))
      (fun z => φ z * ∑ j : Fin 3,
        Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) ≤
      morreyNorm (6 / 5) (min q (25 / 9))
        (fun z => C₁₀ * ∑ j : Fin 3,
          Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) := by
    apply morreyNorm_mono (by norm_num)
    intro z
    rw [abs_mul, abs_mul, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hbound z) (abs_nonneg _)
  have hconst := morreyNorm_const_mul_le (P := (6 / 5 : ℝ))
    (τ := min q (25 / 9 : ℝ)) (by norm_num) C₁₀
    (fun z => ∑ j : Fin 3,
      Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z)
  have hconst' : morreyNorm (6 / 5) (min q (25 / 9))
      (fun z => C₁₀ * ∑ j : Fin 3,
        Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) ≤
      ENNReal.ofReal C₁₀ *
        morreyNorm (6 / 5) (min q (25 / 9)) (fun z => ∑ j : Fin 3,
          Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) := by
    simpa only [abs_of_nonneg hC] using hconst
  calc
    _ ≤ morreyNorm (6 / 5) (min q (25 / 9))
        (fun z => C₁₀ * ∑ j : Fin 3,
          Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) := hmono
    _ ≤ ENNReal.ofReal C₁₀ *
        morreyNorm (6 / 5) (min q (25 / 9)) (fun z => ∑ j : Fin 3,
          Q.indicator (fun w => u w j) z * Q.indicator (fun w => Du w i j) z) := hconst'
    _ ≤ ENNReal.ofReal C₁₀ *
        (sourceRadiusFactor (min q (25 / 9)) (25 / 9) R *
          (3 * KU25 * KD)) :=
      mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = sourceRadiusFactor (min q (25 / 9)) (25 / 9) R *
        ENNReal.ofReal C₁₀ * (3 * KU25 * KD) := by ac_rfl

/-- The force term, starting from a scalar `L^q` norm on the carrier. -/
theorem gradient_source_force_morrey_bound
    (q C₁₀ R : ℝ) (Fnorm : ℝ≥0∞) (hq : 5 / 2 < q) (hR : 0 < R)
    (hC : 0 ≤ C₁₀) {z₀ : ParabolicPoint} {Q : Set ParabolicPoint}
    {φ : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} (i : Fin 3)
    (hQ : Q ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hf : AEMeasurable (Q.indicator (fun z => f z i)) volume)
    (hF : eLpNorm' (Q.indicator (fun z => f z i)) q volume ≤ Fnorm)
    (hbound : ∀ z, |φ z| ≤ C₁₀) (hzero : ∀ z ∉ Q, φ z = 0) :
    morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => φ z * f z i) ≤
      sourceRadiusFactor (min q (25 / 9 : ℝ)) q R * ENNReal.ofReal C₁₀ *
        sourceUnitCylinderVolume ^ (5 / 6 - 1 / q : ℝ) * Fnorm := by
  have hqP : (6 / 5 : ℝ) ≤ q := by linarith only [hq]
  have hθ : (6 / 5 : ℝ) ≤ min q (25 / 9 : ℝ) :=
    le_min hqP (by norm_num)
  have hqmor := morreyNorm_le_eLpNorm' (p := (6 / 5 : ℝ)) (q := q)
    (by norm_num) hqP hf
  have hqmor' : morreyNorm (6 / 5) q
      (Q.indicator (fun z => f z i)) ≤
      sourceUnitCylinderVolume ^ (5 / 6 - 1 / q : ℝ) * Fnorm :=
    by
      calc
        _ ≤ volume (parabolicCylinder (0 : Vec3) 0 1) ^
            (1 / (6 / 5 : ℝ) - 1 / q) *
            eLpNorm' (Q.indicator (fun z => f z i)) q volume := hqmor
        _ ≤ volume (parabolicCylinder (0 : Vec3) 0 1) ^
            (1 / (6 / 5 : ℝ) - 1 / q) * Fnorm :=
          mul_le_mul_of_nonneg_left hF (by positivity)
        _ = sourceUnitCylinderVolume ^ (5 / 6 - 1 / q : ℝ) * Fnorm := by
          norm_num [sourceUnitCylinderVolume]
  have hlow := source_lower_radius_bound (Q := Q) (z₀ := z₀)
    (f := Q.indicator (fun z => f z i))
    (K := sourceUnitCylinderVolume ^ (5 / 6 - 1 / q : ℝ) * Fnorm)
    (P := (6 / 5 : ℝ)) (θ := min q (25 / 9 : ℝ)) (θ₀ := q)
    (by norm_num) hθ (min_le_left q (25 / 9)) hR hQ
    (fun z hz => indicator_of_notMem hz _) hqmor'
  have hmul := morrey_norm_mul_le_indicator (6 / 5)
    (min q (25 / 9)) C₁₀ (by norm_num) hC Q φ (fun z => f z i)
    hbound hzero
  have hmul' := hmul.trans (mul_le_mul_of_nonneg_left hlow (by positivity))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul'

/-- A bounded cutoff preserves a supplied pressure-gradient Morrey bound. -/
theorem gradient_source_pressure_morrey_bound
    (q τ C₁₀ : ℝ) (KP : ℝ≥0∞)
    (hC : 0 ≤ C₁₀) {Q : Set ParabolicPoint}
    {φ : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3} (i : Fin 3)
    (hDp : morreyNorm (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q)
      (Q.indicator (fun z => Dp z i)) ≤ KP)
    (hbound : ∀ z, |φ z| ≤ C₁₀) (hzero : ∀ z ∉ Q, φ z = 0) :
    morreyNorm (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q)
      (fun z => φ z * Dp z i) ≤ ENNReal.ofReal C₁₀ * KP := by
  have hmul := morrey_norm_mul_le_indicator (6 / 5)
    (min ((1 / τ + 8 / 25)⁻¹) q) C₁₀ (by norm_num) hC Q φ
    (fun z => Dp z i) hbound hzero
  exact hmul.trans (mul_le_mul_of_nonneg_left hDp (by positivity))

end CKN.Core.Step4
