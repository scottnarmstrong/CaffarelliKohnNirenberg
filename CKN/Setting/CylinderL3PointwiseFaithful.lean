-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.CylinderSliceEnergy
import CKN.Setting.InterpolationCylinder
import CKN.Setting.SliceNormBounds
import CKN.Core.Caccioppoli.Finiteness
import CKN.Core.Caccioppoli.FinitenessComponentBounds
import CKN.Setting.PoincareSobolevL1Vec
import CKN.Pressure.SpatialGradientSqENorm

/-! # Pointwise two-radius cubic interpolation

This is the slice-wise two-radius `L³` estimate. Its scale powers follow the
paper's convention `A(z,ρ) = alpha(z,ρ)^2`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

set_option autoImplicit false

noncomputable section
namespace CKN

private noncomputable def interpolationC₈ENN : ℝ≥0∞ :=
  (81 * ENNReal.ofReal (Real.sqrt 3) *
      Classical.choose interpolationBall_three_finite) *
    ENNReal.ofReal (1 + 2 ^ (3 / 2 : ℝ) *
      (2 * poincareSobolevL1VectorConstant) ^ (3 / 2 : ℝ) +
      2 ^ (3 / 2 : ℝ))

/-- A fixed finite constant for the pointwise two-radius cubic interpolation
estimate. It depends only on the ball interpolation and Poincaré constants. -/
noncomputable def interpolationC₈ : ℝ := interpolationC₈ENN.toReal

private theorem vec3Ball_eq_euclideanBall_cylL3 {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : vec3Ball x₀ r = euclideanBall x₀ r := by
  ext x
  change vec3EuclideanNorm (x - x₀) < r ↔ x ∈ euclideanBall x₀ r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
    using (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).symm

private theorem slice_l3_lintegral_bound
    {Ω' : Set Vec3} {x₀ : Vec3} {r s : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ Ω')
    (hs : (MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
      ∀ i : Fin 3, HasWeakGradientOn Ω'
        (fun x => u (x, s) i) (fun x => Du (x, s) i)) :
    (∫⁻ y in vec3Ball x₀ r,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      (81 * ENNReal.ofReal (Real.sqrt 3) *
        Classical.choose interpolationBall_three_finite) *
          (∫⁻ y in vec3Ball x₀ r,
            ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ^
              (3 / 4 : ℝ) *
          (∫⁻ y in vec3Ball x₀ r,
            ENNReal.ofReal (spatialGradientSq u Du (y, s))) ^ (3 / 4 : ℝ) +
        (81 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite) *
          ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
          (∫⁻ y in vec3Ball x₀ r,
            ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ^
              (3 / 2 : ℝ) := by
  let B : Set Vec3 := vec3Ball x₀ r
  let E : ℝ≥0∞ := ∫⁻ y in B,
    ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)
  let D : ℝ≥0∞ := ∫⁻ y in B, ENNReal.ofReal (spatialGradientSq u Du (y, s))
  let μ : Measure Vec3 := volume.restrict B
  have hballEq : B = euclideanBall x₀ r := vec3Ball_eq_euclideanBall_cylL3 hr
  have hball' : B ⊆ Ω' := by simpa [hballEq] using hball
  have huB : MemLp (fun x : Vec3 => u (x, s)) 2 μ :=
    hs.1.1.mono_measure (Measure.restrict_mono_set volume hball')
  have hDuB : MemLp (fun x : Vec3 => Du (x, s)) 2 μ :=
    hs.1.2.mono_measure (Measure.restrict_mono_set volume hball')
  have huMeas : AEStronglyMeasurable (fun x : Vec3 => u (x, s)) μ :=
    huB.aestronglyMeasurable
  have hDuMeas : AEStronglyMeasurable (fun x : Vec3 => Du (x, s)) μ :=
    hDuB.aestronglyMeasurable
  have hL : ∀ i : Fin 3,
      lpNormOn 2 B (fun x => u (x, s) i) ≤ E ^ (1 / 2 : ℝ) := by
    intro i
    exact caccioppoli_l2_component_bound ((huB.eval i).aemeasurable) huMeas
  have hG : ∀ i : Fin 3,
      weakGradientLpNormOn 2 B (fun x => Du (x, s) i) ≤ D ^ (1 / 2 : ℝ) := by
    intro i
    simpa [spatialGradientSq, D, B] using
      (caccioppoli_gradient_component_bound hDuMeas (i := i))
  have hopen : IsOpen (euclideanBall x₀ r) := by
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  let H : ∀ i : Fin 3, H1Function (euclideanBall x₀ r) := fun i =>
    { toFun := fun x => u (x, s) i
      grad := fun x => Du (x, s) i
      memL2 := (MemLp.eval hs.1.1 i).mono_measure
        (Measure.restrict_mono_set volume hball)
      gradMemL2 := fun j => (MemLp.eval (MemLp.eval hs.1.2 i) j).mono_measure
        (Measure.restrict_mono_set volume hball)
      hasWeakGradient := (hs.2 i).restrict hopen hball }
  have hcomp : ∀ i : Fin 3, (H i).toFun = fun x => (u (x, s)) i := by
    intro i
    rfl
  have hC₆ : ∀ {x₀ : Vec3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn 3 (euclideanBall x₀ r) v.toFun ^ (3 : ℕ) ≤
          Classical.choose interpolationBall_three_finite *
              weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
                (3 / 2 : ℝ) * lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
                (3 / 2 : ℝ) +
            Classical.choose interpolationBall_three_finite *
              ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
                lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (3 : ℕ) := by
    intro x r hr v
    exact (Classical.choose_spec interpolationBall_three_finite).2 hr v
  have hsp := vector_interpolation_ball_l3_fixed hr hC₆ H hcomp
  have hsumL : ∑ i : Fin 3,
      lpNormOn 2 (euclideanBall x₀ r) (H i).toFun ≤ 3 * E ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin 3, E ^ (1 / 2 : ℝ) :=
        Finset.sum_le_sum (fun i _ => by
          simpa [H, hballEq, E, B] using hL i)
      _ = 3 * E ^ (1 / 2 : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsumG : ∑ i : Fin 3,
      weakGradientLpNormOn 2 (euclideanBall x₀ r) (H i).grad ≤ 3 * D ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin 3, D ^ (1 / 2 : ℝ) :=
        Finset.sum_le_sum (fun i _ => by
          simpa [H, hballEq, D, B] using hG i)
      _ = 3 * D ^ (1 / 2 : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsp' : (∫⁻ y in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      3 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite *
          (3 * D ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) *
          (3 * E ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) +
        3 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite *
          ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
          (3 * E ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
    calc
      _ ≤ 3 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite *
          (∑ i : Fin 3, weakGradientLpNormOn 2 (euclideanBall x₀ r)
            (H i).grad) ^ (3 / 2 : ℝ) *
          (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ r) (H i).toFun) ^
            (3 / 2 : ℝ) +
        3 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite *
          ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
          (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ r) (H i).toFun) ^
            (3 : ℝ) := by
        simpa [H] using hsp
      _ ≤ _ := by gcongr
  have hmain : (∫⁻ y in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      (81 * ENNReal.ofReal (Real.sqrt 3) *
        Classical.choose interpolationBall_three_finite) *
          E ^ (3 / 4 : ℝ) * D ^ (3 / 4 : ℝ) +
        (81 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite) *
        ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) * E ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ 3 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite *
          (3 * D ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) *
          (3 * E ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) +
        3 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite *
          ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
          (3 * E ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := hsp'
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg (3 : ℝ≥0∞) _ (by norm_num),
          ENNReal.mul_rpow_of_nonneg (3 : ℝ≥0∞) _ (by norm_num),
          ENNReal.mul_rpow_of_nonneg (3 : ℝ≥0∞) _ (by norm_num)]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
        have hthree : (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
            (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) = (3 : ℝ≥0∞) ^ (3 : ℝ) := by
          rw [← ENNReal.rpow_add]
          all_goals norm_num
        have hfirst :
            3 * ENNReal.ofReal (Real.sqrt 3) *
                Classical.choose interpolationBall_three_finite *
                ((3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * D ^ (3 / 4 : ℝ)) *
                ((3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * E ^ (3 / 4 : ℝ)) =
              (81 * ENNReal.ofReal (Real.sqrt 3) *
                Classical.choose interpolationBall_three_finite) *
                E ^ (3 / 4 : ℝ) * D ^ (3 / 4 : ℝ) := by
          calc
            _ = 3 * ENNReal.ofReal (Real.sqrt 3) *
                Classical.choose interpolationBall_three_finite *
                ((3 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
                  (3 : ℝ≥0∞) ^ (3 / 2 : ℝ)) *
                (D ^ (3 / 4 : ℝ) * E ^ (3 / 4 : ℝ)) := by ring
            _ = _ := by rw [hthree]; norm_num; ring
        have hsecond :
            3 * ENNReal.ofReal (Real.sqrt 3) *
                Classical.choose interpolationBall_three_finite *
                ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
                ((3 : ℝ≥0∞) ^ (3 : ℝ) * E ^ (3 / 2 : ℝ)) =
              (81 * ENNReal.ofReal (Real.sqrt 3) *
                Classical.choose interpolationBall_three_finite) *
                ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) * E ^ (3 / 2 : ℝ) := by
          norm_num
          ring_nf
        rw [hfirst]
        norm_num
        ring_nf
  simpa [E, D, B] using hmain

private theorem real_rpow_add_bound {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (3 / 2 : ℝ) ≤
      2 ^ (3 / 2 : ℝ) * (a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ)) := by
  have hm : 0 ≤ max a b := le_max_of_le_left ha
  have hab : a + b ≤ 2 * max a b := by
    have h₁ := le_max_left a b
    have h₂ := le_max_right a b
    linarith only [h₁, h₂]
  calc
    (a + b) ^ (3 / 2 : ℝ) ≤ (2 * max a b) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hab (by norm_num)
    _ = 2 ^ (3 / 2 : ℝ) * (max a b) ^ (3 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) hm
    _ ≤ 2 ^ (3 / 2 : ℝ) *
        (a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases hab' : a ≤ b
      · rw [max_eq_right hab']
        exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)
      · have hba : b ≤ a := le_of_not_ge hab'
        rw [max_eq_left hba]
        exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)

private theorem slice_gradient_lintegral_ne_top
    {Ω' : Set Vec3} {x₀ : Vec3} {r s : ℝ}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hDu : MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω'))
    (hball : vec3Ball x₀ r ⊆ Ω') :
    (∫⁻ y in vec3Ball x₀ r,
      ENNReal.ofReal (spatialGradientSq (fun _ => 0) Du (y, s))) ≠ ∞ := by
  let B : Set Vec3 := vec3Ball x₀ r
  have hDuB : MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict B) :=
    hDu.mono_measure (Measure.restrict_mono_set volume hball)
  have hnormtop : (∫⁻ y in B, ‖Du (y, s)‖ₑ ^ (2 : ℝ)) < ∞ := by
    have hiff := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hDuB.aestronglyMeasurable
    exact hiff.mp hDuB.eLpNorm_lt_top
  have hbound :
      (∫⁻ y in B, ENNReal.ofReal (spatialGradientSq (fun _ => 0) Du (y, s))) ≤
        9 * (∫⁻ y in B, ‖Du (y, s)‖ₑ ^ (2 : ℝ)) := by
    calc
      _ ≤ ∫⁻ y in B, 9 * ‖Du (y, s)‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (fun y => ofReal_spatialGradientSq_le_nine_mul
          (fun _ => 0) Du (y, s))
      _ = _ := lintegral_const_mul' _ _ (by norm_num)
  exact ne_of_lt (lt_of_le_of_lt hbound (ENNReal.mul_lt_top (by norm_num) hnormtop))

private theorem slice_l3_real_bound_of_data
    {Ω' : Set Vec3} {z : ParabolicPoint} {r ρ s : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ ρ)
    (hball : euclideanBall z.1 ρ ⊆ Ω')
    (hs : (MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
      ∀ i : Fin 3, HasWeakGradientOn Ω'
        (fun x => u (x, s) i) (fun x => Du (x, s) i))
    (henergy : (∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (ρ * alpha u z ρ ^ 2))
    (hinner : (∫ y in vec3Ball z.1 r,
        vec3EuclideanNorm (u (y, s)) ^ 2) ≤
      2 * poincareSobolevL1VectorConstant * ρ ^ (3 / 2 : ℝ) *
          alpha u z ρ *
          (∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s)) ^ (1 / 2 : ℝ) +
        r ^ 3 / ρ ^ 2 * alpha u z ρ ^ 2) :
    (∫ y in euclideanBall z.1 r,
        vec3EuclideanNorm (u (y, s)) ^ (3 : ℝ)) ≤
      interpolationC₈ * (ρ ^ (3 / 4 : ℝ) +
        ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
        alpha u z ρ ^ (3 / 2 : ℝ) *
        (∫ y in euclideanBall z.1 ρ,
          spatialGradientSq u Du (y, s)) ^ (3 / 4 : ℝ) +
      interpolationC₈ * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ (3 : ℝ) := by
  let Bi : Set Vec3 := vec3Ball z.1 r
  let Bo : Set Vec3 := vec3Ball z.1 ρ
  let Ai : ℝ≥0∞ := ∫⁻ y in Bi,
    ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)
  let Di : ℝ≥0∞ := ∫⁻ y in Bi, ENNReal.ofReal (spatialGradientSq u Du (y, s))
  let Do : ℝ≥0∞ := ∫⁻ y in Bo, ENNReal.ofReal (spatialGradientSq u Du (y, s))
  let Li : ℝ≥0∞ := ∫⁻ y in Bi,
    ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)
  let Y : ℝ := ∫ y in Bi, vec3EuclideanNorm (u (y, s)) ^ 2
  let G : ℝ := ∫ y in Bo, spatialGradientSq u Du (y, s)
  have hballEqI : Bi = euclideanBall z.1 r :=
    vec3Ball_eq_euclideanBall_cylL3 hr
  have hballEqO : Bo = euclideanBall z.1 ρ :=
    vec3Ball_eq_euclideanBall_cylL3 hρ
  have hballI : euclideanBall z.1 r ⊆ Ω' := by
    intro x hx
    have hxv : x ∈ Bi := by simpa [Bi, hballEqI] using hx
    have hxO : x ∈ Bo := vec3Ball_mono hrρ hxv
    have hxO' : x ∈ euclideanBall z.1 ρ := by simpa [Bo, hballEqO] using hxO
    exact hball hxO'
  have hballIv : Bi ⊆ Ω' := by
    intro x hx
    exact hballI (by simpa [hballEqI] using hx)
  have hballOv : Bo ⊆ Ω' := by
    intro x hx
    exact hball (by simpa [Bo, hballEqO] using hx)
  have hAiDo : Ai ≤ ∫⁻ y in Bo,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) :=
    lintegral_mono_set (vec3Ball_mono hrρ)
  have hDiDo : Di ≤ Do := lintegral_mono_set (vec3Ball_mono hrρ)
  have hAibound : Ai ≤ ENNReal.ofReal (ρ * alpha u z ρ ^ 2) := by
    exact hAiDo.trans henergy
  have hAiTop : Ai ≠ ∞ := ne_of_lt (lt_of_le_of_lt hAibound ENNReal.ofReal_lt_top)
  have hDoTop : Do ≠ ∞ :=
    slice_gradient_lintegral_ne_top hs.1.2 hballOv
  have hDiTop : Di ≠ ∞ := ne_of_lt (lt_of_le_of_lt hDiDo (lt_top_iff_ne_top.mpr hDoTop))
  have huI : MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Bi) :=
    hs.1.1.mono_measure (Measure.restrict_mono_set volume hballIv)
  have hDuI : MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Bi) :=
    hs.1.2.mono_measure (Measure.restrict_mono_set volume hballIv)
  have huO : MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Bo) :=
    hs.1.1.mono_measure (Measure.restrict_mono_set volume hballOv)
  have hDuO : MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Bo) :=
    hs.1.2.mono_measure (Measure.restrict_mono_set volume hballOv)
  have hYmeas : AEStronglyMeasurable
      (fun y : Vec3 => vec3EuclideanNorm (u (y, s)) ^ 2)
      (volume.restrict Bi) :=
    (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      huI.aestronglyMeasurable).pow 2
  have hYlin : (∫⁻ y in Bi,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s)) ^ 2)) = Ai := by
    dsimp [Ai]
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)]
    norm_num
  have hYeq : Y = Ai.toReal := by
    dsimp [Y]
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hYmeas, hYlin]
  have hAiof : Ai = ENNReal.ofReal Y := by
    calc
      Ai = ENNReal.ofReal Ai.toReal := (ENNReal.ofReal_toReal hAiTop).symm
      _ = ENNReal.ofReal Y := by rw [← hYeq]
  have hDuMeasO : AEStronglyMeasurable
      (fun y : Vec3 => Du (y, s)) (volume.restrict Bo) := hDuO.aestronglyMeasurable
  have hgradSqMeasO : AEStronglyMeasurable
      (fun y : Vec3 => spatialGradientSq u Du (y, s)) (volume.restrict Bo) := by
    have hc : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ)) := by fun_prop
    simpa [spatialGradientSq, Function.comp_def] using
      hc.comp_aestronglyMeasurable hDuMeasO
  have hgradSqMeasI : AEStronglyMeasurable
      (fun y : Vec3 => spatialGradientSq u Du (y, s)) (volume.restrict Bi) := by
    have hc : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ)) := by fun_prop
    simpa [spatialGradientSq, Function.comp_def] using
      hc.comp_aestronglyMeasurable hDuI.aestronglyMeasurable
  have hGouterEq : G = Do.toReal := by
    dsimp [G]
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => by
        unfold spatialGradientSq
        positivity)) hgradSqMeasO]
  have hgradSqMeasE : AEStronglyMeasurable
      (fun y : Vec3 => spatialGradientSq u Du (y, s))
      (volume.restrict (euclideanBall z.1 ρ)) := by
    simpa only [hballEqO] using hgradSqMeasO
  have hGouterOf : Do = ENNReal.ofReal G := by
    calc
      Do = ENNReal.ofReal Do.toReal := (ENNReal.ofReal_toReal hDoTop).symm
      _ = ENNReal.ofReal G := by rw [← hGouterEq]
  have hLmeas : AEStronglyMeasurable
      (fun y : Vec3 => vec3EuclideanNorm (u (y, s)) ^ (3 : ℝ))
      (volume.restrict Bi) := by
    have hcont := continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      huI.aestronglyMeasurable
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3)).comp_aestronglyMeasurable hcont
  have hLmeasE : AEStronglyMeasurable
      (fun y : Vec3 => vec3EuclideanNorm (u (y, s)) ^ (3 : ℝ))
      (volume.restrict (euclideanBall z.1 r)) := by
    simpa only [hballEqI] using hLmeas
  have hLlin : (∫⁻ y in euclideanBall z.1 r,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s)) ^ (3 : ℝ))) = Li := by
    rw [← hballEqI]
    dsimp [Li]
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _) (by norm_num)]
  have hLreal : (∫ y in euclideanBall z.1 r,
      vec3EuclideanNorm (u (y, s)) ^ (3 : ℝ)) = Li.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => Real.rpow_nonneg
        (vec3EuclideanNorm_nonneg (u (y, s))) _))
      hLmeasE]
    exact congrArg ENNReal.toReal hLlin
  have hbase := slice_l3_lintegral_bound hr hballI hs
  let K₀ : ℝ≥0∞ :=
    81 * ENNReal.ofReal (Real.sqrt 3) * Classical.choose interpolationBall_three_finite
  have hK₀top : K₀ ≠ ∞ := by
    dsimp [K₀]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (Classical.choose_spec interpolationBall_three_finite).1
  have hrad : ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) =
      ENNReal.ofReal (r ^ (-(3 / 2 : ℝ))) := by
    rw [ENNReal.ofReal_rpow_of_pos hr]
  have hfirstTop : K₀ * Ai ^ (3 / 4 : ℝ) * Di ^ (3 / 4 : ℝ) ≠ ∞ := by
    dsimp [K₀]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hK₀top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAiTop))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hDiTop)
  have hsecondTop : K₀ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
      Ai ^ (3 / 2 : ℝ) ≠ ∞ := by
    rw [hrad]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hK₀top ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAiTop)
  have hKreal : K₀.toReal =
      81 * Real.sqrt 3 * (Classical.choose interpolationBall_three_finite).toReal := by
    simp [K₀, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
      Real.sqrt_nonneg]
  have hbaseReal : Li.toReal ≤
      K₀.toReal * Y ^ (3 / 4 : ℝ) * Di.toReal ^ (3 / 4 : ℝ) +
        K₀.toReal * (r ^ (-(3 / 2 : ℝ))) * Y ^ (3 / 2 : ℝ) := by
    have hsumTop : K₀ * Ai ^ (3 / 4 : ℝ) * Di ^ (3 / 4 : ℝ) +
        K₀ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) * Ai ^ (3 / 2 : ℝ) ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨hfirstTop, hsecondTop⟩
    have hbase' : Li ≤ K₀ * Ai ^ (3 / 4 : ℝ) * Di ^ (3 / 4 : ℝ) +
        K₀ * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) * Ai ^ (3 / 2 : ℝ) := by
      simpa [Li, K₀, Ai, Di] using hbase
    have hLiTop : Li ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt hbase' (lt_top_iff_ne_top.mpr hsumTop))
    have hto := ENNReal.toReal_mono hsumTop hbase'
    rw [ENNReal.toReal_add hfirstTop hsecondTop,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hto
    rw [← hYeq, hKreal, ENNReal.toReal_ofReal hr.le] at hto
    rw [hKreal]
    simpa [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal,
      Real.sqrt_nonneg] using hto
  have hYupper : Y ≤ ρ * alpha u z ρ ^ 2 := by
    have hAiEnergy : Ai ≤ ENNReal.ofReal (ρ * alpha u z ρ ^ 2) := hAibound
    rw [hAiof] at hAiEnergy
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hρ.le (sq_nonneg _))).mp hAiEnergy
  have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hGnonneg : 0 ≤ G := by
    rw [hGouterEq]
    exact ENNReal.toReal_nonneg
  have hYnonneg : 0 ≤ Y := by
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hY : Y ≤
      2 * poincareSobolevL1VectorConstant * ρ ^ (3 / 2 : ℝ) *
          alpha u z ρ * G ^ (1 / 2 : ℝ) +
        r ^ 3 / ρ ^ 2 * alpha u z ρ ^ 2 := hinner
  have hGupper : Di.toReal ≤ G := by
    rw [hGouterEq]
    exact ENNReal.toReal_mono hDoTop hDiDo
  have hC₅ : 0 ≤ poincareSobolevL1VectorConstant := by
    unfold poincareSobolevL1VectorConstant
    positivity
  let S₁ : ℝ := 2 * poincareSobolevL1VectorConstant *
    ρ ^ (3 / 2 : ℝ) * alpha u z ρ * G ^ (1 / 2 : ℝ)
  let S₂ : ℝ := r ^ 3 / ρ ^ 2 * alpha u z ρ ^ 2
  have hS₁ : 0 ≤ S₁ := by
    dsimp [S₁]
    positivity
  have hS₂ : 0 ≤ S₂ := by
    dsimp [S₂]
    positivity
  have hYsum : Y ≤ S₁ + S₂ := by
    simpa [S₁, S₂] using hY
  have hYpow : Y ^ (3 / 2 : ℝ) ≤
      2 ^ (3 / 2 : ℝ) * (S₁ ^ (3 / 2 : ℝ) + S₂ ^ (3 / 2 : ℝ)) := by
    calc
      Y ^ (3 / 2 : ℝ) ≤ (S₁ + S₂) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hYnonneg hYsum (by norm_num)
      _ ≤ _ := real_rpow_add_bound hS₁ hS₂
  have hYfirst : Y ^ (3 / 4 : ℝ) ≤
      ρ ^ (3 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ) := by
    calc
      Y ^ (3 / 4 : ℝ) ≤ (ρ * alpha u z ρ ^ 2) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hYnonneg hYupper (by norm_num)
      _ = ρ ^ (3 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow hρ.le (sq_nonneg _),
          ← Real.rpow_natCast (alpha u z ρ) 2,
          ← Real.rpow_mul hα]
        norm_num
  have hS₁pow : S₁ ^ (3 / 2 : ℝ) =
      (2 * poincareSobolevL1VectorConstant) ^ (3 / 2 : ℝ) *
        ρ ^ (9 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ) *
          G ^ (3 / 4 : ℝ) := by
    dsimp [S₁]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hα,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hρ.le _),
      ← Real.rpow_mul hρ.le, ← Real.rpow_mul hGnonneg]
    norm_num
  have hS₂pow : S₂ ^ (3 / 2 : ℝ) =
      (r ^ 3 / ρ ^ 2) ^ (3 / 2 : ℝ) * alpha u z ρ ^ 3 := by
    dsimp [S₂]
    rw [Real.mul_rpow (div_nonneg (pow_nonneg hr.le _) (sq_nonneg _))
      (sq_nonneg _),
      ← Real.rpow_natCast (alpha u z ρ) 2,
      ← Real.rpow_mul hα]
    norm_num
  have hscale₁ : r ^ (-(3 / 2 : ℝ)) * ρ ^ (9 / 4 : ℝ) =
      ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_neg hr.le, div_eq_mul_inv]
    ring_nf
  have hscale₂ : r ^ (-(3 / 2 : ℝ)) *
      (r ^ 3 / ρ ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 / ρ ^ 3 := by
    rw [Real.div_rpow (pow_nonneg hr.le _) (sq_nonneg ρ),
      ← Real.rpow_natCast r 3, ← Real.rpow_mul hr.le,
      ← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le]
    norm_num
    have hcombine : r ^ (-(3 / 2 : ℝ)) * r ^ (9 / 2 : ℝ) = r ^ 3 := by
      rw [← Real.rpow_add hr]
      norm_num
    calc
      _ = (r ^ (-(3 / 2 : ℝ)) * r ^ (9 / 2 : ℝ)) / ρ ^ 3 := by ring
      _ = _ := by rw [hcombine]
  let K : ℝ := K₀.toReal
  let c : ℝ := 2 ^ (3 / 2 : ℝ)
  let d : ℝ := (2 * poincareSobolevL1VectorConstant) ^ (3 / 2 : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; exact ENNReal.toReal_nonneg
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hC₈eq : interpolationC₈ = K * (1 + c * d + c) := by
    unfold interpolationC₈
    change (K₀ * ENNReal.ofReal
      (1 + 2 ^ (3 / 2 : ℝ) *
        (2 * poincareSobolevL1VectorConstant) ^ (3 / 2 : ℝ) +
        2 ^ (3 / 2 : ℝ))).toReal = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hunit : 1 ≤ 1 + c * d + c := by
    calc
      1 ≤ 1 + c * d := le_add_of_nonneg_right (mul_nonneg hc hd)
      _ ≤ 1 + c * d + c := le_add_of_nonneg_right hc
  have hcd : c * d ≤ 1 + c * d + c := by
    calc
      c * d ≤ 1 + c * d := le_add_of_nonneg_left (by norm_num)
      _ ≤ 1 + c * d + c := le_add_of_nonneg_right hc
  have hcsmall : c ≤ 1 + c * d + c := by
    calc
      c ≤ 1 + c := le_add_of_nonneg_left (by norm_num)
      _ ≤ 1 + c * d + c := by
        calc
          1 + c ≤ (1 + c) + c * d := le_add_of_nonneg_right (mul_nonneg hc hd)
          _ = 1 + c * d + c := by ring
  have hKle : K ≤ interpolationC₈ := by
    rw [hC₈eq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit hK
  have hKcd : K * c * d ≤ interpolationC₈ := by
    rw [hC₈eq]
    calc
      K * c * d = K * (c * d) := by ring
      _ ≤ K * (1 + c * d + c) := by
        exact mul_le_mul_of_nonneg_left hcd hK
  have hKc : K * c ≤ interpolationC₈ := by
    rw [hC₈eq]
    exact mul_le_mul_of_nonneg_left hcsmall hK
  have hfirstBase : K * Y ^ (3 / 4 : ℝ) * Di.toReal ^ (3 / 4 : ℝ) ≤
      K * ρ ^ (3 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ) *
        G ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ K * (ρ ^ (3 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ)) *
          G ^ (3 / 4 : ℝ) := by
        gcongr
      _ = _ := by ring_nf
  have hfirstFinal : K * Y ^ (3 / 4 : ℝ) * Di.toReal ^ (3 / 4 : ℝ) ≤
      interpolationC₈ * ρ ^ (3 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ) *
        G ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ K * (ρ ^ (3 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ) *
          G ^ (3 / 4 : ℝ)) := by simpa only [mul_assoc] using hfirstBase
      _ ≤ interpolationC₈ * (ρ ^ (3 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ) *
          G ^ (3 / 4 : ℝ)) := mul_le_mul_of_nonneg_right hKle (by positivity)
      _ = _ := by ring
  have hsecondExpanded : K * r ^ (-(3 / 2 : ℝ)) * Y ^ (3 / 2 : ℝ) ≤
      K * c * d * (ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
          alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ) +
        K * c * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ 3 := by
    calc
      _ ≤ K * r ^ (-(3 / 2 : ℝ)) *
          (c * (S₁ ^ (3 / 2 : ℝ) + S₂ ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hYpow (by positivity)
      _ = K * c * d * (ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
            alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ) +
          K * c * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ 3 := by
        rw [hS₁pow, hS₂pow]
        rw [← hscale₁, ← hscale₂]
        dsimp [c, d]
        ring_nf
  have hsecondFinal : K * r ^ (-(3 / 2 : ℝ)) * Y ^ (3 / 2 : ℝ) ≤
      interpolationC₈ * (ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
          alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ) +
        interpolationC₈ * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ 3 := by
    calc
      _ ≤ K * c * d * (ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
            alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ) +
          K * c * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ 3 := hsecondExpanded
      _ ≤ _ := by
        apply add_le_add
        · calc
            K * c * d * (ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
                alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ) =
              (K * c * d) * ((ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
                alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ)) := by ring
            _ ≤ interpolationC₈ * ((ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
                alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_right hKcd (by positivity)
            _ = _ := by ring
        · calc
            K * c * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ 3 =
              (K * c) * ((r ^ 3 / ρ ^ 3) * alpha u z ρ ^ 3) := by ring
            _ ≤ interpolationC₈ * ((r ^ 3 / ρ ^ 3) * alpha u z ρ ^ 3) :=
              mul_le_mul_of_nonneg_right hKc (by positivity)
            _ = _ := by ring
  have hLreal' :
      (∫ y in euclideanBall z.1 r,
        vec3EuclideanNorm (u (y, s)) ^ (3 : ℝ)) ≤
      interpolationC₈ * (ρ ^ (3 / 4 : ℝ) +
        ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
        alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ) +
      interpolationC₈ * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ (3 : ℝ) := by
    rw [hLreal]
    calc
      _ ≤ interpolationC₈ * ρ ^ (3 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ) *
          G ^ (3 / 4 : ℝ) +
        interpolationC₈ * (ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
          alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ) +
        interpolationC₈ * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ 3 := by
        calc
          _ ≤ K * Y ^ (3 / 4 : ℝ) * Di.toReal ^ (3 / 4 : ℝ) +
              K * r ^ (-(3 / 2 : ℝ)) * Y ^ (3 / 2 : ℝ) := hbaseReal
          _ ≤ interpolationC₈ * ρ ^ (3 / 4 : ℝ) * alpha u z ρ ^ (3 / 2 : ℝ) *
                G ^ (3 / 4 : ℝ) +
              (interpolationC₈ * (ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
                alpha u z ρ ^ (3 / 2 : ℝ) * G ^ (3 / 4 : ℝ) +
                interpolationC₈ * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ 3) :=
            add_le_add hfirstFinal hsecondFinal
          _ = _ := by ring
      _ = _ := by
        simp only [mul_add, add_mul, div_eq_mul_inv]
        rw [← Real.rpow_natCast (alpha u z ρ) 3]
        ring_nf
  simpa [G, Bo, hballEqO] using hLreal'

/-- The pointwise-in-time two-radius cubic estimate from the scale quantities
with the paper's convention `A(z,ρ) = alpha(z,ρ)^2`. -/
theorem cylinder_L3_pointwise
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r ρ : ℝ} (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂(volume.restrict (Ioc (z.2 - r ^ 2) z.2)),
      (∫ x in euclideanBall z.1 r,
        vec3EuclideanNorm (u (x, s)) ^ (3 : ℝ)) ≤
        interpolationC₈ * (ρ ^ (3 / 4 : ℝ) +
          ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
          alpha u z ρ ^ (3 / 2 : ℝ) *
          (∫ x in euclideanBall z.1 ρ,
            spatialGradientSq u Du (x, s)) ^ (3 / 4 : ℝ) +
        interpolationC₈ * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ (3 : ℝ) := by
  have hρ : 0 < ρ := by
    have hh : 2 * r ≤ ρ := by nlinarith only [hhalf]
    linarith only [hr, hh]
  have hrρ : r ≤ ρ := by
    have hh : 2 * r ≤ ρ := by nlinarith only [hhalf]
    linarith only [hr, hh]
  obtain ⟨R, Ω', J, hρR, hbox, hball, hT, _hpoincare⟩ :=
    caccioppoli_slice_poincare_ae hsol hρ hsub
  have hballρ : euclideanBall z.1 ρ ⊆ Ω' := by
    intro x hx
    have hxv : x ∈ vec3Ball z.1 ρ := by
      rw [vec3Ball_eq_euclideanBall_cylL3 hρ]
      exact hx
    exact hball x (vec3Ball_mono hρR.le hxv)
  let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  let Tr : Set ℝ := Ioc (z.2 - r ^ 2) z.2
  have hTrTρ : Tr ⊆ Tρ := by
    intro s hs
    refine ⟨?_, hs.2⟩
    apply lt_of_le_of_lt _ hs.1
    exact sub_le_sub_left (pow_le_pow_left₀ hr.le hrρ 2) _
  have hsliceJ := slice_memLp_ae_of_sws hsol hbox
  have hgradJ : ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
      HasWeakGradientOn Ω' (fun x => u (x, s) i)
        (fun x => Du (x, s) i) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.2.2.2.2.2
  have hgradAllJ : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x => u (x, s) i)
        (fun x => Du (x, s) i) := by
    rw [ae_all_iff]
    intro i
    exact hgradJ i
  have hslice : ∀ᵐ s ∂volume.restrict Tρ,
      ((MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
        ∀ i : Fin 3, HasWeakGradientOn Ω'
          (fun x => u (x, s) i) (fun x => Du (x, s) i)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hT hsliceJ,
      ae_restrict_of_ae_restrict_of_subset hT hgradAllJ] with s hs hg
    exact ⟨hs, hg⟩
  have henergy0 := ENNReal.ae_le_essSup (μ := volume.restrict Tρ)
    (fun s => timeSliceBallEnergy z.1 ρ s
      (fun w => vec3EuclideanNorm (u w)))
  have henergyEq := sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq
    hsol z hρ hsub
  change essSup _ (volume.restrict Tρ) = _ at henergyEq
  rw [henergyEq] at henergy0
  have henergy : ∀ᵐ s ∂volume.restrict Tρ,
      (∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
          ENNReal.ofReal (ρ * alpha u z ρ ^ 2) := by
    filter_upwards [henergy0] with s hs
    simpa only [timeSliceBallEnergy, Real.enorm_eq_ofReal
      (vec3EuclideanNorm_nonneg _)] using hs
  have hinner := slice_inner_ball_energy_bound_of_sws
    hsol hρ hr hrρ hsub
  have hgradEq (s : ℝ) :
      (∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s)) =
        ∫ y in vec3Ball z.1 ρ,
          ∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with y
    unfold spatialGradientSq vec3EuclideanNorm
    simp only [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  have hpoint : ∀ᵐ s ∂volume.restrict Tρ,
      (∫ y in euclideanBall z.1 r,
        vec3EuclideanNorm (u (y, s)) ^ (3 : ℝ)) ≤
        interpolationC₈ * (ρ ^ (3 / 4 : ℝ) +
          ρ ^ (9 / 4 : ℝ) / r ^ (3 / 2 : ℝ)) *
          alpha u z ρ ^ (3 / 2 : ℝ) *
          (∫ y in euclideanBall z.1 ρ,
            spatialGradientSq u Du (y, s)) ^ (3 / 4 : ℝ) +
        interpolationC₈ * (r ^ 3 / ρ ^ 3) * alpha u z ρ ^ (3 : ℝ) := by
    filter_upwards [hslice, henergy, hinner] with s hs he hi
    rw [← hgradEq s] at hi
    exact slice_l3_real_bound_of_data hr hρ hrρ hballρ hs he hi
  exact ae_restrict_of_ae_restrict_of_subset hTrTρ hpoint

end CKN
