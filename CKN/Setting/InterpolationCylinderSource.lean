-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.InterpolationCylinder
import CKN.Setting.SobolevPoincareConstantFinite
import CKN.Foundation.Parabolic.Vec3Norm

/-! # Two-radius interpolation from the energy data

Subtracting each spatial mean separates the inner-ball volume term from the
mean-free Sobolev term. Hölder in time then yields the cubic interpolation
estimate using only the square-integrable velocity and weak gradient.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN

private theorem cubic_holder {μ : Measure Vec3} {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ ^ (3 : ℝ) ∂μ) ≤
      eLpNorm f 2 μ ^ (3/2 : ℝ) * eLpNorm f 6 μ ^ (3/2 : ℝ) := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (4/3 : ℝ).HolderConjugate 4 by constructor <;> norm_num)
    (hf.enorm.pow_const (3/2 : ℝ))
    (hf.enorm.pow_const (3/2 : ℝ))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num) hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (6 : ℝ≥0∞) ≠ 0)
      (by norm_num) hf]
  simp only [← ENNReal.rpow_mul] at hh ⊢
  norm_num at hh ⊢
  convert hh using 1
  apply lintegral_congr
  intro x
  rw [← ENNReal.rpow_add_of_nonneg (x := ‖f x‖ₑ) (y := (3/2 : ℝ)) (z := (3/2 : ℝ)) (by norm_num) (by norm_num)]
  norm_num

private theorem average_enorm_bound {μ : Measure Vec3} [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) {f : Vec3 → ℝ} (hf : AEStronglyMeasurable f μ) :
    ‖average μ f‖ₑ ≤ (μ univ) ^ (-(1/2 : ℝ)) * eLpNorm f 2 μ := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    hf.enorm (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at hh
  have he : ‖average μ f‖ₑ = (μ univ)⁻¹ * ‖∫ x, f x ∂μ‖ₑ := by
    rw [average_eq, smul_eq_mul, enorm_mul, Real.enorm_eq_ofReal,
      ENNReal.ofReal_inv_of_pos, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ univ)]
    · exact ENNReal.toReal_pos hμ (measure_ne_top μ univ)
    · positivity
  rw [he]
  calc
    _ ≤ (μ univ)⁻¹ * ∫⁻ x, ‖f x‖ₑ ∂μ := by
      gcongr
      exact enorm_integral_le_lintegral_enorm f
    _ ≤ (μ univ)⁻¹ * ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1/2 : ℝ) *
        (μ univ) ^ (1/2 : ℝ)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num) hf]
      norm_num only [ENNReal.toReal_ofNat]
      rw [mul_comm _ ((μ univ) ^ (1/2 : ℝ)), ← mul_assoc,
        ← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ hμ (measure_ne_top μ univ)]
      norm_num

private theorem scalar_inner_cubic {μ ν : Measure Vec3} [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) (hν : ν ≤ μ) {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f μ) {S D : ℝ≥0∞}
    (hsob : eLpNorm (fun x => f x - average μ f) 6 μ ≤ S * D) :
    (∫⁻ x, ‖f x‖ₑ ^ (3 : ℝ) ∂ν) ≤
      4 * ((2 * S) ^ (3/2 : ℝ) * eLpNorm f 2 μ ^ (3/2 : ℝ) * D ^ (3/2 : ℝ) +
        ν univ * (μ univ) ^ (-(3/2 : ℝ)) * eLpNorm f 2 μ ^ (3 : ℝ)) := by
  let c : ℝ := average μ f
  have hc := average_enorm_bound hμ hf
  have hc2 : eLpNorm (fun _ : Vec3 => c) 2 μ ≤ eLpNorm f 2 μ := by
    rw [eLpNorm_const' c (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat]
    calc
      _ ≤ ((μ univ) ^ (-(1/2 : ℝ)) * eLpNorm f 2 μ) * (μ univ) ^ (1/2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by
        rw [mul_assoc, mul_comm (eLpNorm f 2 μ), ← mul_assoc,
          ← ENNReal.rpow_add _ _ hμ (measure_ne_top μ univ)]
        norm_num
  have hcenter : AEStronglyMeasurable (fun x => f x - c) μ :=
    hf.sub aestronglyMeasurable_const
  have hcenter2 : eLpNorm (fun x => f x - c) 2 μ ≤ 2 * eLpNorm f 2 μ := by
    calc
      _ ≤ eLpNorm f 2 μ + eLpNorm (fun _ : Vec3 => c) 2 μ :=
        eLpNorm_sub_le (by norm_num)
      _ ≤ eLpNorm f 2 μ + eLpNorm f 2 μ := add_le_add_right hc2 _
      _ = _ := (two_mul _).symm
  have hcenter3 : (∫⁻ x, ‖f x - c‖ₑ ^ (3 : ℝ) ∂ν) ≤
      (2 * S) ^ (3/2 : ℝ) * eLpNorm f 2 μ ^ (3/2 : ℝ) * D ^ (3/2 : ℝ) := by
    calc
      _ ≤ ∫⁻ x, ‖f x - c‖ₑ ^ (3 : ℝ) ∂μ := lintegral_mono' hν le_rfl
      _ ≤ eLpNorm (fun x => f x - c) 2 μ ^ (3/2 : ℝ) *
          eLpNorm (fun x => f x - c) 6 μ ^ (3/2 : ℝ) := cubic_holder hcenter
      _ ≤ (2 * eLpNorm f 2 μ) ^ (3/2 : ℝ) * (S * D) ^ (3/2 : ℝ) := by
        exact mul_le_mul' (ENNReal.rpow_le_rpow hcenter2 (by norm_num))
          (ENNReal.rpow_le_rpow hsob (by norm_num))
      _ = _ := by simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3/2)]; ring
  have hc3 : ‖c‖ₑ ^ (3 : ℝ) ≤
      (μ univ) ^ (-(3/2 : ℝ)) * eLpNorm f 2 μ ^ (3 : ℝ) := by
    have hh := ENNReal.rpow_le_rpow hc (by norm_num : (0 : ℝ) ≤ 3)
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3),
      ← ENNReal.rpow_mul, show (-(1/2 : ℝ)) * 3 = -(3/2 : ℝ) by norm_num] using hh
  calc
    _ ≤ ∫⁻ x, 4 * (‖f x - c‖ₑ ^ (3 : ℝ) + ‖c‖ₑ ^ (3 : ℝ)) ∂ν := by
      apply lintegral_mono
      intro x
      have htri : ‖f x‖ₑ ≤ ‖f x - c‖ₑ + ‖c‖ₑ := by
        simpa only [sub_add_cancel] using enorm_add_le (f x - c) c
      exact (ENNReal.rpow_le_rpow htri (by norm_num)).trans (by
        convert ENNReal.rpow_add_le_mul_rpow_add_rpow ‖f x - c‖ₑ ‖c‖ₑ
          (by norm_num : (1 : ℝ) ≤ 3) using 1
        norm_num)
    _ = 4 * ((∫⁻ x, ‖f x - c‖ₑ ^ (3 : ℝ) ∂ν) + ν univ * ‖c‖ₑ ^ (3 : ℝ)) := by
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_left' ((hcenter.mono_measure hν).enorm.pow_const _)]
      simp only [lintegral_const, mul_comm (‖c‖ₑ ^ (3 : ℝ))]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add hcenter3 (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc3 (show 0 ≤ ν univ from bot_le))

private def cubicConstant : ℝ≥0∞ :=
  12 * ENNReal.ofReal (Real.sqrt 3) * ((2 * sobolevPoincareL6Constant) ^ (3/2 : ℝ) + 1)

private theorem cubicConstant_ne_top : cubicConstant ≠ ⊤ := by
  unfold cubicConstant
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) sobolevPoincareL6Constant_ne_top), by norm_num⟩)

private theorem vector_inner_cubic {x₀ : Vec3} {r ρ : ℝ} (hρ : 0 < ρ)
    (hrρ : r ≤ ρ) {u : Vec3 → Vec3}
    (H : ∀ _i : Fin 3, H1Function (euclideanBall x₀ ρ))
    (hcomp : ∀ i : Fin 3, (H i).toFun = fun x => u x i)
    {A G : ℝ≥0∞}
    (hA : ∀ i, lpNormOn 2 (euclideanBall x₀ ρ) (H i).toFun ≤ A)
    (hG : ∀ i, weakGradientLpNormOn 2 (euclideanBall x₀ ρ) (H i).grad ≤ G) :
    (∫⁻ x in vec3Ball x₀ r, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℝ)) ≤
      cubicConstant * (A ^ (3/2 : ℝ) * G ^ (3/2 : ℝ) +
        volume (vec3Ball x₀ r) * volume (vec3Ball x₀ ρ) ^ (-(3/2 : ℝ)) * A ^ (3 : ℝ)) := by
  let μ := volume.restrict (vec3Ball x₀ ρ)
  let ν := volume.restrict (vec3Ball x₀ r)
  have hball : euclideanBall x₀ ρ = vec3Ball x₀ ρ := by
    ext x
    change x ∈ euclideanBall x₀ ρ ↔ vec3EuclideanNorm (x - x₀) < ρ
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      using mem_euclideanBall_iff_vecEuclideanNorm_lt hρ
  have : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using volume_vec3Ball_lt_top (x := x₀) (r := ρ)⟩
  have hμ : μ univ ≠ 0 := by
    simpa only [μ, Measure.restrict_apply_univ] using (volume_vec3Ball_pos hρ).ne'
  have hν : ν ≤ μ := Measure.restrict_mono_set volume (vec3Ball_mono hrρ)
  have hm (i : Fin 3) : AEStronglyMeasurable (fun x => u x i) μ := by
    simpa only [μ, hball, hcomp i] using (H i).memL2.aestronglyMeasurable
  let X := A ^ (3/2 : ℝ) * G ^ (3/2 : ℝ)
  let Y := volume (vec3Ball x₀ r) * volume (vec3Ball x₀ ρ) ^ (-(3/2 : ℝ)) * A ^ (3 : ℝ)
  let K := (2 * sobolevPoincareL6Constant) ^ (3/2 : ℝ)
  have hi (i : Fin 3) : (∫⁻ x in vec3Ball x₀ r, ‖u x i‖ₑ ^ (3 : ℝ)) ≤
      4 * (K + 1) * (X + Y) := by
    have hsob := sobolevPoincare_L6_ball_weak x₀ hρ (H i)
    have hsob' : eLpNorm (fun x => u x i - average μ (fun x => u x i)) 6 μ ≤
        sobolevPoincareL6Constant * G := by
      exact (show _ ≤ sobolevPoincareL6Constant *
        weakGradientLpNormOn 2 (euclideanBall x₀ ρ) (H i).grad by
          simpa only [lpNormOn, hcomp i, hball, μ] using hsob).trans
            (mul_le_mul_of_nonneg_left (hG i) (by positivity))
    have ha : eLpNorm (fun x => u x i) 2 μ ≤ A := by
      simpa only [lpNormOn, hcomp i, hball, μ] using hA i
    have hb := scalar_inner_cubic hμ hν (hm i) hsob'
    calc
      _ ≤ 4 * (K * X + Y) := by
        apply hb.trans
        dsimp [K, X, Y]
        simp only [μ, ν, Measure.restrict_apply_univ, ← mul_assoc]
        gcongr
      _ ≤ 4 * ((K + 1) * X + (K + 1) * Y) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
        · calc
            Y = 1 * Y := (one_mul Y).symm
            _ ≤ (K + 1) * Y := mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left (by positivity)) (by positivity)
      _ = _ := by ring
  have hv := lintegral_vec3EuclideanNorm_rpow_le_sum
    (s := vec3Ball x₀ r) (u := u) (p := (3 : ℝ)) (by norm_num)
    (fun i => ((hm i).mono_measure hν).aemeasurable)
  have hpow : (3 : ℝ) ^ max 0 ((3 : ℝ)/2 - 1) = Real.sqrt 3 := by
    norm_num only [show max 0 ((3 : ℝ)/2 - 1) = 1/2 by norm_num, max_eq_right (by norm_num : (0 : ℝ) ≤ 1/2)]
    exact (Real.sqrt_eq_rpow _).symm
  rw [hpow] at hv
  apply hv.trans
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt 3) * ∑ _i : Fin 3, 4 * (K + 1) * (X + Y) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [cubicConstant, K, X, Y]
      ring

private lemma component_norm_le_vec3_step2 (v : Vec3) (i : Fin 3) :
    ‖v i‖ ≤ vec3EuclideanNorm v := by
  change |v i| ≤ vec3EuclideanNorm v
  unfold vec3EuclideanNorm
  exact Real.abs_le_sqrt (Finset.single_le_sum
    (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
private lemma component_norm_sq_le_spatialGradientSq_step2
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (w : ParabolicPoint) (i : Fin 3) :
    ‖Du w i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (spatialGradientSq u Du w) := by
  have hnorm : ‖Du w i‖ ^ 2 ≤ spatialGradientSq u Du w := by
    rw [Pi.norm_def]
    change (↑(Finset.univ.sup (fun j : Fin 3 => ‖Du w i j‖₊) : ℝ≥0) : ℝ) ^ 2 ≤ _
    have hsup : (Finset.univ.sup (fun j : Fin 3 => ‖Du w i j‖₊) : ℝ≥0) ≤
        ⟨Real.sqrt (spatialGradientSq u Du w), by positivity⟩ := by
      apply Finset.sup_le
      intro j hj
      change ‖Du w i j‖₊ ≤ ⟨Real.sqrt (spatialGradientSq u Du w), by positivity⟩
      exact_mod_cast (show ‖Du w i j‖ ≤ Real.sqrt (spatialGradientSq u Du w) by
      apply (Real.le_sqrt (by positivity) (by
        unfold spatialGradientSq
        positivity)).2
      unfold spatialGradientSq
      have hterm : (Du w i j) ^ 2 ≤
          ∑ k : Fin 3, ∑ l : Fin 3, (Du w k l) ^ 2 := by
        calc
          _ ≤ ∑ l : Fin 3, (Du w i l) ^ 2 :=
            Finset.single_le_sum (fun l _ => sq_nonneg (Du w i l))
              (Finset.mem_univ j)
          _ ≤ _ := Finset.single_le_sum
            (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (Du w k l)))
            (Finset.mem_univ i)
      simpa [Real.norm_eq_abs, sq_abs] using hterm)
    have hsq : (Real.sqrt (spatialGradientSq u Du w)) ^ 2 =
        spatialGradientSq u Du w := by
      rw [Real.sq_sqrt]
      unfold spatialGradientSq
      positivity
    have hsupR : (↑(Finset.univ.sup (fun j : Fin 3 => ‖Du w i j‖₊) : ℝ≥0) : ℝ) ≤
        Real.sqrt (spatialGradientSq u Du w) := by exact_mod_cast hsup
    calc
      _ ≤ (Real.sqrt (spatialGradientSq u Du w)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsupR 2
      _ = _ := hsq
  calc
    ‖Du w i‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖Du w i‖ ^ 2) := by
      rw [show ‖Du w i‖ₑ = ENNReal.ofReal ‖Du w i‖ from (ofReal_norm _).symm,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (norm_nonneg (Du w i))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hnorm
private theorem prod_lintegral_swap_step2 {S : Set Vec3} {T : Set ℝ}
    {F : Vec3 × ℝ → ℝ≥0∞}
    (hF : AEMeasurable F ((volume.restrict S).prod (volume.restrict T))) :
    (∫⁻ z in S ×ˢ T, F z) = ∫⁻ s in T, ∫⁻ y in S, F (y, s) := by
  rw [show (volume : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) from
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict]
  calc
    _ = ∫⁻ y : Vec3, ∫⁻ s : ℝ, F (y, s)
        ∂(volume.restrict T) ∂(volume.restrict S) :=
      MeasureTheory.lintegral_prod F hF
    _ = _ := MeasureTheory.lintegral_lintegral_swap (by
      change AEMeasurable F ((volume.restrict S).prod (volume.restrict T))
      exact hF)
private lemma enorm_norm_pow_two {E : Type*} [SeminormedAddGroup E] (v : E) :
    ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2, ENNReal.rpow_natCast,
    show ‖v‖ₑ = ENNReal.ofReal ‖v‖ from (ofReal_norm v).symm,
    ← ENNReal.ofReal_pow (norm_nonneg v)]

private lemma ofReal_vec3EuclideanNorm_pow_two_le (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) ≤ 3 * ‖v‖ₑ ^ (2 : ℝ) := by
  have h2n : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2n]
  have hle : vec3EuclideanNorm v ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
    have h := vec3EuclideanNorm_le_sqrt_three_mul_norm v
    have h2 : (vec3EuclideanNorm v) ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (vec3EuclideanNorm_nonneg v) h 2
    simpa [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using h2
  calc ENNReal.ofReal (vec3EuclideanNorm v) ^ ((2 : ℕ) : ℝ)
      = ENNReal.ofReal (vec3EuclideanNorm v ^ ((2 : ℕ) : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg v) (by norm_num)
    _ = ENNReal.ofReal (vec3EuclideanNorm v ^ 2) := by rw [Real.rpow_natCast]
    _ ≤ ENNReal.ofReal (3 * ‖v‖ ^ 2) := ENNReal.ofReal_le_ofReal hle
    _ = 3 * ‖v‖ₑ ^ ((2 : ℕ) : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        show ENNReal.ofReal (3 : ℝ) = 3 by norm_num,
        show ‖v‖ₑ ^ ((2 : ℕ) : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) from by
          rw [ENNReal.rpow_natCast,
            show ‖v‖ₑ = ENNReal.ofReal ‖v‖ from (ofReal_norm v).symm,
            ← ENNReal.ofReal_pow (norm_nonneg v)]]

private lemma ofReal_spatialGradientSq_le (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    ENNReal.ofReal (spatialGradientSq u Du z) ≤ 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
  have hsq : spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ 2 := by
    rw [spatialGradientSq]
    calc ∑ i, ∑ j, (Du z i j) ^ (2 : ℕ)
        ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            ((norm_le_pi_norm (Du z i) j).trans (norm_le_pi_norm (Du z) i)) 2
      _ = 9 * ‖Du z‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          try ring
  calc ENNReal.ofReal (spatialGradientSq u Du z)
      ≤ ENNReal.ofReal (9 * ‖Du z‖ ^ 2) := ENNReal.ofReal_le_ofReal hsq
    _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
          show ENNReal.ofReal (9 : ℝ) = 9 by norm_num,
          ← enorm_norm_pow_two (Du z)]

private theorem square_slice_memLp {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {T : Set ℝ} {v : Vec3 × ℝ → E}
    (hv : AEStronglyMeasurable v ((volume.restrict B).prod (volume.restrict T)))
    (hfin : (∫⁻ z, ‖v z‖ₑ ^ (2 : ℝ) ∂((volume.restrict B).prod (volume.restrict T))) < ⊤) :
    ∀ᵐ s ∂volume.restrict T, MemLp (fun x => v (x,s)) 2 (volume.restrict B) := by
  have hm := hv.enorm.pow_const (2 : ℝ)
  have ht : (∫⁻ s in T, ∫⁻ x in B, ‖v (x,s)‖ₑ ^ (2 : ℝ)) < ⊤ := by
    rw [← lintegral_prod_symm _ hm]
    exact hfin
  filter_upwards [hv.prodMk_right, ae_lt_top' hm.lintegral_prod_left' ht.ne]
    with s hs hsf
  change eLpNorm _ 2 _ < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num) hs]
  simpa only [ENNReal.toReal_ofNat] using hsf

private theorem cubic_cylinder_mass
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (r ρ : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ)
    (hu : AEStronglyMeasurable u (volume.restrict (parabolicCylinder z.1 z.2 ρ)))
    (hDu : AEStronglyMeasurable Du (volume.restrict (parabolicCylinder z.1 z.2 ρ)))
    (he : essSup (fun s => ∫⁻ x in vec3Ball z.1 ρ, ‖u (x,s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioc (z.2-ρ^2) z.2)) < ⊤)
    (hd : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ‖u w‖ₑ ^ (2 : ℝ) + ‖Du w‖ₑ ^ (2 : ℝ)) < ⊤)
    (hw : ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict (Ioc (z.2-ρ^2) z.2),
      HasWeakGradientOn (vec3Ball z.1 ρ) (fun x => u (x,s) i) (fun x => Du (x,s) i)) :
    let E := timeSliceEnergyEssSup z.1 z.2 ρ (fun w => vec3EuclideanNorm (u w))
    let D := ∫⁻ w in parabolicCylinder z.1 z.2 ρ, ENNReal.ofReal (spatialGradientSq u Du w)
    E < ⊤ ∧ D < ⊤ ∧
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
        cubicConstant * (E ^ (3/4 : ℝ) * D ^ (3/4 : ℝ) * ENNReal.ofReal (r^2) ^ (1/4 : ℝ) +
          volume (vec3Ball z.1 r) * volume (vec3Ball z.1 ρ) ^ (-(3/2 : ℝ)) *
            ENNReal.ofReal (r^2) * E ^ (3/2 : ℝ)) := by
  let B := vec3Ball z.1 ρ
  let T := Ioc (z.2 - ρ^2) z.2
  let T₁ := Ioc (z.2 - r^2) z.2
  let μ := volume.restrict B
  let E := timeSliceEnergyEssSup z.1 z.2 ρ (fun w => vec3EuclideanNorm (u w))
  let D := ∫⁻ w in parabolicCylinder z.1 z.2 ρ, ENNReal.ofReal (spatialGradientSq u Du w)
  let A : ℝ → ℝ≥0∞ := fun s => (∫⁻ x in B,
    ENNReal.ofReal (vec3EuclideanNorm (u (x,s))) ^ (2 : ℝ)) ^ (1/2 : ℝ)
  let G : ℝ → ℝ≥0∞ := fun s => (∫⁻ x in B,
    ENNReal.ofReal (spatialGradientSq u Du (x,s))) ^ (1/2 : ℝ)
  let R := volume (vec3Ball z.1 r) * volume B ^ (-(3/2 : ℝ))
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hT : T₁ ⊆ T := by
    intro s hs
    exact ⟨lt_of_le_of_lt (sub_le_sub_left (pow_le_pow_left₀ hr.le hrρ 2) _) hs.1, hs.2⟩
  have hup : AEStronglyMeasurable u (μ.prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    exact hu
  have hDup : AEStronglyMeasurable Du (μ.prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    exact hDu
  have hu2 : (∫⁻ w in parabolicCylinder z.1 z.2 ρ, ‖u w‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono (fun w => le_add_of_nonneg_right (by positivity))).trans_lt hd
  have hDu2 : (∫⁻ w in parabolicCylinder z.1 z.2 ρ, ‖Du w‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono (fun w => le_add_of_nonneg_left (by positivity))).trans_lt hd
  have hE : E < ⊤ := by
    have hp : ∀ s, timeSliceBallEnergy z.1 ρ s (fun w => vec3EuclideanNorm (u w)) ≤
        3 * ∫⁻ x in B, ‖u (x,s)‖ₑ ^ (2 : ℝ) := by
      intro s
      unfold timeSliceBallEnergy
      simp only [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
      calc
        _ ≤ ∫⁻ x in B, 3 * ‖u (x,s)‖ₑ ^ (2 : ℝ) :=
          lintegral_mono (fun x => ofReal_vec3EuclideanNorm_pow_two_le (u (x,s)))
        _ = _ := lintegral_const_mul' _ _ (by norm_num)
    have hh := essSup_mono_ae (μ := volume.restrict T) (Eventually.of_forall hp)
    rw [ENNReal.essSup_const_mul] at hh
    exact hh.trans_lt (ENNReal.mul_lt_top (by norm_num) he)
  have hD : D < ⊤ := by
    calc
      D ≤ ∫⁻ w in parabolicCylinder z.1 z.2 ρ, 9 * ‖Du w‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (ofReal_spatialGradientSq_le u Du)
      _ = 9 * ∫⁻ w in parabolicCylinder z.1 z.2 ρ, ‖Du w‖ₑ ^ (2 : ℝ) :=
        lintegral_const_mul' _ _ (by norm_num)
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hDu2
  refine ⟨hE, hD, ?_⟩
  have hum := (ENNReal.continuous_ofReal.comp continuous_vec3EuclideanNorm).comp_aestronglyMeasurable hup
  have hdm : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal (spatialGradientSq u Du w))
      (μ.prod (volume.restrict T)) := by
    exact ((ENNReal.continuous_ofReal.comp
      (show Continuous (fun v : Fin 3 → Vec3 => ∑ i, ∑ j, (v i j)^2) by fun_prop)).comp_aestronglyMeasurable hDup).aemeasurable
  have hA : AEMeasurable A (volume.restrict T₁) :=
    ((hum.aemeasurable.pow_const (2 : ℝ)).lintegral_prod_left'.pow_const (1/2 : ℝ)).mono_measure
      (Measure.restrict_mono_set volume hT)
  have hG : AEMeasurable G (volume.restrict T₁) :=
    (hdm.lintegral_prod_left'.pow_const (1/2 : ℝ)).mono_measure
      (Measure.restrict_mono_set volume hT)
  have hA₀ : ∀ᵐ s ∂volume.restrict T₁, A s ≤ E ^ (1/2 : ℝ) := by
    have hb := ENNReal.ae_le_essSup (μ := volume.restrict T)
      (fun s => timeSliceBallEnergy z.1 ρ s (fun w => vec3EuclideanNorm (u w)))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hT hb] with s hs
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    simpa only [E, timeSliceEnergyEssSup, timeSliceBallEnergy, B, T, Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)] using hs
  have hG₂ : (∫⁻ s in T₁, G s ^ (2 : ℝ)) ≤ D := by
    simp only [G, ← ENNReal.rpow_mul, show (1/2 : ℝ)*2 = 1 by norm_num, ENNReal.rpow_one]
    calc
      _ ≤ ∫⁻ s in T, ∫⁻ x in B, ENNReal.ofReal (spatialGradientSq u Du (x,s)) :=
        lintegral_mono_set hT
      _ = D := by
        rw [← lintegral_prod_symm _ hdm, Measure.prod_restrict]
        rfl
  have hV : volume T₁ ≤ ENNReal.ofReal (r^2) := by
    dsimp [T₁]
    rw [Real.volume_Ioc]
    exact le_of_eq (congrArg ENNReal.ofReal (by ring))
  have hsU : ∀ᵐ s ∂volume.restrict T, MemLp (fun x => u (x,s)) 2 μ := by
    apply square_slice_memLp hup
    rw [Measure.prod_restrict]
    exact hu2
  have hsD : ∀ᵐ s ∂volume.restrict T, MemLp (fun x => Du (x,s)) 2 μ := by
    apply square_slice_memLp hDup
    rw [Measure.prod_restrict]
    exact hDu2
  have hsW : ∀ᵐ s ∂volume.restrict T, ∀ i,
      HasWeakGradientOn B (fun x => u (x,s) i) (fun x => Du (x,s) i) :=
    ae_all_iff.mpr hw
  have hballeq : euclideanBall z.1 ρ = B := by
    ext x
    change x ∈ euclideanBall z.1 ρ ↔ vec3EuclideanNorm (x - z.1) < ρ
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      using mem_euclideanBall_iff_vecEuclideanNorm_lt hρ
  have hpoint : ∀ᵐ s ∂volume.restrict T₁,
      (∫⁻ x in vec3Ball z.1 r, ENNReal.ofReal (vec3EuclideanNorm (u (x,s))) ^ (3 : ℝ)) ≤
        cubicConstant * A s ^ (3/2 : ℝ) * G s ^ (3/2 : ℝ) + cubicConstant * R * A s ^ (3 : ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hT hsU,
      ae_restrict_of_ae_restrict_of_subset hT hsD,
      ae_restrict_of_ae_restrict_of_subset hT hsW] with s hsU hsD hsW
    let H : ∀ _i : Fin 3, H1Function (euclideanBall z.1 ρ) := fun i =>
      { toFun := fun x => u (x,s) i
        grad := fun x => Du (x,s) i
        memL2 := by rw [hballeq]; exact MemLp.eval hsU i
        gradMemL2 := fun j => by rw [hballeq]; exact MemLp.eval (MemLp.eval hsD i) j
        hasWeakGradient := by rw [hballeq]; exact hsW i }
    have hAi (i : Fin 3) : lpNormOn 2 (euclideanBall z.1 ρ) (H i).toFun ≤ A s := by
      change eLpNorm (fun x => u (x,s) i) 2 (volume.restrict (euclideanBall z.1 ρ)) ≤ _
      rw [hballeq, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num) (MemLp.eval hsU i).aestronglyMeasurable]
      norm_num only [ENNReal.toReal_ofNat]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply lintegral_mono
      intro x
      change ‖u (x,s) i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (vec3EuclideanNorm (u (x,s))) ^ (2 : ℝ)
      rw [← ofReal_norm]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
        (component_norm_le_vec3_step2 (u (x,s)) i)) (by norm_num)
    have hGi (i : Fin 3) : weakGradientLpNormOn 2 (euclideanBall z.1 ρ) (H i).grad ≤ G s := by
      change eLpNorm (fun x => Du (x,s) i) 2 (volume.restrict (euclideanBall z.1 ρ)) ≤ _
      rw [hballeq, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num) (MemLp.eval hsD i).aestronglyMeasurable]
      norm_num only [ENNReal.toReal_ofNat]
      exact ENNReal.rpow_le_rpow (lintegral_mono
        (fun x => component_norm_sq_le_spatialGradientSq_step2 (x,s) i)) (by norm_num)
    have hv := vector_inner_cubic (u := fun x => u (x,s)) hρ hrρ H (fun _ => rfl) hAi hGi
    simpa only [R, B, mul_add, ← mul_assoc] using hv
  have hmeas : AEMeasurable (fun w : Vec3 × ℝ =>
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
      ((volume.restrict (vec3Ball z.1 r)).prod (volume.restrict T₁)) :=
    (hum.aemeasurable.pow_const (3 : ℝ)).mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume (vec3Ball_mono hrρ)) (Measure.restrict_mono_set volume hT))
  calc
    _ = ∫⁻ s in T₁, ∫⁻ x in vec3Ball z.1 r,
        ENNReal.ofReal (vec3EuclideanNorm (u (x,s))) ^ (3 : ℝ) :=
      prod_lintegral_swap_step2 hmeas
    _ ≤ ∫⁻ s in T₁, cubicConstant * A s ^ (3/2 : ℝ) * G s ^ (3/2 : ℝ) +
        cubicConstant * R * A s ^ (3 : ℝ) := lintegral_mono_ae hpoint
    _ ≤ cubicConstant * (E ^ (1/2 : ℝ)) ^ (3/2 : ℝ) * D ^ (3/4 : ℝ) *
        ENNReal.ofReal (r^2) ^ (1/4 : ℝ) +
        cubicConstant * R * ENNReal.ofReal (r^2) * (E ^ (1/2 : ℝ)) ^ (3 : ℝ) := by
      exact time_interpolation_ball_l3 hA hG cubicConstant_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE.ne) hA₀ hG₂ hV
    _ = _ := by
      simp only [← ENNReal.rpow_mul, show (1/2 : ℝ)*(3/2) = 3/4 by norm_num,
        show (1/2 : ℝ)*3 = 3/2 by norm_num]
      ring

/-- The two-radius cubic interpolation estimate follows from the velocity and
weak-gradient energy data, with one absolute constant fixed before the fields. -/
theorem interpolation_cylinder_source :
  ∃ C₇ : ℝ, 0 ≤ C₇ ∧ ∀ (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) (r ρ : ℝ),
    0 < r → r ≤ ρ →
    AEStronglyMeasurable u (volume.restrict (parabolicCylinder z.1 z.2 ρ)) →
    AEStronglyMeasurable Du (volume.restrict (parabolicCylinder z.1 z.2 ρ)) →
    (essSup (fun s => ∫⁻ x in vec3Ball z.1 ρ, ‖u (x,s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioc (z.2-ρ^2) z.2)) < ⊤) →
    ((∫⁻ w in parabolicCylinder z.1 z.2 ρ, ‖u w‖ₑ^(2 : ℝ) + ‖Du w‖ₑ^(2 : ℝ)) < ⊤) →
    (∀ i : Fin 3, ∀ᵐ s ∂volume.restrict (Ioc (z.2-ρ^2) z.2),
      HasWeakGradientOn (vec3Ball z.1 ρ) (fun x => u (x,s) i) (fun x => Du (x,s) i)) →
    gamma u z r ^ (3 : ℕ) ≤ C₇ * ((r/ρ)^3 * alpha u z ρ ^ (3 : ℕ) +
      (ρ/r)^3 * alpha u z ρ ^ (3/2 : ℝ) * beta u Du z ρ ^ (3/2 : ℝ)) := by
  let v : ℝ := Real.pi * 4 / 3
  let K : ℝ := cubicConstant.toReal
  refine ⟨K * (1 + v ^ (-(1/2 : ℝ))), by positivity, ?_⟩
  intro u Du z r ρ hr hrρ hu hDu he hd hw
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hv : 0 < v := by dsimp [v]; positivity
  let E := timeSliceEnergyEssSup z.1 z.2 ρ (fun w => vec3EuclideanNorm (u w))
  let D := ∫⁻ w in parabolicCylinder z.1 z.2 ρ, ENNReal.ofReal (spatialGradientSq u Du w)
  obtain ⟨hE, hD, hbound⟩ := cubic_cylinder_mass u Du z r ρ hr hrρ hu hDu he hd hw
  have hvol0 : volume (vec3Ball z.1 ρ) ≠ 0 := (volume_vec3Ball_pos hρ).ne'
  have hvoltop : volume (vec3Ball z.1 ρ) ≠ ⊤ := volume_vec3Ball_lt_top.ne
  have hvpow : volume (vec3Ball z.1 ρ) ^ (-(3/2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hvol0 hvoltop
  have hRtop : cubicConstant * (E ^ (3/4 : ℝ) * D ^ (3/4 : ℝ) *
      ENNReal.ofReal (r^2) ^ (1/4 : ℝ) +
      volume (vec3Ball z.1 r) * volume (vec3Ball z.1 ρ) ^ (-(3/2 : ℝ)) *
        ENNReal.ofReal (r^2) * E ^ (3/2 : ℝ)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top cubicConstant_ne_top
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE.ne)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hD.ne))
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top volume_vec3Ball_lt_top.ne hvpow) ENNReal.ofReal_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE.ne)
  have ht := ENNReal.toReal_mono hRtop hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_add
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE.ne)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hD.ne))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top volume_vec3Ball_lt_top.ne hvpow) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE.ne))] at ht
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (sq_nonneg r)] at ht
  have ha : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hb : 0 ≤ beta u Du z ρ := by unfold beta; positivity
  have hEA : E.toReal = ρ * alpha u z ρ ^ 2 := by
    dsimp [alpha]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num only [show (1/2 : ℝ)*2 = 1 by norm_num, Real.rpow_one]
    dsimp [E]
    field_simp
  have hDB : D.toReal = ρ * beta u Du z ρ ^ 2 := by
    dsimp [beta]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num only [show (1/2 : ℝ)*2 = 1 by norm_num, Real.rpow_one]
    dsimp [D]
    field_simp
  have hvol (a : ℝ) (ha : 0 < a) : (volume (vec3Ball z.1 a)).toReal = a^3 * v := by
    rw [volume_vec3Ball_eq, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal hv.le]
  rw [hEA, hDB, hvol r hr, hvol ρ hρ] at ht
  have hfirst : r ^ (-2 : ℝ) *
      ((ρ * alpha u z ρ ^ 2) ^ (3/4 : ℝ) * (ρ * beta u Du z ρ ^ 2) ^ (3/4 : ℝ) *
        (r^2) ^ (1/4 : ℝ)) = (ρ/r) ^ (3/2 : ℝ) * alpha u z ρ ^ (3/2 : ℝ) *
          beta u Du z ρ ^ (3/2 : ℝ) := by
    rw [Real.mul_rpow hρ.le (sq_nonneg _), Real.mul_rpow hρ.le (sq_nonneg _),
      ← Real.rpow_natCast (alpha u z ρ) 2, ← Real.rpow_mul ha,
      ← Real.rpow_natCast (beta u Du z ρ) 2, ← Real.rpow_mul hb,
      ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num only [Nat.cast_ofNat, show (2 : ℝ)*(3/4) = 3/2 by norm_num,
      show (2 : ℝ)*(1/4) = 1/2 by norm_num]
    have hρpow : ρ ^ (3/4 : ℝ) * ρ ^ (3/4 : ℝ) = ρ ^ (3/2 : ℝ) := by
      rw [← Real.rpow_add hρ]; norm_num
    have hrpow : r ^ (-2 : ℝ) * r ^ (1/2 : ℝ) = r ^ (-(3/2 : ℝ)) := by
      rw [← Real.rpow_add hr]; norm_num
    calc
      _ = (r ^ (-2 : ℝ) * r ^ (1/2 : ℝ)) *
          (ρ ^ (3/4 : ℝ) * ρ ^ (3/4 : ℝ)) * alpha u z ρ ^ (3/2 : ℝ) *
            beta u Du z ρ ^ (3/2 : ℝ) := by ring
      _ = _ := by
        rw [hrpow, hρpow, Real.div_rpow hρ.le hr.le, Real.rpow_neg hr.le]
        ring
  have hsecond : r ^ (-2 : ℝ) *
      (r^3 * v * (ρ^3 * v) ^ (-(3/2 : ℝ)) * r^2 * (ρ * alpha u z ρ ^ 2) ^ (3/2 : ℝ)) =
        v ^ (-(1/2 : ℝ)) * (r/ρ)^3 * alpha u z ρ ^ 3 := by
    rw [Real.mul_rpow (by positivity) hv.le, Real.mul_rpow hρ.le (sq_nonneg _),
      ← Real.rpow_natCast ρ 3, ← Real.rpow_mul hρ.le,
      ← Real.rpow_natCast (alpha u z ρ) 2, ← Real.rpow_mul ha]
    norm_num only [Nat.cast_ofNat, show (3 : ℝ)*(-(3/2)) = -(9/2) by norm_num,
      show (2 : ℝ)*(3/2) = 3 by norm_num, Real.rpow_ofNat]
    have hrpow : r ^ (-2 : ℝ) * r^2 = 1 := by
      rw [Real.rpow_neg hr.le, Real.rpow_two, inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]
    have hρpow : ρ ^ (-(9/2 : ℝ)) * ρ ^ (3/2 : ℝ) = (ρ^3)⁻¹ := by
      rw [← Real.rpow_add hρ]
      norm_num only [show (-(9/2 : ℝ)) + 3/2 = -3 by norm_num]
      rw [Real.rpow_neg hρ.le]
      norm_num only [Real.rpow_ofNat]
    have hvpow : v * v ^ (-(3/2 : ℝ)) = v ^ (-(1/2 : ℝ)) := by
      nth_rw 1 [← Real.rpow_one v]
      rw [← Real.rpow_add hv]
      norm_num
    calc
      _ = (r ^ (-2 : ℝ) * r^2) * r^3 * (v * v ^ (-(3/2 : ℝ))) *
          (ρ ^ (-(9/2 : ℝ)) * ρ ^ (3/2 : ℝ)) * alpha u z ρ ^ 3 := by ring
      _ = _ := by rw [hrpow, hvpow, hρpow]; simp only [one_mul, div_eq_mul_inv]; ring
  have hnorm : gamma u z r ^ 3 ≤ K * ((ρ/r) ^ (3/2 : ℝ) *
      alpha u z ρ ^ (3/2 : ℝ) * beta u Du z ρ ^ (3/2 : ℝ) +
      v ^ (-(1/2 : ℝ)) * (r/ρ)^3 * alpha u z ρ ^ 3) := by
    unfold gamma
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num only [Nat.cast_ofNat, show (1/3 : ℝ)*3 = 1 by norm_num, Real.rpow_one]
    have hn := mul_le_mul_of_nonneg_left ht (show 0 ≤ r ^ (-2 : ℝ) by positivity)
    change _ ≤ r ^ (-2 : ℝ) * (K * _) at hn
    rw [mul_left_comm (r ^ (-2 : ℝ)) K, mul_add, hfirst, hsecond] at hn
    exact hn
  have hratio : 1 ≤ ρ/r := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hrρ)
  have hpow : (ρ/r) ^ (3/2 : ℝ) ≤ (ρ/r)^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hratio
      (by norm_num : (3/2 : ℝ) ≤ 3)
  apply hnorm.trans
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hX : 0 ≤ (ρ/r)^3 * alpha u z ρ ^ (3/2 : ℝ) * beta u Du z ρ ^ (3/2 : ℝ) := by positivity
  have hY : 0 ≤ (r/ρ)^3 * alpha u z ρ ^ 3 := by positivity
  calc
    _ ≤ K * ((ρ/r)^3 * alpha u z ρ ^ (3/2 : ℝ) * beta u Du z ρ ^ (3/2 : ℝ) +
        v ^ (-(1/2 : ℝ)) * (r/ρ)^3 * alpha u z ρ ^ 3) := by gcongr
    _ ≤ _ := by
      nlinarith only [mul_nonneg hK hY, mul_nonneg (mul_nonneg hK
        (Real.rpow_nonneg hv.le (-(1/2 : ℝ)))) hX]

end CKN
