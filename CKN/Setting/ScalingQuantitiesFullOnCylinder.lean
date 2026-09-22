-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.ScalingQuantities
import CKN.Setting.ExcessComparisonCore

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

set_option autoImplicit false
noncomputable section

namespace CKN

/-! # Full scaling identities under cylinder containment

This file exports the ten change-of-variables identities for the scale
quantities. The geometric hypothesis is the open-cylinder containment used by
the source statement; the identities themselves follow from the rescaling
formulas and do not use a closure-containment assumption.
-/

private theorem scaling_rescaleMap_measurableEmbedding (a : ℝ) (ha : 0 < a)
    (x : Vec3) (t : ℝ) :
    MeasurableEmbedding
      (fun z : ParabolicPoint => parabolicTranslate x t (parabolicScale a z)) := by
  have hsp : MeasurableEmbedding (fun y : Vec3 => x + a • y) := by
    have h : (fun y : Vec3 => x + a • y) =
        (fun y : Vec3 => x + y) ∘
          (fun y : Vec3 => (isUnit_iff_ne_zero.2 ha.ne').unit • y) := by
      funext y
      simp [Units.smul_def]
    rw [h]
    exact (Homeomorph.addLeft x).measurableEmbedding.comp
      (Homeomorph.smul (isUnit_iff_ne_zero.2 ha.ne').unit).measurableEmbedding
  have htm : MeasurableEmbedding (fun s : ℝ => t + a ^ 2 * s) := by
    have h : (fun s : ℝ => t + a ^ 2 * s) =
        (fun s : ℝ => t + s) ∘
          (fun s : ℝ => (isUnit_iff_ne_zero.2 (pow_pos ha 2).ne').unit • s) := by
      funext s
      simp [Units.smul_def]
    rw [h]
    exact (Homeomorph.addLeft t).measurableEmbedding.comp
      (Homeomorph.smul (isUnit_iff_ne_zero.2 (pow_pos ha 2).ne').unit).measurableEmbedding
  have h : (fun z : ParabolicPoint => parabolicTranslate x t (parabolicScale a z)) =
      Prod.map (fun y : Vec3 => x + a • y) (fun s : ℝ => t + a ^ 2 * s) := by
    funext z
    rfl
  rw [h]
  exact MeasurableEmbedding.prodMap hsp htm

private theorem scaling_map_rescaleMap (a : ℝ) (ha : 0 < a) (x : Vec3) (t : ℝ) :
    Measure.map (fun z : ParabolicPoint => parabolicTranslate x t (parabolicScale a z))
        (volume : Measure ParabolicPoint) =
      ENNReal.ofReal (a⁻¹ ^ 5) • (volume : Measure ParabolicPoint) := by
  have hsp : Measure.map (fun y : Vec3 => x + a • y) (volume : Measure Vec3) =
      ENNReal.ofReal (a⁻¹ ^ 3) • (volume : Measure Vec3) := by
    have h : (fun y : Vec3 => x + a • y) =
        (fun y : Vec3 => x + y) ∘ (fun y : Vec3 => a • y) := by
      funext y
      simp
    rw [h, ← Measure.map_map (measurable_const_add x) (measurable_const_smul a),
      Measure.map_addHaar_smul (μ := (volume : Measure Vec3)) ha.ne', Measure.map_smul,
      MeasureTheory.map_add_left_eq_self]
    · congr 1
      rw [Module.finrank_fin_fun, abs_of_pos (inv_pos.mpr (pow_pos ha 3)), ← inv_pow]
    · exact (measurable_const_add x).aemeasurable
  have htm : Measure.map (fun s : ℝ => t + a ^ 2 * s) (volume : Measure ℝ) =
      ENNReal.ofReal ((a ^ 2)⁻¹) • (volume : Measure ℝ) := by
    have h : (fun s : ℝ => t + a ^ 2 * s) =
        (fun s : ℝ => t + s) ∘ (fun s : ℝ => a ^ 2 • s) := by
      funext s
      simp [smul_eq_mul]
    rw [h, ← Measure.map_map (measurable_const_add t) (measurable_const_smul (a ^ 2)),
      Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (pow_pos ha 2).ne',
      Measure.map_smul, MeasureTheory.map_add_left_eq_self]
    · congr 1
      rw [Module.finrank_self]
      norm_num
    · exact (measurable_const_add t).aemeasurable
  have hcoef : ENNReal.ofReal (a⁻¹ ^ 3) * ENNReal.ofReal ((a ^ 2)⁻¹) =
      ENNReal.ofReal (a⁻¹ ^ 5) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [inv_pow, inv_pow, mul_comm (a ^ 3)⁻¹, ← mul_inv_rev, ← pow_add]
  have hm1 : Measurable (fun y : Vec3 => x + a • y) := by fun_prop
  have hm2 : Measurable (fun s : ℝ => t + a ^ 2 * s) := by fun_prop
  have hmap := Measure.map_prod_map (volume : Measure Vec3) (volume : Measure ℝ) hm1 hm2
  rw [hsp, htm, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, hcoef] at hmap
  exact hmap.symm

private theorem scaling_cylinder_integral_comp_rescale
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (x : Vec3) (t r : ℝ) (F : ParabolicPoint → E) :
    ∫ z in parabolicCylinder 0 0 r,
      F (parabolicTranslate x t (parabolicScale a z)) =
        a⁻¹ ^ 5 • ∫ z in parabolicCylinder x t (a * r), F z := by
  set e : ParabolicPoint → ParabolicPoint :=
    fun z => parabolicTranslate x t (parabolicScale a z) with he
  have hemb := scaling_rescaleMap_measurableEmbedding a ha x t
  have hmeas : MeasurableSet (parabolicCylinder x t (a * r)) :=
    (vec3Ball_measurable x (a * r)).prod measurableSet_Ioc
  have himg : e '' parabolicCylinder 0 0 r = parabolicCylinder x t (a * r) := by
    rw [he, ← Set.image_image]
    exact parabolicCylinder_rescale_image ha x t r
  have hpre : e ⁻¹' parabolicCylinder x t (a * r) = parabolicCylinder 0 0 r := by
    rw [← himg, Set.preimage_image_eq _ hemb.injective]
  have hmap : Measure.map e (volume.restrict (parabolicCylinder 0 0 r)) =
      ENNReal.ofReal (a⁻¹ ^ 5) • volume.restrict (parabolicCylinder x t (a * r)) := by
    have h := Measure.restrict_map (μ := (volume : Measure ParabolicPoint))
      hemb.measurable hmeas
    rw [scaling_map_rescaleMap a ha x t, Measure.restrict_smul, hpre] at h
    exact h.symm
  calc
    ∫ z in parabolicCylinder 0 0 r,
        F (parabolicTranslate x t (parabolicScale a z)) =
        ∫ z, F (e z) ∂volume.restrict (parabolicCylinder 0 0 r) := rfl
    _ = ∫ w, F w ∂Measure.map e (volume.restrict (parabolicCylinder 0 0 r)) :=
      (hemb.integral_map F).symm
    _ = ∫ w, F w ∂(ENNReal.ofReal (a⁻¹ ^ 5) •
          volume.restrict (parabolicCylinder x t (a * r))) := by rw [hmap]
    _ = a⁻¹ ^ 5 • ∫ w in parabolicCylinder x t (a * r), F w := by
      rw [integral_smul_measure,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ a⁻¹ ^ 5)]

private theorem scaling_toReal_volume_parabolicCylinder
    (x : Vec3) (t r : ℝ) (hr : 0 ≤ r) :
    (volume (parabolicCylinder x t r)).toReal = Real.pi * 4 / 3 * r ^ 5 := by
  rw [volume_parabolicCylinder, volume_vec3Ball_eq, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  ring

private theorem scaling_toReal_volume_vec3Ball (x : Vec3) (r : ℝ) (hr : 0 ≤ r) :
    (volume (vec3Ball x r)).toReal = Real.pi * 4 / 3 * r ^ 3 := by
  rw [volume_vec3Ball_eq, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  ring

private theorem scaling_cylinder_setAverage_comp_rescale
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ}
    (ha : 0 < a) (x : Vec3) (t r : ℝ) (hr : 0 < r) (F : ParabolicPoint → E) :
    ⨍ z in parabolicCylinder 0 0 r,
      F (parabolicTranslate x t (parabolicScale a z)) =
        ⨍ z in parabolicCylinder x t (a * r), F z := by
  rw [setAverage_eq_toReal_inv_smul, setAverage_eq_toReal_inv_smul,
    scaling_cylinder_integral_comp_rescale ha x t r F, smul_smul,
    scaling_toReal_volume_parabolicCylinder _ _ _ hr.le,
    scaling_toReal_volume_parabolicCylinder _ _ _
      (by positivity : (0 : ℝ) ≤ a * r)]
  congr 1
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

private theorem scaling_ball_setAverage_comp_rescale {a : ℝ} (ha : 0 < a)
    (x : Vec3) (r : ℝ) (hr : 0 < r) (F : Vec3 → ℝ) :
    ⨍ y in vec3Ball 0 r, F (x + a • y) = ⨍ y in vec3Ball x (a * r), F y := by
  have hbase := timeSlice_setIntegral_comp_parabolicRescale ha x (0 : ℝ) r (0 : ℝ) F
  simp only [parabolicTranslate, parabolicScale, Module.finrank_fin_fun] at hbase
  rw [setAverage_eq_toReal_inv_smul, setAverage_eq_toReal_inv_smul, hbase,
    smul_eq_mul, smul_eq_mul, ← mul_assoc,
    scaling_toReal_volume_vec3Ball _ _ hr.le,
    scaling_toReal_volume_vec3Ball _ _ (by positivity : (0 : ℝ) ≤ a * r)]
  congr 1
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

private theorem scaling_setAverage_const_smul
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set ParabolicPoint) (c : ℝ) (F : ParabolicPoint → E) :
    ⨍ w in s, c • F w = c • ⨍ w in s, F w := by
  rw [setAverage_eq_toReal_inv_smul, setAverage_eq_toReal_inv_smul, integral_smul,
    smul_comm]

private theorem scaling_setAverage_ball_const_mul
    (s : Set Vec3) (c : ℝ) (F : Vec3 → ℝ) :
    ⨍ y in s, c * F y = c * ⨍ y in s, F y := by
  rw [setAverage_eq_toReal_inv_smul, setAverage_eq_toReal_inv_smul,
    integral_const_mul, smul_eq_mul, smul_eq_mul]
  ring

private theorem scaling_cylinderMean_rescaleVelocity (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (u : ParabolicPoint → Vec3) (r : ℝ) (hr : 0 < r) :
    ⨍ w in parabolicCylinder 0 0 r, rescaleVelocity μ z₀ u w =
      μ • ⨍ w in parabolicCylinder z₀.1 z₀.2 (μ * r), u w := by
  have h : ⨍ w in parabolicCylinder 0 0 r, rescaleVelocity μ z₀ u w =
      ⨍ w in parabolicCylinder 0 0 r,
        μ • u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)) := rfl
  rw [h, scaling_setAverage_const_smul,
    scaling_cylinder_setAverage_comp_rescale hμ z₀.1 z₀.2 r hr]

private theorem scaling_tsaiPsi_rescale (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (u : ParabolicPoint → Vec3) (r : ℝ) (hr : 0 < r) :
    tsaiPsi (rescaleVelocity μ z₀ u) ((0 : Vec3), (0 : ℝ)) r =
      tsaiPsi u z₀ (μ * r) := by
  simp only [tsaiPsi]
  rw [scaling_cylinderMean_rescaleVelocity μ hμ z₀ u r hr,
    vec3EuclideanNorm_smul, abs_of_pos hμ]
  ring

private lemma scaling_excess_coeff (μ r J : ℝ) (hμ : μ ≠ 0) (hr : r ≠ 0) :
    r⁻¹ ^ (2 : ℕ) * (μ ^ 3 * (μ⁻¹ ^ 5 * J)) = (μ * r)⁻¹ ^ (2 : ℕ) * J := by
  field_simp

private theorem scaling_tsaiVelocityExcess_rescale (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (u : ParabolicPoint → Vec3) (r : ℝ) (hr : 0 < r) :
    tsaiVelocityExcess (rescaleVelocity μ z₀ u) ((0 : Vec3), (0 : ℝ)) r =
      tsaiVelocityExcess u z₀ (μ * r) := by
  set A : Vec3 := ⨍ w in parabolicCylinder z₀.1 z₀.2 (μ * r), u w with hA
  have hmean := scaling_cylinderMean_rescaleVelocity μ hμ z₀ u r hr
  have hpt : ∀ w : ParabolicPoint,
      vec3EuclideanNorm (rescaleVelocity μ z₀ u w -
          ⨍ y in parabolicCylinder 0 0 r, rescaleVelocity μ z₀ u y) ^ (3 : ℕ) =
        μ ^ 3 * vec3EuclideanNorm
          (u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)) - A) ^ (3 : ℕ) := by
    intro w
    rw [hmean, ← hA]
    have hsub : rescaleVelocity μ z₀ u w - μ • A =
        μ • (u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)) - A) := by
      simp only [rescaleVelocity, smul_sub]
    rw [hsub, vec3EuclideanNorm_smul, abs_of_pos hμ, mul_pow]
  have hint : ∫ w in parabolicCylinder 0 0 r,
      vec3EuclideanNorm (rescaleVelocity μ z₀ u w -
        ⨍ y in parabolicCylinder 0 0 r, rescaleVelocity μ z₀ u y) ^ (3 : ℕ) =
      μ ^ 3 * (μ⁻¹ ^ 5 * ∫ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
          vec3EuclideanNorm (u w - A) ^ (3 : ℕ)) := by
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    have hcov := scaling_cylinder_integral_comp_rescale (E := ℝ) hμ z₀.1 z₀.2 r
      (fun w => vec3EuclideanNorm (u w - A) ^ (3 : ℕ))
    simpa only [smul_eq_mul] using hcov
  simp only [tsaiVelocityExcess]
  rw [hint, ← hA, scaling_excess_coeff μ r _ hμ.ne' hr.ne']

private lemma scaling_rpow_sq_three_halves (μ : ℝ) (hμ : 0 < μ) :
    (μ ^ 2 : ℝ) ^ (3 / 2 : ℝ) = μ ^ 3 := by
  rw [← Real.rpow_natCast μ 2, ← Real.rpow_mul hμ.le]
  norm_num

private theorem scaling_spatialAverage_rescalePressure (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (p : ParabolicPoint → ℝ) (r : ℝ) (hr : 0 < r) (s : ℝ) :
    spatialAverage 0 r s (rescalePressure μ z₀ p) =
      μ ^ 2 * spatialAverage z₀.1 (μ * r) (z₀.2 + μ ^ 2 * s) p := by
  have h : spatialAverage 0 r s (rescalePressure μ z₀ p) =
      ⨍ y in vec3Ball 0 r,
        μ ^ 2 * (fun y : Vec3 => p (y, z₀.2 + μ ^ 2 * s)) (z₀.1 + μ • y) := rfl
  rw [h, scaling_setAverage_ball_const_mul,
    scaling_ball_setAverage_comp_rescale hμ z₀.1 r hr
      (fun y : Vec3 => p (y, z₀.2 + μ ^ 2 * s))]
  rfl

private theorem scaling_tsaiPressureExcess_rescale (μ : ℝ) (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (p : ParabolicPoint → ℝ) (r : ℝ) (hr : 0 < r) :
    tsaiPressureExcess (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) r =
      tsaiPressureExcess p z₀ (μ * r) := by
  have hpt : ∀ w : ParabolicPoint,
      |rescalePressure μ z₀ p w -
          spatialAverage 0 r w.2 (rescalePressure μ z₀ p)| ^ (3 / 2 : ℝ) =
        μ ^ 3 * (fun v : ParabolicPoint =>
            |p v - spatialAverage z₀.1 (μ * r) v.2 p| ^ (3 / 2 : ℝ))
          (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)) := by
    intro w
    rw [scaling_spatialAverage_rescalePressure μ hμ z₀ p r hr w.2]
    have hsub : rescalePressure μ z₀ p w -
        μ ^ 2 * spatialAverage z₀.1 (μ * r) (z₀.2 + μ ^ 2 * w.2) p =
          μ ^ 2 * (p (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)) -
            spatialAverage z₀.1 (μ * r) (z₀.2 + μ ^ 2 * w.2) p) := by
      simp only [rescalePressure]
      ring
    rw [hsub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < μ ^ 2),
      Real.mul_rpow (by positivity) (abs_nonneg _),
      scaling_rpow_sq_three_halves μ hμ]
    rfl
  have hint : ∫ w in parabolicCylinder 0 0 r,
      |rescalePressure μ z₀ p w -
        spatialAverage 0 r w.2 (rescalePressure μ z₀ p)| ^ (3 / 2 : ℝ) =
      μ ^ 3 * (μ⁻¹ ^ 5 * ∫ w in parabolicCylinder z₀.1 z₀.2 (μ * r),
        |p w - spatialAverage z₀.1 (μ * r) w.2 p| ^ (3 / 2 : ℝ)) := by
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    have hcov := scaling_cylinder_integral_comp_rescale (E := ℝ) hμ z₀.1 z₀.2 r
      (fun w : ParabolicPoint =>
        |p w - spatialAverage z₀.1 (μ * r) w.2 p| ^ (3 / 2 : ℝ))
    simpa only [smul_eq_mul] using hcov
  simp only [tsaiPressureExcess]
  rw [hint, scaling_excess_coeff μ r _ hμ.ne' hr.ne']

private theorem scaling_rescaleVelocity_comp (μ : ℝ) (z₀ ζ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) :
    rescaleVelocity 1 ζ (rescaleVelocity μ z₀ u) =
      rescaleVelocity μ
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) u := by
  funext w
  simp [rescaleVelocity, parabolicTranslate, parabolicScale, smul_smul,
    add_assoc, mul_add, smul_add]

private theorem scaling_rescaleGradient_comp (μ : ℝ) (z₀ ζ : ParabolicPoint)
    (Du : ParabolicPoint → Fin 3 → Vec3) :
    rescaleGradient 1 ζ (rescaleGradient μ z₀ Du) =
      rescaleGradient μ
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) Du := by
  funext w i
  simp [rescaleGradient, parabolicTranslate, parabolicScale, smul_smul,
    add_assoc, mul_add, smul_add]

private theorem scaling_rescalePressure_comp (μ : ℝ) (z₀ ζ : ParabolicPoint)
    (p : ParabolicPoint → ℝ) :
    rescalePressure 1 ζ (rescalePressure μ z₀ p) =
      rescalePressure μ
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) p := by
  funext w
  simp [rescalePressure, parabolicTranslate, parabolicScale, add_assoc, mul_add]

private theorem scaling_rescaleForce_comp (μ : ℝ) (z₀ ζ : ParabolicPoint)
    (f : ParabolicPoint → Vec3) :
    rescaleForce 1 ζ (rescaleForce μ z₀ f) =
      rescaleForce μ
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) f := by
  funext w
  simp [rescaleForce, parabolicTranslate, parabolicScale, smul_smul,
    add_assoc, mul_add, smul_add]

private theorem scaling_isBoundedUnder_top (E : ℝ → ℝ≥0∞) (l : Filter ℝ) :
    Filter.IsBoundedUnder (· ≤ ·) l E :=
  ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩

private theorem scaling_alpha_rescale_center (μ : ℝ) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (u : ParabolicPoint → Vec3) (r : ℝ) :
    alpha (rescaleVelocity μ z₀ u) ζ r =
      alpha u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  have h := alpha_rescale 1 one_pos ζ (rescaleVelocity μ z₀ u) r
    (scaling_isBoundedUnder_top _ _) (scaling_isBoundedUnder_top _ _)
  rw [one_mul] at h
  rw [← h, scaling_rescaleVelocity_comp,
    alpha_rescale μ hμ _ u r (scaling_isBoundedUnder_top _ _)
      (scaling_isBoundedUnder_top _ _)]

private theorem scaling_beta_rescale_center (μ : ℝ) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (r : ℝ) :
    beta (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du) ζ r =
      beta u Du (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  have h := beta_rescale 1 one_pos ζ (rescaleVelocity μ z₀ u)
    (rescaleGradient μ z₀ Du) r
  rw [one_mul] at h
  rw [← h, scaling_rescaleVelocity_comp, scaling_rescaleGradient_comp,
    beta_rescale μ hμ _ u Du r]

private theorem scaling_gamma_rescale_center (μ : ℝ) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (u : ParabolicPoint → Vec3) (r : ℝ) (hr : 0 < r) :
    gamma (rescaleVelocity μ z₀ u) ζ r =
      gamma u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  have h := gamma_rescale 1 one_pos ζ (rescaleVelocity μ z₀ u) r hr
  rw [one_mul] at h
  rw [← h, scaling_rescaleVelocity_comp, gamma_rescale μ hμ _ u r hr]

private theorem scaling_delta_rescale_center (μ : ℝ) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (p : ParabolicPoint → ℝ) (r : ℝ) (hr : 0 < r) :
    delta (rescalePressure μ z₀ p) ζ r =
      delta p (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  have h := delta_rescale 1 one_pos ζ (rescalePressure μ z₀ p) r hr
  rw [one_mul] at h
  rw [← h, scaling_rescalePressure_comp, delta_rescale μ hμ _ p r hr]

private theorem scaling_lambda_rescale_center (q μ : ℝ) (hq : 0 < q) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (f : ParabolicPoint → Vec3) (r : ℝ) (hr : 0 < r) :
    lambda q (rescaleForce μ z₀ f) ζ r =
      lambda q f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  have h := lambda_rescale q 1 hq one_pos ζ (rescaleForce μ z₀ f) r hr
  rw [one_mul] at h
  rw [← h, scaling_rescaleForce_comp, lambda_rescale q μ hq hμ _ f r hr]

private theorem scaling_theta_rescale_center (κ μ : ℝ) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (r : ℝ) (hr : 0 < r) :
    theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
        (rescalePressure μ z₀ p) ζ r =
      theta κ u Du p
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  simp only [theta]
  rw [scaling_alpha_rescale_center μ hμ z₀ ζ u r,
    scaling_beta_rescale_center μ hμ z₀ ζ u Du r,
    scaling_delta_rescale_center μ hμ z₀ ζ p r hr]

private theorem scaling_tsaiVelocityExcess_rescale_center (μ : ℝ) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (u : ParabolicPoint → Vec3) (r : ℝ) (hr : 0 < r) :
    tsaiVelocityExcess (rescaleVelocity μ z₀ u) ζ r =
      tsaiVelocityExcess u
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  have h := scaling_tsaiVelocityExcess_rescale 1 one_pos ζ (rescaleVelocity μ z₀ u) r hr
  rw [one_mul] at h
  rw [← h, scaling_rescaleVelocity_comp,
    scaling_tsaiVelocityExcess_rescale μ hμ _ u r hr]

private theorem scaling_tsaiPressureExcess_rescale_center (μ : ℝ) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (p : ParabolicPoint → ℝ) (r : ℝ) (hr : 0 < r) :
    tsaiPressureExcess (rescalePressure μ z₀ p) ζ r =
      tsaiPressureExcess p
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  have h := scaling_tsaiPressureExcess_rescale 1 one_pos ζ (rescalePressure μ z₀ p) r hr
  rw [one_mul] at h
  rw [← h, scaling_rescalePressure_comp,
    scaling_tsaiPressureExcess_rescale μ hμ _ p r hr]

private theorem scaling_tsaiPhi_rescale_center (μ : ℝ) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (r : ℝ) (hr : 0 < r) :
    tsaiPhi (rescaleVelocity μ z₀ u) (rescalePressure μ z₀ p) ζ r =
      tsaiPhi u p
        (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  simp only [tsaiPhi]
  rw [scaling_tsaiVelocityExcess_rescale_center μ hμ z₀ ζ u r hr,
    scaling_tsaiPressureExcess_rescale_center μ hμ z₀ ζ p r hr]

private theorem scaling_tsaiPsi_rescale_center (μ : ℝ) (hμ : 0 < μ)
    (z₀ ζ : ParabolicPoint) (u : ParabolicPoint → Vec3) (r : ℝ) (hr : 0 < r) :
    tsaiPsi (rescaleVelocity μ z₀ u) ζ r =
      tsaiPsi u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)) (μ * r) := by
  have h := scaling_tsaiPsi_rescale 1 one_pos ζ (rescaleVelocity μ z₀ u) r hr
  rw [one_mul] at h
  rw [← h, scaling_rescaleVelocity_comp, scaling_tsaiPsi_rescale μ hμ _ u r hr]

/-- The full scale-quantity identities under containment of the open rescaled
parabolic cylinder. -/
theorem scaling_quantities_full_on_cylinder_source :
∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (_hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (μ : ℝ) (_hμ : 0 < μ) (z₀ ζ : ParabolicPoint) (r κ : ℝ) (_hr : 0 < r)
    (__hdom : parabolicCylinder
      (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)).1
      (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)).2 (μ*r) ⊆ spaceTimeSet Ω I),
    let z := parabolicTranslate z₀.1 z₀.2 (parabolicScale μ ζ)
    alpha (rescaleVelocity μ z₀ u) ζ r = alpha u z (μ*r) ∧
    beta (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du) ζ r = beta u Du z (μ*r) ∧
    gamma (rescaleVelocity μ z₀ u) ζ r = gamma u z (μ*r) ∧
    delta (rescalePressure μ z₀ p) ζ r = delta p z (μ*r) ∧
    lambda q (rescaleForce μ z₀ f) ζ r = lambda q f z (μ*r) ∧
    theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du) (rescalePressure μ z₀ p) ζ r =
      theta κ u Du p z (μ*r) ∧
    tsaiVelocityExcess (rescaleVelocity μ z₀ u) ζ r = tsaiVelocityExcess u z (μ*r) ∧
    tsaiPressureExcess (rescalePressure μ z₀ p) ζ r = tsaiPressureExcess p z (μ*r) ∧
    tsaiPhi (rescaleVelocity μ z₀ u) (rescalePressure μ z₀ p) ζ r = tsaiPhi u p z (μ*r) ∧
    tsaiPsi (rescaleVelocity μ z₀ u) ζ r = tsaiPsi u z (μ*r) := by
  intro Ω I q u Du p f hsol μ hμ z₀ ζ r κ hr hdom z
  have hq : (0 : ℝ) < q := lt_trans (by norm_num) hsol.2.2.2.1
  exact ⟨scaling_alpha_rescale_center μ hμ z₀ ζ u r,
    scaling_beta_rescale_center μ hμ z₀ ζ u Du r,
    scaling_gamma_rescale_center μ hμ z₀ ζ u r hr,
    scaling_delta_rescale_center μ hμ z₀ ζ p r hr,
    scaling_lambda_rescale_center q μ hq hμ z₀ ζ f r hr,
    scaling_theta_rescale_center κ μ hμ z₀ ζ u Du p r hr,
    scaling_tsaiVelocityExcess_rescale_center μ hμ z₀ ζ u r hr,
    scaling_tsaiPressureExcess_rescale_center μ hμ z₀ ζ p r hr,
    scaling_tsaiPhi_rescale_center μ hμ z₀ ζ u p r hr,
    scaling_tsaiPsi_rescale_center μ hμ z₀ ζ u r hr⟩

end CKN
end
