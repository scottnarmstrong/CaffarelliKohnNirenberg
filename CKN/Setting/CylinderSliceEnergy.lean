-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Caccioppoli.CaccioppoliMeanSubtraction
import CKN.Setting.SliceNormBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Inner-ball slice energy

Splitting the energy into its mean and oscillation on the outer ball gives
an inner-ball estimate. Spatial Hölder and the vector Poincaré inequality
control the oscillation; the essential slice-energy supremum supplies alpha.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

noncomputable section
namespace CKN

private theorem slice_energy_split {x : Vec3} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≤ ρ) {E : Vec3 → ℝ}
    (hE : MemLp E (ENNReal.ofReal (3/2 : ℝ)) (volume.restrict (vec3Ball x ρ))) :
    (∫ y in vec3Ball x r, E y) ≤
      (∫ y in vec3Ball x ρ, |E y - ⨍ w in vec3Ball x ρ, E w| ^ (3/2 : ℝ)) ^
          (2/3 : ℝ) * ((Real.pi * 4 / 3) ^ (1/3 : ℝ) * ρ) +
        (r / ρ) ^ 3 * ∫ y in vec3Ball x ρ, E y := by
  let B := vec3Ball x ρ
  let b := vec3Ball x r
  let c := ⨍ y in B, E y
  have hsub : b ⊆ B := vec3Ball_mono hrρ
  have : IsFiniteMeasure (volume.restrict B) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (volume_vec3Ball_lt_top (x := x) (r := ρ))⟩
  have : IsFiniteMeasure (volume.restrict b) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (volume_vec3Ball_lt_top (x := x) (r := r))⟩
  have hEi : IntegrableOn E B volume := hE.integrable (by norm_num)
  have hEc := hE.sub (memLp_const c)
  have hEci : IntegrableOn (fun y => E y - c) B volume := hEc.integrable (by norm_num)
  have hsplit : (∫ y in b, E y) = (∫ y in b, E y - c) + volume.real b * c := by
    rw [integral_sub (hEi.mono_set hsub) (integrable_const c), integral_const]
    simp only [smul_eq_mul, Measure.restrict_apply_univ, measureReal_def]
    ring
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict B) (f := fun y => E y - c) (g := fun _ : Vec3 => (1 : ℝ))
    (p := (3/2 : ℝ)) (q := 3) (by constructor <;> norm_num)
    hEc (memLp_const 1)
  have hvol (a : ℝ) (ha : 0 < a) : volume.real (vec3Ball x a) = a ^ 3 * (Real.pi * 4 / 3) := by
    rw [measureReal_def, volume_vec3Ball_eq, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal (by positivity)]
  have hvolroot : (volume.real B) ^ (1/3 : ℝ) = (Real.pi * 4 / 3) ^ (1/3 : ℝ) * ρ := by
    rw [hvol ρ hρ, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hρ.le]
    norm_num
    ring
  have hmean : volume.real b * c = (r / ρ) ^ 3 * ∫ y in B, E y := by
    dsimp [c]
    rw [average_eq, smul_eq_mul]
    simp only [Measure.real, Measure.restrict_apply_univ]
    rw [← measureReal_def, ← measureReal_def, hvol r hr, hvol ρ hρ]
    field_simp [ne_of_gt hρ, Real.pi_ne_zero]
  have hosc : (∫ y in b, E y - c) ≤ ∫ y in B, |E y - c| := by
    calc
      _ ≤ ∫ y in b, |E y - c| := integral_mono
        (hEci.mono_set hsub) ((hEci.mono_set hsub).abs) (fun y => le_abs_self _)
      _ ≤ ∫ y in B, |E y - c| := setIntegral_mono_set hEci.abs
        (Filter.Eventually.of_forall (fun y => abs_nonneg _)) (Filter.Eventually.of_forall hsub)
  have hh : (∫ y in B, |E y - c|) ≤
      (∫ y in B, |E y - c| ^ (3/2 : ℝ)) ^ (2/3 : ℝ) *
        ((Real.pi * 4 / 3) ^ (1/3 : ℝ) * ρ) := by
    simpa only [Real.norm_eq_abs, abs_one, mul_one, Real.one_rpow, integral_const,
      smul_eq_mul, show (volume.restrict B).real univ = volume.real B by
        simp only [measureReal_def, Measure.restrict_apply_univ],
      show 1/(3/2 : ℝ) = 2/3 by norm_num, hvolroot] using hholder
  rw [hsplit, hmean]
  exact add_le_add (hosc.trans hh) le_rfl

private theorem slice_energy_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (t₀-ρ^2) t₀),
      MemLp (fun y => vec3EuclideanNorm (u (y,s)) ^ 2)
        (ENNReal.ofReal (3/2 : ℝ)) (volume.restrict (vec3Ball x₀ ρ)) ∧
      (∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (u (y,s)) ^ 2) ≤
        ρ * alpha u (x₀,t₀) ρ ^ 2 := by
  let B := vec3Ball x₀ ρ
  let T := Ioc (t₀-ρ^2) t₀
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1 hρ hsub
  have hu : AEStronglyMeasurable u (volume.restrict (parabolicCylinder x₀ t₀ ρ)) :=
    ((hsol.2.2.2.2.2.1 Ω' J hbox).1).mono_measure (Measure.restrict_mono_set volume hcyl)
  have huProd : AEStronglyMeasurable u ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    exact hu
  have hn := continuous_vec3EuclideanNorm.comp_aestronglyMeasurable huProd
  have hF := (ENNReal.continuous_ofReal.comp continuous_vec3EuclideanNorm).comp_aestronglyMeasurable hu
  have hFpow : AEMeasurable (fun w : ParabolicPoint =>
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := hF.aemeasurable.pow_const _
  have ht : (∫⁻ s in T, ∫⁻ y in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (y,s))) ^ (3 : ℝ)) < ⊤ := by
    rw [← lintegral_parabolicCylinder hFpow]
    exact lt_top_iff_ne_top.mpr (caccioppoli_velocity_integral_ne_top hsol hρ hsub)
  have htime : AEMeasurable (fun s => ∫⁻ y in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (y,s))) ^ (3 : ℝ)) (volume.restrict T) :=
    ((ENNReal.continuous_ofReal.comp_aestronglyMeasurable hn).aemeasurable.pow_const
      (3 : ℝ)).lintegral_prod_left'
  have hbound := ENNReal.ae_le_essSup (μ := volume.restrict T)
    (fun s => timeSliceBallEnergy x₀ ρ s (fun w => vec3EuclideanNorm (u w)))
  have heq := sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq hsol (x₀,t₀) hρ hsub
  change essSup _ (volume.restrict T) = _ at heq
  rw [heq] at hbound
  filter_upwards [hn.prodMk_right, ae_lt_top' htime ht.ne, hbound] with s hs htop hb
  have hsq : AEStronglyMeasurable (fun y => vec3EuclideanNorm (u (y,s)) ^ 2)
      (volume.restrict B) := hs.pow 2
  have hmem : MemLp (fun y => vec3EuclideanNorm (u (y,s)) ^ 2)
      (ENNReal.ofReal (3/2 : ℝ)) (volume.restrict B) := by
    change eLpNorm _ (ENNReal.ofReal (3/2 : ℝ)) (volume.restrict B) < ⊤
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hsq]
    convert htop using 1
    apply lintegral_congr
    intro y
    rw [ENNReal.toReal_ofReal (by norm_num), Real.enorm_eq_ofReal (sq_nonneg _),
      ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _), ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
  refine ⟨hmem, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun y => sq_nonneg _)) hsq]
  have he : (∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (u (y,s)) ^ 2)) =
      timeSliceBallEnergy x₀ ρ s (fun w => vec3EuclideanNorm (u w)) := by
    unfold timeSliceBallEnergy
    apply lintegral_congr
    intro y
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _),
      ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _), ENNReal.rpow_two]
  rw [he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg hρ.le (sq_nonneg _)))

/-- The inner-ball energy estimate for almost every time of a suitable solution.
The coefficient is the fixed vector Poincaré constant, independent of all data. -/
theorem slice_inner_ball_energy_bound_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≤ ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∫ y in vec3Ball z.1 r, vec3EuclideanNorm (u (y,s)) ^ 2) ≤
        2 * poincareSobolevL1VectorConstant * ρ ^ (3/2 : ℝ) * alpha u z ρ *
          (∫ y in vec3Ball z.1 ρ,
            ∑ i : Fin 3, vec3EuclideanNorm (Du (y,s) i) ^ 2) ^ (1/2 : ℝ) +
        r ^ 3 / ρ ^ 2 * alpha u z ρ ^ 2 := by
  obtain ⟨R, Ω', J, hR, hbox, hball, hT, hpoincare⟩ :=
    caccioppoli_slice_poincare_ae hsol hρ hsub
  have hdata := slice_energy_data hsol hρ hsub
  have hC : 0 ≤ poincareSobolevL1VectorConstant := by
    unfold poincareSobolevL1VectorConstant
    positivity
  have ha : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hv : (Real.pi * 4 / 3) ^ (1/3 : ℝ) ≤ 2 := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0 : ℝ) < 3)).mp
    rw [← Real.rpow_mul (by positivity)]
    norm_num
    linarith only [Real.pi_lt_four]
  filter_upwards [hpoincare, hdata] with s hp hd
  have hroot : (∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y,s)) ^ 2) ^ (1/2 : ℝ) ≤
      ρ ^ (1/2 : ℝ) * alpha u z ρ := by
    calc
      _ ≤ (ρ * alpha u z ρ ^ 2) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg (fun y => sq_nonneg _)) hd.2 (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow hρ.le (sq_nonneg _), ← Real.rpow_natCast, ← Real.rpow_mul ha]
        norm_num
  have hgrad : (∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y,s)) =
      ∫ y in vec3Ball z.1 ρ, ∑ i : Fin 3, vec3EuclideanNorm (Du (y,s) i) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with y
    unfold spatialGradientSq vec3EuclideanNorm
    simp only [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [hgrad] at hp
  have hs := slice_energy_split hρ hr hrρ hd.1
  have hfirst :
      (∫ y in vec3Ball z.1 ρ,
        |vec3EuclideanNorm (u (y,s)) ^ 2 - ⨍ w in vec3Ball z.1 ρ,
          vec3EuclideanNorm (u (w,s)) ^ 2| ^ (3/2 : ℝ)) ^ (2/3 : ℝ) *
          ((Real.pi * 4 / 3) ^ (1/3 : ℝ) * ρ) ≤
      2 * poincareSobolevL1VectorConstant * ρ ^ (3/2 : ℝ) * alpha u z ρ *
        (∫ y in vec3Ball z.1 ρ, ∑ i : Fin 3, vec3EuclideanNorm (Du (y,s) i) ^ 2) ^
          (1/2 : ℝ) := by
    calc
      _ ≤ (poincareSobolevL1VectorConstant *
          (ρ ^ (1/2 : ℝ) * alpha u z ρ) *
          (∫ y in vec3Ball z.1 ρ, ∑ i : Fin 3, vec3EuclideanNorm (Du (y,s) i) ^ 2) ^
            (1/2 : ℝ)) * (2 * ρ) := by
        apply mul_le_mul _ (mul_le_mul_of_nonneg_right hv hρ.le) (by positivity) (by positivity)
        exact hp.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot hC) (by positivity))
      _ = _ := by
        have hpow : ρ ^ (1/2 : ℝ) * ρ = ρ ^ (3/2 : ℝ) := by
          have hh := Real.rpow_add hρ (1/2 : ℝ) 1
          norm_num only [Real.rpow_one, show (1/2 : ℝ) + 1 = 3/2 by norm_num] at hh
          exact hh.symm
        calc
          _ = 2 * poincareSobolevL1VectorConstant * (ρ ^ (1/2 : ℝ) * ρ) * alpha u z ρ *
            (∫ y in vec3Ball z.1 ρ, ∑ i : Fin 3, vec3EuclideanNorm (Du (y,s) i) ^ 2) ^
              (1/2 : ℝ) := by ring
          _ = _ := by rw [hpow]
  have hsecond : (r / ρ) ^ 3 * (∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y,s)) ^ 2) ≤
      r ^ 3 / ρ ^ 2 * alpha u z ρ ^ 2 := by
    calc
      _ ≤ (r / ρ) ^ 3 * (ρ * alpha u z ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hd.2 (by positivity)
      _ = _ := by field_simp
  exact hs.trans (add_le_add hfirst hsecond)

end CKN
