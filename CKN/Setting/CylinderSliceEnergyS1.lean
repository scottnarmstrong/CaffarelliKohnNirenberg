-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.CylinderL3PointwisePaperCore
import CKN.Core.Caccioppoli.CaccioppoliMeanSubtraction
import CKN.Setting.SliceNormBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Inner-ball slice energy from the local data clause

The local data clause supplies the slice weak gradients and the finite local
energy needed by the vector Poincare estimate.  No equation or force data is
used here.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

set_option autoImplicit false

noncomputable section
namespace CKN

private theorem s1_integrable_sq_of_local_energy
    {Ω' : Set Vec3} {J : Set ℝ} {E : Type}
    [NormedAddCommGroup E] {v : ParabolicPoint → E}
    (hv : AEStronglyMeasurable v (volume.restrict (spaceTimeSet Ω' J)))
    (hvlt : (∫⁻ z in spaceTimeSet Ω' J, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hvmeas : AEStronglyMeasurable
      (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict (spaceTimeSet Ω' J)) := hv.norm.pow 2
  have hvfin : ∫⁻ z in spaceTimeSet Ω' J,
      ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ)) ≠ ⊤ := by
    convert ne_of_lt hvlt using 1
    congr 1
    funext z
    calc
      ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ)) =
          ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℝ)) := by
            norm_num [Real.rpow_natCast]
      _ = ENNReal.ofReal ‖v z‖ ^ (2 : ℝ) :=
        (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)).symm
      _ = ‖v z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
  exact (lintegral_ofReal_ne_top_iff_integrable hvmeas
    (Filter.Eventually.of_forall fun z => sq_nonneg _)).mp hvfin

private theorem s1_integrable_sq_of_local_energy_prod
    {Ω' : Set Vec3} {J : Set ℝ} {E : Type}
    [NormedAddCommGroup E] {v : ParabolicPoint → E}
    (hv : AEStronglyMeasurable v (volume.restrict (spaceTimeSet Ω' J)))
    (hvlt : (∫⁻ z in spaceTimeSet Ω' J, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
  rw [Measure.prod_restrict Ω' J]
  exact s1_integrable_sq_of_local_energy hv hvlt

private theorem s1_slice_data_ae
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hdata : AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) ∧
      essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) < ⊤ ∧
      (∫⁻ w in spaceTimeSet Ω' J,
        ‖u w‖ₑ ^ (2 : ℝ) + ‖Du w‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) ∧
      ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i)) :
    ∀ᵐ s ∂volume.restrict J,
      (MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
      ∀ i : Fin 3, HasWeakGradientOn Ω'
        (fun x => u (x, s) i) (fun x => Du (x, s) i) := by
  rcases hdata with ⟨hu, hDu, hp, hess, henergy, hpMem, hgrad⟩
  have hu_lt : (∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono (fun z => le_add_right le_rfl)) henergy
  have hDu_lt : (∫⁻ z in spaceTimeSet Ω' J, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono (fun z => le_add_left le_rfl)) henergy
  have hu_sq := s1_integrable_sq_of_local_energy_prod hu hu_lt
  have hDu_sq := s1_integrable_sq_of_local_energy_prod hDu hDu_lt
  have hu_prod : AEStronglyMeasurable u
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hu
  have hDu_prod : AEStronglyMeasurable Du
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hDu
  have hu_slice : ∀ᵐ s ∂volume.restrict J,
      AEStronglyMeasurable (fun x : Vec3 => u (x, s)) (volume.restrict Ω') :=
    hu_prod.prodMk_right
  have hDu_slice : ∀ᵐ s ∂volume.restrict J,
      AEStronglyMeasurable (fun x : Vec3 => Du (x, s)) (volume.restrict Ω') :=
    hDu_prod.prodMk_right
  have hu_sq_slice : ∀ᵐ s ∂volume.restrict J,
      Integrable (fun x : Vec3 => (‖u (x, s)‖ : ℝ) ^ (2 : ℕ))
        (volume.restrict Ω') := hu_sq.prod_left_ae
  have hDu_sq_slice : ∀ᵐ s ∂volume.restrict J,
      Integrable (fun x : Vec3 => (‖Du (x, s)‖ : ℝ) ^ (2 : ℕ))
        (volume.restrict Ω') := hDu_sq.prod_left_ae
  have hgrad_all : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i) := by
    rw [ae_all_iff]
    intro i
    exact hgrad i
  filter_upwards [hu_slice, hDu_slice, hu_sq_slice, hDu_sq_slice, hgrad_all]
    with s hu_meas hDu_meas hu_sq_s hDu_sq_s hgrad_s
  exact ⟨⟨(memLp_two_iff_integrable_sq_norm hu_meas).2 hu_sq_s,
    (memLp_two_iff_integrable_sq_norm hDu_meas).2 hDu_sq_s⟩, hgrad_s⟩

private theorem s1_energy_split {x : Vec3} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≤ ρ) {E : Vec3 → ℝ}
    (hE : MemLp E (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x ρ))) :
    (∫ y in vec3Ball x r, E y) ≤
      (∫ y in vec3Ball x ρ, |E y - ⨍ w in vec3Ball x ρ, E w| ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) * ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ) +
        (r / ρ) ^ 3 * ∫ y in vec3Ball x ρ, E y := by
  let B := vec3Ball x ρ
  let b := vec3Ball x r
  let c := ⨍ y in B, E y
  have hsub : b ⊆ B := vec3Ball_mono hrρ
  have : IsFiniteMeasure (volume.restrict B) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (volume_vec3Ball_lt_top (x := x) (r := ρ))⟩
  have : IsFiniteMeasure (volume.restrict b) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (volume_vec3Ball_lt_top (x := x) (r := r))⟩
  have hEi : IntegrableOn E B volume := hE.integrable (by norm_num)
  have hEc := hE.sub (memLp_const c)
  have hEci : IntegrableOn (fun y => E y - c) B volume := hEc.integrable (by norm_num)
  have hsplit : (∫ y in b, E y) = (∫ y in b, E y - c) + volume.real b * c := by
    rw [integral_sub (hEi.mono_set hsub) (integrable_const c), integral_const]
    simp only [smul_eq_mul, Measure.restrict_apply_univ, measureReal_def]
    ring
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict B) (f := fun y => E y - c) (g := fun _ : Vec3 => (1 : ℝ))
    (p := (3 / 2 : ℝ)) (q := 3) (by constructor <;> norm_num)
    hEc (memLp_const 1)
  have hvol (a : ℝ) (ha : 0 < a) :
      volume.real (vec3Ball x a) = a ^ 3 * (Real.pi * 4 / 3) := by
    rw [measureReal_def, volume_vec3Ball_eq, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal (by positivity)]
  have hvolroot : (volume.real B) ^ (1 / 3 : ℝ) =
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ := by
    rw [hvol ρ hρ, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
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
        (Filter.Eventually.of_forall (fun y => abs_nonneg _))
        (Filter.Eventually.of_forall hsub)
  have hh : (∫ y in B, |E y - c|) ≤
      (∫ y in B, |E y - c| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ) := by
    simpa only [Real.norm_eq_abs, abs_one, mul_one, Real.one_rpow, integral_const,
      smul_eq_mul, show (volume.restrict B).real univ = volume.real B by
        simp only [measureReal_def, Measure.restrict_apply_univ],
      show 1 / (3 / 2 : ℝ) = 2 / 3 by norm_num, hvolroot] using hholder
  rw [hsplit, hmean]
  exact add_le_add (hosc.trans hh) le_rfl

private theorem s1_ofReal_vec3Norm_sq_le (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) ≤
      3 * ‖v‖ₑ ^ (2 : ℝ) := by
  have h2n : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2n]
  have hle : vec3EuclideanNorm v ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
    have h := vec3EuclideanNorm_le_sqrt_three_mul_norm v
    have h2 : (vec3EuclideanNorm v) ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (vec3EuclideanNorm_nonneg v) h 2
    simpa [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using h2
  calc
    ENNReal.ofReal (vec3EuclideanNorm v) ^ ((2 : ℕ) : ℝ) =
        ENNReal.ofReal (vec3EuclideanNorm v ^ ((2 : ℕ) : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg v) (by norm_num)
    _ = ENNReal.ofReal (vec3EuclideanNorm v ^ 2) := by
      rw [Real.rpow_natCast]
    _ ≤ ENNReal.ofReal (3 * ‖v‖ ^ 2) := ENNReal.ofReal_le_ofReal hle
    _ = 3 * ‖v‖ₑ ^ ((2 : ℕ) : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        show ENNReal.ofReal (3 : ℝ) = 3 by norm_num,
        show ‖v‖ₑ ^ ((2 : ℕ) : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) from by
          rw [ENNReal.rpow_natCast,
            show ‖v‖ₑ = ENNReal.ofReal ‖v‖ from (ofReal_norm v).symm,
            ← ENNReal.ofReal_pow (norm_nonneg v)] ]

private theorem s1_energy_memLp_of_slice_data
    {Ω' : Set Vec3} {z : ParabolicPoint} {ρ s : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hρ : 0 < ρ) (hball : euclideanBall z.1 ρ ⊆ Ω')
    (hs : (MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
      ∀ i : Fin 3, HasWeakGradientOn Ω'
        (fun x => u (x, s) i) (fun x => Du (x, s) i))
    (henergy : (∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (ρ * alpha u z ρ ^ 2)) :
    MemLp (fun y : Vec3 => vec3EuclideanNorm (u (y, s)) ^ 2)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball z.1 ρ)) := by
  let B := vec3Ball z.1 ρ
  let Ei : ℝ≥0∞ := ∫⁻ y in B,
    ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)
  let Di : ℝ≥0∞ := ∫⁻ y in B, ENNReal.ofReal (spatialGradientSq u Du (y, s))
  have hEiTop : Ei ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt (by simpa only [Ei, B] using henergy)
      ENNReal.ofReal_lt_top)
  have hDiTop : Di ≠ ∞ := by
    apply slice_gradient_lintegral_ne_top hs.1.2
    simpa [B, vec3Ball_eq_euclideanBall_cylL3 hρ] using hball
  have hconst : (81 * ENNReal.ofReal (Real.sqrt 3) *
      Classical.choose interpolationBall_three_finite) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (Classical.choose_spec interpolationBall_three_finite).1
  have hrpow : ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hρ)
      ENNReal.ofReal_ne_top
  have hRhsTop :
      (81 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite) *
          Ei ^ (3 / 4 : ℝ) * Di ^ (3 / 4 : ℝ) +
        (81 * ENNReal.ofReal (Real.sqrt 3) *
          Classical.choose interpolationBall_three_finite) *
          ENNReal.ofReal ρ ^ (-(3 / 2 : ℝ)) * Ei ^ (3 / 2 : ℝ) ≠ ∞ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hconst
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hEiTop))
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hDiTop)
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hconst hrpow)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hEiTop)
  have hL3 := slice_l3_lintegral_bound hρ hball hs
  have hL3top : (∫⁻ y in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (by simpa [Ei, Di, B] using hL3)
      (lt_top_iff_ne_top.mpr hRhsTop)
  have hballSub : vec3Ball z.1 ρ ⊆ Ω' := by
    simpa [vec3Ball_eq_euclideanBall_cylL3 hρ] using hball
  have huBall : MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict B) :=
    hs.1.1.mono_measure (Measure.restrict_mono_set volume hballSub)
  have hmeas : AEStronglyMeasurable
      (fun y : Vec3 => vec3EuclideanNorm (u (y, s)) ^ 2)
      (volume.restrict B) :=
    (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      huBall.aestronglyMeasurable).pow 2
  change eLpNorm _ (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B) < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) hmeas]
  have htop := lt_top_iff_ne_top.mpr hL3top
  have hident : (∫⁻ y in B,
      ‖vec3EuclideanNorm (u (y, s)) ^ 2‖ₑ ^ (3 / 2 : ℝ)) =
      ∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ) := by
    apply lintegral_congr
    intro y
    rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow
      (vec3EuclideanNorm_nonneg _), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (3 / 2 : ℝ)), hident]
  exact htop

theorem slice_inner_ball_energy_bound_of_s1
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hIord : OrdConnected I)
    (hS1 : ∀ (Ω' : Set Vec3) (J : Set ℝ), localBox Ω I Ω' J →
      AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) ∧
      essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) < ⊤ ∧
      (∫⁻ w in spaceTimeSet Ω' J,
        ‖u w‖ₑ ^ (2 : ℝ) + ‖Du w‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) ∧
      ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i))
    {z : ParabolicPoint} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≤ ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∫ y in vec3Ball z.1 r,
        vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ≤
        2 * poincareSobolevL1VectorConstant * ρ ^ (3 / 2 : ℝ) *
            alpha u z ρ *
            (∫ y in vec3Ball z.1 ρ,
              ∑ i, vec3EuclideanNorm (Du (y, s) i) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) +
          r ^ (3 : ℕ) / ρ ^ (2 : ℕ) * alpha u z ρ ^ (2 : ℕ) := by
  let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  obtain ⟨R, hρR, hRΩ⟩ := caccioppoli_poincare_radius hΩ hρ hsub
  let R' : ℝ := (ρ + R) / 2
  have hρR' : ρ < R' := by
    dsimp [R']
    linarith only [hρR]
  have hR'R : R' < R := by
    dsimp [R']
    linarith only [hρR]
  have hR'pos : 0 < R' := by linarith only [hρ, hρR']
  have hclosed : euclideanClosedBall z.1 R' ⊆ Ω := by
    intro x hx
    apply hRΩ
    rw [mem_vec3Ball]
    have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR'pos.le).1 hx
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      hx'.trans_lt hR'R
  let K : Set ParabolicPoint := parabolicHomeomorph ⁻¹'
    (euclideanClosedBall z.1 R' ×ˢ Icc (z.2 - ρ ^ 2) z.2)
  have hKcompact : IsCompact K := by
    exact (parabolicHomeomorph.isCompact_preimage).2
      ((isCompact_euclideanClosedBall z.1 hR'pos.le).prod isCompact_Icc)
  have hKsub : K ⊆ spaceTimeSet Ω I := by
    rintro ⟨x, s⟩ hxs
    have hxs' : x ∈ euclideanClosedBall z.1 R' ∧
        s ∈ Icc (z.2 - ρ ^ 2) z.2 := by
      change (x, s) ∈ euclideanClosedBall z.1 R' ×ˢ Icc (z.2 - ρ ^ 2) z.2 at hxs
      exact hxs
    rcases hxs' with ⟨hx, hs⟩
    refine ⟨hclosed hx, ?_⟩
    have hz : (z.1, s) ∈ closure (parabolicCylinder z.1 z.2 ρ) := by
      rw [closure_parabolicCylinder hρ]
      exact ⟨by simp [vec3EuclideanNorm_zero, hρ.le], hs⟩
    exact (hsub hz).2
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    caccioppoli_localBox_of_compact_subset hΩ hI hIord hKcompact hKsub
  have hballR' : ∀ x ∈ vec3Ball z.1 R', x ∈ Ω' := by
    intro x hx
    have hx' : x ∈ euclideanClosedBall z.1 R' := by
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR'pos.le).2
      have hxe := mem_vec3Ball.mp hx
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hxe.le
    have hm : (x, z.2) ∈ K := by
      change parabolicHomeomorph (x, z.2) ∈
        euclideanClosedBall z.1 R' ×ˢ Icc (z.2 - ρ ^ 2) z.2
      change x ∈ euclideanClosedBall z.1 R' ∧
        z.2 ∈ Icc (z.2 - ρ ^ 2) z.2
      exact ⟨hx', ⟨sub_le_self _ (sq_nonneg ρ), le_rfl⟩⟩
    exact (hKbox hm).1
  have hT : Tρ ⊆ J := by
    intro s hs
    have hx : z.1 ∈ euclideanClosedBall z.1 R' := by
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR'pos.le).2
      simpa [vecEuclideanNorm, vecNormSq, vecDot] using hR'pos.le
    have hm : (z.1, s) ∈ K := by
      change parabolicHomeomorph (z.1, s) ∈
        euclideanClosedBall z.1 R' ×ˢ Icc (z.2 - ρ ^ 2) z.2
      change z.1 ∈ euclideanClosedBall z.1 R' ∧
        s ∈ Icc (z.2 - ρ ^ 2) z.2
      exact ⟨hx, ⟨le_of_lt hs.1, hs.2⟩⟩
    exact (hKbox hm).2
  have hlocal := hS1 Ω' J hbox
  have hslicesJ := s1_slice_data_ae hlocal
  have hslices : ∀ᵐ s ∂volume.restrict Tρ,
      (MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
      ∀ i : Fin 3, HasWeakGradientOn Ω'
        (fun x => u (x, s) i) (fun x => Du (x, s) i) :=
    ae_restrict_of_ae_restrict_of_subset hT hslicesJ
  have hball : euclideanBall z.1 ρ ⊆ Ω' := by
    intro x hx
    apply hballR'
    have hxv : x ∈ vec3Ball z.1 ρ := by
      rw [vec3Ball_eq_euclideanBall_cylL3 hρ]
      exact hx
    exact vec3Ball_mono (le_of_lt hρR') hxv
  have hpoincare : ∀ᵐ s ∂volume.restrict Tρ,
      (∫ x in vec3Ball z.1 ρ,
        |vec3EuclideanNorm (u (x, s)) ^ 2 -
          ⨍ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ 2| ^
            (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        poincareSobolevL1VectorConstant *
          (∫ x in vec3Ball z.1 ρ,
            vec3EuclideanNorm (u (x, s)) ^ 2) ^ (1 / 2 : ℝ) *
          (∫ x in vec3Ball z.1 ρ, spatialGradientSq u Du (x, s)) ^
            (1 / 2 : ℝ) := by
    filter_upwards [hslices] with s hs
    have hp := poincareSobolevL1_vec3_slice_euclidean
      (U := Ω') hbox.1 hρ hρR' (fun x hx => hballR' x hx)
      (fun x => u (x, s)) (fun x => Du (x, s))
      (fun i => hs.1.1.eval i) (fun i => hs.1.2.eval i) hs.2
    simpa [spatialGradientSq] using hp
  have henergy : ∀ᵐ s ∂volume.restrict Tρ,
      (∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
          ENNReal.ofReal (ρ * alpha u z ρ ^ 2) := by
    have hballV : vec3Ball z.1 ρ ⊆ Ω' := by
      simpa [vec3Ball_eq_euclideanBall_cylL3 hρ] using hball
    have hess : essSup
        (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) < ⊤ := hlocal.2.2.2.1
    have hessPoint : ∀ s,
        timeSliceBallEnergy z.1 ρ s (fun w => vec3EuclideanNorm (u w)) ≤
          3 * ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ) := by
      intro s
      unfold timeSliceBallEnergy
      calc
        ∫⁻ y in vec3Ball z.1 ρ,
            ‖vec3EuclideanNorm (u (y, s))‖ₑ ^ (2 : ℝ) =
          ∫⁻ y in vec3Ball z.1 ρ,
            ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) :=
          lintegral_congr (fun y => by
            rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)])
        _ ≤ ∫⁻ y in vec3Ball z.1 ρ,
            3 * ‖u (y, s)‖ₑ ^ (2 : ℝ) :=
          lintegral_mono (fun y => by
            exact s1_ofReal_vec3Norm_sq_le (u (y, s)))
        _ = 3 * ∫⁻ y in vec3Ball z.1 ρ, ‖u (y, s)‖ₑ ^ (2 : ℝ) :=
          lintegral_const_mul' 3 _ (by norm_num)
        _ ≤ 3 * ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hballV) (by positivity)
    have hmono := essSup_mono_measure_and_ae
      (μ := volume.restrict Tρ) (ν := volume.restrict J)
      (Measure.restrict_mono hT le_rfl)
      (Filter.Eventually.of_forall hessPoint)
    rw [ENNReal.essSup_const_mul] at hmono
    have hEssFin : timeSliceEnergyEssSup z.1 z.2 ρ
        (fun w => vec3EuclideanNorm (u w)) < ⊤ := by
      unfold timeSliceEnergyEssSup
      exact lt_of_le_of_lt hmono (ENNReal.mul_lt_top (by norm_num) hess)
    have hEssEq := timeSliceEnergyEssSup_eq_ofReal_alpha_sq u z hρ hEssFin.ne
    have hEssAEMajor := ENNReal.ae_le_essSup (μ := volume.restrict Tρ)
      (fun s => timeSliceBallEnergy z.1 ρ s (fun w => vec3EuclideanNorm (u w)))
    have hEssBound : ∀ᵐ s ∂volume.restrict Tρ,
        timeSliceBallEnergy z.1 ρ s (fun w => vec3EuclideanNorm (u w)) ≤
          ENNReal.ofReal (ρ * alpha u z ρ ^ 2) := by
      filter_upwards [hEssAEMajor] with s hs
      calc
        _ ≤ timeSliceEnergyEssSup z.1 z.2 ρ
            (fun w => vec3EuclideanNorm (u w)) := hs
        _ = _ := hEssEq
    simpa only [timeSliceBallEnergy, Real.enorm_eq_ofReal
      (vec3EuclideanNorm_nonneg _)] using hEssBound
  filter_upwards [hslices, hpoincare, henergy] with s hs hp he
  have hEmem := s1_energy_memLp_of_slice_data hρ hball hs he
  have ha : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have henergyMeas : AEStronglyMeasurable
      (fun y : Vec3 => vec3EuclideanNorm (u (y, s)) ^ 2)
      (volume.restrict (vec3Ball z.1 ρ)) := by
    exact ((continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      ((hs.1.1.mono_measure
        (Measure.restrict_mono_set volume
          (by simpa [vec3Ball_eq_euclideanBall_cylL3 hρ] using hball))).aestronglyMeasurable)).pow 2)
  have hconvert : (∫⁻ y in vec3Ball z.1 ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s)) ^ 2)) =
      ∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) := by
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _),
      ← ENNReal.rpow_natCast, ENNReal.rpow_two]
    norm_num
  have henergyReal : (∫ y in vec3Ball z.1 ρ,
      vec3EuclideanNorm (u (y, s)) ^ 2) ≤ ρ * alpha u z ρ ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => sq_nonneg _)) henergyMeas]
    rw [hconvert]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hρ.le (sq_nonneg _)))
  have hroot : (∫ y in vec3Ball z.1 ρ,
      vec3EuclideanNorm (u (y, s)) ^ 2) ^ (1 / 2 : ℝ) ≤
      ρ ^ (1 / 2 : ℝ) * alpha u z ρ := by
    calc
      _ ≤ (ρ * alpha u z ρ ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg (fun y => sq_nonneg _)) henergyReal
          (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow hρ.le (sq_nonneg _), ← Real.rpow_natCast,
          ← Real.rpow_mul ha]
        norm_num
  have hgrad : (∫ y in vec3Ball z.1 ρ, spatialGradientSq u Du (y, s)) =
      ∫ y in vec3Ball z.1 ρ,
        ∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with y
    unfold spatialGradientSq vec3EuclideanNorm
    simp only [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [hgrad] at hp
  have hspl := s1_energy_split hρ hr hrρ hEmem
  have hv : (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) ≤ 2 := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num)
      (by norm_num : (0 : ℝ) < 3)).mp
    rw [← Real.rpow_mul (by positivity)]
    norm_num
    linarith only [Real.pi_lt_four]
  have hC : 0 ≤ poincareSobolevL1VectorConstant := by
    unfold poincareSobolevL1VectorConstant
    positivity
  have hfirst :
      (∫ y in vec3Ball z.1 ρ,
        |vec3EuclideanNorm (u (y, s)) ^ 2 -
          ⨍ w in vec3Ball z.1 ρ, vec3EuclideanNorm (u (w, s)) ^ 2| ^
            (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
          ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ) ≤
      2 * poincareSobolevL1VectorConstant * ρ ^ (3 / 2 : ℝ) *
        alpha u z ρ *
        (∫ y in vec3Ball z.1 ρ,
          ∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2) ^
            (1 / 2 : ℝ) := by
    calc
      _ ≤ (poincareSobolevL1VectorConstant *
          (ρ ^ (1 / 2 : ℝ) * alpha u z ρ) *
          (∫ y in vec3Ball z.1 ρ,
            ∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2) ^
              (1 / 2 : ℝ)) * (2 * ρ) := by
        apply mul_le_mul _ (mul_le_mul_of_nonneg_right hv hρ.le)
          (by positivity) (by positivity)
        exact hp.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot hC) (by positivity))
      _ = _ := by
        have hpow : ρ ^ (1 / 2 : ℝ) * ρ = ρ ^ (3 / 2 : ℝ) := by
          have hh := Real.rpow_add hρ (1 / 2 : ℝ) 1
          norm_num only [Real.rpow_one,
            show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at hh
          exact hh.symm
        calc
          _ = 2 * poincareSobolevL1VectorConstant *
              (ρ ^ (1 / 2 : ℝ) * ρ) * alpha u z ρ *
              (∫ y in vec3Ball z.1 ρ,
                ∑ i : Fin 3, vec3EuclideanNorm (Du (y, s) i) ^ 2) ^
                (1 / 2 : ℝ) := by ring
          _ = _ := by rw [hpow]
  have hsecond : (r / ρ) ^ 3 *
      (∫ y in vec3Ball z.1 ρ, vec3EuclideanNorm (u (y, s)) ^ 2) ≤
      r ^ 3 / ρ ^ 2 * alpha u z ρ ^ 2 := by
    calc
      _ ≤ (r / ρ) ^ 3 * (ρ * alpha u z ρ ^ 2) :=
        mul_le_mul_of_nonneg_left henergyReal (by positivity)
      _ = _ := by field_simp
  exact hspl.trans (add_le_add hfirst hsecond)

end CKN
