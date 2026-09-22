-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbolHeatKernelSplit
import CKN.Core.HeatPotential.GeneralSymbolHeatNearOscillation
import CKN.Core.HeatPotential.GeneralSymbolHeatNear
import CKN.Core.HeatPotential.SubordinatedNear
import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelLocalIntegrable

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

private lemma neg_four_le_of_le_mul {m ρ : ℝ}
    (hm : 0 < m) (hρ : 0 < ρ) (hρm : ρ ≤ 2 * m) :
    m ^ (-4 : ℝ) ≤ 16 * ρ ^ (-4 : ℝ) := by
  rw [Real.rpow_neg hm.le, Real.rpow_neg hρ.le]
  have hp : ρ ^ (4 : ℝ) ≤ (2 * m) ^ (4 : ℝ) := by
    exact Real.rpow_le_rpow hρ.le hρm (by norm_num)
  have hi : ((2 * m) ^ (4 : ℝ))⁻¹ ≤ (ρ ^ (4 : ℝ))⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hp
  calc
    (m ^ (4 : ℝ))⁻¹ = 16 * ((2 * m) ^ (4 : ℝ))⁻¹ := by
      rw [Real.mul_rpow (by norm_num) hm.le]
      norm_num
      field_simp
    _ ≤ 16 * (ρ ^ (4 : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hi (by norm_num)

private lemma rho_le_two_max (x : Vec3) {t : ℝ} (ht : 0 < t) :
    parabolicRho₂ (0, 0) (x, t) ≤
      2 * max (vec3EuclideanNorm x) (Real.sqrt t) := by
  have h := subordinated_parabolicRho₂_le_two_parabolicDist (0, 0) (x, t)
  simpa [parabolicDist, vec3EuclideanNorm_neg, abs_of_pos ht] using h

private lemma multiplier_kernel_riesz_one_bound
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec3, ∀ t : ℝ,
      ‖spatialMultiplierHeatKernel σ x t‖ ≤
        C * parabolicRho₂ (0, 0) (x, t) ^ (-4 : ℝ) := by
  obtain ⟨C, hC, hB⟩ := exists_spatialMultiplierHeatKernel_bounds_of_degreeOne
    σ hσ hhom
  refine ⟨16 * C, by positivity, ?_⟩
  intro x t
  by_cases ht : 0 < t
  · let m : ℝ := max (vec3EuclideanNorm x) (Real.sqrt t)
    let ρ : ℝ := parabolicRho₂ (0, 0) (x, t)
    have hm : 0 < m := by
      dsimp [m]
      exact (Real.sqrt_pos.2 ht).trans_le (le_max_right _ _)
    have hρ : 0 < ρ := by
      dsimp [ρ, parabolicRho₂]
      have hsq : 0 < Real.sqrt |t| := Real.sqrt_pos.2 (abs_pos.mpr ht.ne')
      have hle : Real.sqrt |(0 : ℝ) - t| ≤
          Real.sqrt |(0 : ℝ) - t| + vec3EuclideanNorm ((0 : Vec3) - x) :=
        le_add_of_nonneg_right (vec3EuclideanNorm_nonneg _)
      exact lt_of_lt_of_le (by simpa [abs_neg] using hsq) hle
    have hρm : ρ ≤ 2 * m := by
      exact rho_le_two_max x ht
    have hpow := neg_four_le_of_le_mul hm hρ hρm
    have hbound : ‖spatialMultiplierHeatKernel σ x t‖ ≤ C * m ^ (-4 : ℝ) := by
      simpa [m] using (hB x t ht).2.2.1
    have hbound' : ‖spatialMultiplierHeatKernel σ x t‖ ≤
        (16 * C) * ρ ^ (-4 : ℝ) := by
      calc
        _ ≤ C * m ^ (-4 : ℝ) := hbound
        _ ≤ C * (16 * ρ ^ (-4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow hC
        _ = (16 * C) * ρ ^ (-4 : ℝ) := by ring
    exact hbound'
  · have ht' : t ≤ 0 := le_of_not_gt ht
    rw [spatialMultiplierHeatKernel_of_nonpos σ x ht']
    have hnon : 0 ≤ (16 * C) *
        parabolicRho₂ (0, 0) (x, t) ^ (-4 : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hC)
        (Real.rpow_nonneg (parabolicRho₂_nonneg (0, 0) (x, t)) _)
    simpa using hnon

private lemma multiplier_near_set_subset_riesz_ball
    {z p : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    multiplierHeatNearSet z r ⊆
      {v | parabolicRho₂ p v < 256 * r} := by
  intro v hv
  have hpdist : parabolicDist p z ≤ r := by
    rw [← dist_eq_parabolicDist]
    exact Metric.mem_closedBall.mp hp
  have hvdist : parabolicDist z v < (2 : ℝ) ^ (6 : ℕ) * r := by
    change dist v z < (2 : ℝ) ^ (6 : ℕ) * r at hv
    rw [dist_comm] at hv
    simpa [dist_eq_parabolicDist] using hv
  have hprho : parabolicRho₂ p z ≤ 2 * r := by
    exact (subordinated_parabolicRho₂_le_two_parabolicDist p z).trans
      (mul_le_mul_of_nonneg_left hpdist (by norm_num))
  have hpv : parabolicDist p v ≤ r + (2 : ℝ) ^ (6 : ℕ) * r := by
    rw [← dist_eq_parabolicDist] at hpdist ⊢
    rw [← dist_eq_parabolicDist] at hvdist
    exact (dist_triangle p z v).trans (add_le_add hpdist (le_of_lt hvdist))
  have hquasi : parabolicRho₂ p v ≤ 2 * parabolicDist p v :=
    subordinated_parabolicRho₂_le_two_parabolicDist p v
  calc
    parabolicRho₂ p v ≤ 2 * parabolicDist p v := hquasi
    _ ≤ 2 * (r + (2 : ℝ) ^ (6 : ℕ) * r) :=
      mul_le_mul_of_nonneg_left hpv (by norm_num)
    _ < 256 * r := by norm_num; linarith only [hr]

private lemma multiplier_near_integral_bound
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x : Vec3, ∀ t : ℝ,
      ‖spatialMultiplierHeatKernel σ x t‖ ≤
        C * parabolicRho₂ (0, 0) (x, t) ^ (-4 : ℝ))
    {G : ParabolicPoint → ℝ} {z p : ParabolicPoint} {r P θ : ℝ}
    (hr : 0 < r) (hP : 1 ≤ P) (hPθ : P ≤ θ)
    (hG : AEMeasurable G volume) (hN : morreyNorm P θ G < ∞)
    (hδ : 0 < 1 - 5 / θ)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    IntegrableOn (fun v =>
        ‖spatialMultiplierHeatKernel σ (p.1 - v.1) (p.2 - v.2) * (G v : ℂ)‖)
        (multiplierHeatNearSet z r) volume ∧
      (∫ v in multiplierHeatNearSet z r,
      ‖spatialMultiplierHeatKernel σ (p.1 - v.1) (p.2 - v.2) * (G v : ℂ)‖) ≤
      C *
        ((2 : ℝ) ^ (9 - 5 / θ) *
          (1 - (2 : ℝ) ^ (-(1 - 5 / θ)))⁻¹ * (256 : ℝ) ^ (1 - 5 / θ) *
          (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
          (morreyNorm P θ G).toReal) * r ^ (1 - 5 / θ) := by
  let S : Set ParabolicPoint := multiplierHeatNearSet z r
  let T : Set ParabolicPoint := {v | parabolicRho₂ p v < 256 * r}
  have hST : S ⊆ T := by
    exact multiplier_near_set_subset_riesz_ball hr hp
  have hRiesz := heatPotential_near_riesz_bound (F := G) (z := p)
    (R := 256 * r) (β := (1 : ℝ)) (P := P) (θ := θ) (by positivity)
    hP hPθ (by norm_num) hG hN hδ
  have hzero : volume {v : ParabolicPoint | parabolicRho₂ p v = 0} = 0 := by
    apply measure_mono_null (parabolicRho₂_zero_subset_singleton p)
    rcases p with ⟨x, t⟩
    change (volume : Measure (Vec3 × ℝ)) ({(x, t)} : Set (Vec3 × ℝ)) = 0
    have hset : ({(x, t)} : Set (Vec3 × ℝ)) = {x} ×ˢ {t} := by
      ext w
      rcases w with ⟨y, s⟩
      simp only [mem_singleton_iff, mem_prod]
      constructor
      · intro h
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · rintro ⟨hy, hs⟩
        exact Prod.ext hy hs
    rw [hset]
    change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      ({x} ×ˢ {t}) = 0
    rw [Measure.prod_prod]
    simp
  have hae : ∀ᵐ v : ParabolicPoint ∂volume,
      parabolicRho₂ p v ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hzero
  have hkernel_meas : Measurable
      (fun v : ParabolicPoint =>
        spatialMultiplierHeatKernel σ (p.1 - v.1) (p.2 - v.2)) := by
    change Measurable
      ((fun q : ParabolicPoint =>
        spatialMultiplierHeatKernel σ q.1 q.2) ∘
        (fun v : ParabolicPoint => (p.1 - v.1, p.2 - v.2)))
    exact (measurable_spatialMultiplierHeatKernel hσ hhom).comp
      ((measurable_const.sub measurable_fst).prodMk
        (measurable_const.sub measurable_snd))
  have hpoint : ∀ᵐ v ∂(volume.restrict S),
      ENNReal.ofReal
          |‖spatialMultiplierHeatKernel σ (p.1 - v.1) (p.2 - v.2) *
            (G v : ℂ)‖| ≤
        ENNReal.ofReal C *
          (parabolicRieszKernel 1 p v * ENNReal.ofReal |G v|) := by
    filter_upwards [ae_restrict_of_ae hae] with v hv
    have hρ : 0 < parabolicRho₂ p v :=
      lt_of_le_of_ne (parabolicRho₂_nonneg p v) (Ne.symm hv)
    have hK := hbound (p.1 - v.1) (p.2 - v.2)
    have hρeq : parabolicRho₂ (0, 0) (p.1 - v.1, p.2 - v.2) =
        parabolicRho₂ p v := by
      unfold parabolicRho₂
      simp only [zero_sub]
      rw [abs_neg, vec3EuclideanNorm_neg]
    rw [hρeq] at hK
    have hK' : ENNReal.ofReal
        ‖spatialMultiplierHeatKernel σ (p.1 - v.1) (p.2 - v.2)‖ ≤
        ENNReal.ofReal C * parabolicRieszKernel 1 p v := by
      calc
        _ ≤ ENNReal.ofReal (C * parabolicRho₂ p v ^ (-4 : ℝ)) :=
          ENNReal.ofReal_le_ofReal hK
        _ = ENNReal.ofReal C * parabolicRieszKernel 1 p v := by
          rw [ENNReal.ofReal_mul (by positivity)]
          unfold parabolicRieszKernel
          rw [show -(5 - (1 : ℝ)) = (-4 : ℝ) by norm_num,
            ENNReal.ofReal_rpow_of_pos hρ]
    rw [norm_mul]
    simp only [Complex.norm_real]
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    rw [ENNReal.ofReal_mul (norm_nonneg _)]
    calc
      _ ≤ (ENNReal.ofReal C * parabolicRieszKernel 1 p v) *
          ENNReal.ofReal |G v| :=
        mul_le_mul_of_nonneg_right hK' bot_le
      _ = ENNReal.ofReal C *
          (parabolicRieszKernel 1 p v * ENNReal.ofReal |G v|) := by
        ac_rfl
  let M : ℝ≥0∞ := ENNReal.ofReal C *
      ((ENNReal.ofReal 2) ^ (9 - 5 / θ) *
        (1 - (ENNReal.ofReal 2) ^ (-(1 - 5 / θ)))⁻¹ *
        (ENNReal.ofReal (256 * r)) ^ (1 - 5 / θ) *
        (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
        morreyNorm P θ G)
  have hM : (∫⁻ v in S,
      ENNReal.ofReal
        |‖spatialMultiplierHeatKernel σ (p.1 - v.1) (p.2 - v.2) *
          (G v : ℂ)‖|) ≤ M := by
    calc
      _ ≤ ∫⁻ v in S, ENNReal.ofReal C *
          (parabolicRieszKernel 1 p v * ENNReal.ofReal |G v|) :=
        lintegral_mono_ae hpoint
      _ = ENNReal.ofReal C *
          (∫⁻ v in S, parabolicRieszKernel 1 p v * ENNReal.ofReal |G v|) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal C *
          (∫⁻ v in T, parabolicRieszKernel 1 p v * ENNReal.ofReal |G v|) := by
        gcongr
      _ ≤ M := by
        dsimp [M]
        gcongr
        simpa only [show (10 : ℝ) - 1 - 5 / θ = 9 - 5 / θ by ring] using hRiesz
  have hMtop : M ≠ ∞ := by
    dsimp [M]
    apply ENNReal.mul_ne_top
    · exact ENNReal.ofReal_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · apply ENNReal.mul_ne_top
            · exact ENNReal.rpow_ne_top_of_nonneg (by
                have hθ : 1 ≤ θ := hP.trans hPθ
                have hθinv : 1 / θ ≤ (1 : ℝ) := by
                  simpa using one_div_le_one_div_of_le zero_lt_one hθ
                have hdiv : 5 / θ = 5 * (1 / θ) := by ring
                rw [hdiv]
                linarith only [hθinv]) ENNReal.ofReal_ne_top
            · exact ENNReal.inv_ne_top.mpr (by
                have hq : (ENNReal.ofReal 2) ^ (-(1 - 5 / θ)) < 1 := by
                  rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
                  apply ENNReal.ofReal_lt_one.mpr
                  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
                    (by linarith only [hδ])
                exact (tsub_pos_iff_lt.mpr hq).ne')
          · exact ENNReal.rpow_ne_top_of_nonneg hδ.le ENNReal.ofReal_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg
            (sub_nonneg.mpr (by
              simpa using one_div_le_one_div_of_le zero_lt_one hP))
            Integration.volume_parabolicCylinder_lt_top.ne
      · exact hN.ne
  have hfinite : (∫⁻ v in S,
      ENNReal.ofReal
        |‖spatialMultiplierHeatKernel σ (p.1 - v.1) (p.2 - v.2) *
          (G v : ℂ)‖|) < ∞ := hM.trans_lt (lt_top_iff_ne_top.mpr hMtop)
  have hmeas : AEMeasurable (fun v : ParabolicPoint =>
      ‖spatialMultiplierHeatKernel σ (p.1 - v.1) (p.2 - v.2) *
        (G v : ℂ)‖) volume := by
    have hGcomplex : AEMeasurable (fun v : ParabolicPoint => (G v : ℂ)) volume := by
      exact Complex.measurable_ofReal.comp_aemeasurable hG
    exact (hkernel_meas.aemeasurable.mul hGcomplex).norm
  have hreal := real_integral_abs_le_of_lintegral_le hmeas hfinite hMtop hM
  have hnorm : IntegrableOn (fun v : ParabolicPoint =>
      ‖spatialMultiplierHeatKernel σ (p.1 - v.1) (p.2 - v.2) *
        (G v : ℂ)‖) S volume := by
    simpa only [abs_of_nonneg (norm_nonneg _)] using
      (integrableOn_of_abs_integrable hmeas hfinite)
  have hfactor := heatPotential_near_factor_toReal
    (δ := 1 - 5 / θ) (q := 9 - 5 / θ) (r := r) (b := 1 - 1 / P)
    (N := morreyNorm P θ G) hr hδ
  rw [ENNReal.toReal_mul, hfactor] at hreal
  rw [ENNReal.toReal_ofReal hC] at hreal
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 256) hr.le] at hreal
  exact ⟨by simpa [S] using hnorm,
    by simpa [S, mul_assoc, mul_left_comm, mul_comm] using hreal⟩

private lemma heat_near_scalar_integral_bound
    {F : ParabolicPoint → ℝ} {z p : ParabolicPoint} {r P θ : ℝ}
    (hr : 0 < r) (hP : 1 ≤ P) (hPθ : P ≤ θ)
    (hF : AEMeasurable F volume) (hN : morreyNorm P θ F < ∞)
    (hδ : 0 < 2 - 5 / θ)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    IntegrableOn (fun v => heatPotentialKernel p v * F v)
        (multiplierHeatNearSet z r) volume ∧
      (∫ v in multiplierHeatNearSet z r,
        |heatPotentialKernel p v * F v|) ≤
        1000 * ((2 : ℝ) ^ (8 - 5 / θ) *
          (1 - (2 : ℝ) ^ (-(2 - 5 / θ)))⁻¹ * (256 : ℝ) ^ (2 - 5 / θ) *
          (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
          (morreyNorm P θ F).toReal) * r ^ (2 - 5 / θ) := by
  let S : Set ParabolicPoint := multiplierHeatNearSet z r
  let T : Set ParabolicPoint := {v | parabolicRho₂ p v < 256 * r}
  have hST : S ⊆ T := multiplier_near_set_subset_riesz_ball hr hp
  have hRiesz := heatPotential_near_riesz_bound (F := F) (z := p)
    (R := 256 * r) (β := (2 : ℝ)) (P := P) (θ := θ) (by positivity)
    hP hPθ (by norm_num) hF hN hδ
  have hbound := heatPotential_near_kernel_abs_lintegral_bound
    (p := p) (R := 256 * r) (P := P) (θ := θ) (by positivity)
    hP hPθ hF hN hδ
  have hzero : volume {v : ParabolicPoint | parabolicRho₂ p v = 0} = 0 := by
    apply measure_mono_null (parabolicRho₂_zero_subset_singleton p)
    rcases p with ⟨x, t⟩
    change (volume : Measure (Vec3 × ℝ)) ({(x, t)} : Set (Vec3 × ℝ)) = 0
    have hset : ({(x, t)} : Set (Vec3 × ℝ)) = {x} ×ˢ {t} := by
      ext w
      rcases w with ⟨y, s⟩
      simp only [mem_singleton_iff, mem_prod]
      constructor
      · intro h
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · rintro ⟨hy, hs⟩
        exact Prod.ext hy hs
    rw [hset]
    change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      ({x} ×ˢ {t}) = 0
    rw [Measure.prod_prod]
    simp
  have hae : ∀ᵐ v : ParabolicPoint ∂volume,
      parabolicRho₂ p v ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hzero
  have hpoint : ∀ᵐ v ∂(volume.restrict S),
      ENNReal.ofReal |heatPotentialKernel p v * F v| ≤
        1000 * (parabolicRieszKernel 2 p v * ENNReal.ofReal |F v|) := by
    filter_upwards [ae_restrict_of_ae hae] with v hv
    have hρ : 0 < parabolicRho₂ p v :=
      lt_of_le_of_ne (parabolicRho₂_nonneg p v) (Ne.symm hv)
    have hK := heatPotentialKernel_abs_le_riesz₂ p v
    have htop := heatPotential_riesz_ne_top_of_pos (β := (2 : ℝ)) hρ
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg (heatPotentialKernel p v))]
    have hK' : ENNReal.ofReal |heatPotentialKernel p v| ≤
        1000 * parabolicRieszKernel 2 p v := by
      calc
        ENNReal.ofReal |heatPotentialKernel p v| ≤
            ENNReal.ofReal (1000 * (parabolicRieszKernel 2 p v).toReal) :=
          ENNReal.ofReal_le_ofReal hK
        _ = 1000 * parabolicRieszKernel 2 p v := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1000)]
          rw [ENNReal.ofReal_toReal htop]
          norm_num
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_right hK'
        (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal |F v|))
  let M : ℝ≥0∞ := 1000 *
      ((ENNReal.ofReal 2) ^ (8 - 5 / θ) *
        (1 - (ENNReal.ofReal 2) ^ (-(2 - 5 / θ)))⁻¹ *
        (ENNReal.ofReal (256 * r)) ^ (2 - 5 / θ) *
        (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
        morreyNorm P θ F)
  have hM : (∫⁻ v in S,
      ENNReal.ofReal |heatPotentialKernel p v * F v|) ≤ M := by
    calc
      _ ≤ ∫⁻ v in S, 1000 *
          (parabolicRieszKernel 2 p v * ENNReal.ofReal |F v|) :=
        lintegral_mono_ae hpoint
      _ = 1000 * (∫⁻ v in S,
          parabolicRieszKernel 2 p v * ENNReal.ofReal |F v|) := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 1000 * (∫⁻ v in T,
          parabolicRieszKernel 2 p v * ENNReal.ofReal |F v|) := by
        gcongr
      _ ≤ M := by
        dsimp [M]
        gcongr
        simpa only [show (10 : ℝ) - 2 - 5 / θ = 8 - 5 / θ by ring] using hRiesz
  have hMtop : M ≠ ∞ := by
    dsimp [M]
    exact ENNReal.mul_ne_top (by norm_num)
      (heatPotential_near_factor_ne_top (δ := 2 - 5 / θ)
        (q := 8 - 5 / θ) (r := r) (b := 1 - 1 / P)
        (N := morreyNorm P θ F) hr hδ (by
          have hθ : 1 ≤ θ := hP.trans hPθ
          have hθinv : 1 / θ ≤ (1 : ℝ) := by
            simpa using one_div_le_one_div_of_le zero_lt_one hθ
          have hdiv : 5 / θ = 5 * (1 / θ) := by ring
          rw [hdiv]
          linarith only [hθinv])
        (sub_nonneg.mpr (by
          simpa using one_div_le_one_div_of_le zero_lt_one hP)) hN)
  have hfinite : (∫⁻ v in S,
      ENNReal.ofReal |heatPotentialKernel p v * F v|) < ∞ :=
    hM.trans_lt (lt_top_iff_ne_top.mpr hMtop)
  have hint : IntegrableOn (fun v => heatPotentialKernel p v * F v) S volume :=
    integrableOn_of_abs_integrable
      ((measurable_heatPotentialKernel_translate p).aemeasurable.mul hF) hfinite
  have hreal := real_integral_abs_le_of_lintegral_le
    ((measurable_heatPotentialKernel_translate p).aemeasurable.mul hF)
    hfinite hMtop hM
  have hfactor := heatPotential_near_factor_toReal
    (δ := 2 - 5 / θ) (q := 8 - 5 / θ) (r := r) (b := 1 - 1 / P)
    (N := morreyNorm P θ F) hr hδ
  rw [ENNReal.toReal_mul, hfactor] at hreal
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 256) hr.le] at hreal
  exact ⟨by simpa [S] using hint,
    by simpa [S, mul_assoc, mul_left_comm, mul_comm] using hreal⟩

/-- The near block of the general-symbol heat family has the approved local
Lp and Campanato-size bound. -/
theorem heatNear
    {K : ℕ} {γ θ₀ θ₁ P : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀)
    (σ : Fin K → Vec3 → ℂ) (hσ : ∀ k, SmoothOffOrigin (σ k))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ},
        AEMeasurable F volume → (∀ k, AEMeasurable (G k) volume) →
        morreyNorm P θ₀ F < ∞ → (∀ k, morreyNorm P θ₁ (G k) < ∞) →
        HasCompactSupport F → (∀ k, HasCompactSupport (G k)) →
        ∀ {z : ParabolicPoint} {r : ℝ}, 0 < r →
        ∃ hnear : ParabolicPoint → ℂ,
          LocallyIntegrable hnear volume ∧
          hnear =ᵐ[volume] multiplierHeatPotentialNear σ F G z r ∧
          MemLp hnear (ENNReal.ofReal P)
            (volume.restrict (Metric.closedBall z r)) ∧
          multiplierHeatPairOscillation hnear z r P ≤
            C * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G := by
  have hδ₀ : 0 < 2 - 5 / θ₀ := by
    rw [heat_morrey_theta_zero_identity hθ₀]
    exact hγ
  have hδ₁ : 0 < 1 - 5 / θ₁ := by
    rw [heat_morrey_theta_one_identity hθ₁]
    exact hγ
  have hθ₀pos : 0 < θ₀ := by
    apply one_div_pos.mp
    rw [hθ₀]
    have h : 0 < 2 - γ := by linarith only [hγ1]
    positivity
  have hθ₁pos : 0 < θ₁ := by
    apply one_div_pos.mp
    rw [hθ₁]
    positivity
  have hinv : 1 / θ₁ ≤ 1 / θ₀ := by
    rw [hθ₁, hθ₀]
    gcongr
    linarith only [hγ]
  have hθ₀θ₁ : θ₀ ≤ θ₁ :=
    (one_div_le_one_div hθ₁pos hθ₀pos).mp hinv
  have hPθ₁ : P ≤ θ₁ := hPθ₀.trans hθ₀θ₁
  have hσtop : ∀ k, ∀ n : ℕ,
      ContDiffOn ℝ (n : ℕ∞) (σ k) ({0}ᶜ : Set Vec3) := by
    intro k n
    exact hσ k n
  have hkernelData : ∀ k : Fin K, ∃ Ck : ℝ, 0 ≤ Ck ∧
      ∀ x : Vec3, ∀ t : ℝ,
        ‖spatialMultiplierHeatKernel (σ k) x t‖ ≤
          Ck * parabolicRho₂ (0, 0) (x, t) ^ (-4 : ℝ) := by
    intro k
    exact multiplier_kernel_riesz_one_bound (contDiffOn_infty.2 (hσ k))
      (hhom k)
  choose Ck hCk hKk using hkernelData
  let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
  let AF : ℝ := 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
    (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * V ^ (1 - 1 / P)
  let AG : Fin K → ℝ := fun k => Ck k * (2 : ℝ) ^ (9 - 5 / θ₁) *
    (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * V ^ (1 - 1 / P)
  let C : ℝ := 2 * (AF + ∑ k, AG k)
  have hden : 0 < 1 - (2 : ℝ) ^ (-γ) := by
    have hq : (2 : ℝ) ^ (-γ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ])
    linarith only [hq]
  have hV : 0 ≤ V := by
    dsimp [V]
    exact ENNReal.toReal_nonneg
  have hAF : 0 ≤ AF := by
    dsimp [AF]
    have hden' : 0 ≤ (1 - (2 : ℝ) ^ (-γ))⁻¹ := inv_nonneg.mpr hden.le
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) hden')
        (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg hV _)
  have hAG : ∀ k, 0 ≤ AG k := by
    intro k
    dsimp [AG]
    have hden' : 0 ≤ (1 - (2 : ℝ) ^ (-γ))⁻¹ := inv_nonneg.mpr hden.le
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (hCk k) (Real.rpow_nonneg (by norm_num) _)) hden')
        (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg hV _)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num)
      (add_nonneg hAF (Finset.sum_nonneg fun k _ => hAG k))
  refine ⟨C, hC, ?_⟩
  intro F G hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp z r hr
  let B : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r
  have hB : MeasurableSet B := measurableSet_closedBall
  have hBpos : 0 < volume B := by
    dsimp [B]
    exact parabolicBall_closedBall_pos hr
  have hBtop : volume B < ∞ := by
    dsimp [B]
    exact parabolicBall_closedBall_top hr
  let S : Set ParabolicPoint := multiplierHeatNearSet z r
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hFnearMeas : AEMeasurable (S.indicator F) volume :=
    (aemeasurable_indicator_iff hS).mpr
      (hFmeas.mono_measure Measure.restrict_le_self)
  have hGnearMeas : ∀ k, AEMeasurable (S.indicator (G k)) volume := by
    intro k
    exact (aemeasurable_indicator_iff hS).mpr
      ((hGmeas k).mono_measure Measure.restrict_le_self)
  have hFnearMorrey : morreyNorm P θ₀ (S.indicator F) < ∞ :=
    (morreyNorm_indicator_le hP0 S F).trans_lt hFmorrey
  have hGnearMorrey : ∀ k, morreyNorm P θ₁ (S.indicator (G k)) < ∞ := by
    intro k
    exact (morreyNorm_indicator_le hP0 S (G k)).trans_lt (hGmorrey k)
  have hFnearSupp : HasCompactSupport (S.indicator F) :=
    indicator_hasCompactSupport_of_hasCompactSupport hFsupp
  have hGnearSupp : ∀ k, HasCompactSupport (S.indicator (G k)) := by
    intro k
    exact indicator_hasCompactSupport_of_hasCompactSupport (hGsupp k)
  have hlocal := locallyIntegrable_multiplierHeatPotential_of_morrey
    hP hPθ₀ hPθ₁ hσtop hhom hFnearMeas hGnearMeas hFnearMorrey
    hGnearMorrey hFnearSupp hGnearSupp
  let hnear : ParabolicPoint → ℂ := multiplierHeatPotentialNear σ F G z r
  have hnearLocal : LocallyIntegrable hnear volume := by
    change LocallyIntegrable (multiplierHeatPotential σ
      ((multiplierHeatNearSet z r).indicator F)
      (fun k => (multiplierHeatNearSet z r).indicator (G k))) volume
    exact hlocal
  let NF : ℝ := (morreyNorm P θ₀ F).toReal
  let NG : Fin K → ℝ := fun k => (morreyNorm P θ₁ (G k)).toReal
  have hNF : 0 ≤ NF := by dsimp [NF]; exact ENNReal.toReal_nonneg
  have hNG : ∀ k, 0 ≤ NG k := by
    intro k
    dsimp [NG]
    exact ENNReal.toReal_nonneg
  let H : ℝ := AF * NF * r ^ γ + ∑ k, AG k * NG k * r ^ γ
  have hpoint : ∀ w ∈ B, ‖hnear w‖ ≤ H := by
    intro w hw
    have hF := heat_near_scalar_integral_bound (F := F) (z := z) (p := w)
      hr hP hPθ₀ hFmeas hFmorrey hδ₀ hw
    have hG : ∀ k, IntegrableOn
        (fun v => ‖spatialMultiplierHeatKernel (σ k) (w.1 - v.1)
          (w.2 - v.2) * (G k v : ℂ)‖) S volume ∧
        (∫ v in S, ‖spatialMultiplierHeatKernel (σ k) (w.1 - v.1)
          (w.2 - v.2) * (G k v : ℂ)‖) ≤
          AG k * NG k * r ^ γ := by
      intro k
      have hk := multiplier_near_integral_bound (σ := σ k) (contDiffOn_infty.2 (hσ k))
        (hhom k) (hCk k) (hKk k) hr hP hPθ₁ (hGmeas k) (hGmorrey k) hδ₁ hw
      rw [heat_morrey_theta_one_identity hθ₁] at hk
      refine ⟨?_, ?_⟩
      · simpa [S] using hk.1
      · simpa [AG, NG, V, mul_assoc, mul_left_comm, mul_comm] using hk.2
    have hFbound :
        (∫ v in S, |heatPotentialKernel w v * F v|) ≤ AF * NF * r ^ γ := by
      rw [heat_morrey_theta_zero_identity hθ₀] at hF
      simpa [S, AF, NF, V, mul_assoc, mul_left_comm, mul_comm] using hF.2
    have hFval : ‖∫ v in S,
        (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ)‖ ≤
        AF * NF * r ^ γ := by
      calc
        _ ≤ ∫ v in S, ‖(heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ)‖ :=
          MeasureTheory.norm_integral_le_integral_norm
            (f := fun v => (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ))
            (μ := volume.restrict S)
        _ = ∫ v in S, |heatPotentialKernel w v * F v| := by
          apply integral_congr_ae
          filter_upwards [] with v
          simp [heatPotentialKernel, Complex.norm_real]
        _ ≤ _ := hFbound
    have hGval : ∀ k, ‖∫ v in S,
        spatialMultiplierHeatKernel (σ k) (w.1 - v.1) (w.2 - v.2) *
          (G k v : ℂ)‖ ≤ AG k * NG k * r ^ γ := by
      intro k
      have hnorm := MeasureTheory.norm_integral_le_integral_norm
        (f := fun v => spatialMultiplierHeatKernel (σ k) (w.1 - v.1)
          (w.2 - v.2) * (G k v : ℂ)) (μ := volume.restrict S)
      exact hnorm.trans (hG k).2
    have hFrewrite :
        (∫ v, (heatKernelPlus (pointSub w v) : ℂ) *
          ((S.indicator F v : ℝ) : ℂ)) =
        ∫ v in S, (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ) := by
      rw [← integral_indicator hS]
      apply integral_congr_ae
      filter_upwards [] with v
      by_cases hv : v ∈ S
      · simp [Set.indicator_of_mem hv]
      · simp [Set.indicator_of_notMem hv]
    have hGrewrite : ∀ k,
        (∫ v, spatialMultiplierHeatKernel (σ k) (w.1 - v.1)
          (w.2 - v.2) * ((S.indicator (G k) v : ℝ) : ℂ)) =
        ∫ v in S, spatialMultiplierHeatKernel (σ k) (w.1 - v.1)
          (w.2 - v.2) * (G k v : ℂ) := by
      intro k
      rw [← integral_indicator hS]
      apply integral_congr_ae
      filter_upwards [] with v
      by_cases hv : v ∈ S
      · simp [Set.indicator_of_mem hv]
      · simp [Set.indicator_of_notMem hv]
    change ‖(∫ v, (heatKernelPlus (pointSub w v) : ℂ) *
      ((S.indicator F v : ℝ) : ℂ)) + ∑ k, ∫ v,
        spatialMultiplierHeatKernel (σ k) (w.1 - v.1) (w.2 - v.2) *
          ((S.indicator (G k) v : ℝ) : ℂ)‖ ≤ H
    rw [hFrewrite]
    simp_rw [hGrewrite]
    calc
      _ ≤ ‖∫ v in S, (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ)‖ +
          ‖∑ k, ∫ v in S, spatialMultiplierHeatKernel (σ k)
            (w.1 - v.1) (w.2 - v.2) * (G k v : ℂ)‖ := norm_add_le _ _
      _ ≤ AF * NF * r ^ γ + ∑ k, AG k * NG k * r ^ γ := by
        exact add_le_add hFval
          ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hGval k))
      _ = H := rfl
  have hcoeff : AF * NF + ∑ k, AG k * NG k ≤
      (AF + ∑ k, AG k) * (NF + ∑ k, NG k) := by
    have hAFle : AF ≤ AF + ∑ k, AG k :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hAG k)
    have hAGle : ∀ k, AG k ≤ AF + ∑ j, AG j := by
      intro k
      exact (Finset.single_le_sum (fun j _ => hAG j) (Finset.mem_univ k)).trans
        (le_add_of_nonneg_left hAF)
    calc
      AF * NF + ∑ k, AG k * NG k ≤
          (AF + ∑ k, AG k) * NF +
            ∑ k, (AF + ∑ j, AG j) * NG k := by
        exact add_le_add (mul_le_mul_of_nonneg_right hAFle hNF)
          (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hAGle k) (hNG k))
      _ = (AF + ∑ k, AG k) * (NF + ∑ k, NG k) := by
        rw [mul_add, Finset.mul_sum]
  have hHfinal : H ≤ (AF + ∑ k, AG k) * r ^ γ *
      (NF + ∑ k, NG k) := by
    dsimp [H]
    calc
      AF * NF * r ^ γ + ∑ k, AG k * NG k * r ^ γ =
          (AF * NF + ∑ k, AG k * NG k) * r ^ γ := by
            rw [add_mul]
            congr 1
            rw [Finset.sum_mul]
      _ ≤ ((AF + ∑ k, AG k) * (NF + ∑ k, NG k)) * r ^ γ :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hr.le _)
      _ = (AF + ∑ k, AG k) * r ^ γ * (NF + ∑ k, NG k) := by ring
  have hH : 0 ≤ H := by
    dsimp [H]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hAF hNF) (Real.rpow_nonneg hr.le _))
      (Finset.sum_nonneg fun k _ =>
        mul_nonneg (mul_nonneg (hAG k) (hNG k)) (Real.rpow_nonneg hr.le _))
  let _ : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hBtop⟩
  have hnearAE : AEStronglyMeasurable hnear (volume.restrict B) :=
    hnearLocal.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hpointAE : ∀ᵐ w ∂(volume.restrict B), ‖hnear w‖ ≤ H := by
    filter_upwards [MeasureTheory.ae_restrict_mem hB] with w hw
    exact hpoint w hw
  have hmem : MemLp hnear (ENNReal.ofReal P) (volume.restrict B) := by
    exact MemLp.of_bound hnearAE H hpointAE
  have hosc : multiplierHeatPairOscillation hnear z r P ≤
      C * r ^ γ * (NF + ∑ k, NG k) := by
    unfold multiplierHeatPairOscillation
    have hp : 1 ≤ P := hP
    have hpBound := heat_near_pair_average_rpow_bound hp hB hBpos hBtop hnearAE
      hpointAE hH
    calc
      _ ≤ 2 * H := hpBound
      _ ≤ 2 * ((AF + ∑ k, AG k) * r ^ γ * (NF + ∑ k, NG k)) :=
        mul_le_mul_of_nonneg_left hHfinal (by norm_num)
      _ = C * r ^ γ * (NF + ∑ k, NG k) := by simp [C]; ring
  refine ⟨hnear, hnearLocal, Filter.Eventually.of_forall (fun w => rfl), hmem, ?_⟩
  simpa [multiplierHeatSourceSize, NF, NG] using hosc

end CKN.Core.HeatPotential
