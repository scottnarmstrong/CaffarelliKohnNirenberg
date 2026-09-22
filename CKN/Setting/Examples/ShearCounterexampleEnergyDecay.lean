-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.


import CKN.Setting.Examples.ShearCounterexample
import CKN.Setting.Examples.ShearCounterexampleCoordinateEnergy
import CKN.Setting.Examples.ShearCounterexample.ScaleSeries
import CKN.Statements.SpatialGradientSq
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Small-scale decay of the normalized rough-shear gradient energy. -/


set_option autoImplicit false
noncomputable section

open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CKN

private theorem shearWeight_nonneg_energy (n : ℕ) : 0 ≤ shearWeight n := by
  unfold shearWeight
  positivity

private theorem shearWeight_le_one_energy (n : ℕ) : shearWeight n ≤ 1 := by
  have hn : 1 ≤ (n + 1 : ℝ) := by
    exact_mod_cast (Nat.le_add_left 1 n)
  have hp : 1 ≤ (n + 1 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow hn (by norm_num)
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
  simpa [shearWeight] using h

private theorem shearScale_summable_energy : Summable shearScale := by
  change Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n)
  exact summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (by norm_num : (1 / 4 : ℝ) < 1)

private theorem shearScale_sum_energy : (∑' n : ℕ, shearScale n) = 4 / 3 := by
  change (∑' n : ℕ, (1 / 4 : ℝ) ^ n) = 4 / 3
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
  norm_num

theorem shearReducedGradientTerm_eLpNorm_bound_energy {i : Fin 2} {n : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (shearReducedGradientTerm i n) 2 volume ≤
        ENNReal.ofReal (8 * C * shearScale n) := by
  obtain ⟨C, hC, hUnit⟩ := shearUnitBump_bound
  refine ⟨C, hC, ?_⟩
  have hr := shearScale_pos n
  have hnorm := shearSpatialFirstField_eLpNorm hr hC hUnit i
  change eLpNorm (shearWeight n • shearSpatialFirstField (shearScale n) i) 2 volume ≤ _
  rw [eLpNorm_const_smul, Real.enorm_of_nonneg (shearWeight_nonneg_energy n)]
  calc
    ENNReal.ofReal (shearWeight n) *
        eLpNorm (shearSpatialFirstField (shearScale n) i) 2 volume ≤
      ENNReal.ofReal (shearWeight n) *
        ENNReal.ofReal (8 * C * shearScale n) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = ENNReal.ofReal (shearWeight n * (8 * C * shearScale n)) :=
      (ENNReal.ofReal_mul (shearWeight_nonneg_energy n)).symm
    _ ≤ ENNReal.ofReal (8 * C * shearScale n) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_of_le_one_left (by positivity) (shearWeight_le_one_energy n)

theorem shearReducedGradientTerm_memLp_energy (i : Fin 2) (n : ℕ) :
    MemLp (shearReducedGradientTerm i n) 2 volume := by
  obtain ⟨C, hC, hbound⟩ := shearReducedGradientTerm_eLpNorm_bound_energy
  rw [memLp_iff]
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

private theorem shearReducedGradientTerm_continuous_energy (i : Fin 2) (n : ℕ) :
    Continuous (shearReducedGradientTerm i n) := by
  unfold shearReducedGradientTerm
  exact continuous_const.mul
    (shearSpatialFirstField_continuous (shearScale_pos n) i)

private theorem shearReducedGradientTerm_energy_integral_le (C : ℝ) (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (i : Fin 2) (n : ℕ) :
    ∫⁻ z : Vec2 × ℝ, ENNReal.ofReal (shearReducedGradientTerm i n z ^ 2) ≤
      ENNReal.ofReal (8 * C * shearScale n) ^ (2 : ℝ) := by
  have hbound : eLpNorm (shearReducedGradientTerm i n) 2 volume ≤
      ENNReal.ofReal (8 * C * shearScale n) := by
    have hr := shearScale_pos n
    have hnorm := shearSpatialFirstField_eLpNorm hr hC hUnit i
    change eLpNorm (shearWeight n • shearSpatialFirstField (shearScale n) i) 2 volume ≤ _
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg (shearWeight_nonneg_energy n)]
    calc
      ENNReal.ofReal (shearWeight n) *
          eLpNorm (shearSpatialFirstField (shearScale n) i) 2 volume ≤
        ENNReal.ofReal (shearWeight n) *
          ENNReal.ofReal (8 * C * shearScale n) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = ENNReal.ofReal (shearWeight n * (8 * C * shearScale n)) :=
        (ENNReal.ofReal_mul (shearWeight_nonneg_energy n)).symm
      _ ≤ ENNReal.ofReal (8 * C * shearScale n) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_of_le_one_left (by positivity) (shearWeight_le_one_energy n)
  have hmeas : AEStronglyMeasurable (shearReducedGradientTerm i n) volume :=
    (shearReducedGradientTerm_continuous_energy i n).measurable.aestronglyMeasurable
  have hnorm' := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hmeas
  have hnormEq :
      eLpNorm (shearReducedGradientTerm i n) 2 volume =
        (∫⁻ z : Vec2 × ℝ, ‖shearReducedGradientTerm i n z‖ₑ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
    simpa only [show (2 : ℝ≥0∞).toReal = 2 by norm_num] using hnorm'
  have hroot :
      (∫⁻ z : Vec2 × ℝ, ‖shearReducedGradientTerm i n z‖ₑ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) ≤ ENNReal.ofReal (8 * C * shearScale n) := by
    rw [← hnormEq]
    exact hbound
  have henergyEq :
      (∫⁻ z : Vec2 × ℝ, ENNReal.ofReal (shearReducedGradientTerm i n z ^ 2)) =
        ∫⁻ z : Vec2 × ℝ, ‖shearReducedGradientTerm i n z‖ₑ ^ (2 : ℝ) := by
    apply lintegral_congr
    intro z
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
    rw [← ofReal_norm]
    rw [← ENNReal.ofReal_pow (norm_nonneg (shearReducedGradientTerm i n z)) 2]
    congr 1
    rw [Real.norm_eq_abs]
    exact (sq_abs _).symm
  have hIle :
      (∫⁻ z : Vec2 × ℝ, ‖shearReducedGradientTerm i n z‖ₑ ^ (2 : ℝ)) ≤
        ENNReal.ofReal (8 * C * shearScale n) ^ (2 : ℝ) := by
    calc
      (∫⁻ z : Vec2 × ℝ, ‖shearReducedGradientTerm i n z‖ₑ ^ (2 : ℝ)) =
          ((∫⁻ z : Vec2 × ℝ, ‖shearReducedGradientTerm i n z‖ₑ ^ (2 : ℝ)) ^
            (1 / 2 : ℝ)) ^ (2 : ℝ) := by
            rw [← ENNReal.rpow_mul]
            norm_num
      _ ≤ ENNReal.ofReal (8 * C * shearScale n) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hroot (by norm_num : 0 ≤ (2 : ℝ))
  exact henergyEq.trans_le hIle


end CKN

namespace CKN

def shearReducedGradientTailEnergy (i : Fin 2) (N : ℕ) (z : Vec2 × ℝ) : ℝ≥0∞ :=
  ∑' n, if N ≤ n then
    ENNReal.ofReal (shearReducedGradientTerm i n z ^ 2) else 0

private theorem shearReducedGradientTailEnergy_aemeasurable (i : Fin 2) (N : ℕ) :
    ∀ n, AEMeasurable (fun z : Vec2 × ℝ =>
      if N ≤ n then ENNReal.ofReal (shearReducedGradientTerm i n z ^ 2) else 0)
      volume := by
  intro n
  by_cases hn : N ≤ n
  · simp only [hn, ↓reduceIte]
    exact (ENNReal.continuous_ofReal.comp
      ((shearReducedGradientTerm_continuous_energy i n).pow 2)).aemeasurable
  · simp only [hn, ↓reduceIte]
    exact aemeasurable_const

private theorem shearScale_partial_le_energy (k : ℕ) :
    ∑ n ∈ Finset.range k, shearScale n ≤ 4 / 3 := by
  have hsum := (shearScale_summable_energy).sum_le_tsum (Finset.range k)
    (fun n _ => (shearScale_pos n).le)
  rw [shearScale_sum_energy] at hsum
  exact hsum

private theorem shearScale_sum_ofReal_le_energy (K : ℝ) (hK : 0 ≤ K) :
    ∑' n, ENNReal.ofReal (K * shearScale n) ≤ ENNReal.ofReal (K * (4 / 3)) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro k
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · apply ENNReal.ofReal_le_ofReal
    calc
      ∑ n ∈ Finset.range k, K * shearScale n =
          K * ∑ n ∈ Finset.range k, shearScale n := by
            rw [Finset.mul_sum]
      _ ≤ K * (4 / 3) := mul_le_mul_of_nonneg_left
        (shearScale_partial_le_energy k) hK
  · intro n hn
    exact mul_nonneg hK (shearScale_pos n).le

private theorem shearReducedGradientTerm_energy_integral_le_tail
    {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (i : Fin 2) (N n : ℕ)
    (hNn : N ≤ n) :
    ∫⁻ z : Vec2 × ℝ, ENNReal.ofReal (shearReducedGradientTerm i n z ^ 2) ≤
      ENNReal.ofReal (64 * C ^ 2 * shearScale N * shearScale n) := by
  have hterm := shearReducedGradientTerm_energy_integral_le C hC hUnit i n
  have hscale : shearScale n ≤ shearScale N := shearScale_antitone hNn
  have hsN : 0 ≤ shearScale N := (shearScale_pos N).le
  have hsn : 0 ≤ shearScale n := (shearScale_pos n).le
  have hreal : (8 * C * shearScale n) ^ 2 ≤
      64 * C ^ 2 * shearScale N * shearScale n := by
    calc
      (8 * C * shearScale n) ^ 2 = 64 * C ^ 2 * shearScale n ^ 2 := by ring
      _ ≤ 64 * C ^ 2 * (shearScale N * shearScale n) := by
        have hsq : shearScale n ^ 2 ≤ shearScale N * shearScale n := by
          simpa [pow_two] using mul_le_mul_of_nonneg_right hscale hsn
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 64 * C ^ 2 * shearScale N * shearScale n := by ring
  have henorm : ENNReal.ofReal (8 * C * shearScale n) ^ (2 : ℝ) =
      ENNReal.ofReal ((8 * C * shearScale n) ^ 2) := by
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
    rw [← ENNReal.ofReal_pow (by positivity) 2]
  rw [henorm] at hterm
  exact hterm.trans (ENNReal.ofReal_le_ofReal hreal)

theorem shearReducedGradientTailEnergy_integral_le
    {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) (i : Fin 2) (N : ℕ) :
    ∫⁻ z : Vec2 × ℝ, shearReducedGradientTailEnergy i N z ≤
      ENNReal.ofReal ((256 / 3 : ℝ) * C ^ 2 * shearScale N) := by
  unfold shearReducedGradientTailEnergy
  rw [lintegral_tsum (shearReducedGradientTailEnergy_aemeasurable i N)]
  calc
    ∑' n, ∫⁻ z : Vec2 × ℝ,
        (if N ≤ n then ENNReal.ofReal (shearReducedGradientTerm i n z ^ 2)
          else 0) ≤
      ∑' n, ENNReal.ofReal (64 * C ^ 2 * shearScale N * shearScale n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        by_cases hNn : N ≤ n
        · simp only [hNn, ↓reduceIte]
          exact shearReducedGradientTerm_energy_integral_le_tail hC hUnit i N n hNn
        · simp [hNn]
    _ = ∑' n, ENNReal.ofReal ((64 * C ^ 2 * shearScale N) * shearScale n) := by
      congr 1
    _ ≤ ENNReal.ofReal ((64 * C ^ 2 * shearScale N) * (4 / 3)) := by
      have hK : 0 ≤ 64 * C ^ 2 * shearScale N := by
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C))
          (shearScale_pos N).le
      exact shearScale_sum_ofReal_le_energy (64 * C ^ 2 * shearScale N) hK
    _ = ENNReal.ofReal ((256 / 3 : ℝ) * C ^ 2 * shearScale N) := by
      congr 1
      ring

end CKN

namespace CKN


private theorem shearReducedGradientTerm_norm_le_head
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C)
    {n : ℕ} (hscale : r / 4 < shearScale n)
    (i : Fin 2) (z : Vec2 × ℝ) :
    ‖shearReducedGradientTerm i n z‖ ≤ 4 * C / r := by
  have hfield := shearScaleBump_spatialFirst_bound (shearScale_pos n)
    hUnit i z
  have hweight := shearWeight_le_one_energy n
  have hweight0 := shearWeight_nonneg_energy n
  have hterm : ‖shearReducedGradientTerm i n z‖ ≤
      shearWeight n * (C * (shearScale n)⁻¹) := by
    change ‖shearWeight n • shearSpatialFirstField (shearScale n) i z‖ ≤ _
    rw [smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hweight0]
    exact mul_le_mul_of_nonneg_left hfield hweight0
  have hinv : (shearScale n)⁻¹ ≤ (r / 4)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by positivity) hscale.le)
  have hinv' : (shearScale n)⁻¹ ≤ 4 / r := by
    calc
      (shearScale n)⁻¹ ≤ (r / 4)⁻¹ := hinv
      _ = 4 / r := by field_simp [ne_of_gt hr]
  calc
    ‖shearReducedGradientTerm i n z‖ ≤
        shearWeight n * (C * (shearScale n)⁻¹) := hterm
    _ ≤ 1 * (C * (shearScale n)⁻¹) := by
      exact mul_le_mul_of_nonneg_right hweight
        (mul_nonneg hC (inv_nonneg.mpr (shearScale_pos n).le))
    _ ≤ 1 * (C * (4 / r)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv' hC) (by positivity)
    _ = 4 * C / r := by field_simp [ne_of_gt hr]

private theorem shearReducedGradientSeries_energy_split
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C)
    (i : Fin 2) (N : ℕ)
    (hmin : ∀ n < N, r / 4 < shearScale n) (z : Vec2 × ℝ) :
    ENNReal.ofReal (shearReducedGradientSeries i z ^ 2) ≤
      ENNReal.ofReal ((4 * C / r) ^ 2) + shearReducedGradientTailEnergy i N z := by
  by_cases hex : ∃ n, shearReducedGradientTerm i n z ≠ 0
  · rcases hex with ⟨n, hn⟩
    have hzero : ∀ m, m ≠ n → shearReducedGradientTerm i m z = 0 := by
      intro m hmn
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · rcases shearReducedGradientTerms_separated hlt z with hmz | hnz
        · exact hmz
        · exact (hn hnz).elim
      · rcases shearReducedGradientTerms_separated hgt z with hnz | hmz
        · exact (hn hnz).elim
        · exact hmz
    have hseries : shearReducedGradientSeries i z = shearReducedGradientTerm i n z := by
      unfold shearReducedGradientSeries
      exact tsum_eq_single n hzero
    rw [hseries]
    by_cases hhead : n < N
    · have hb := shearReducedGradientTerm_norm_le_head hC hr hUnit
        (hmin n hhead) i z
      have hsq : shearReducedGradientTerm i n z ^ 2 ≤ (4 * C / r) ^ 2 := by
        calc
          shearReducedGradientTerm i n z ^ 2 =
              ‖shearReducedGradientTerm i n z‖ ^ 2 := by
                rw [Real.norm_eq_abs]
                exact (sq_abs _).symm
          _ ≤ (4 * C / r) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hb
      exact (ENNReal.ofReal_le_ofReal hsq).trans
        (le_add_right (le_refl _))
    · have htail : N ≤ n := Nat.le_of_not_gt hhead
      have hle := ENNReal.le_tsum
        (f := fun m => if N ≤ m then
          ENNReal.ofReal (shearReducedGradientTerm i m z ^ 2) else 0) n
      have hle' : ENNReal.ofReal (shearReducedGradientTerm i n z ^ 2) ≤
          shearReducedGradientTailEnergy i N z := by
        unfold shearReducedGradientTailEnergy
        simpa [htail] using hle
      exact le_add_left hle'
  · have hzero : ∀ n, shearReducedGradientTerm i n z = 0 := by
      intro n
      by_contra hn
      exact hex ⟨n, hn⟩
    have hs : shearReducedGradientSeries i z = 0 := by
      unfold shearReducedGradientSeries
      simp [hzero]
    rw [hs]
    simp

end CKN

namespace CKN

private theorem shearScale_tendsto_zero_energy :
    Tendsto shearScale atTop (𝓝 (0 : ℝ)) := by
  unfold shearScale
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private theorem shearScale_threshold_energy {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, shearScale N ≤ r / 4 ∧
      ∀ n < N, r / 4 < shearScale n := by
  have hev : ∀ᶠ n : ℕ in atTop, shearScale n ≤ r / 4 :=
    (shearScale_tendsto_zero_energy).eventually
      (Iic_mem_nhds (by positivity))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  let P : ℕ → Prop := fun n => shearScale n ≤ r / 4
  have hP : ∃ n, P n := ⟨N₀, hN₀ N₀ le_rfl⟩
  let N := Nat.find hP
  have hN : shearScale N ≤ r / 4 := Nat.find_spec hP
  refine ⟨N, hN, ?_⟩
  intro n hn
  by_contra hnot
  have hPn : P n := le_of_not_gt hnot
  have hfind : N ≤ n := Nat.find_min' hP hPn
  exact (Nat.not_lt_of_ge hfind) hn

private theorem shearReducedGradientTailEnergy_measurable (i : Fin 2) (N : ℕ) :
    Measurable (shearReducedGradientTailEnergy i N) := by
  unfold shearReducedGradientTailEnergy
  apply Measurable.tsum
  intro n
  by_cases hn : N ≤ n
  · simp only [hn, ↓reduceIte]
    exact (ENNReal.continuous_ofReal.comp
      ((shearReducedGradientTerm_continuous_energy i n).pow 2)).measurable
  · simp only [hn, ↓reduceIte]
    exact measurable_const

private theorem shear_volume_cylinder_le {r : ℝ} (hr : 0 < r) :
    volume (parabolicCylinder (0 : Vec3) 0 r) ≤
      ENNReal.ofReal ((16 / 3 : ℝ) * r ^ 5) := by
  rw [volume_parabolicCylinder_zero,
    CKN.Foundation.Parabolic.volume_vec3Ball_eq]
  calc
    ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) *
        ENNReal.ofReal (r ^ 2) =
      ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3) * r ^ 2) := by
        rw [← ENNReal.ofReal_pow hr.le 3]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 3)]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 3 * (Real.pi * 4 / 3))]
    _ ≤ ENNReal.ofReal ((16 / 3 : ℝ) * r ^ 5) := by
      apply ENNReal.ofReal_le_ofReal
      have hpi : Real.pi * 4 / 3 ≤ 16 / 3 := by
        gcongr
        nlinarith only [Real.pi_le_four]
      have hr3 : 0 ≤ r ^ 3 := by positivity
      have hr2 : 0 ≤ r ^ 2 := by positivity
      calc
        r ^ 3 * (Real.pi * 4 / 3) * r ^ 2 ≤
            r ^ 3 * (16 / 3) * r ^ 2 := by gcongr
        _ = (16 / 3) * r ^ 5 := by ring

end CKN

namespace CKN

private theorem shearFullGradient_cylinder_energy_le
    {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C) {i : Fin 2}
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
      ENNReal.ofReal (shearFullGradient i z ^ 2) ≤
        ENNReal.ofReal (128 * C ^ 2 * r ^ 2) := by
  obtain ⟨N, hN, hmin⟩ := shearScale_threshold_energy hr
  let tail : ParabolicPoint → ℝ≥0∞ := fun z =>
    shearReducedGradientTailEnergy i N (shearCoordinateEquiv z).2
  have htail : Measurable tail := by
    exact (shearReducedGradientTailEnergy_measurable i N).comp
      (measurable_snd.comp shearCoordinateEquiv.measurable)
  have hsplit : ∀ z : ParabolicPoint,
      ENNReal.ofReal (shearFullGradient i z ^ 2) ≤
        ENNReal.ofReal ((4 * C / r) ^ 2) + tail z := by
    intro z
    have hred := shearReducedGradientSeries_energy_split hC hr hUnit i N hmin
      (shearCoordinateEquiv z).2
    simpa [tail, shearFullGradient, shearReducedView,
      shearCoordinateEquiv_apply] using hred
  have hsum : Measurable (fun z : ParabolicPoint =>
      ENNReal.ofReal ((4 * C / r) ^ 2) + tail z) :=
    measurable_const.add htail
  have hmono :
      ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        ENNReal.ofReal (shearFullGradient i z ^ 2) ≤
      ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        ENNReal.ofReal ((4 * C / r) ^ 2) + tail z := by
    exact setLIntegral_mono hsum (fun z _ => hsplit z)
  have htailInt :
      ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r, tail z ≤
        ENNReal.ofReal (2 * r) *
          ∫⁻ y : Vec2 × ℝ, shearReducedGradientTailEnergy i N y := by
    exact shear_lintegral_cylinder_le_reduced hr
      (shearReducedGradientTailEnergy i N)
      (shearReducedGradientTailEnergy_measurable i N)
  have htailBound := shearReducedGradientTailEnergy_integral_le hC hUnit i N
  have hvol := shear_volume_cylinder_le hr
  have hhead :
      ENNReal.ofReal ((4 * C / r) ^ 2) *
          volume (parabolicCylinder (0 : Vec3) 0 r) ≤
        ENNReal.ofReal ((256 / 3 : ℝ) * C ^ 2 * r ^ 3) := by
    calc
      ENNReal.ofReal ((4 * C / r) ^ 2) *
          volume (parabolicCylinder (0 : Vec3) 0 r) ≤
        ENNReal.ofReal ((4 * C / r) ^ 2) *
          ENNReal.ofReal ((16 / 3 : ℝ) * r ^ 5) :=
        mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = ENNReal.ofReal (((4 * C / r) ^ 2) * ((16 / 3 : ℝ) * r ^ 5)) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      _ = ENNReal.ofReal ((256 / 3 : ℝ) * C ^ 2 * r ^ 3) := by
        congr 1
        field_simp [ne_of_gt hr]
        ring
  have htail' :
      ENNReal.ofReal (2 * r) *
          ∫⁻ y : Vec2 × ℝ, shearReducedGradientTailEnergy i N y ≤
        ENNReal.ofReal ((128 / 3 : ℝ) * C ^ 2 * r ^ 2) := by
    calc
      ENNReal.ofReal (2 * r) *
          ∫⁻ y : Vec2 × ℝ, shearReducedGradientTailEnergy i N y ≤
        ENNReal.ofReal (2 * r) *
          ENNReal.ofReal ((256 / 3 : ℝ) * C ^ 2 * shearScale N) :=
        mul_le_mul_of_nonneg_left htailBound (by positivity)
      _ = ENNReal.ofReal ((2 * r) *
          ((256 / 3 : ℝ) * C ^ 2 * shearScale N)) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * r)]
      _ ≤ ENNReal.ofReal ((128 / 3 : ℝ) * C ^ 2 * r ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hscale : shearScale N ≤ r / 4 := hN
        have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
        calc
          (2 * r) * ((256 / 3 : ℝ) * C ^ 2 * shearScale N) =
              (512 / 3 : ℝ) * C ^ 2 * r * shearScale N := by ring
          _ ≤ (512 / 3 : ℝ) * C ^ 2 * r * (r / 4) := by
            exact mul_le_mul_of_nonneg_left hscale (by positivity)
          _ = (128 / 3 : ℝ) * C ^ 2 * r ^ 2 := by ring
  calc
    ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        ENNReal.ofReal (shearFullGradient i z ^ 2) ≤
      ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        ENNReal.ofReal ((4 * C / r) ^ 2) + tail z := hmono
    _ = ENNReal.ofReal ((4 * C / r) ^ 2) *
          volume (parabolicCylinder (0 : Vec3) 0 r) +
        ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r, tail z := by
      rw [lintegral_add_left measurable_const]
      rw [lintegral_const]
      simp only [Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal ((256 / 3 : ℝ) * C ^ 2 * r ^ 3) +
        ENNReal.ofReal ((128 / 3 : ℝ) * C ^ 2 * r ^ 2) := by
      have htailFull :
          ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r, tail z ≤
            ENNReal.ofReal ((128 / 3 : ℝ) * C ^ 2 * r ^ 2) :=
        htailInt.trans htail'
      exact add_le_add hhead htailFull
    _ ≤ ENNReal.ofReal (128 * C ^ 2 * r ^ 2) := by
      rw [← ENNReal.ofReal_add]
      · apply ENNReal.ofReal_le_ofReal
        have hr3 : r ^ 3 ≤ r ^ 2 := by
          have hr2 : 0 ≤ r ^ 2 := by positivity
          simpa [pow_succ] using mul_le_mul_of_nonneg_left hr1 hr2
        have hfirst :
            (256 / 3 : ℝ) * C ^ 2 * r ^ 3 ≤
              (256 / 3 : ℝ) * C ^ 2 * r ^ 2 := by
          exact mul_le_mul_of_nonneg_left hr3 (by positivity)
        calc
          (256 / 3 : ℝ) * C ^ 2 * r ^ 3 +
              (128 / 3 : ℝ) * C ^ 2 * r ^ 2 ≤
              (256 / 3 : ℝ) * C ^ 2 * r ^ 2 +
                (128 / 3 : ℝ) * C ^ 2 * r ^ 2 :=
            add_le_add hfirst (le_refl _)
          _ = 128 * C ^ 2 * r ^ 2 := by ring
      · positivity
      · positivity

end CKN

namespace CKN

private theorem shearCounterexample_cylinder_energy_le
    {C : ℝ} (hC : 0 ≤ C)
    (hUnit : ∀ k ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ k shearUnitBump z‖ ≤ C)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        ENNReal.ofReal (spatialGradientSq shearCounterexampleVelocity
          shearCounterexampleDu z) ≤
      ENNReal.ofReal (256 * C ^ 2 * r ^ 2) := by
  have hEq :
      (fun z : ParabolicPoint =>
        ENNReal.ofReal (spatialGradientSq shearCounterexampleVelocity
          shearCounterexampleDu z)) =
      (fun z => ENNReal.ofReal (shearFullGradient 0 z ^ 2) +
        ENNReal.ofReal (shearFullGradient 1 z ^ 2)) := by
    funext z
    rw [shearCounterexampleDu_energy_eq z]
    rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  have h0 := shearFullGradient_cylinder_energy_le hC hUnit (i := 0) hr hr1
  have h1 := shearFullGradient_cylinder_energy_le hC hUnit (i := 1) hr hr1
  have hm0 : Measurable (fun z : ParabolicPoint =>
      ENNReal.ofReal (shearFullGradient 0 z ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((shearFullGradient_measurable 0).pow_const 2)
  have hsumInt :
      (∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        ENNReal.ofReal (shearFullGradient 0 z ^ 2) +
          ENNReal.ofReal (shearFullGradient 1 z ^ 2)) =
        (∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
          ENNReal.ofReal (shearFullGradient 0 z ^ 2)) +
        ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
          ENNReal.ofReal (shearFullGradient 1 z ^ 2) := by
    exact lintegral_add_left hm0 _
  rw [hEq, hsumInt]
  have hadd := add_le_add h0 h1
  calc
    (∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        ENNReal.ofReal (shearFullGradient 0 z ^ 2)) +
      ∫⁻ z in parabolicCylinder (0 : Vec3) 0 r,
        ENNReal.ofReal (shearFullGradient 1 z ^ 2) ≤
      ENNReal.ofReal ((128 * C ^ 2 * r ^ 2)) +
        ENNReal.ofReal ((128 * C ^ 2 * r ^ 2)) := hadd
    _ = ENNReal.ofReal (256 * C ^ 2 * r ^ 2) := by
      rw [← ENNReal.ofReal_add]
      · congr 1
        ring
      · positivity
      · positivity

private theorem shearCounterexample_normalized_energy_tendsto_zero :
    Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹ *
        ∫⁻ w in parabolicCylinder (0 : Vec3) 0 r,
          ENNReal.ofReal (spatialGradientSq shearCounterexampleVelocity
            shearCounterexampleDu w)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC, hUnit⟩ := shearUnitBump_bound
  let K : ℝ := 256 * C ^ 2
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder (0 : Vec3) 0 r,
            ENNReal.ofReal (spatialGradientSq shearCounterexampleVelocity
              shearCounterexampleDu w) ≤ ENNReal.ofReal (K * r) := by
    have hpos : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [] with r hr
      exact hr
    have hone : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ≤ 1 := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with r hr _
      exact hr
    filter_upwards [hpos, hone] with r hr hr1
    have hE := shearCounterexample_cylinder_energy_le hC hUnit hr hr1
    have hmul :
        (ENNReal.ofReal r)⁻¹ *
            ∫⁻ w in parabolicCylinder (0 : Vec3) 0 r,
              ENNReal.ofReal (spatialGradientSq shearCounterexampleVelocity
                shearCounterexampleDu w) ≤
          (ENNReal.ofReal r)⁻¹ * ENNReal.ofReal (K * r ^ 2) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    calc
      (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder (0 : Vec3) 0 r,
            ENNReal.ofReal (spatialGradientSq shearCounterexampleVelocity
              shearCounterexampleDu w) ≤
          (ENNReal.ofReal r)⁻¹ * ENNReal.ofReal (K * r ^ 2) := hmul
      _ = ENNReal.ofReal (r⁻¹ * (K * r ^ 2)) := by
        rw [← ENNReal.ofReal_inv_of_pos hr]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r⁻¹)]
      _ = ENNReal.ofReal (K * r) := by
        congr 1
        field_simp [ne_of_gt hr]
  have hcont : Continuous (fun r : ℝ => ENNReal.ofReal (K * r)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
  refine (tendsto_order.2 ⟨?_, ?_⟩)
  · intro a ha
    filter_upwards [] with r
    have hnonneg : 0 ≤
        (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder (0 : Vec3) 0 r,
            ENNReal.ofReal (spatialGradientSq shearCounterexampleVelocity
              shearCounterexampleDu w) := by positivity
    exact lt_of_lt_of_le ha hnonneg
  · intro a ha
    have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (K * r))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun r : ℝ => ENNReal.ofReal (K * r))
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have h0' := ((hcont.continuousAt :
          ContinuousAt (fun r : ℝ => ENNReal.ofReal (K * r)) (0 : ℝ)).tendsto)
        simpa using h0'
      exact h0.mono_left nhdsWithin_le_nhds
    filter_upwards [hbound, hlim.eventually (Iio_mem_nhds ha)] with r hle hsmall
    exact lt_of_le_of_lt hle hsmall

theorem shear_counterexample_energy_limsup_zero :
    Filter.limsup (fun r : ℝ => (ENNReal.ofReal r)⁻¹ *
        ∫⁻ w in parabolicCylinder (0 : Vec3) 0 r,
          ENNReal.ofReal (spatialGradientSq shearCounterexampleVelocity
            shearCounterexampleDu w)) (𝓝[>] (0 : ℝ)) = 0 := by
  exact shearCounterexample_normalized_energy_tendsto_zero.limsup_eq

end CKN
