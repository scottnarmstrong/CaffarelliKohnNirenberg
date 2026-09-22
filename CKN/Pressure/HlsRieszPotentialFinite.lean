-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.PkBoundsP7SolutionBound

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- The three-dimensional Hardy--Littlewood--Sobolev constant is finite. -/
theorem hlsRieszConstant_lt_top : hlsRieszConstant < ∞ := by
  by_contra! h
  have htop : hlsRieszConstant = ∞ := top_unique h
  have hq : 5 / 2 < (3 : ℝ) := by norm_num
  have hcontr : pressureP7SolutionConstant (3 : ℝ) = ∞ := by
    unfold pressureP7SolutionConstant
    rw [htop]
    have hpos1 : ENNReal.ofReal ((4 * Real.pi)⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have h3 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
    have hpow : ENNReal.ofReal (4 * Real.pi / 3) ^ (1 - 1 / (3 : ℝ) : ℝ) ≠ 0 :=
      (ENNReal.rpow_pos (by positivity) ENNReal.ofReal_ne_top).ne'
    rw [ENNReal.mul_top hpos1]
    rw [ENNReal.mul_top h3]
    exact ENNReal.top_mul hpow
  exact pressureP7SolutionConstant_ne_top (q := 3) hq hcontr

/-- The one-dimensional Riesz potential of a measurable function is measurable. -/
theorem measurable_rieszPotentialOne {g : Vec3 → ℝ} (hg : Measurable g) :
    Measurable (rieszPotentialOne g) := by
  unfold rieszPotentialOne
  have hkernel : Measurable (fun (p : Vec3 × Vec3) => rieszKernelOne p.1 p.2) := by
    have hdist : Measurable (fun (p : Vec3 × Vec3) => dist p.1 p.2) :=
      measurable_dist.comp measurable_id
    have hofReal : Measurable (ENNReal.ofReal : ℝ → ℝ≥0∞) :=
      ENNReal.measurable_ofReal
    have hrpow : Measurable (fun (x : ℝ≥0∞) => x ^ (-2 : ℝ)) :=
      ENNReal.continuous_rpow_const.measurable
    have hcomp : Measurable (fun (p : Vec3 × Vec3) =>
        ENNReal.ofReal (dist p.1 p.2)) :=
      hofReal.comp hdist
    exact hrpow.comp hcomp
  have hgpart : Measurable (fun (p : Vec3 × Vec3) => ENNReal.ofReal |g p.2|) := by
    have habs : Measurable (fun (w : ℝ) => |w|) :=
      continuous_abs.measurable
    have hg_meas : Measurable (fun (p : Vec3 × Vec3) => g p.2) :=
      hg.comp measurable_snd
    have habs_g : Measurable (fun (p : Vec3 × Vec3) => |g p.2|) :=
      habs.comp hg_meas
    exact ENNReal.measurable_ofReal.comp habs_g
  have hprod : Measurable (fun (p : Vec3 × Vec3) =>
      rieszKernelOne p.1 p.2 * ENNReal.ofReal |g p.2|) :=
    hkernel.mul hgpart
  exact hprod.lintegral_prod_right'

/-- For a measurable function `g` with finite `L^{5/2}` norm, the Riesz potential
`rieszPotentialOne g` is almost everywhere finite. -/
theorem ae_rieszPotentialOne_lt_top {g : Vec3 → ℝ} (hg : Measurable g)
    (hfinite : (∫⁻ y, ENNReal.ofReal |g y| ^ (5 / 2 : ℝ)) < ∞) :
    ∀ᵐ x ∂volume, rieszPotentialOne g x < ∞ := by
  let R := rieszPotentialOne g
  have hRmeas : Measurable R := measurable_rieszPotentialOne hg
  have hR_bound : (∫⁻ z, R z ^ (15 : ℝ)) ^ (1 / 15 : ℝ) < ∞ := by
    have hineq := rieszPotentialOne_hls_of_zero_or_good hg hfinite
    apply lt_of_le_of_lt hineq
    apply ENNReal.mul_lt_top hlsRieszConstant_lt_top
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinite.ne
  have hint_lt_top : ∫⁻ z, R z ^ (15 : ℝ) < ∞ := by
    have hpos : 0 < (1 / 15 : ℝ) := by norm_num
    exact ((ENNReal.rpow_lt_top_iff_of_pos hpos).mp hR_bound)
  have hRmeas_pow : Measurable (fun z => R z ^ (15 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp hRmeas
  have hae_pow : ∀ᵐ x ∂volume, R x ^ (15 : ℝ) < ∞ :=
    ae_lt_top hRmeas_pow hint_lt_top.ne
  filter_upwards [hae_pow] with x hx
  have hpos15 : 0 < (15 : ℝ) := by norm_num
  exact ((ENNReal.rpow_lt_top_iff_of_pos hpos15).mp hx)
