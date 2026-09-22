-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SliceNormBounds
import CKN.Foundation.Parabolic.Topology

/-!
# The beta-squared gradient limsup identity

This file proves the equality in the paper display `eq:thmB-hyp`
in `paper/ckn.tex`. At an interior point of a suitable weak
solution, sufficiently small cylinders have compact closure in the domain.
Their gradient integrals are finite, so the definition of beta gives an
eventual equality of the two nonnegative extended-real quantities.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- The limsup of `β(z₀, r)²` as `r → 0⁺` equals the limsup of the
rescaled gradient integral, using the SWS identity on small cylinders. -/
theorem betaSq_limsup_eq_gradient_limsup {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} (hz₀ : z₀ ∈ spaceTimeSet Ω I) :
    Filter.limsup (fun r : ℝ => ENNReal.ofReal (beta u Du z₀ r ^ 2)) (𝓝[>] (0 : ℝ)) =
      Filter.limsup (fun r : ℝ => (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r, ENNReal.ofReal (spatialGradientSq u Du w))
        (𝓝[>] (0 : ℝ)) := by
  obtain ⟨Rx, hRx, hRxsub⟩ := Metric.mem_nhds_iff.mp (hsol.1.mem_nhds hz₀.1)
  obtain ⟨Rt, hRt, hRtsub⟩ := Metric.mem_nhds_iff.mp (hsol.2.1.mem_nhds hz₀.2)
  set R := min Rx (Real.sqrt Rt) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact lt_min hRx (Real.sqrt_pos.2 hRt)
  have hRclosure : ∀ {r : ℝ}, 0 < r → r < R →
      closure (parabolicCylinder z₀.1 z₀.2 r) ⊆ spaceTimeSet Ω I := by
    intro r hr hrr y hy
    rw [closure_parabolicCylinder hr] at hy
    rcases hy with ⟨hyx, hyt⟩
    have hrdx : dist y.1 z₀.1 < Rx := by
      rw [dist_eq_norm]
      change vec3EuclideanNorm (y.1 - z₀.1) ≤ r at hyx
      have hnorm : ‖y.1 - z₀.1‖ ≤ vec3EuclideanNorm (y.1 - z₀.1) := by
        rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
        intro i
        change |(y.1 - z₀.1) i| ≤ vec3EuclideanNorm (y.1 - z₀.1)
        rw [vec3EuclideanNorm]
        apply Real.abs_le_sqrt
        exact Finset.single_le_sum (fun j _ => sq_nonneg ((y.1 - z₀.1) j))
          (Finset.mem_univ i)
      have hmin : R ≤ Rx := by
        rw [hRdef]
        exact min_le_left _ _
      exact hnorm.trans_lt (hyx.trans_lt (hrr.trans_le hmin))
    have hrdt : dist y.2 z₀.2 < Rt := by
      rw [Real.dist_eq]
      have hsq : r ^ 2 < Rt := by
        have hsqrt_sq : (Real.sqrt Rt) ^ 2 = Rt := Real.sq_sqrt hRt.le
        have hrr' : r < Real.sqrt Rt := by
          have hmin : R ≤ Real.sqrt Rt := by
            rw [hRdef]
            exact min_le_right _ _
          exact hrr.trans_le hmin
        nlinarith only [hr, hrr', hsqrt_sq]
      rcases hyt with ⟨hytlow, hythigh⟩
      rw [abs_of_nonpos (by linarith only [hythigh])]
      calc
        -(y.2 - z₀.2) = z₀.2 - y.2 := by ring
        _ ≤ r ^ 2 := by linarith only [hytlow]
        _ < Rt := hsq
    have hy1_mem : y.1 ∈ Metric.ball z₀.1 Rx := by
      simpa [Metric.mem_ball, dist_comm] using hrdx
    have hy2_mem : y.2 ∈ Metric.ball z₀.2 Rt := by
      simpa [Metric.mem_ball, dist_comm] using hrdt
    have hyΩ : y.1 ∈ Ω := hRxsub hy1_mem
    have hyI : y.2 ∈ I := hRtsub hy2_mem
    exact show y ∈ spaceTimeSet Ω I from ⟨hyΩ, hyI⟩
  have h_eventually : ∀ᶠ (r : ℝ) in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (beta u Du z₀ r ^ 2) =
        (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r, ENNReal.ofReal (spatialGradientSq u Du w) := by
    have h_mem : Ioo (0 : ℝ) R ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT hRpos
    filter_upwards [h_mem] with r hr
    have hrpos : 0 < r := hr.1
    have hrltR : r < R := hr.2
    have hsub : closure (parabolicCylinder z₀.1 z₀.2 r) ⊆ spaceTimeSet Ω I :=
      hRclosure hrpos hrltR
    rw [sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq hsol z₀ hrpos hsub]
    rw [← ENNReal.ofReal_inv_of_pos hrpos,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ r⁻¹)]
    congr 1
    field_simp
  exact Filter.limsup_congr h_eventually

end CKN
