-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.RepresentativeBound
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Reanchoring by an actual L^(10/3) velocity bound

Finite L^(10/3) control supplies integrability and the velocity average.
Together with a global Hölder seminorm this gives an explicit full norm,
with a center-independent coefficient on parabolic balls.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- A nonnegative scalar L^(10/3) bound supplies integrability and its
normalized average estimate on a positive finite-measure set. -/
theorem integrableOn_and_average_le_of_eLpNorm_ten_thirds
    {S : Set ParabolicPoint} {f : ParabolicPoint → ℝ} {U : ℝ}
    (hSpos : 0 < volume S) (hStop : volume S < ⊤) (hU : 0 ≤ U)
    (hf : AEStronglyMeasurable f (volume.restrict S))
    (hfnonneg : ∀ᵐ x ∂volume.restrict S, 0 ≤ f x)
    (hbound : eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict S) ≤
      ENNReal.ofReal U) :
    IntegrableOn f S ∧
      (⨍ x in S, f x) ≤ (volume S).toReal ^ (-3 / 10 : ℝ) * U := by
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hStop.ne
  have hm : MemLp f (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict S) :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  have hi : IntegrableOn f S := hm.integrable (by norm_num)
  refine ⟨hi, ?_⟩
  have hnorm : eLpNorm f 1 (volume.restrict S) ≤
      ENNReal.ofReal U * volume S ^ (7 / 10 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := (1 : ℝ≥0∞)) (q := ENNReal.ofReal (10 / 3 : ℝ)) (by norm_num) hf
    norm_num at h
    exact h.trans (mul_le_mul_left hbound _)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hStop.ne)) hnorm
  have hint : (∫ x in S, f x) ≤ U * (volume S).toReal ^ (7 / 10 : ℝ) := by
    have heq : lpNorm f 1 (volume.restrict S) = ∫ x in S, f x := by
      rw [lpNorm_one_eq_integral_norm hf]
      apply integral_congr_ae
      filter_upwards [hfnonneg] with x hx
      exact Real.norm_of_nonneg hx
    simpa only [toReal_eLpNorm, heq, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hU, ENNReal.toReal_rpow] using hreal
  have hpos : 0 < (volume S).toReal := ENNReal.toReal_pos hSpos.ne' hStop.ne
  rw [Integration.setAverage_eq_toReal_inv_smul]
  calc
    (volume S).toReal⁻¹ * (∫ x in S, f x) ≤
        (volume S).toReal⁻¹ * (U * (volume S).toReal ^ (7 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpos.le)
    _ = ((volume S).toReal⁻¹ * (volume S).toReal ^ (7 / 10 : ℝ)) * U := by ring
    _ = (volume S).toReal ^ (-3 / 10 : ℝ) * U := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hpos]
      norm_num

/-- A global Hölder seminorm and an actual L^(10/3) velocity bound control
the full representative norm on any set at bounded distance from the anchor. -/
theorem holder_norm_of_seminorm_of_eLpNorm_ten_thirds
    {S T : Set ParabolicPoint} {u w : ParabolicPoint → Vec3} {γ K D U : ℝ}
    (hS : MeasurableSet S) (hSpos : 0 < volume S) (hStop : volume S < ⊤)
    (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hdist : ∀ x ∈ T, ∀ y ∈ S, parabolicDist x y ≤ D)
    (hsemi : ∀ x y, vec3EuclideanNorm (w x - w y) ≤ K * parabolicDist x y ^ γ)
    (hrep : w =ᵐ[volume.restrict S] u)
    (hu : AEStronglyMeasurable (fun x => vec3EuclideanNorm (u x)) (volume.restrict S))
    (hbound : eLpNorm (fun x => vec3EuclideanNorm (u x))
      (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict S) ≤ ENNReal.ofReal U) :
    ParabolicHolderVecNormLE T w γ
      (K * D ^ γ + (volume S).toReal ^ (-3 / 10 : ℝ) * U + K) := by
  obtain ⟨hint, havg⟩ := integrableOn_and_average_le_of_eLpNorm_ten_thirds
    hSpos hStop hU hu (Filter.Eventually.of_forall fun x => vec3EuclideanNorm_nonneg _) hbound
  refine ⟨K * D ^ γ + (volume S).toReal ^ (-3 / 10 : ℝ) * U, K,
    add_nonneg (mul_nonneg hK (Real.rpow_nonneg hD _))
      (mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) hU), hK, le_rfl, ?_,
    fun x _ y _ => hsemi x y⟩
  intro x hx
  have hpoint : ∀ᵐ y ∂volume.restrict S,
      vec3EuclideanNorm (w x) ≤ K * D ^ γ + vec3EuclideanNorm (u y) := by
    filter_upwards [hrep, ae_restrict_mem hS] with y hy hys
    have htri : vec3EuclideanNorm (w x) ≤
        vec3EuclideanNorm (w x - w y) + vec3EuclideanNorm (w y) := by
      rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
        WithLp.toLp_sub]
      have h := norm_add_le (WithLp.toLp 2 (w x - w y)) (WithLp.toLp 2 (w y))
      simpa only [WithLp.toLp_sub, sub_add_cancel] using h
    have hdiff := (hsemi x y).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (parabolicDist_nonneg x y) (hdist x hx y hys) hγ) hK)
    exact htri.trans (add_le_add hdiff (by rw [hy]))
  have hav := Integration.setAverage_mono_of_ae
    (integrableOn_const hStop.ne) ((integrableOn_const hStop.ne).add hint) hpoint
  rw [Integration.setAverage_add_of_integrableOn
    (f := fun _ : ParabolicPoint => K * D ^ γ) (integrableOn_const hStop.ne) hint,
    Integration.setAverage_const_of_pos_of_lt_top hSpos hStop,
    Integration.setAverage_const_of_pos_of_lt_top hSpos hStop] at hav
  exact hav.trans (add_le_add_right havg _)

/-- On a radius-`a` parabolic ball the anchoring coefficient is explicit
and independent of its center. -/
theorem ball_holder_norm_of_seminorm_of_eLpNorm_ten_thirds
    (z : ParabolicPoint) {a γ K U : ℝ} {u w : ParabolicPoint → Vec3}
    (ha : 0 < a) (hγ : 0 ≤ γ) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hsemi : ∀ x y, vec3EuclideanNorm (w x - w y) ≤ K * parabolicDist x y ^ γ)
    (hrep : w =ᵐ[volume.restrict (Metric.ball z a)] u)
    (hu : AEStronglyMeasurable (fun x => vec3EuclideanNorm (u x))
      (volume.restrict (Metric.ball z a)))
    (hbound : eLpNorm (fun x => vec3EuclideanNorm (u x))
      (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict (Metric.ball z a)) ≤ ENNReal.ofReal U) :
    ParabolicHolderVecNormLE (Metric.ball z a) w γ
      (K * (2 * a) ^ γ + (8 * Real.pi / 3 * a ^ 5) ^ (-3 / 10 : ℝ) * U + K) := by
  have hvol := volume_metricBall z ha.le
  have hcoef : 0 < 8 * Real.pi / 3 * a ^ 5 := by positivity
  have hpos : 0 < volume (Metric.ball z a) := by rw [hvol]; exact ENNReal.ofReal_pos.mpr hcoef
  have htop : volume (Metric.ball z a) < ⊤ := by rw [hvol]; exact ENNReal.ofReal_lt_top
  have hdist : ∀ x ∈ Metric.ball z a, ∀ y ∈ Metric.ball z a,
      parabolicDist x y ≤ 2 * a := by
    intro x hx y hy
    rw [← dist_eq_parabolicDist]
    have ht := dist_triangle x z y
    have hx' := Metric.mem_ball.mp hx
    have hy' : dist z y < a := by simpa only [dist_comm] using Metric.mem_ball.mp hy
    linarith only [ht, hx', hy']
  have h := holder_norm_of_seminorm_of_eLpNorm_ten_thirds Metric.isOpen_ball.measurableSet
    hpos htop hγ hK (by positivity) hU hdist hsemi hrep hu hbound
  simpa only [hvol, ENNReal.toReal_ofReal hcoef.le] using h

end CKN.Core.Endgame
