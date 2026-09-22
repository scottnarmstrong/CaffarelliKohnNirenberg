-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Lipschitz.Domain

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

namespace CKN

set_option autoImplicit false

private theorem isOpen_vec3Ball (c : Vec3) {r : ℝ} :
    IsOpen (vec3Ball c r) := by
  change IsOpen {y : Vec3 | vec3EuclideanNorm (y - c) < r}
  exact isOpen_lt (continuous_vec3EuclideanNorm.comp
    (continuous_id.sub continuous_const)) continuous_const

private theorem isBounded_vec3Ball (c : Vec3) {r : ℝ} :
    Bornology.IsBounded (vec3Ball c r) := by
  apply (Metric.isBounded_iff_subset_closedBall c).2
  refine ⟨r, ?_⟩
  intro y hy
  rw [Metric.mem_closedBall]
  rw [dist_eq_norm]
  exact (norm_le_vec3EuclideanNorm (y - c)).trans (le_of_lt hy)

private theorem frontier_vec3Ball_norm (c : Vec3) {r : ℝ}
    {x : Vec3} (hx : x ∈ frontier (vec3Ball c r)) :
    vec3EuclideanNorm (x - c) = r := by
  have hle : vec3EuclideanNorm (x - c) ≤ r := by
    apply (closure_minimal (s := vec3Ball c r) (t := {y : Vec3 |
        vec3EuclideanNorm (y - c) ≤ r}))
    · intro y hy
      change vec3EuclideanNorm (y - c) < r at hy
      exact le_of_lt hy
    · exact isClosed_le (continuous_vec3EuclideanNorm.comp
        (continuous_id.sub continuous_const)) continuous_const
    · rw [frontier_eq_closure_inter_closure] at hx
      exact hx.1
  have hge : r ≤ vec3EuclideanNorm (x - c) := by
    apply (closure_minimal (s := (vec3Ball c r)ᶜ) (t := {y : Vec3 |
        r ≤ vec3EuclideanNorm (y - c)}))
    · intro y hy
      change ¬vec3EuclideanNorm (y - c) < r at hy
      exact le_of_not_gt hy
    · exact isClosed_le continuous_const (continuous_vec3EuclideanNorm.comp
        (continuous_id.sub continuous_const))
    · rw [frontier_eq_closure_inter_closure] at hx
      exact hx.2
  exact le_antisymm hle hge

private theorem exists_ne_component (v : Vec3) (hv : v ≠ 0) :
    ∃ k : Fin 3, v k ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  funext i
  exact h i

private theorem coordinateChart_vec3Norm (k : Fin 3) (negate : Bool) (v : Vec3) :
    vec3EuclideanNorm (coordinateChart k negate v) = vec3EuclideanNorm v := by
  classical
  by_cases hs : negate
  · simp only [coordinateChart_apply, coordinateChartLinear, hs, ↓reduceIte,
      LinearEquiv.trans_apply, coordinatePermutation, negateLast]
    change Real.sqrt (∑ i : Fin 3,
      (if i = 2 then -(v ((Equiv.swap k 2) i)) else v ((Equiv.swap k 2) i)) ^ 2) = _
    simp only [vec3EuclideanNorm]
    congr 1
    simp_rw [show ∀ i : Fin 3,
        (if i = 2 then -(v ((Equiv.swap k 2) i)) else v ((Equiv.swap k 2) i)) ^ 2 =
          v ((Equiv.swap k 2) i) ^ 2 by
      intro i
      by_cases hi : i = 2 <;> simp [hi]]
    exact Fintype.sum_equiv (Equiv.swap k 2)
      (fun i => v ((Equiv.swap k 2) i) ^ 2) (fun i => v i ^ 2) (by
        intro i
        rfl)
  · simp only [coordinateChart_apply, coordinateChartLinear, hs,
      coordinatePermutation]
    change Real.sqrt (∑ i : Fin 3, v ((Equiv.swap k 2) i) ^ 2) = _
    simp only [vec3EuclideanNorm]
    congr 1
    exact Fintype.sum_equiv (Equiv.swap k 2)
      (fun i => v ((Equiv.swap k 2) i) ^ 2) (fun i => v i ^ 2) (by
        intro i
        rfl)

private theorem vec3EuclideanNorm_sq_split (z : Vec3) :
    vec3EuclideanNorm z ^ 2 =
      (∑ j : Fin 2, z j.castSucc ^ 2) + z 2 ^ 2 := by
  simp [vec3EuclideanNorm, Fin.sum_univ_succ]
  rw [Real.sq_sqrt (by positivity)]
  ring

private def quad2 (w : Fin 2 → ℝ) : ℝ := ∑ j : Fin 2, w j ^ 2

private theorem quad2_sub_bound (u v : Fin 2 → ℝ) :
    |quad2 u - quad2 v| ≤ 2 * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  simp only [quad2, Fin.sum_univ_two]
  have h0u : |u 0| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm u 0
  have h1u : |u 1| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm u 1
  have h0v : |v 0| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have h1v : |v 1| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 1
  have h0d : |u 0 - v 0| ≤ ‖u - v‖ := by
    have h := norm_le_pi_norm (u - v) 0
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using h
  have h1d : |u 1 - v 1| ≤ ‖u - v‖ := by
    have h := norm_le_pi_norm (u - v) 1
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using h
  rw [show u 0 ^ 2 + u 1 ^ 2 - (v 0 ^ 2 + v 1 ^ 2) =
      (u 0 ^ 2 - v 0 ^ 2) + (u 1 ^ 2 - v 1 ^ 2) by ring,
    show u 0 ^ 2 - v 0 ^ 2 = (u 0 - v 0) * (u 0 + v 0) by ring,
    show u 1 ^ 2 - v 1 ^ 2 = (u 1 - v 1) * (u 1 + v 1) by ring]
  calc
    |(u 0 - v 0) * (u 0 + v 0) + (u 1 - v 1) * (u 1 + v 1)| ≤
        |u 0 - v 0| * |u 0 + v 0| +
          |u 1 - v 1| * |u 1 + v 1| := by
      simpa only [abs_mul] using abs_add_le
        ((u 0 - v 0) * (u 0 + v 0)) ((u 1 - v 1) * (u 1 + v 1))
    _ ≤ ‖u - v‖ * (‖u‖ + ‖v‖) +
          ‖u - v‖ * (‖u‖ + ‖v‖) := by
      have h0s : |u 0 + v 0| ≤ ‖u‖ + ‖v‖ :=
        (abs_add_le _ _).trans (add_le_add h0u h0v)
      have h1s : |u 1 + v 1| ≤ ‖u‖ + ‖v‖ :=
        (abs_add_le _ _).trans (add_le_add h1u h1v)
      exact add_le_add
        (mul_le_mul h0d h0s (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul h1d h1s (abs_nonneg _) (norm_nonneg _))
    _ = 2 * (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

private theorem sqrt_sub_le_div {A B m : ℝ} (hm : 0 < m) (hA : m ≤ A)
    (hB : m ≤ B) :
    |Real.sqrt A - Real.sqrt B| ≤ |A - B| / (2 * Real.sqrt m) := by
  have hm0 : 0 ≤ m := hm.le
  have hA0 : 0 ≤ A := hm0.trans hA
  have hB0 : 0 ≤ B := hm0.trans hB
  have hmroot : 0 < Real.sqrt m := (Real.sqrt_pos).2 hm
  have hAroot : Real.sqrt m ≤ Real.sqrt A := Real.sqrt_le_sqrt hA
  have hBroot : Real.sqrt m ≤ Real.sqrt B := Real.sqrt_le_sqrt hB
  have hden : 0 < Real.sqrt A + Real.sqrt B := by
    exact add_pos_of_pos_of_nonneg (lt_of_lt_of_le hmroot hAroot) (Real.sqrt_nonneg _)
  have hiden : (Real.sqrt A - Real.sqrt B) *
      (Real.sqrt A + Real.sqrt B) = A - B := by
    calc
      (Real.sqrt A - Real.sqrt B) * (Real.sqrt A + Real.sqrt B) =
          Real.sqrt A ^ 2 - Real.sqrt B ^ 2 := by ring
      _ = A - B := by rw [Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hfrac : (A - B) / (Real.sqrt A + Real.sqrt B) =
      Real.sqrt A - Real.sqrt B := by
    apply (div_eq_iff (ne_of_gt hden)).2
    exact hiden.symm
  calc
    |Real.sqrt A - Real.sqrt B| =
        |A - B| / (Real.sqrt A + Real.sqrt B) := by
      rw [← hfrac, abs_div, abs_of_pos hden]
    _ ≤ |A - B| / (2 * Real.sqrt m) := by
      have hden' : 2 * Real.sqrt m ≤ Real.sqrt A + Real.sqrt B := by
        linarith only [hAroot, hBroot]
      have hpos : 0 < 2 * Real.sqrt m := by positivity
      gcongr

private theorem sphere_graph_lipschitzOn_neg {r a m L : ℝ} (w₀ : Fin 2 → ℝ)
    (S : Set (Fin 2 → ℝ)) (hm : 0 < m) (hL : 0 ≤ L)
    (hlower : ∀ w ∈ S, m ≤ r ^ 2 - quad2 (w₀ + w))
    (hquad : ∀ w ∈ S, ∀ z ∈ S,
      |quad2 (w₀ + w) - quad2 (w₀ + z)| ≤ L * ‖w - z‖) :
    LipschitzOnWith (Real.toNNReal (L / (2 * Real.sqrt m)))
      (fun w => -Real.sqrt (r ^ 2 - quad2 (w₀ + w)) - a) S := by
  have hmroot : 0 < Real.sqrt m := (Real.sqrt_pos).2 hm
  have hcoef : 0 ≤ L / (2 * Real.sqrt m) := by positivity
  have hcoe : (Real.toNNReal (L / (2 * Real.sqrt m)) : ℝ) =
      L / (2 * Real.sqrt m) := Real.coe_toNNReal _ hcoef
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro w hw z hz
  rw [Real.dist_eq]
  have hroot := sqrt_sub_le_div hm (hlower w hw) (hlower z hz)
  have hcancel :
      (-Real.sqrt (r ^ 2 - quad2 (w₀ + w)) - a) -
          (-Real.sqrt (r ^ 2 - quad2 (w₀ + z)) - a) =
        -(Real.sqrt (r ^ 2 - quad2 (w₀ + w)) -
          Real.sqrt (r ^ 2 - quad2 (w₀ + z))) := by ring
  rw [hcancel, abs_neg]
  calc
    |Real.sqrt (r ^ 2 - quad2 (w₀ + w)) -
          Real.sqrt (r ^ 2 - quad2 (w₀ + z))| ≤
        |(r ^ 2 - quad2 (w₀ + w)) -
          (r ^ 2 - quad2 (w₀ + z))| / (2 * Real.sqrt m) := hroot
    _ = |quad2 (w₀ + w) - quad2 (w₀ + z)| / (2 * Real.sqrt m) := by
      congr 1
      rw [show r ^ 2 - quad2 (w₀ + w) -
          (r ^ 2 - quad2 (w₀ + z)) =
          -(quad2 (w₀ + w) - quad2 (w₀ + z)) by ring, abs_neg]
    _ ≤ (L * ‖w - z‖) / (2 * Real.sqrt m) := by
      gcongr
      exact hquad w hw z hz
    _ = (L / (2 * Real.sqrt m)) * dist w z := by
      rw [dist_eq_norm]
      ring
    _ = ↑(Real.toNNReal (L / (2 * Real.sqrt m))) * dist w z := by
      rw [hcoe]

theorem isBoundedLipschitzDomain_vec3Ball :
    ∀ (c : Vec3) {r : ℝ}, 0 < r →
        IsBoundedLipschitzDomain (vec3Ball c r) := by
  intro c r hr
  refine ⟨isOpen_vec3Ball c, isBounded_vec3Ball c, ?_⟩
  intro x hx
  have hnorm : vec3EuclideanNorm (x - c) = r :=
    frontier_vec3Ball_norm c hx
  have hv : x - c ≠ 0 := by
    intro hzero
    rw [hzero, vec3EuclideanNorm_zero] at hnorm
    exact (ne_of_gt hr) hnorm.symm
  obtain ⟨k, hk⟩ := exists_ne_component (x - c) hv
  let negate : Bool := decide (0 < (x - c) k)
  let e : Vec3 ≃L[ℝ] Vec3 := coordinateChart k negate
  let a : ℝ := e (x - c) 2
  have ha : a < 0 := by
    by_cases hpos : 0 < (x - c) k
    · have hcoord : a = -((x - c) k) := by
        dsimp [a, e]
        have hxc : c k < x k := sub_pos.mp hpos
        by_cases hk2 : k = 2
        · subst k
          simp [coordinateChartLinear, negate, coordinatePermutation, negateLast, hxc]
        · simp [coordinateChartLinear, negate, coordinatePermutation, negateLast, hxc]
      rw [hcoord]
      exact neg_neg_of_pos hpos
    · have hneg : (x - c) k < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hk
      have hcoord : a = (x - c) k := by
        dsimp [a, e]
        have hxc : ¬c k < x k := fun h => hpos (sub_pos.mpr h)
        by_cases hk2 : k = 2
        · subst k
          simp [coordinateChartLinear, negate, coordinatePermutation, hxc]
        · simp [coordinateChartLinear, negate, coordinatePermutation, hxc]
      rw [hcoord]
      exact hneg
  let w₀ : Fin 2 → ℝ := fun j => e (x - c) j.castSucc
  let δ : ℝ := a ^ 2 / (16 * (r + 1))
  let m : ℝ := a ^ 2 / 2
  let S : Set (Fin 2 → ℝ) := Metric.closedBall 0 δ
  have hnorme : vec3EuclideanNorm (e (x - c)) = r := by
    rw [coordinateChart_vec3Norm, hnorm]
  have ha_le : -a ≤ r := by
    have hh := abs_apply_le_vec3EuclideanNorm (e (x - c)) 2
    calc
      -a = |e (x - c) 2| := by rw [abs_of_neg ha]
      _ ≤ vec3EuclideanNorm (e (x - c)) := hh
      _ = r := hnorme
  have hδ : 0 < δ := by
    dsimp [δ]
    have ha2 : 0 < a ^ 2 := sq_pos_of_neg ha
    positivity
  have hm : 0 < m := by
    dsimp [m]
    have ha2 : 0 < a ^ 2 := sq_pos_of_neg ha
    positivity
  have hδa : δ ≤ (-a) / 16 := by
    dsimp [δ]
    have hr1 : 0 < r + 1 := by linarith only [hr]
    have hma0 : 0 ≤ -a := neg_nonneg.mpr ha.le
    have hrel : (-a) / (r + 1) ≤ 1 := by
      apply (div_le_iff₀ hr1).2
      linarith only [ha_le]
    have hform : a ^ 2 / (16 * (r + 1)) =
        ((-a) / 16) * ((-a) / (r + 1)) := by
      field_simp
    rw [hform]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hrel (by positivity : 0 ≤ (-a) / 16)
  have hsplit : quad2 w₀ + a ^ 2 = r ^ 2 := by
    have hh := vec3EuclideanNorm_sq_split (e (x - c))
    rw [hnorme] at hh
    simpa [w₀, a, quad2, add_comm, add_left_comm, add_assoc] using hh.symm
  have hw₀ : ‖w₀‖ ≤ r := by
    rw [Pi.norm_def]
    have hnn : Finset.univ.sup (fun j : Fin 2 => ‖w₀ j‖₊) ≤
        (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro j hj
      have hj' := norm_le_pi_norm (e (x - c)) j.castSucc
      have he : ‖e (x - c)‖ ≤ r := by
        rw [← hnorme]
        exact norm_le_vec3EuclideanNorm _
      exact_mod_cast hj'.trans he
    exact_mod_cast hnn
  have hquad_lower : ∀ w ∈ S, m ≤ r ^ 2 - quad2 (w₀ + w) := by
    intro w hw
    have hw' : ‖w‖ ≤ δ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      simpa using hw
    have hq := quad2_sub_bound (w₀ + w) w₀
    have hsum : ‖w₀ + w‖ ≤ r + δ :=
      (norm_add_le _ _).trans (add_le_add hw₀ hw')
    have hdiff : ‖(w₀ + w) - w₀‖ = ‖w‖ := by
      congr 1
      ext j
      simp
    rw [hdiff] at hq
    have hq' : |quad2 (w₀ + w) - quad2 w₀| ≤
        2 * (r + δ + r) * δ := by
      calc
        |quad2 (w₀ + w) - quad2 w₀| ≤
            2 * (‖w₀ + w‖ + ‖w₀‖) * ‖w‖ := hq
        _ ≤ 2 * (r + δ + r) * δ := by gcongr
    have hδrel : δ * (16 * (r + 1)) = a ^ 2 := by
      dsimp [δ]
      field_simp
    have hqhalf : 2 * (r + δ + r) * δ ≤ a ^ 2 / 2 := by
      have hr0 : 0 ≤ r := hr.le
      have hδr : δ ≤ r / 16 := by
        exact hδa.trans (div_le_div_of_nonneg_right ha_le (by norm_num))
      have hrd : r * δ ≤ a ^ 2 / 16 := by
        nlinarith only [hδrel, hr0, hδ]
      have h2rδ : 2 * r + δ ≤ (33 / 16 : ℝ) * r := by
        nlinarith only [hr0, hδr]
      calc
        2 * (r + δ + r) * δ = 2 * (2 * r + δ) * δ := by ring
        _ ≤ 2 * ((33 / 16 : ℝ) * r) * δ := by
          gcongr
        _ = (33 / 8 : ℝ) * (r * δ) := by ring
        _ ≤ (33 / 8 : ℝ) * (a ^ 2 / 16) := by gcongr
        _ ≤ a ^ 2 / 2 := by nlinarith only [sq_nonneg a]
    have hqle : quad2 (w₀ + w) - quad2 w₀ ≤ a ^ 2 / 2 :=
      (le_abs_self _).trans (hq'.trans hqhalf)
    dsimp [m]
    linarith only [hsplit, hqle]
  have hquad_lip : ∀ w ∈ S, ∀ z ∈ S,
      |quad2 (w₀ + w) - quad2 (w₀ + z)| ≤
        2 * (r + δ + (r + δ)) * ‖w - z‖ := by
    intro w hw z hz
    have hw' : ‖w‖ ≤ δ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      simpa using hw
    have hz' : ‖z‖ ≤ δ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      simpa using hz
    have hw0w : ‖w₀ + w‖ ≤ r + δ :=
      (norm_add_le _ _).trans (add_le_add hw₀ hw')
    have hw0z : ‖w₀ + z‖ ≤ r + δ :=
      (norm_add_le _ _).trans (add_le_add hw₀ hz')
    have hq := quad2_sub_bound (w₀ + w) (w₀ + z)
    have hsum : ‖w₀ + w‖ + ‖w₀ + z‖ ≤ r + δ + (r + δ) :=
      add_le_add hw0w hw0z
    have hdiff : (w₀ + w) - (w₀ + z) = w - z := by
      ext j
      simp [Pi.add_apply, Pi.sub_apply]
    rw [hdiff] at hq
    calc
      |quad2 (w₀ + w) - quad2 (w₀ + z)| ≤
          2 * (‖w₀ + w‖ + ‖w₀ + z‖) * ‖w - z‖ := hq
      _ ≤ 2 * (r + δ + (r + δ)) * ‖w - z‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum (by positivity)) (norm_nonneg _)
  have hLip := sphere_graph_lipschitzOn_neg (r := r) (a := a) (m := m)
      (L := 2 * (r + δ + (r + δ))) w₀ S hm (by positivity) hquad_lower hquad_lip
  obtain ⟨g, hg, hgS⟩ := hLip.extend_real
  refine ⟨e, δ, hδ, ?_⟩
  refine ⟨g, _, hg, ?_, ?_⟩
  · have hzeroS : (0 : Fin 2 → ℝ) ∈ S := by
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa using le_of_lt hδ
    rw [← hgS hzeroS]
    dsimp
    have hq0 : quad2 (w₀ + 0) = quad2 w₀ := by simp
    rw [hq0]
    have hsqa : Real.sqrt (r ^ 2 - quad2 w₀) = -a := by
      rw [show r ^ 2 - quad2 w₀ = a ^ 2 by linarith only [hsplit]]
      exact Real.sqrt_sq_eq_abs a ▸ abs_of_neg ha
    simp [hsqa]
  intro y hy
  have hy' : ‖y - x‖ < δ := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    simpa using hy
  let ξ : Vec3 := e (y - x)
  let w : Fin 2 → ℝ := fun j => ξ j.castSucc
  have hξ : ‖ξ‖ ≤ ‖y - x‖ := by
    simpa [ξ, e] using coordinateChart_norm_le k negate (y - x)
  have hwξ : ‖w‖ ≤ ‖ξ‖ := by
    rw [Pi.norm_def]
    have hnn : Finset.univ.sup (fun j : Fin 2 => ‖w j‖₊) ≤
        (⟨‖ξ‖, norm_nonneg ξ⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro j hj
      exact_mod_cast norm_le_pi_norm ξ j.castSucc
    exact_mod_cast hnn
  have hw : w ∈ S := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [sub_eq_add_neg] using hwξ.trans (hξ.trans (le_of_lt hy'))
  have hgw : g w = -Real.sqrt (r ^ 2 - quad2 (w₀ + w)) - a := by
    simpa using (hgS hw).symm
  have hlin : e (y - c) = e (y - x) + e (x - c) := by
    have hsub : y - c = (y - x) + (x - c) := by ring
    rw [hsub]
    exact e.map_add _ _
  have hfirst : (fun j : Fin 2 => e (y - c) j.castSucc) = w₀ + w := by
    funext j
    rw [hlin]
    simp [w, w₀, ξ]
  have hlast : e (y - c) 2 = a + ξ 2 := by
    rw [hlin]
    simp [a, ξ]
  have hxi2 : |ξ 2| ≤ ‖ξ‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ 2
  have hδlt : δ < -a := by
    exact hδa.trans_lt (by nlinarith only [ha])
  have hxi2lt : |ξ 2| < -a :=
    (hxi2.trans (hξ.trans (le_of_lt hy'))).trans_lt hδlt
  have hlastneg : a + ξ 2 < 0 := by
    nlinarith only [le_abs_self (ξ 2), hxi2lt]
  have hA : 0 ≤ r ^ 2 - quad2 (w₀ + w) := by
    exact le_of_lt (hm.trans_le (hquad_lower w hw))
  have hsplity : vec3EuclideanNorm (e (y - c)) ^ 2 =
      quad2 (w₀ + w) + (a + ξ 2) ^ 2 := by
    calc
      vec3EuclideanNorm (e (y - c)) ^ 2 =
          (∑ j : Fin 2, e (y - c) j.castSucc ^ 2) + e (y - c) 2 ^ 2 :=
        vec3EuclideanNorm_sq_split _
      _ = (∑ j : Fin 2, (w₀ + w) j ^ 2) + (a + ξ 2) ^ 2 := by
        rw [hlast]
        congr 1
        change (∑ j : Fin 2, (fun j => e (y - c) j.castSucc) j ^ 2) = _
        rw [hfirst]
      _ = quad2 (w₀ + w) + (a + ξ 2) ^ 2 := by rfl
  have hsq : vec3EuclideanNorm (y - c) < r ↔
      (a + ξ 2) ^ 2 < r ^ 2 - quad2 (w₀ + w) := by
    calc
      vec3EuclideanNorm (y - c) < r ↔
          vec3EuclideanNorm (e (y - c)) < r := by
            rw [coordinateChart_vec3Norm]
      _ ↔ vec3EuclideanNorm (e (y - c)) ^ 2 < r ^ 2 :=
        (sq_lt_sq₀ (vec3EuclideanNorm_nonneg _) hr.le).symm
      _ ↔ (a + ξ 2) ^ 2 < r ^ 2 - quad2 (w₀ + w) := by
        rw [hsplity]
        constructor
        · intro h
          linarith only [h]
        · intro h
          linarith only [h]
  have hsqrt : -Real.sqrt (r ^ 2 - quad2 (w₀ + w)) - a < ξ 2 ↔
      (a + ξ 2) ^ 2 < r ^ 2 - quad2 (w₀ + w) :=
    (by
      have hroot :
          -(a + ξ 2) < Real.sqrt (r ^ 2 - quad2 (w₀ + w)) ↔
            (-(a + ξ 2)) ^ 2 < r ^ 2 - quad2 (w₀ + w) :=
        Real.lt_sqrt (neg_nonneg.mpr hlastneg.le)
      constructor
      · intro h
        have h' : -(a + ξ 2) < Real.sqrt (r ^ 2 - quad2 (w₀ + w)) := by
          linarith only [h]
        have h'' := hroot.mp h'
        convert h'' using 1
        ring
      · intro h
        have h' := hroot.mpr (by
          convert h using 1
          ring)
        linarith only [h'])
  have hgraph : g w < ξ 2 ↔
      -Real.sqrt (r ^ 2 - quad2 (w₀ + w)) - a < ξ 2 := by
    rw [hgw]
  change vec3EuclideanNorm (y - c) < r ↔ g w < ξ 2
  exact hsq.trans (hsqrt.symm.trans hgraph.symm)

theorem IsBoundedLipschitzDomain_satisfiable :
    IsBoundedLipschitzDomain (vec3Ball (0 : Vec3) 1) := by
  exact isBoundedLipschitzDomain_vec3Ball (0 : Vec3) (r := 1) (by norm_num)

end CKN
