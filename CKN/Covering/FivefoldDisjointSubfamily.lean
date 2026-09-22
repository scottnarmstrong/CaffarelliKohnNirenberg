-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Covering.Vitali

/-! # Fivefold covering by a selected disjoint family

The selected centres form a countable set, possibly empty or finite. Radii
are inherited from the prescribed family, so any property already established
for each original radius remains available after selection.
-/

open Set Metric

namespace CKN.Foundation.Parabolic

/-- A prescribed family of small parabolic balls inside an open neighbourhood
has a countable disjoint subfamily whose fivefold balls cover every original ball. -/
theorem exists_fivefold_disjoint_subfamily
    {E V : Set ParabolicPoint} {δ : ℝ}
    (hδ : 0 < δ) (hV : IsOpen V) (hEV : E ⊆ V)
    (r : ParabolicPoint → ℝ)
    (hr : ∀ z ∈ E, 0 < r z ∧ r z < δ ∧ Metric.ball z (r z) ⊆ V) :
    ∃ T : Set ParabolicPoint, T ⊆ E ∧ T.Countable ∧
      T.PairwiseDisjoint (fun z => Metric.ball z (r z)) ∧
      (∀ z ∈ E, ∃ w ∈ T, Metric.ball z (r z) ⊆ Metric.ball w (5 * r w)) ∧
      E ⊆ ⋃ w ∈ T, Metric.ball w (5 * r w) ∧
      ∀ w ∈ T, 0 < r w ∧ r w < δ ∧
        Metric.ball w (r w) ⊆ V ∧ 5 * r w < 5 * δ := by
  obtain ⟨T, hTE, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball E id r (max δ 0)
      (fun z hz => (hr z hz).2.1.le.trans (le_max_left δ 0)) 5 (by norm_num)
  simp only [id_eq] at hdisj hcover
  have hcount : T.Countable := hdisj.countable_of_isOpen (by
    intro w hw
    rw [← inter_eq_left.mpr (hr w (hTE hw)).2.2]
    exact isOpen_ball.inter hV) (by
      intro w hw
      have hne : (Metric.ball w (r w) ∩ V).Nonempty :=
        ⟨w, mem_ball_self (hr w (hTE hw)).1, hEV (hTE hw)⟩
      exact hne.mono inter_subset_left)
  refine ⟨T, hTE, hcount, hdisj, hcover, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := hcover z hz
    exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨hw, hzw (mem_ball_self (hr z hz).1)⟩⟩
  · intro w hw
    have hscale : max δ 0 = δ := max_eq_left hδ.le
    have hsmall : r w < max δ 0 := (hr w (hTE hw)).2.1.trans_le (le_max_left δ 0)
    rw [hscale] at hsmall
    exact ⟨(hr w (hTE hw)).1, hsmall, (hr w (hTE hw)).2.2,
      mul_lt_mul_of_pos_left hsmall (by norm_num)⟩

end CKN.Foundation.Parabolic
