-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# A fivefold parabolic covering selection

For an arbitrary admissible radius assignment on a set of space-time points,
the Vitali selection produces a countable pairwise disjoint subfamily of the
associated parabolic metric balls whose fivefold dilations still cover the
original set.  This is the selection display used by the covering step of
Theorem C; the measure estimate of `CKN/Foundation/Parabolic/Covering.lean`
consumes the same selection internally but does not export it.
-/

open scoped ENNReal NNReal Topology

open MeasureTheory Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Fivefold covering selection: from radii bounded by `δ` on `S` one extracts
a countable pairwise disjoint subfamily `D ⊆ S` of parabolic balls whose
fivefold dilations cover every ball of the original family, hence `S`. -/
theorem thmC_fivefold_cover_source
    (S : Set ParabolicPoint) (δ : ℝ) (_ : 0 < δ) (r : ParabolicPoint → ℝ)
    (hr : ∀ z ∈ S, 0 < r z ∧ r z < δ) :
    ∃ D : Set ParabolicPoint, D ⊆ S ∧ D.Countable ∧
      D.Pairwise (fun z w => Disjoint (Metric.ball z (r z)) (Metric.ball w (r w))) ∧
      (∀ z ∈ S, ∃ w ∈ D, Metric.ball z (r z) ⊆ Metric.ball w (5 * r w)) ∧
      S ⊆ ⋃ z ∈ D, Metric.ball z (5 * r z) := by
  obtain ⟨D, hDS, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (α := ParabolicPoint) S id r δ (fun a ha => (hr a ha).2.le) 5 (by norm_num)
  have hballs : ∀ z ∈ S, ∃ w ∈ D,
      Metric.ball z (r z) ⊆ Metric.ball w (5 * r w) := by
    intro z hz
    obtain ⟨w, hwD, hsub⟩ := hcover z hz
    exact ⟨w, hwD, hsub⟩
  refine ⟨D, hDS, ?_, hdisj, hballs, ?_⟩
  · exact hdisj.countable_of_isOpen (fun z _ => Metric.isOpen_ball)
      (fun z hz => ⟨z, Metric.mem_ball_self (hr z (hDS hz)).1⟩)
  · intro z hz
    obtain ⟨w, hwD, hsub⟩ := hballs z hz
    exact Set.mem_biUnion hwD (hsub (Metric.mem_ball_self (hr z hz).1))

end CKN.Foundation.Parabolic

end
