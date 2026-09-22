-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Integration.Average
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Filter
import Mathlib.MeasureTheory.Measure.Prod

/-!
# A non-integrability witness on parabolic boxes

This module records one negative fact about the parabolic volume measure: the
time-singular weight `(t - a)⁻¹` is not integrable on a spatial ball times a
time interval `(a, b)` that has `a` as a left endpoint.  The spatial factor
carries positive, finite volume, so Fubini reduces the claim to a purely
one-dimensional statement about `(t - a)⁻¹` near the singularity `a`, which is
Mathlib's standard non-integrability of the reciprocal.

The statement is a refutation witness: it shows that no argument may treat
such a weight as an integrable function on the box.
-/

open MeasureTheory MeasureTheory.Measure Set Filter

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- The time-singular weight `(t - a)⁻¹` is not integrable on the product of a
positive-radius Euclidean ball and a nondegenerate time interval whose left
endpoint is the singularity.  The ball provides a positive-measure spatial
factor, so almost every spatial slice would have to be integrable in time, and
the one-dimensional reciprocal is not. -/
theorem not_integrable_time_singular
    {x₀ : Vec3} {r a b : ℝ} (hr : 0 < r) (hab : a < b) :
    ¬ Integrable (fun z : ParabolicPoint => (z.2 - a)⁻¹)
      (volume.restrict (vec3Ball x₀ r ×ˢ Set.Ioo a b)) := by
  intro h
  -- Rewrite the product-restricted measure as a product of restricted measures.
  have h' : Integrable (fun z : Vec3 × ℝ => (z.2 - a)⁻¹)
      ((volume.restrict (vec3Ball x₀ r)).prod (volume.restrict (Set.Ioo a b))) := by
    rw [Measure.prod_restrict]
    exact h
  -- The spatial factor has nonzero total mass, so its almost-everywhere
  -- statements have a witness.
  have hμne : (volume.restrict (vec3Ball x₀ r)) ≠ 0 := by
    intro h0
    have h1 : (volume.restrict (vec3Ball x₀ r)) Set.univ = 0 := by
      rw [h0]
      simp
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h1
    exact absurd h1 (ne_of_gt (volume_vec3Ball_pos hr))
  have hae : ∀ᵐ x ∂(volume.restrict (vec3Ball x₀ r)),
      Integrable (fun t : ℝ => (t - a)⁻¹) (volume.restrict (Set.Ioo a b)) :=
    h'.prod_right_ae
  obtain ⟨_x, hx⟩ :=
    @Filter.Eventually.exists _ _ _ (ae_neBot.mpr hμne) hae
  -- The one-dimensional reciprocal is not interval integrable across its pole.
  have hii : IntervalIntegrable (fun t : ℝ => (t - a)⁻¹) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hx
  have hni : ¬ IntervalIntegrable (fun t : ℝ => (t - a)⁻¹) volume a b := by
    rw [intervalIntegrable_sub_inv_iff]
    simp [hab.ne, left_mem_uIcc]
  exact hni hii

end CKN.Foundation.Parabolic
