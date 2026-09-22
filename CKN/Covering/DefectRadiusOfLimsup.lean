-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Covering.TheoremCDefectFaithful

/-! # Radius selection from positive normalized mass

The lower limsup bound gives arbitrarily small cylinders carrying more than
half the threshold times their radius, as in `eq:defect-r`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN

/-- A positive lower bound for the normalized-mass limsup gives arbitrarily
small positive radii with mass strictly above half that threshold. -/
theorem defect_radius_of_limsup
    (g : ParabolicPoint → ℝ≥0∞) (z : ParabolicPoint) (ε : ℝ) (hε : 0 < ε)
    (hlim : ENNReal.ofReal ε ≤ Filter.limsup
      (fun r : ℝ => (ENNReal.ofReal r)⁻¹ * ∫⁻ w in parabolicCylinder z.1 z.2 r, g w)
      (nhdsWithin 0 (Ioi 0))) :
    ∀ τ : ℝ, 0 < τ → ∃ r : ℝ, 0 < r ∧ r < τ ∧
      ENNReal.ofReal (ε * r / 2) < ∫⁻ w in parabolicCylinder z.1 z.2 r, g w := by
  intro τ hτ
  let X : ℝ → ℝ≥0∞ := fun r => ∫⁻ w in parabolicCylinder z.1 z.2 r, g w
  let L : ℝ → ℝ≥0∞ := fun r => (ENNReal.ofReal r)⁻¹ * X r
  have hhalf : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε := by
    apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr
    linarith only [hε]
  have hsup : Filter.limsup L (𝓝[>] (0 : ℝ)) ≤ ⨆ r ∈ Ioo (0 : ℝ) τ, L r := by
    rw [Filter.limsup_eq_iInf_iSup]
    exact iInf₂_le _ (Ioo_mem_nhdsGT hτ)
  have hlt : ENNReal.ofReal (ε / 2) < ⨆ r ∈ Ioo (0 : ℝ) τ, L r :=
    (hhalf.trans_le hlim).trans_le hsup
  obtain ⟨r, hr⟩ := lt_iSup_iff.mp hlt
  obtain ⟨hrmem, hrlt⟩ := lt_iSup_iff.mp hr
  refine ⟨r, hrmem.1, hrmem.2, ?_⟩
  have hne : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hrmem.1).ne'
  have htop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmul := ENNReal.mul_lt_mul_left hne htop hrlt
  have hcancel : L r * ENNReal.ofReal r = X r := by
    dsimp only [L]
    rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hne htop, one_mul]
  have hleft : ENNReal.ofReal (ε / 2) * ENNReal.ofReal r =
      ENNReal.ofReal (ε * r / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hleft, hcancel] at hmul
  exact hmul

end CKN
