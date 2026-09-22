-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.FullFields
import CKN.Setting.Examples.ShearCounterexample.ScaleSupport

/-! # Separation estimates for the reduced shear gradient. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

private theorem shearScale_succ_quarter_grad (n : ℕ) :
    shearScale (n + 1) = shearScale n / 4 := by
  unfold shearScale
  rw [pow_succ]
  ring

private theorem shearScale_le_quarter_grad {m n : ℕ} (hmn : m < n) :
    shearScale n ≤ shearScale m / 4 := by
  have hsucc : m + 1 ≤ n := by omega
  have h := shearScale_antitone (m := m + 1) (n := n) hsucc
  rw [shearScale_succ_quarter_grad] at h
  exact h

private theorem shearReducedGradientTerm_nonzero_support_grad
    {i : Fin 2} {n : ℕ} {z : Vec 2 × ℝ}
    (h : shearReducedGradientTerm i n z ≠ 0) :
    z ∈ tsupport (shearScaleBump (shearScale n)) := by
  have hmap : iteratedFDeriv ℝ 1 (shearScaleBump (shearScale n)) z ≠ 0 := by
    intro hz
    apply h
    simp [shearReducedGradientTerm, shearSpatialFirstField, hz]
  exact (tsupport_iteratedFDeriv_subset 1)
    (subset_tsupport (iteratedFDeriv ℝ 1 (shearScaleBump (shearScale n)))
      (Function.mem_support.mpr hmap))

private theorem shearSmallSupport_subset_core_grad {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) (hscale : s ≤ r / 4) :
    tsupport (shearScaleBump s) ⊆ shearScaleCore r := by
  intro z hz
  have hreg := shearScaleBump_tsupport_region hs hz
  rcases hreg with ⟨hx, ht⟩
  change euclideanSqDist z.1 0 ≤ s ^ 2 at hx
  have hsSq : s ^ 2 ≤ (r / 4) ^ 2 := by nlinarith only [hs.le, hscale]
  have hspace : euclideanSqDist z.1 0 < (r / 2) ^ 2 := by
    have hrad : (r / 4) ^ 2 < (r / 2) ^ 2 := by nlinarith only [hr]
    exact (hx.trans hsSq).trans_lt hrad
  have htimeAbs : |z.2| ≤ s ^ 2 := abs_le.mpr ⟨by linarith only [ht.1], ht.2⟩
  have htime : |z.2| < r ^ 2 / 8 := by nlinarith only [htimeAbs, hsSq, hr]
  change z.1 ∈ euclideanBall 0 (r / 2) ∧
    z.2 ∈ Ioo (-(r ^ 2 / 8)) (r ^ 2 / 8)
  constructor
  · change euclideanSqDist z.1 0 < (r / 2) ^ 2
    exact hspace
  · rw [Set.mem_Ioo]
    exact abs_lt.mp htime

theorem shearReducedGradientTerms_separated {i : Fin 2} {m n : ℕ}
    (hmn : m < n) (z : Vec 2 × ℝ) :
    shearReducedGradientTerm i m z = 0 ∨ shearReducedGradientTerm i n z = 0 := by
  by_cases hn : shearReducedGradientTerm i n z = 0
  · exact Or.inr hn
  · have hsupport := shearReducedGradientTerm_nonzero_support_grad hn
    have hscale := shearScale_le_quarter_grad hmn
    have hcore : z ∈ shearScaleCore (shearScale m) := by
      apply shearSmallSupport_subset_core_grad (shearScale_pos n) (shearScale_pos m)
      · nlinarith only [hscale]
      · exact hsupport
    left
    unfold shearReducedGradientTerm
    rw [shearSpatialFirstField_zero_on_core (shearScale_pos m) hcore]
    simp


theorem shearReducedGradientPartial_abs_le (i : Fin 2) (N : ℕ)
    (z : Vec 2 × ℝ) :
    ‖∑ n ∈ Finset.range N, shearReducedGradientTerm i n z‖ ≤
      ‖shearReducedGradientSeries i z‖ := by
  by_cases hex : ∃ n, shearReducedGradientTerm i n z ≠ 0
  · rcases hex with ⟨n, hn⟩
    have hzero (m : ℕ) (hm : m ≠ n) : shearReducedGradientTerm i m z = 0 := by
      rcases lt_or_gt_of_ne hm with hmn | hnm
      · rcases shearReducedGradientTerms_separated hmn z with hmz | hnz
        · exact hmz
        · exact (hn hnz).elim
      · rcases shearReducedGradientTerms_separated hnm z with hnz | hmz
        · exact (hn hnz).elim
        · exact hmz
    have hseries : shearReducedGradientSeries i z = shearReducedGradientTerm i n z := by
      unfold shearReducedGradientSeries
      exact tsum_eq_single n hzero
    rw [hseries]
    by_cases hnN : n < N
    · have hsum : (∑ m ∈ Finset.range N, shearReducedGradientTerm i m z) =
          shearReducedGradientTerm i n z := by
        exact Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr hnN)
          (fun m hm hmn => hzero m hmn)
      rw [hsum]
    · have hsum : (∑ m ∈ Finset.range N, shearReducedGradientTerm i m z) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        exact hzero m (by
          intro hmn
          subst m
          exact (hnN (Finset.mem_range.mp hm)).elim)
      rw [hsum]
      simp only [norm_zero]
      exact norm_nonneg _
  · have hzero (n : ℕ) : shearReducedGradientTerm i n z = 0 := by
      by_contra hn
      exact hex ⟨n, hn⟩
    have hs : shearReducedGradientSeries i z = 0 := by
      unfold shearReducedGradientSeries
      calc
        ∑' n, shearReducedGradientTerm i n z = ∑' n, (0 : ℝ) :=
          tsum_congr (fun n => hzero n)
        _ = 0 := by simp
    rw [hs]
    simp [hzero]

end CKN
