-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Cutoff.SpaceTime
import CKN.Foundation.Parabolic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Pointwise bounds for the scaled shear profile. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN
private def shearSpaceDilation (r : ℝ) : Vec 2 →L[ℝ] Vec 2 :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj (R := ℝ) i).smulRight (r⁻¹)


def shearParabolicDilation (r : ℝ) : Vec 2 × ℝ →L[ℝ] Vec 2 × ℝ :=
  ((shearSpaceDilation r).comp (ContinuousLinearMap.fst ℝ (Vec 2) ℝ)).prod
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (r⁻¹ ^ 2)).comp
      (ContinuousLinearMap.snd ℝ (Vec 2) ℝ))

theorem shearParabolicDilation_apply {r : ℝ} (z : Vec 2 × ℝ) :
    shearParabolicDilation r z = (fun i => z.1 i / r, z.2 / r ^ 2) := by
  ext <;> simp [shearParabolicDilation, shearSpaceDilation, div_eq_mul_inv,
    smul_eq_mul, ContinuousLinearMap.smulRight_apply, mul_comm]

theorem shearParabolicDilation_norm {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z : Vec 2 × ℝ) :
    ‖shearParabolicDilation r z‖ ≤ r⁻¹ ^ 2 * ‖z‖ := by
  rw [shearParabolicDilation_apply]
  rw [norm_prod_le_iff]
  constructor
  · have hz : ‖z.1‖ ≤ ‖z‖ := (norm_prod_le_iff.mp (le_refl ‖z‖)).1
    have hinv : 1 ≤ r⁻¹ := (one_le_inv₀ hr).2 hr1
    have hsq : r⁻¹ ≤ r⁻¹ ^ 2 := by nlinarith only [hinv, inv_pos.mpr hr]
    calc
      ‖fun i => z.1 i / r‖ ≤ r⁻¹ * ‖z.1‖ := by
        rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (norm_nonneg z.1))]
        intro i
        rw [Real.norm_eq_abs, div_eq_mul_inv, abs_mul,
          abs_of_pos (inv_pos.mpr hr)]
        have hi : |z.1 i| ≤ ‖z.1‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 i
        calc
          |z.1 i| * r⁻¹ ≤ ‖z.1‖ * r⁻¹ :=
            mul_le_mul_of_nonneg_right hi (by positivity)
          _ = r⁻¹ * ‖z.1‖ := by ring
      _ ≤ r⁻¹ * ‖z‖ := mul_le_mul_of_nonneg_left hz (by positivity)
      _ ≤ r⁻¹ ^ 2 * ‖z‖ := mul_le_mul_of_nonneg_right hsq (norm_nonneg z)
  · have hz : |z.2| ≤ ‖z‖ := by
      have h := (norm_prod_le_iff.mp (le_refl ‖z‖)).2
      simpa only [Real.norm_eq_abs] using h
    rw [Real.norm_eq_abs, div_eq_mul_inv, abs_mul,
      abs_of_pos (inv_pos.mpr (sq_pos_of_pos hr)), ← inv_pow]
    calc
      |z.2| * r⁻¹ ^ 2 ≤ ‖z‖ * r⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right hz (by positivity)
      _ = r⁻¹ ^ 2 * ‖z‖ := by ring

private theorem shearDilation_fderiv (r : ℝ) :
    fderiv ℝ (shearParabolicDilation r) = fun _ => shearParabolicDilation r := by
  funext z
  exact (shearParabolicDilation r).fderiv

theorem shearDilation_iterated_bound {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 2) (z : Vec 2 × ℝ) :
    ‖iteratedFDeriv ℝ k (shearParabolicDilation r) z‖ ≤ (r⁻¹ ^ 2) ^ k := by
  have hD : ‖shearParabolicDilation r‖ ≤ r⁻¹ ^ 2 :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (shearParabolicDilation_norm hr hr1)
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      rw [norm_iteratedFDeriv_one, shearDilation_fderiv]
      simpa only [Nat.zero_add, pow_one] using hD
    | succ k =>
      have hk3 : k + 1 ≠ 0 := by omega
      rw [← norm_iteratedFDeriv_fderiv, shearDilation_fderiv,
        iteratedFDeriv_const_of_ne hk3]
      have hnonneg : 0 ≤ (r⁻¹ ^ 2) ^ (k + 1 + 1) :=
        pow_nonneg (by positivity) _
      simpa [shearDilation_fderiv, iteratedFDeriv_const_of_ne hk3] using hnonneg

def shearUnitBump (z : Vec 2 × ℝ) : ℝ :=
  spaceTimeCutoff (0 : Vec 2) (1 / 8) (1 / 2) 1 z

theorem shearUnitBump_smooth : ContDiff ℝ (⊤ : ℕ∞) shearUnitBump := by
  unfold shearUnitBump
  exact spaceTimeCutoff_smooth 0 (1 / 8) (1 / 2) 1 (by norm_num) (by norm_num)

private theorem shearUnitBump_compact : HasCompactSupport shearUnitBump := by
  have hs0 : Function.support shearUnitBump ⊆
      euclideanBall (0 : Vec 2) 1 ×ˢ Ioo (-1) 1 := by
    unfold shearUnitBump
    have h := spaceTimeCutoff_support_subset
      (x₀ := (0 : Vec 2)) (t₀ := (1 / 8 : ℝ))
      (r := (1 / 2 : ℝ)) (R := 1) (by norm_num) (by norm_num)
    intro z hz
    refine ⟨h hz |>.1, ?_⟩
    rcases (h hz).2 with ⟨htl, htu⟩
    constructor <;> norm_num at * <;> linarith only [htl, htu]
  have hclosed : IsClosed (euclideanClosedBall (0 : Vec 2) 1 ×ˢ
      Icc (-1 : ℝ) 1) :=
    (isClosed_euclideanClosedBall (0 : Vec 2) 1).prod isClosed_Icc
  have hs1 : Function.support shearUnitBump ⊆
      euclideanClosedBall (0 : Vec 2) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    rcases hs0 hz with ⟨hx, ht⟩
    refine ⟨?_, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩
    change euclideanSqDist z.1 0 < 1 ^ 2 at hx
    change euclideanSqDist z.1 0 ≤ 1 ^ 2
    exact hx.le
  have hsub : tsupport shearUnitBump ⊆
      euclideanClosedBall (0 : Vec 2) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    change closure (Function.support shearUnitBump) ⊆ _
    exact closure_minimal hs1 hclosed
  change IsCompact (tsupport shearUnitBump)
  apply (isCompact_euclideanClosedBall (0 : Vec 2) (by norm_num)).prod isCompact_Icc
    |>.of_isClosed_subset (isClosed_tsupport shearUnitBump) hsub

theorem shearUnitBump_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ i shearUnitBump z‖ ≤ C := by
  exact shearUnitBump_compact.exists_bound_iteratedFDeriv shearUnitBump_smooth 2



private def shearTimeCore (t : ℝ) : ℝ :=
  smoothTransitionProfile ((t + 1 / 2) / (3 / 8)) *
    smoothTransitionProfile ((1 / 2 - t) / (3 / 8))

def shearScaleBump (r : ℝ) (z : Vec 2 × ℝ) : ℝ :=
  canonicalBallCutoff (0 : Vec 2) (r / 2) r z.1 *
    timeCutoff (r ^ 2 / 8) (r / 2) r z.2

private theorem shearTimeCutoff_scale {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    timeCutoff (r ^ 2 / 8) (r / 2) r t = shearTimeCore (t / r ^ 2) := by
  unfold shearTimeCore
  change smoothTransitionProfile
      ((t - (r ^ 2 / 8 - r ^ 2 + ((r ^ 2 - (r / 2) ^ 2) / 2))) /
        ((r ^ 2 - (r / 2) ^ 2) / 2)) *
      smoothTransitionProfile
        ((r ^ 2 / 8 + (r ^ 2 - (r / 2) ^ 2) / 2 - t) /
          ((r ^ 2 - (r / 2) ^ 2) / 2)) = _
  congr 2 <;> field_simp [hr] <;> ring

private theorem shearSpaceCutoff_scale {r : ℝ} (hr : r ≠ 0) (x : Vec 2) :
    canonicalBallCutoff (0 : Vec 2) (r / 2) r x =
      canonicalBallCutoff 0 (1 / 2) 1 (fun i => x i / r) := by
  have hvec : (fun i : Fin 2 => x i / r) = r⁻¹ • x := by
    funext i
    simp [div_eq_mul_inv, smul_eq_mul]
    ring
  have hdist : euclideanSqDist (fun i : Fin 2 => x i / r) 0 =
      r⁻¹ ^ 2 * euclideanSqDist x 0 := by
    rw [hvec]
    simp [euclideanSqDist, vecNormSq_smul]
  unfold canonicalBallCutoff
  apply congrArg smoothTransitionProfile
  unfold ballCutoffArgument ballCutoffMidRadius
  rw [hdist]
  field_simp [hr]

theorem shearScaleBump_scale {r : ℝ} (hr : r ≠ 0) (z : Vec 2 × ℝ) :
    shearScaleBump r z = shearUnitBump (shearParabolicDilation r z) := by
  rw [shearScaleBump, shearParabolicDilation_apply, shearSpaceCutoff_scale hr]
  change canonicalBallCutoff 0 (1 / 2) 1 (fun i => z.1 i / r) *
      timeCutoff (r ^ 2 / 8) (r / 2) r z.2 =
    canonicalBallCutoff 0 (1 / 2) 1 (fun i => z.1 i / r) *
      timeCutoff (1 / 8) (1 / 2) 1 (z.2 / r ^ 2)
  rw [shearTimeCutoff_scale hr]
  apply congrArg (fun y : ℝ =>
    canonicalBallCutoff 0 (1 / 2) 1 (fun i => z.1 i / r) * y)
  simpa using (shearTimeCutoff_scale (r := 1) (by norm_num) (z.2 / r ^ 2)).symm

theorem shearParabolicDilation_smooth (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (shearParabolicDilation r) := by
  fun_prop

theorem shearScaleBump_iteratedFDeriv_bound {r C : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1)
    (hUnit : ∀ i ≤ 2, ∀ z,
      ‖iteratedFDeriv ℝ i shearUnitBump z‖ ≤ C)
    (k : ℕ) (hk : k ≤ 2) (z : Vec 2 × ℝ) :
    ‖iteratedFDeriv ℝ k (shearScaleBump r) z‖ ≤
      (k.factorial : ℝ) * C * (r⁻¹ ^ 2) ^ k := by
  have hcomp : (shearScaleBump r) = shearUnitBump ∘ shearParabolicDilation r := by
    funext z
    exact shearScaleBump_scale (ne_of_gt hr) z
  rw [hcomp]
  have hbound := norm_iteratedFDeriv_comp_le (n := k) shearUnitBump_smooth
    (shearParabolicDilation_smooth r) (by simp) z
    (C := C) (D := r⁻¹ ^ 2)
    (fun i hi => hUnit i (le_trans hi hk) (shearParabolicDilation r z))
    (fun i hi hile => shearDilation_iterated_bound hr hr1 i hi
      (le_trans hile hk) z)
  exact hbound


















def shearProfileBox (r : ℝ) : Set (Vec 2 × ℝ) :=
  (Set.univ.pi fun _ : Fin 2 => Ioo (-(2 * r)) (2 * r)) ×ˢ
    Ioo (-(2 * r ^ 2)) (2 * r ^ 2)

theorem shearScaleBump_support_box {r : ℝ} (hr : 0 < r) :
    tsupport (shearScaleBump r) ⊆ shearProfileBox r := by
  have hs : Function.support (shearScaleBump r) ⊆
      euclideanBall (0 : Vec 2) r ×ˢ Ioo (-(r ^ 2)) (r ^ 2) := by
    intro z hz
    have hspace : z.1 ∈ Function.support
        (canonicalBallCutoff (0 : Vec 2) (r / 2) r) := by
      apply Function.mem_support.mpr
      intro hzero
      apply hz
      simp [shearScaleBump, hzero]
    have hspace' := canonicalBallCutoff_tsupport_subset_outer
      (by positivity : 0 ≤ r / 2) (by linarith only [hr])
      (subset_tsupport (f := canonicalBallCutoff (0 : Vec 2) (r / 2) r) hspace)
    have htime : z.2 ∈ Function.support (timeCutoff (r ^ 2 / 8) (r / 2) r) := by
      apply Function.mem_support.mpr
      intro hzero
      apply hz
      simp [shearScaleBump, hzero]
    have htime' := timeCutoff_support_subset
      (by positivity : 0 ≤ r / 2) (by linarith only [hr]) htime
    have hlow : -(r ^ 2) < z.2 := by nlinarith only [htime'.1, hr]
    have hupp : z.2 < r ^ 2 := by nlinarith only [htime'.2, hr]
    exact ⟨hspace', ⟨hlow, hupp⟩⟩
  have hs' : Function.support (shearScaleBump r) ⊆
      euclideanClosedBall (0 : Vec 2) r ×ˢ Icc (-(r ^ 2)) (r ^ 2) := by
    intro z hz
    rcases hs hz with ⟨hx, ht⟩
    refine ⟨?_, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩
    change euclideanSqDist z.1 0 < r ^ 2 at hx
    change euclideanSqDist z.1 0 ≤ r ^ 2
    exact hx.le
  have hclosed : IsClosed
      (euclideanClosedBall (0 : Vec 2) r ×ˢ Icc (-(r ^ 2)) (r ^ 2)) :=
    (isClosed_euclideanClosedBall (0 : Vec 2) r).prod isClosed_Icc
  have hts : tsupport (shearScaleBump r) ⊆
      euclideanClosedBall (0 : Vec 2) r ×ˢ Icc (-(r ^ 2)) (r ^ 2) := by
    change closure (Function.support (shearScaleBump r)) ⊆ _
    exact closure_minimal hs' hclosed
  unfold shearProfileBox
  intro z hz
  rcases hts hz with ⟨hx, ht⟩
  have hsq : euclideanSqDist z.1 0 ≤ r ^ 2 := by
    change euclideanSqDist z.1 0 ≤ r ^ 2 at hx
    exact hx
  change z.1 ∈ Set.univ.pi (fun _ : Fin 2 => Ioo (-(2 * r)) (2 * r)) ∧
    z.2 ∈ Ioo (-(2 * r ^ 2)) (2 * r ^ 2)
  constructor
  · rw [Set.mem_univ_pi]
    intro i
    have hcoord : (z.1 i) ^ 2 ≤ euclideanSqDist z.1 0 := by
      calc
        (z.1 i) ^ 2 ≤ ∑ j : Fin 2, (z.1 j) ^ 2 :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin 2 => (z.1 j) ^ 2)
            (fun j hj => sq_nonneg (z.1 j)) (Finset.mem_univ i)
        _ = euclideanSqDist z.1 0 := by
          simp [euclideanSqDist, vecNormSq, vecDot]
          ring
    have hcoord' : |z.1 i| ≤ r := by
      have hsq' : (z.1 i) ^ 2 ≤ r ^ 2 := hcoord.trans hsq
      exact abs_le_of_sq_le_sq (by simpa only [sq_abs] using hsq') (by positivity)
    have hlt : |z.1 i| < 2 * r := by linarith only [hcoord', hr]
    rw [Set.mem_Ioo]
    exact abs_lt.mp hlt
  · have habs : |z.2| ≤ r ^ 2 := abs_le.mpr ⟨by linarith only [ht.1], ht.2⟩
    have hlt : |z.2| < 2 * r ^ 2 := by nlinarith only [habs, hr]
    rw [Set.mem_Ioo]
    exact abs_lt.mp hlt

theorem volume_shearProfileBox {r : ℝ} (hr : 0 < r) :
    volume (shearProfileBox r) = ENNReal.ofReal (64 * r ^ 4) := by
  unfold shearProfileBox
  change (Measure.prod (volume : Measure (Vec 2)) (volume : Measure ℝ))
      ((Set.univ.pi fun _ : Fin 2 => Ioo (-(2 * r)) (2 * r)) ×ˢ
        Ioo (-(2 * r ^ 2)) (2 * r ^ 2)) = _
  rw [Measure.prod_prod, volume_pi_pi]
  simp only [Real.volume_Ioo]
  simp_rw [show 2 * r - -(2 * r) = 4 * r by ring,
    show 2 * r ^ 2 - -(2 * r ^ 2) = 4 * r ^ 2 by ring]
  rw [Fin.prod_univ_two]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * r)]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * r) * (4 * r))]
  congr 1
  ring

end CKN
