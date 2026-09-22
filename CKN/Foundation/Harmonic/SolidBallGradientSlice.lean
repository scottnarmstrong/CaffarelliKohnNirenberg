-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.SolidBallMeanValueOrigin
import CKN.Foundation.Harmonic.SolidBallGradientParametric
import CKN.Foundation.Parabolic.BallBasics
import CKN.Foundation.Parabolic.BallDisplays
import CKN.Foundation.Sobolev.Cutoff.NormTriangle
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Set Filter
open scoped Topology BigOperators Interval
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

/-!
# Coordinate estimates from averages over solid balls

The derivative of a ball average can be estimated by slicing the ball along a coordinate.
The transverse sections are two-dimensional Euclidean balls.
-/

namespace CKN.Foundation.Harmonic

private abbrev Vec2 := Fin 2 → ℝ

private def sumSq2 (w : Vec2) : ℝ := ∑ j, w j ^ 2

private def sumSq3 (z : Vec3) : ℝ := ∑ k, z k ^ 2

private lemma vec3Norm_eq_vecNorm (x : Vec3) :
    vec3EuclideanNorm x = vecEuclideanNorm x := by
  simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

private lemma euclideanBall_to_closedBall {x : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x r ⊆ euclideanClosedBall x r := by
  intro y hy
  apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
  exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy |>.le

private def splitFin3 (i : Fin 3) : Vec3 ≃ᵐ ℝ × Vec2 :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i

private def splitBall (r : ℝ) : Set (ℝ × Vec2) :=
  {p | p.1 ^ 2 + sumSq2 p.2 < r ^ 2}

private lemma sumSq3_insertNth (i : Fin 3) (t : ℝ) (w : Vec2) :
    sumSq3 (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) = t ^ 2 + sumSq2 w := by
  unfold sumSq3 sumSq2
  have hsum := Fin.sum_univ_succAbove
    (f := fun k : Fin 3 =>
      (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w k) ^ 2) i
  rw [hsum]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

private lemma splitFin3_measurePreserving (i : Fin 3) :
    MeasurePreserving (splitFin3 i) (volume : Measure Vec3)
      ((volume : Measure ℝ).prod (volume : Measure Vec2)) := by
  simpa only [splitFin3, volume_pi] using
    (MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin 3 => (volume : Measure ℝ)) i)

private lemma splitBall_preimage (i : Fin 3) (r : ℝ) :
    splitFin3 i ⁻¹' splitBall r = euclideanBall (0 : Vec3) r := by
  ext z
  change (splitFin3 i z).1 ^ 2 + sumSq2 (splitFin3 i z).2 < r ^ 2 ↔ _
  rw [show splitFin3 i z =
      (z i, fun j : Fin 2 => z (i.succAbove j)) by rfl]
  simp only [sumSq2]
  change (z i) ^ 2 + (∑ j : Fin 2, z (i.succAbove j) ^ 2) < r ^ 2 ↔
    CKN.euclideanSqDist z 0 < r ^ 2
  rw [CKN.euclideanSqDist]
  change z i ^ 2 + (∑ j : Fin 2, z (i.succAbove j) ^ 2) < r ^ 2 ↔
    CKN.vecNormSq (z - 0) < r ^ 2
  rw [CKN.vecNormSq_eq_sum_sq]
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
  rw [Fin.sum_univ_succAbove (fun k : Fin 3 => z k ^ 2) i]

private lemma disk_volume_formula (r : ℝ) (hr : 0 < r) :
    volume {w : Vec2 | sumSq2 w < r ^ 2} =
      ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
  have hset : {w : Vec2 | sumSq2 w < r ^ 2} =
      {w : Vec2 | (∑ j : Fin 2, |w j| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < r} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    have hsum : ∑ j : Fin 2, |w j| ^ (2 : ℝ) = sumSq2 w := by
      simp [sumSq2, sq_abs]
    rw [hsum, ← Real.sqrt_eq_rpow]
    have hnonneg : 0 ≤ sumSq2 w := by
      change 0 ≤ ∑ j : Fin 2, w j ^ 2
      exact Finset.sum_nonneg fun j hj => sq_nonneg (w j)
    have hsqrt2 : (√(sumSq2 w)) ^ 2 = sumSq2 w := Real.sq_sqrt hnonneg
    have hiff : √(sumSq2 w) < r ↔ sumSq2 w < r ^ 2 := by
      calc
        √(sumSq2 w) < r ↔ (√(sumSq2 w)) ^ 2 < r ^ 2 :=
          (sq_lt_sq₀ (Real.sqrt_nonneg _) hr.le).symm
        _ ↔ sumSq2 w < r ^ 2 := by rw [hsqrt2]
    exact hiff.symm
  rw [hset, MeasureTheory.volume_sum_rpow_lt (ι := Fin 2) (p := (2 : ℝ))
    (by norm_num : 1 ≤ (2 : ℝ)) r]
  have hgamma :
      (2 * Real.Gamma (1 / (2 : ℝ) + 1)) ^ Fintype.card (Fin 2) /
          Real.Gamma ((Fintype.card (Fin 2) : ℝ) / 2 + 1) = Real.pi := by
    simp only [Fintype.card_fin]
    rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    norm_num
    rw [show 2 * (1 / 2 * √Real.pi) = √Real.pi by ring]
    rw [Real.sq_sqrt Real.pi_nonneg]
  rw [hgamma, Fintype.card_fin]

private lemma euclideanBall_zero_volume_toReal (r : ℝ) (hr : 0 < r) :
    (volume (euclideanBall (0 : Vec3) r)).toReal =
      (4 * Real.pi / 3) * r ^ 3 := by
  rw [euclideanBall_eq_vec3Ball hr, volume_vec3Ball_zero,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (le_of_lt hr),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

private lemma insertNth_affine (i : Fin 3) (x : Vec3) (t : ℝ) (w : Vec2) :
    x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w =
      (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 w) +
        t • CKN.basisVec i := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [CKN.basisVec]
  · obtain ⟨j, hj⟩ := (Fin.eq_self_or_eq_succAbove i k).resolve_left hk
    subst k
    have hne : i.succAbove j ≠ i := Fin.succAbove_ne i j
    simp [CKN.basisVec, hne]

private theorem hasDerivAt_line (f : Vec3 → ℝ) (x : Vec3) (i : Fin 3)
    (w : Vec2) (t : ℝ) (hf : DifferentiableAt ℝ f
      (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w)) :
    HasDerivAt (fun a => f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i a w))
      ((fderiv ℝ f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w))
        (CKN.basisVec i)) t := by
  let c : Vec3 := x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 w
  have hline : HasFDerivAt (fun a : ℝ => c + a • CKN.basisVec i)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (CKN.basisVec i)) t := by
    exact (hasFDerivAt_id t).smul_const (CKN.basisVec i) |>.const_add c
  have heq : (fun a : ℝ => x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i a w) =
      fun a => c + a • CKN.basisVec i := by
    funext a
    exact insertNth_affine i x a w
  have hline' : HasFDerivAt
      (fun a : ℝ => x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i a w)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (CKN.basisVec i)) t := by
    rw [heq]
    exact hline
  have hF : HasFDerivAt f (fderiv ℝ f
      (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w))
      (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) := hf.hasFDerivAt
  have hcomp := hF.comp t hline'
  have hder := hcomp.hasDerivAt
  convert hder using 1
  · rfl
  · simp [ContinuousLinearMap.comp_apply]

private lemma splitBall_section_eq_Ioo (r : ℝ) (w : Vec2)
    (hw : sumSq2 w < r ^ 2) :
    {t : ℝ | t ^ 2 + sumSq2 w < r ^ 2} =
      Set.Ioo (-(Real.sqrt (r ^ 2 - sumSq2 w)))
        (Real.sqrt (r ^ 2 - sumSq2 w)) := by
  have hD : 0 < r ^ 2 - sumSq2 w := by linarith only [hw]
  have hsqrt : 0 ≤ Real.sqrt (r ^ 2 - sumSq2 w) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (r ^ 2 - sumSq2 w)) ^ 2 = r ^ 2 - sumSq2 w :=
    Real.sq_sqrt hD.le
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  have hsplit : t ^ 2 + sumSq2 w < r ^ 2 ↔
      t ^ 2 < (Real.sqrt (r ^ 2 - sumSq2 w)) ^ 2 := by rw [hsq]; constructor <;> intro h <;> linarith only [h]
  rw [hsplit]
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  rw [← habs]
  have habslt : |t| < Real.sqrt (r ^ 2 - sumSq2 w) ↔
      -(Real.sqrt (r ^ 2 - sumSq2 w)) < t ∧
        t < Real.sqrt (r ^ 2 - sumSq2 w) := abs_lt
  exact (sq_lt_sq₀ (abs_nonneg t) hsqrt).trans habslt

private lemma endpoint_source_ball (x : Vec3) (s r : ℝ) (hs : 0 < s)
    (hr : 0 < r) (hrs : r < s) (i : Fin 3) (w : Vec2) (σ : ℝ)
    (hw : sumSq2 w < r ^ 2)
    (hσ : σ = Real.sqrt (r ^ 2 - sumSq2 w) ∨
      σ = -Real.sqrt (r ^ 2 - sumSq2 w)) :
    x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i σ w ∈ euclideanBall x s := by
  have hD : 0 < r ^ 2 - sumSq2 w := by linarith only [hw]
  have hσsq : σ ^ 2 = r ^ 2 - sumSq2 w := by
    rcases hσ with hσ | hσ
    · rw [hσ, Real.sq_sqrt hD.le]
    · rw [hσ, neg_sq, Real.sq_sqrt hD.le]
  have hdist : CKN.vecNormSq
      (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i σ w) = r ^ 2 := by
    rw [CKN.vecNormSq_eq_sum_sq]
    change sumSq3 (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i σ w) = r ^ 2
    rw [sumSq3_insertNth]
    unfold sumSq2 at hσsq ⊢
    rw [hσsq]
    ring
  have hnormsq : CKN.vecEuclideanNorm
      ((x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i σ w) - x) ^ 2 = r ^ 2 := by
    rw [CKN.vecEuclideanNorm_sq]
    rw [show (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i σ w) - x =
        Fin.insertNth (α := fun _ : Fin 3 => ℝ) i σ w by ext k; simp]
    exact hdist
  apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
  apply (sq_lt_sq₀ (CKN.vecEuclideanNorm_nonneg _) hs.le).1
  rw [hnormsq]
  exact (sq_lt_sq₀ hr.le hs.le).2 hrs

private lemma interval_partial_bound (U : Set Vec3) (hU : IsOpen U)
    (f : Vec3 → ℝ) (hf : ContDiffOn ℝ 1 f U) (x : Vec3)
    (s r M : ℝ) (hs : 0 < s) (hr : 0 < r) (hrs : r < s)
    (hsrc : euclideanBall x s ⊆ U)
    (hM : ∀ y ∈ euclideanBall x s, |f y| ≤ M)
    (i : Fin 3) (w : Vec2) (hw : sumSq2 w < r ^ 2) :
    |∫ t in (-(Real.sqrt (r ^ 2 - sumSq2 w)))..
        (Real.sqrt (r ^ 2 - sumSq2 w)),
        (fderiv ℝ f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w))
          (CKN.basisVec i)| ≤ 2 * M := by
  let a := Real.sqrt (r ^ 2 - sumSq2 w)
  have hD : 0 < r ^ 2 - sumSq2 w := by linarith only [hw]
  have ha : 0 < a := by dsimp [a]; exact Real.sqrt_pos.2 hD
  have ha_sq : a ^ 2 = r ^ 2 - sumSq2 w := by
    dsimp [a]
    exact Real.sq_sqrt hD.le
  have hI : (-a : ℝ) ≤ a := le_of_lt (neg_lt_self ha)
  have hderiv : ∀ t ∈ Set.uIcc (-a) a,
      HasDerivAt (fun b => f (x +
        Fin.insertNth (α := fun _ : Fin 3 => ℝ) i b w))
        ((fderiv ℝ f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w))
          (CKN.basisVec i)) t := by
    intro t ht
    have ht' : -a ≤ t ∧ t ≤ a := by
      simpa [Set.uIcc_of_le hI] using ht
    have htab : |t| ≤ a := abs_le.mpr ht'
    have ht2 : t ^ 2 ≤ a ^ 2 := by
      have hsq := (sq_le_sq₀ (abs_nonneg t) ha.le).2 htab
      simpa only [sq_abs] using hsq
    have hnormsq : vecEuclideanNorm
        ((x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) - x) ^ 2 ≤ r ^ 2 := by
      rw [show (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) - x =
          Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w by ext k; simp]
      rw [CKN.vecEuclideanNorm_sq]
      rw [CKN.vecNormSq_eq_sum_sq]
      change sumSq3 (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) ≤ r ^ 2
      rw [sumSq3_insertNth]
      have htq : t ^ 2 + sumSq2 w ≤ r ^ 2 := by rw [ha_sq] at ht2; linarith only [ht2]
      exact htq
    have hy : x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w ∈
        euclideanBall x s := by
      apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
      apply (sq_lt_sq₀ (CKN.vecEuclideanNorm_nonneg _ ) hs.le).1
      exact lt_of_le_of_lt hnormsq ((sq_lt_sq₀ hr.le hs.le).2 hrs)
    have hyU := hsrc hy
    have hfat := hf.contDiffAt (hU.mem_nhds hyU)
    exact hasDerivAt_line f x i w t (hfat.differentiableAt (by norm_num))
  have hlinecont : Continuous (fun t : ℝ =>
      x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) := by
    rw [show (fun t : ℝ => x +
        Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) =
        fun t => (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 w) +
          t • CKN.basisVec i from by funext t; exact insertNth_affine i x t w]
    fun_prop
  have hmap : ∀ t ∈ Set.uIcc (-a) a,
      x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w ∈ U := by
    intro t ht
    have ht' : -a ≤ t ∧ t ≤ a := by
      simpa [Set.uIcc_of_le hI] using ht
    have htab : |t| ≤ a := abs_le.mpr ht'
    have ht2 : t ^ 2 ≤ a ^ 2 := by
      have hsq := (sq_le_sq₀ (abs_nonneg t) ha.le).2 htab
      simpa only [sq_abs] using hsq
    have hnormsq : vecEuclideanNorm
        ((x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) - x) ^ 2 ≤ r ^ 2 := by
      rw [show (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) - x =
          Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w by ext k; simp]
      rw [CKN.vecEuclideanNorm_sq, CKN.vecNormSq_eq_sum_sq]
      change sumSq3 (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) ≤ r ^ 2
      rw [sumSq3_insertNth]
      have htq : t ^ 2 + sumSq2 w ≤ r ^ 2 := by rw [ha_sq] at ht2; linarith only [ht2]
      exact htq
    have hy : x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w ∈
        euclideanBall x s := by
      apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
      apply (sq_lt_sq₀ (CKN.vecEuclideanNorm_nonneg _) hs.le).1
      exact lt_of_le_of_lt hnormsq ((sq_lt_sq₀ hr.le hs.le).2 hrs)
    exact hsrc hy
  have hfderivcont : ContinuousOn (fderiv ℝ f) U :=
    hf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hpartialcont : ContinuousOn
      (fun t : ℝ => (fderiv ℝ f (x +
        Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w)) (CKN.basisVec i))
      (Set.uIcc (-a) a) := by
    exact (hfderivcont.comp hlinecont.continuousOn hmap).clm_apply
      continuousOn_const
  have hint : IntervalIntegrable (fun t : ℝ =>
      (fderiv ℝ f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w))
        (CKN.basisVec i)) volume (-a) a := hpartialcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have htop := endpoint_source_ball x s r hs hr hrs i w a hw
    (Or.inl rfl)
  have hbottom := endpoint_source_ball x s r hs hr hrs i w (-a) hw
    (Or.inr rfl)
  calc
    |∫ t in (-a)..a,
        (fderiv ℝ f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w))
          (CKN.basisVec i)| =
        |f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i a w) -
          f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i (-a) w)| := by rw [hFTC]
    _ ≤ |f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i a w)| +
        |f (x + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i (-a) w)| := abs_sub _ _
    _ ≤ M + M := add_le_add (hM _ htop) (hM _ hbottom)
    _ = 2 * M := by ring

private lemma coordinate_partial_integral_bound (U : Set Vec3) (hU : IsOpen U)
    (f : Vec3 → ℝ) (hf : ContDiffOn ℝ 1 f U) (x : Vec3)
    (s r M : ℝ) (hs : 0 < s) (hr : 0 < r) (hrs : r < s)
    (hsrc : euclideanBall x s ⊆ U)
    (hM : ∀ y ∈ euclideanBall x s, |f y| ≤ M) (i : Fin 3) :
    |∫ z in euclideanBall (0 : Vec3) r,
        (fderiv ℝ f (x + z)) (CKN.basisVec i)| ≤
      2 * M * (volume {w : Vec2 | sumSq2 w < r ^ 2}).toReal := by
  let B : Set Vec3 := euclideanBall 0 r
  let D : Set Vec2 := {w | sumSq2 w < r ^ 2}
  let d : Vec3 → ℝ := fun z => (fderiv ℝ f (x + z)) (CKN.basisVec i)
  let E : Vec3 ≃ᵐ ℝ × Vec2 := splitFin3 i
  have hBmeas : MeasurableSet B := measurableSet_euclideanBall 0 r
  have hDopen : IsOpen D := by
    change IsOpen {w : Vec2 | sumSq2 w < r ^ 2}
    have hsum : Continuous (fun w : Vec2 => sumSq2 w) := by
      unfold sumSq2
      fun_prop
    exact isOpen_lt hsum continuous_const
  have hDmeas : MeasurableSet D := hDopen.measurableSet
  have hK : IsCompact (euclideanClosedBall (0 : Vec3) r) :=
    CKN.isCompact_euclideanClosedBall 0 hr.le
  have hBK : B ⊆ euclideanClosedBall 0 r := by
    intro z hz
    apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
    exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hz |>.le
  have hKmap : ∀ z ∈ euclideanClosedBall (0 : Vec3) r, x + z ∈ U := by
    intro z hz
    have hzNorm : vecEuclideanNorm z ≤ r := by
      have hz' := (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).1 hz
      simpa only [sub_zero] using hz'
    have hy : x + z ∈ euclideanBall x s := by
      apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
      rw [show (x + z) - x = z by ext k; simp]
      exact lt_of_le_of_lt hzNorm hrs
    exact hsrc hy
  have hfderivcont : ContinuousOn (fderiv ℝ f) U :=
    hf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hDcont : ContinuousOn d (euclideanClosedBall (0 : Vec3) r) := by
    change ContinuousOn (fun z => (fderiv ℝ f (x + z)) (CKN.basisVec i)) _
    have hfield : ContinuousOn (fun z : Vec3 => fderiv ℝ f (x + z))
        (euclideanClosedBall 0 r) :=
      hfderivcont.comp (continuous_const.add continuous_id).continuousOn hKmap
    exact hfield.clm_apply continuousOn_const
  have hDintOnK : IntegrableOn d (euclideanClosedBall 0 r) volume :=
    hDcont.integrableOn_compact hK
  have hDintOn : IntegrableOn d B volume := hDintOnK.mono_set hBK
  have hDint : Integrable (B.indicator d) volume := hDintOn.integrable_indicator hBmeas
  have hEvol : MeasurePreserving E (volume : Measure Vec3)
      ((volume : Measure ℝ).prod (volume : Measure Vec2)) := splitFin3_measurePreserving i
  have hEintegral : ∫ p : ℝ × Vec2, (B.indicator d) (E.symm p) =
      ∫ z : Vec3, B.indicator d z :=
    hEvol.symm.integral_comp E.symm.measurableEmbedding (B.indicator d)
  have hEintegrable : Integrable (fun p : ℝ × Vec2 => (B.indicator d) (E.symm p))
      ((volume : Measure ℝ).prod (volume : Measure Vec2)) :=
    hEvol.symm.integrable_comp_of_integrable hDint
  have hFdef : (fun p : ℝ × Vec2 => (B.indicator d) (E.symm p)) =
      (splitBall r).indicator
        (fun p : ℝ × Vec2 => d (Fin.insertNth (α := fun _ : Fin 3 => ℝ)
          i p.1 p.2)) := by
    funext p
    rcases p with ⟨t, w⟩
    have hmem : E.symm (t, w) ∈ B ↔ (t, w) ∈ splitBall r := by
      have hmem' := congrArg (fun S : Set Vec3 => E.symm (t, w) ∈ S)
        (splitBall_preimage i r)
      simpa [B, E, splitFin3] using hmem'.symm
    have hsym : E.symm (t, w) =
        Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w := by
      change (Fin.insertNthEquiv (fun _ : Fin 3 => ℝ) i) (t, w) = _
      rfl
    simp only [Set.indicator]
    by_cases hleft : E.symm (t, w) ∈ B
    · have hp : (t, w) ∈ splitBall r := hmem.mp hleft
      simp [hleft, hp]
      rw [hsym]
    · have hp : (t, w) ∉ splitBall r := fun hp => hleft (hmem.mpr hp)
      simp [hleft, hp]
  let F : ℝ × Vec2 → ℝ := (splitBall r).indicator
    (fun p => d (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i p.1 p.2))
  have hFint : Integrable F ((volume : Measure ℝ).prod (volume : Measure Vec2)) := by
    change Integrable ((splitBall r).indicator
      (fun p : ℝ × Vec2 => d (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i p.1 p.2))) _
    rw [← hFdef]
    exact hEintegrable
  have hprod := MeasureTheory.integral_prod_symm F hFint
  let G : Vec2 → ℝ := fun w => ∫ t : ℝ, F (t, w)
  have houterInt : Integrable G volume := by
    change Integrable (fun w : Vec2 => ∫ t : ℝ, F (t, w)) volume
    exact hFint.integral_prod_right
  have hGbound : ∀ w ∈ D, |∫ t : ℝ, F (t, w)| ≤ 2 * M := by
    intro w hw
    change sumSq2 w < r ^ 2 at hw
    let a := Real.sqrt (r ^ 2 - sumSq2 w)
    have ha : 0 < a := by
      dsimp [a]
      exact Real.sqrt_pos.2 (by linarith only [hw])
    have hsection : {t : ℝ | t ^ 2 + sumSq2 w < r ^ 2} = Set.Ioo (-a) a := by
      dsimp [a]
      exact splitBall_section_eq_Ioo r w hw
    have hcond : ∀ t : ℝ, (t, w) ∈ splitBall r ↔ t ∈ Set.Ioo (-a) a := by
      intro t
      change t ^ 2 + sumSq2 w < r ^ 2 ↔ t ∈ Set.Ioo (-a) a
      have hsec := congrArg (fun S : Set ℝ => t ∈ S) hsection
      exact Iff.of_eq (by simpa only [Set.mem_ofPred_eq] using hsec)
    have hinner : ∫ t : ℝ, F (t, w) =
        ∫ t in Set.Ioo (-a) a,
          d (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) := by
      calc
        ∫ t : ℝ, F (t, w) =
            ∫ t : ℝ, (Set.Ioo (-a) a).indicator
              (fun t => d (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w)) t := by
                apply integral_congr_ae
                filter_upwards [] with t
                by_cases ht : (t, w) ∈ splitBall r
                · have hi : t ∈ Set.Ioo (-a) a := (hcond t).mp ht
                  simp [F, ht, hi]
                · have hi : t ∉ Set.Ioo (-a) a := fun hi => ht ((hcond t).mpr hi)
                  simp [F, ht, hi]
        _ = ∫ t in Set.Ioo (-a) a,
              d (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) := by
                rw [integral_indicator measurableSet_Ioo]
    have hI : (-a : ℝ) ≤ a := le_of_lt (neg_lt_self ha)
    have hset_interval : ∫ t in Set.Ioo (-a) a,
        d (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) =
        ∫ t in (-a)..a, d (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t w) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hI]
    have hbound := interval_partial_bound U hU f hf x s r M hs hr hrs hsrc hM i w hw
    rw [← hset_interval, ← hinner] at hbound
    exact hbound
  have hGzero : ∀ w ∉ D, (∫ t : ℝ, F (t, w)) = 0 := by
    intro w hw
    change ¬ sumSq2 w < r ^ 2 at hw
    have hzero : (fun t : ℝ => F (t, w)) =ᵐ[volume] fun _ => 0 := by
      filter_upwards [] with t
      have hnot : ¬ t ^ 2 + sumSq2 w < r ^ 2 := by
        intro h
        apply hw
        nlinarith only [h, sq_nonneg t]
      simp [F, splitBall, hnot]
    rw [integral_congr_ae hzero]
    simp
  have hGae : (fun w : Vec2 => D.indicator G w) =ᵐ[volume] G := by
    filter_upwards [] with w
    by_cases hw : w ∈ D
    · simp [hw]
    · simp [hw, G, hGzero w hw]
  have hGset : (∫ w : Vec2, G w) = (∫ w in D, G w) := by
    rw [← integral_indicator hDmeas]
    exact integral_congr_ae hGae.symm
  have hvolD : volume D < ⊤ := by
    rw [show D = {w : Vec2 | sumSq2 w < r ^ 2} by rfl, disk_volume_formula r hr]
    rw [pow_two]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top
  have hCae : ∀ᵐ w ∂volume.restrict D, ‖G w‖ ≤ 2 * M := by
    filter_upwards [ae_restrict_mem hDmeas] with w hw
    simpa only [Real.norm_eq_abs] using hGbound w hw
  have hsetBound := norm_setIntegral_le_of_norm_le_const_ae
    (μ := (volume : Measure Vec2)) (s := D) (f := G)
    hvolD hCae
  have hmain : |∫ w in D, G w| ≤
      2 * M * (volume D).toReal := by
    simpa only [Real.norm_eq_abs, Measure.real_def, smul_eq_mul, mul_comm] using hsetBound
  have hfinal : |∫ z in B, d z| ≤ 2 * M * (volume D).toReal := by
    calc
      |∫ z in B, d z| = |∫ z : Vec3, B.indicator d z| := by
        rw [← integral_indicator hBmeas]
      _ = |∫ p : ℝ × Vec2, (B.indicator d) (E.symm p)| := by
        rw [← hEintegral]
      _ = |∫ p : ℝ × Vec2, F p| := by
        rw [hFdef]
      _ = |∫ w : Vec2, G w| := by
        change |∫ p : ℝ × Vec2, F p| =
          |∫ w : Vec2, ∫ t : ℝ, F (t, w)|
        exact congrArg abs hprod
      _ = |∫ w in D, G w| := by
        rw [hGset]
      _ ≤ 2 * M * (volume D).toReal := hmain
  simpa only [B, D, d] using hfinal

/-- A `C²` harmonic function on an open neighbourhood of a closed solid ball satisfies the
interior gradient estimate with the source's constant `3 / s`. -/
theorem harmonic_solidBall_gradient_estimate
    (U : Set Vec3) (hU : IsOpen U) (f : Vec3 → ℝ)
    (hf : ContDiffOn ℝ 2 f U)
    (hHarm : ∀ y ∈ U, CKN.spatialLaplacian f y = 0)
    (x : Vec3) (s : ℝ) (hs : 0 < s)
    (hball : closure (euclideanBall x s) ⊆ U)
    (M : ℝ) (hM : ∀ y ∈ euclideanBall x s, |f y| ≤ M) :
    vec3EuclideanNorm (classicalGradient f x) ≤ 3 / s * M := by
  let r : ℝ := (9 / 10) * s
  let δ : ℝ := (s - r) / 2
  let B : Set Vec3 := euclideanBall (0 : Vec3) r
  let D : Set Vec2 := {w | sumSq2 w < r ^ 2}
  let c : ℝ := (volume B).toReal⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r < s := by dsimp [r]; nlinarith only [hs]
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hrs]
  have hδr : δ + r < s := by dsimp [δ]; linarith only [hrs]
  have hBmeas : MeasurableSet B := CKN.measurableSet_euclideanBall 0 r
  have hSopen : IsOpen (euclideanBall x δ) := CKN.isOpen_euclideanBall x δ
  have hxS : x ∈ euclideanBall x δ := by
    apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).2
    have hzero : vecEuclideanNorm (0 : Vec3) = 0 :=
      vecEuclideanNorm_eq_zero_iff.mpr rfl
    simpa [hzero] using hδ
  have hSnhds : euclideanBall x δ ∈ 𝓝 x := hSopen.mem_nhds hxS
  have hsrc : euclideanBall x s ⊆ U := by
    intro y hy
    exact hball (subset_closure hy)
  have hmeanAt (y : Vec3) (hy : y ∈ euclideanBall x δ) :
      f y = c * ∫ z in B, f (y + z) := by
    have hclosedY : closure (euclideanBall y r) ⊆ euclideanClosedBall y r :=
      closure_minimal (euclideanBall_to_closedBall hr)
        (CKN.isClosed_euclideanClosedBall y r)
    have hyx := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hδ).1 hy
    have hyBall : closure (euclideanBall y r) ⊆ U := by
      intro z hz
      have hzY := (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).1
        (hclosedY hz)
      have hadd : vecEuclideanNorm (z - x) ≤
          vecEuclideanNorm (z - y) + vecEuclideanNorm (y - x) := by
        rw [show z - x = (z - y) + (y - x) by abel]
        exact CKN.vecEuclideanNorm_add_le _ _
      have hzX : z ∈ euclideanBall x s := by
        apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
        exact hadd.trans_lt (by
          calc
            vecEuclideanNorm (z - y) + vecEuclideanNorm (y - x) < r + δ :=
              add_lt_add_of_le_of_lt hzY hyx
            _ < s := by simpa [add_comm] using hδr)
      exact hball (subset_closure hzX)
    have hmv := harmonic_solidBall_mean_value U hU f hf hHarm y r hr hyBall
    rw [euclideanBall_center_volume y hr,
      ← integral_translate_euclideanBall y hr] at hmv
    simpa [c, B, mul_comm] using hmv
  have hnear : f =ᶠ[𝓝 x]
      (fun y => c * ∫ z in B, f (y + z)) := by
    filter_upwards [hSnhds] with y hy
    exact hmeanAt y hy
  have hparam := hasFDerivAt_integral_fixed_euclideanBall hU hf
    (x := x) (s := s) (r := r) hs hr hrs hball
  have hderivMean : HasFDerivAt f
      (c • ∫ z in B, fderiv ℝ f (x + z)) x :=
    (hparam.const_mul c).congr_of_eventuallyEq hnear
  have hxBall : x ∈ euclideanBall x s := by
    apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
    have hzero : vecEuclideanNorm (0 : Vec3) = 0 :=
      vecEuclideanNorm_eq_zero_iff.mpr rfl
    simpa [hzero] using hs
  have hxU : x ∈ U := hball (subset_closure hxBall)
  have hfd : HasFDerivAt f (fderiv ℝ f x) x :=
    (hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hderivEq := hfd.unique hderivMean
  have hK : IsCompact (euclideanClosedBall (0 : Vec3) r) :=
    CKN.isCompact_euclideanClosedBall 0 hr.le
  have hBK : B ⊆ euclideanClosedBall 0 r := euclideanBall_to_closedBall hr
  have hderivCont : ContinuousOn (fderiv ℝ f) U :=
    hf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hmapK (z : Vec3) (hz : z ∈ euclideanClosedBall 0 r) :
      x + z ∈ U := by
    have hz0 := (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).1 hz
    have hballX : x + z ∈ euclideanBall x s := by
      apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).2
      have heq : x + z - x = z := by abel
      rw [heq]
      exact lt_of_le_of_lt (by simpa only [sub_zero] using hz0) hrs
    exact hball (subset_closure hballX)
  have hderivOnK : ContinuousOn
      (fun z : Vec3 => fderiv ℝ f (x + z)) (euclideanClosedBall 0 r) :=
    hderivCont.comp (continuous_const_add x).continuousOn hmapK
  have hderivIntK : IntegrableOn
      (fun z : Vec3 => fderiv ℝ f (x + z)) (euclideanClosedBall 0 r) volume :=
    hderivOnK.integrableOn_compact hK
  have hderivInt : Integrable
      (fun z : Vec3 => fderiv ℝ f (x + z)) (volume.restrict B) := by
    change IntegrableOn (fun z : Vec3 => fderiv ℝ f (x + z)) B volume
    exact hderivIntK.mono_set hBK
  have hcomponent (i : Fin 3) :
      (fderiv ℝ f x) (CKN.basisVec i) =
        c * ∫ z in B, (fderiv ℝ f (x + z)) (CKN.basisVec i) := by
    have happly := congrArg
      (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i)) hderivEq
    have hIntApply := ContinuousLinearMap.integral_apply hderivInt (CKN.basisVec i)
    simpa only [smul_apply, hIntApply, smul_eq_mul] using happly
  have hM0 : 0 ≤ M := by
    exact (abs_nonneg (f x)).trans (hM x hxBall)
  have hf1 : ContDiffOn ℝ 1 f U := hf.of_le (by norm_num)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hballVol : (volume B).toReal = (4 * Real.pi / 3) * r ^ 3 := by
    simpa [B] using euclideanBall_zero_volume_toReal r hr
  have hdiskVol : (volume D).toReal = Real.pi * r ^ 2 := by
    rw [show D = {w : Vec2 | sumSq2 w < r ^ 2} by rfl, disk_volume_formula r hr,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  have hscale : (volume B).toReal⁻¹ * (2 * M * (volume D).toReal) =
      (3 / (2 * r)) * M := by
    rw [hballVol, hdiskVol]
    field_simp [hr.ne', (ne_of_gt Real.pi_pos)]
    ring
  have hcoordinates : ∀ i : Fin 3,
      |classicalGradient f x i| ≤ (3 / (2 * r)) * M := by
    intro i
    have hraw := coordinate_partial_integral_bound U hU f hf1 x s r M
      hs hr hrs hsrc hM i
    rw [classicalGradient_apply, hcomponent i]
    calc
      |c * ∫ z in B, (fderiv ℝ f (x + z)) (CKN.basisVec i)| =
          c * |∫ z in B, (fderiv ℝ f (x + z)) (CKN.basisVec i)| := by
            rw [abs_mul, abs_of_nonneg hc]
      _ ≤ c * (2 * M * (volume D).toReal) :=
        mul_le_mul_of_nonneg_left hraw hc
      _ = (3 / (2 * r)) * M := hscale
  let C : ℝ := (3 / (2 * r)) * M
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcoordinateSq : ∀ i : Fin 3,
      (classicalGradient f x i) ^ 2 ≤ C ^ 2 := by
    intro i
    have habs := hcoordinates i
    have hsq := (sq_le_sq₀ (abs_nonneg (classicalGradient f x i)) hC).2 habs
    simpa only [sq_abs] using hsq
  have hsum : (∑ i : Fin 3, (classicalGradient f x i) ^ 2) ≤ 3 * C ^ 2 := by
    calc
      (∑ i : Fin 3, (classicalGradient f x i) ^ 2) ≤ ∑ _i : Fin 3, C ^ 2 :=
        Finset.sum_le_sum (fun i _ => hcoordinateSq i)
      _ = 3 * C ^ 2 := by simp
  have hnormSq : vecEuclideanNorm (classicalGradient f x) ^ 2 ≤
      (Real.sqrt 3 * C) ^ 2 := by
    rw [CKN.vecEuclideanNorm_sq, CKN.vecNormSq_eq_sum_sq]
    calc
      (∑ i : Fin 3, (classicalGradient f x i) ^ 2) ≤ 3 * C ^ 2 := hsum
      _ = (Real.sqrt 3) ^ 2 * C ^ 2 := by
        rw [Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
      _ = (Real.sqrt 3 * C) ^ 2 := by
        ring
  have hroot : 0 ≤ Real.sqrt 3 * C := mul_nonneg (Real.sqrt_nonneg _) hC
  have hnorm : vecEuclideanNorm (classicalGradient f x) ≤ Real.sqrt 3 * C :=
    (sq_le_sq₀ (vecEuclideanNorm_nonneg _) hroot).1 hnormSq
  have hsqrt3 : Real.sqrt 3 ≤ 9 / 5 := by
    have hsq := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
    nlinarith only [hsq, Real.sqrt_nonneg (3 : ℝ)]
  have hconst : Real.sqrt 3 * (3 / (2 * r)) ≤ 3 / s := by
    rw [show r = (9 / 10) * s by rfl]
    field_simp [hs.ne']
    nlinarith only [hsqrt3]
  calc
    vec3EuclideanNorm (classicalGradient f x) =
        vecEuclideanNorm (classicalGradient f x) := vec3Norm_eq_vecNorm _
    _ ≤ Real.sqrt 3 * C := hnorm
    _ = (Real.sqrt 3 * (3 / (2 * r))) * M := by dsimp [C]; ring
    _ ≤ 3 / s * M := mul_le_mul_of_nonneg_right hconst hM0

end CKN.Foundation.Harmonic
