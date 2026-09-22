-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.ScaleBounds
import CKN.Foundation.Sobolev.Cutoff.BallTopology
import CKN.Setting.Examples.ShearCounterexample.ScaleDerivatives
import CKN.Setting.Examples.ShearCounterexample.LocalConstDeriv
import CKN.Setting.Examples.ShearCounterexample.ShearWeightedProfile
import CKN.Setting.Examples.ShearCounterexample.WeightSummable

/-! # Support estimates for the scaled shear profile. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

theorem shearScaleBump_tsupport_region {r : ℝ} (hr : 0 < r) :
    tsupport (shearScaleBump r) ⊆
      euclideanClosedBall (0 : Vec 2) r ×ˢ Icc (-(r ^ 2)) (r ^ 2) := by
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
  change closure (Function.support (shearScaleBump r)) ⊆ _
  exact closure_minimal hs' hclosed

def shearScaleCore (r : ℝ) : Set (Vec 2 × ℝ) :=
  euclideanBall (0 : Vec 2) (r / 2) ×ˢ Ioo (-(r ^ 2 / 8)) (r ^ 2 / 8)

private theorem shearScaleCore_open (r : ℝ) : IsOpen (shearScaleCore r) := by
  unfold shearScaleCore
  exact IsOpen.prod (isOpen_euclideanBall (0 : Vec 2) (r / 2)) isOpen_Ioo

private theorem shearScaleBump_eq_one_on_core {r : ℝ} (hr : 0 < r)
    {z : Vec 2 × ℝ} (hz : z ∈ shearScaleCore r) : shearScaleBump r z = 1 := by
  rcases hz with ⟨hx, ht⟩
  have hspace : canonicalBallCutoff (0 : Vec 2) (r / 2) r z.1 = 1 :=
    canonicalBallCutoff_eq_one_on_inner (by positivity) (by linarith only [hr]) hx
  have htime_mem : z.2 ∈ Icc ((r ^ 2 / 8) - (r / 2) ^ 2) (r ^ 2 / 8) := by
    constructor
    · have heq : (r ^ 2 / 8) - (r / 2) ^ 2 = -(r ^ 2 / 8) := by ring
      rw [heq]
      exact le_of_lt ht.1
    · exact le_of_lt ht.2
  have htime : timeCutoff (r ^ 2 / 8) (r / 2) r z.2 = 1 :=
    timeCutoff_eq_one_on (by positivity) (by linarith only [hr]) htime_mem
  simp [shearScaleBump, hspace, htime]

theorem shearScaleBump_derivatives_zero_on_core {r : ℝ} (hr : 0 < r)
    {z : Vec 2 × ℝ} (hz : z ∈ shearScaleCore r) :
    iteratedFDeriv ℝ 1 (shearScaleBump r) z = 0 ∧
      iteratedFDeriv ℝ 2 (shearScaleBump r) z = 0 :=
  iteratedFDeriv_eq_zero_on_open_const (shearScaleCore_open r)
    1 (fun y hy => shearScaleBump_eq_one_on_core (r := r) hr (z := y) hy) hz

private theorem shearSmallSupport_subset_core {s r : ℝ} (hs : 0 < s)
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


end CKN

namespace CKN

theorem shearSpatialFirstField_zero_on_core {r : ℝ} (hr : 0 < r)
    {i : Fin 2} {z : Vec 2 × ℝ} (hz : z ∈ shearScaleCore r) :
    shearSpatialFirstField r i z = 0 := by
  unfold shearSpatialFirstField
  rw [(shearScaleBump_derivatives_zero_on_core hr hz).1]
  simp

theorem shearSpatialSecondField_zero_on_core {r : ℝ} (hr : 0 < r)
    {i : Fin 2} {z : Vec 2 × ℝ} (hz : z ∈ shearScaleCore r) :
    shearSpatialSecondField r i z = 0 := by
  unfold shearSpatialSecondField
  rw [(shearScaleBump_derivatives_zero_on_core hr hz).2]
  simp

theorem shearTimeFirstField_zero_on_core {r : ℝ} (hr : 0 < r)
    {z : Vec 2 × ℝ} (hz : z ∈ shearScaleCore r) :
    shearTimeFirstField r z = 0 := by
  unfold shearTimeFirstField
  rw [(shearScaleBump_derivatives_zero_on_core hr hz).1]
  simp

def shearReducedForceCore (r : ℝ) (z : Vec 2 × ℝ) : ℝ :=
  shearTimeFirstField r z - shearSpatialSecondField r 0 z -
    shearSpatialSecondField r 1 z

def shearReducedForceTerm (n : ℕ) (z : Vec 2 × ℝ) : ℝ :=
  shearWeight n • shearReducedForceCore (shearScale n) z

def shearReducedForceSeries (z : Vec 2 × ℝ) : ℝ :=
  ∑' n, shearReducedForceTerm n z


private theorem shearSpatialSecond_nonzero_support {r : ℝ} {i : Fin 2}
    {z : Vec 2 × ℝ} (h : shearSpatialSecondField r i z ≠ 0) :
    z ∈ tsupport (shearScaleBump r) := by
  have hmap : iteratedFDeriv ℝ 2 (shearScaleBump r) z ≠ 0 := by
    intro hzero
    apply h
    simp [shearSpatialSecondField, hzero]
  have hs := subset_tsupport (iteratedFDeriv ℝ 2 (shearScaleBump r))
    (Function.mem_support.mpr hmap)
  exact (tsupport_iteratedFDeriv_subset 2) hs

private theorem shearTimeFirst_nonzero_support {r : ℝ} {z : Vec 2 × ℝ}
    (h : shearTimeFirstField r z ≠ 0) : z ∈ tsupport (shearScaleBump r) := by
  have hmap : iteratedFDeriv ℝ 1 (shearScaleBump r) z ≠ 0 := by
    intro hzero
    apply h
    simp [shearTimeFirstField, hzero]
  have hs := subset_tsupport (iteratedFDeriv ℝ 1 (shearScaleBump r))
    (Function.mem_support.mpr hmap)
  exact (tsupport_iteratedFDeriv_subset 1) hs

private theorem shearReducedForceCore_nonzero_support {r : ℝ} {z : Vec 2 × ℝ}
    (h : shearReducedForceCore r z ≠ 0) : z ∈ tsupport (shearScaleBump r) := by
  by_cases ht : shearTimeFirstField r z ≠ 0
  · exact shearTimeFirst_nonzero_support ht
  · by_cases h0 : shearSpatialSecondField r 0 z ≠ 0
    · exact shearSpatialSecond_nonzero_support h0
    · by_cases h1 : shearSpatialSecondField r 1 z ≠ 0
      · exact shearSpatialSecond_nonzero_support h1
      · simp [shearReducedForceCore, not_ne_iff.mp ht, not_ne_iff.mp h0,
          not_ne_iff.mp h1] at h

private theorem shearReducedForceTerm_nonzero_support {n : ℕ} {z : Vec 2 × ℝ}
    (h : shearReducedForceTerm n z ≠ 0) :
    z ∈ tsupport (shearScaleBump (shearScale n)) := by
  have hden : 0 < (n + 1 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hw : shearWeight n ≠ 0 := by
    unfold shearWeight
    exact ne_of_gt (one_div_pos.mpr hden)
  have hcore : shearReducedForceCore (shearScale n) z ≠ 0 := by
    intro hz
    apply h
    change shearWeight n * shearReducedForceCore (shearScale n) z = 0
    simp [hz]
  exact shearReducedForceCore_nonzero_support hcore

private theorem shearScale_succ_quarter_local (n : ℕ) :
    shearScale (n + 1) = shearScale n / 4 := by
  unfold shearScale
  rw [pow_succ]
  ring

private theorem shearScale_le_quarter_of_lt {m n : ℕ} (hmn : m < n) :
    shearScale n ≤ shearScale m / 4 := by
  have hsucc : m + 1 ≤ n := by omega
  have h := shearScale_antitone (m := m + 1) (n := n) hsucc
  rw [shearScale_succ_quarter_local] at h
  exact h

theorem shearReducedForceTerms_separated {m n : ℕ} (hmn : m < n)
    (z : Vec 2 × ℝ) :
    shearReducedForceTerm m z = 0 ∨ shearReducedForceTerm n z = 0 := by
  by_cases hn : shearReducedForceTerm n z = 0
  · exact Or.inr hn
  · have hsupport := shearReducedForceTerm_nonzero_support hn
    have hscale := shearScale_le_quarter_of_lt hmn
    have hcore : z ∈ shearScaleCore (shearScale m) :=
      shearSmallSupport_subset_core (shearScale_pos n) (shearScale_pos m) hscale hsupport
    have htime := shearTimeFirstField_zero_on_core (shearScale_pos m) hcore
    have h0 := shearSpatialSecondField_zero_on_core (shearScale_pos m) (i := 0) hcore
    have h1 := shearSpatialSecondField_zero_on_core (shearScale_pos m) (i := 1) hcore
    exact Or.inl (by simp [shearReducedForceTerm, shearReducedForceCore, htime, h0, h1])

end CKN
