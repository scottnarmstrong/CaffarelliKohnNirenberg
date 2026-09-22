-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.DeltaPCentredMeanFreeSWS
import CKN.Pressure.IdentificationExtensionPairingKernel
import CKN.Pressure.IdentificationExtensionPairingWholeSpace
import CKN.Pressure.DecompositionSWS
import CKN.Foundation.Measure.SliceDistributionCore
import CKN.Foundation.Parabolic.BallBasics
import CKN.Setting.UTensor

/-!
# A common exceptional set for the mean-free pressure identity

The mean-free pressure identity is first obtained one test function at a time.
This module uses translated mollifier tests and the slice-distribution upgrade
to obtain one exceptional set of times that works for every smooth compactly
supported test in the spatial ball.
-/

open MeasureTheory MeasureTheory.Measure Set Filter Metric Topology
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

private abbrev DeltaPMeanFreeTestIndex := Sum (Fin 3 × Fin 3) (Fin 3)

private def deltaPMeanFreeCoeff
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ s : ℝ)
    (x : Vec3) (a : DeltaPMeanFreeTestIndex) : ℝ :=
  match a with
  | Sum.inl ij => (if ij.1 = ij.2 then p (x, s) else 0) -
      utensor u x₀ ρ s ij.1 ij.2 x
  | Sum.inr i => f (x, s) i

private def deltaPMeanFreeTransform (ψ : Vec3 → ℝ)
    (a : DeltaPMeanFreeTestIndex) (x : Vec3) : ℝ :=
  match a with
  | Sum.inl ij => mixedSecond ψ ij.1 ij.2 x
  | Sum.inr i => spatialDeriv ψ i x

private def deltaPMeanFreeKernel (n : ℕ)
    (a : DeltaPMeanFreeTestIndex) (x : Vec3) : ℝ :=
  match a with
  | Sum.inl ij => mixedSecond
      (mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n)) ij.1 ij.2 x
  | Sum.inr i => spatialDeriv
      (mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n)) i x

private theorem deltaPMeanFreeKernel_continuous (n : ℕ)
    (a : DeltaPMeanFreeTestIndex) : Continuous (deltaPMeanFreeKernel n a) := by
  cases a with
  | inl ij =>
      exact (contDiff_mixedSecond_smooth
        (mollifier_contDiff (d := 3) (n := ⊤) (sliceRadius_pos n))
        ij.1 ij.2).continuous
  | inr i =>
      exact (contDiff_spatialDeriv_smooth
        (mollifier_contDiff (d := 3) (n := ⊤) (sliceRadius_pos n)) i).continuous

private theorem deltaPMeanFreeKernel_eq_zero (n : ℕ)
    (a : DeltaPMeanFreeTestIndex) {z : Vec3}
    (hz : sliceRadius n < ‖z‖) : deltaPMeanFreeKernel n a z = 0 := by
  cases a with
  | inl ij =>
      change mixedSecond
        (mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n))
        ij.1 ij.2 z = 0
      exact mixedSecond_mollifier_eq_zero (sliceRadius_pos n) ij.1 ij.2 hz
  | inr i =>
      simpa [deltaPMeanFreeKernel, spatialDeriv] using
        fderiv_mollifier_apply_eq_zero (sliceRadius_pos n) hz i

private theorem deltaPMeanFree_mollify_identity {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ)
    (a : DeltaPMeanFreeTestIndex) (x : Vec3) :
    ∫ y, ψ y * deltaPMeanFreeKernel n a (x - y) ∂volume =
      mollify (deltaPMeanFreeTransform ψ a)
        (sliceRadius n) (sliceRadius_pos n) x := by
  cases a with
  | inl ij =>
      change ∫ y, ψ y * mixedSecond
        (mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n))
          ij.1 ij.2 (x - y) ∂volume =
        mollify (mixedSecond ψ ij.1 ij.2)
          (sliceRadius n) (sliceRadius_pos n) x
      exact integral_mul_mixedSecond_mollifier_sub hψ ij.1 ij.2
        (sliceRadius_pos n) x
  | inr i =>
      change ∫ y, ψ y *
        (fderiv ℝ (mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n))
          (x - y)) (basisVec i) ∂volume =
        mollify (fun z => (fderiv ℝ ψ z) (basisVec i))
          (sliceRadius n) (sliceRadius_pos n) x
      exact integral_mul_fderiv_mollifier_sub hψ i (sliceRadius_pos n) x

/-- The singly centred pressure identity holds off one null set of times,
simultaneously for every smooth compactly supported test function supported in
the spatial ball. -/
theorem pressure_delta_p_meanFree_ae_forall_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (vec3Ball x₀ ρ) ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I, ∀ ψ : Vec3 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ ρ →
      ∫ x in vec3Ball x₀ ρ, p (x, s) * spatialLaplacian ψ x =
        (∫ x in vec3Ball x₀ ρ, ∑ i, ∑ j,
          utensor u x₀ ρ s i j x * mixedSecond ψ i j x) -
          ∫ x in vec3Ball x₀ ρ, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
  classical
  let B : Set Vec3 := vec3Ball x₀ ρ
  have hBopen : IsOpen B := isOpen_vec3Ball x₀ ρ
  have hBcompact : IsCompact (closure B) := isCompact_closure_vec3Ball hρ
  obtain ⟨χ, V, hχ, hχc, hχΩ, hV, hBV, hχone⟩ :=
    exists_cutoff_eqOn_one_of_isCompact hBcompact hsol.1 hsub
  obtain ⟨Ω', hΩ'open, hχΩ', _hχΩ', hΩ'compact, hΩ'Ω, hLp⟩ :=
    decomposition_slice_integrability hsol hχc hχΩ hχc hχΩ
  set_option linter.style.haveILetI false in
    letI : IsFiniteMeasure (volume.restrict Ω') := by
      apply isFiniteMeasure_restrict.mpr
      exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
        hΩ'compact.measure_lt_top).ne
  have hBΩ' : B ⊆ Ω' := by
    intro x hx
    have hxV : x ∈ V := hBV (subset_closure hx)
    have hχx : χ x = 1 := hχone hxV
    apply hχΩ'
    exact subset_closure (by simp [Function.mem_support, hχx])
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense Vec3
  set_option linter.style.haveILetI false in
    letI : Countable Q := hQcount.to_subtype

  have hlocalCoeffs : ∀ᵐ s ∂volume.restrict I,
      ∀ a : DeltaPMeanFreeTestIndex,
        LocallyIntegrableOn (fun x => deltaPMeanFreeCoeff u p f x₀ ρ s x a)
          B volume := by
    filter_upwards [hLp] with s hs
    have huComp (i : Fin 3) : MemLp (fun x : Vec3 => u (x, s) i) 2
        (volume.restrict Ω') :=
      hs.1.continuousLinearMap_comp
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
    have huInt (i : Fin 3) : IntegrableOn (fun x : Vec3 => u (x, s) i)
        Ω' volume := (huComp i).integrable (by norm_num)
    have huuInt (i j : Fin 3) : IntegrableOn
        (fun x : Vec3 => u (x, s) i * u (x, s) j) Ω' volume :=
      (huComp i).integrable_mul (huComp j)
    have hpOn : IntegrableOn (fun x : Vec3 => p (x, s)) Ω' volume := hs.2.1
    have hpB : IntegrableOn (fun x : Vec3 => p (x, s)) B volume :=
      hpOn.mono_set hBΩ'
    have hfB (i : Fin 3) : IntegrableOn (fun x : Vec3 => f (x, s) i)
        B volume := by
      have hfi : IntegrableOn (fun x : Vec3 => f (x, s) i) Ω' volume := by
        apply hs.2.2.mono
          ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
            hs.2.2.aestronglyMeasurable)
        filter_upwards [] with x
        change ‖f (x, s) i‖ ≤ ‖f (x, s)‖
        rw [Pi.norm_def]
        simpa only [coe_nnnorm] using
          (NNReal.coe_le_coe.mpr
            (Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
              (f := fun b => ‖f (x, s) b‖₊) (Finset.mem_univ i)))
      exact hfi.mono_set hBΩ'
    have huB (i : Fin 3) : IntegrableOn (fun x : Vec3 => u (x, s) i)
        B volume := (huInt i).mono_set hBΩ'
    have huAvg (i : Fin 3) (c : ℝ) : IntegrableOn
        (fun x : Vec3 => u (x, s) i * c) B volume := by
      have h := (huB i).const_mul c
      exact h.congr (Filter.Eventually.of_forall fun x => by ring)
    have hU (i j : Fin 3) : IntegrableOn
        (fun x : Vec3 => utensor u x₀ ρ s i j x) B volume := by
      have hproduct : IntegrableOn
          (fun x : Vec3 => -(u (x, s) i * u (x, s) j) +
            u (x, s) i * average (volume.restrict B)
              (fun y : Vec3 => u (y, s) j)) B volume := by
        exact ((huuInt i j).mono_set hBΩ').neg.add
          (huAvg i (average (volume.restrict B)
            (fun y : Vec3 => u (y, s) j)))
      refine hproduct.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [utensor, meanFreeComponent]
      ring
    have hpLoc : LocallyIntegrableOn (fun x : Vec3 => p (x, s)) B volume :=
      hpB.locallyIntegrableOn
    have hULoc (i j : Fin 3) : LocallyIntegrableOn
        (fun x : Vec3 => utensor u x₀ ρ s i j x) B volume :=
      (hU i j).locallyIntegrableOn
    intro a
    cases a with
    | inl ij =>
        by_cases hij : ij.1 = ij.2
        · have hbase := hpLoc.sub (hULoc ij.2 ij.2)
          have hfun : (fun x : Vec3 => p (x, s) -
              utensor u x₀ ρ s ij.2 ij.2 x) =
              (fun x => deltaPMeanFreeCoeff u p f x₀ ρ s x (Sum.inl ij)) := by
            funext x
            simp [deltaPMeanFreeCoeff, hij]
          exact (locallyIntegrableOn_congr
            (Filter.Eventually.of_forall fun x => congrFun hfun x)).mp hbase
        · have hbase := MeasureTheory.locallyIntegrableOn_zero.sub
            (hULoc ij.1 ij.2)
          have hfun : ((fun _ : Vec3 => 0) -
              fun x : Vec3 => utensor u x₀ ρ s ij.1 ij.2 x) =
              (fun x => deltaPMeanFreeCoeff u p f x₀ ρ s x (Sum.inl ij)) := by
            funext x
            simp [deltaPMeanFreeCoeff, hij]
          exact (locallyIntegrableOn_congr
            (Filter.Eventually.of_forall fun x => congrFun hfun x)).mp hbase
    | inr i =>
        exact (hfB i).locallyIntegrableOn

  have hprodInt {g θ : Vec3 → ℝ}
      (hg : LocallyIntegrableOn g B volume) (hθ : Continuous θ)
      (hθc : HasCompactSupport θ) (hθB : tsupport θ ⊆ B) :
      IntegrableOn (fun x => g x * θ x) B volume := by
    have hgK : IntegrableOn g (tsupport θ) volume :=
      hg.integrableOn_compact_subset hθB hθc.isCompact
    obtain ⟨C, hC⟩ := hθc.exists_bound_of_continuous hθ
    have hmul : IntegrableOn (fun x => g x * θ x) (tsupport θ) volume :=
      hgK.mul_bdd hθ.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using hC x)
    have hfull : Integrable (fun x => g x * θ x) volume :=
      hmul.integrable_of_forall_notMem_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (f := θ) (fun h => hx h), mul_zero])
    exact hfull.integrableOn.mono_set (subset_univ B)

  have hzeroFamily : ∀ᵐ s ∂volume.restrict I,
      ∀ a : Q × ℕ, closedBall (a.1 : Vec3) (sliceRadius a.2) ⊆ B →
        ∫ x in B, ∑ i : DeltaPMeanFreeTestIndex,
          deltaPMeanFreeCoeff u p f x₀ ρ s x i *
            deltaPMeanFreeKernel a.2 i (x - (a.1 : Vec3)) = 0 := by
    rw [ae_all_iff]
    rintro ⟨⟨y, hyQ⟩, n⟩
    let ψ : Vec3 → ℝ := if h : closedBall y (sliceRadius n) ⊆ B then
      (fun z => mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n) (z - y))
      else 0
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      dsimp [ψ]
      split_ifs with h
      · exact contDiff_mollifier_sub (sliceRadius_pos n) y
      · exact contDiff_const
    have hψc : HasCompactSupport ψ := by
      dsimp [ψ]
      split_ifs with h
      · exact hasCompactSupport_mollifier_sub (sliceRadius_pos n) y
      · exact HasCompactSupport.zero
    have hψB : tsupport ψ ⊆ B := by
      by_cases h : closedBall y (sliceRadius n) ⊆ B
      · have hts : tsupport ψ = closedBall y (sliceRadius n) := by
          rw [show ψ = (fun z : Vec3 =>
              mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n) (z - y)) by
                simp [ψ, h],
            tsupport_mollifier_sub_eq (sliceRadius_pos n) y]
        rw [hts]
        exact h
      · simp [ψ, h]
    have hidentity := pressure_delta_p_meanFree_ae_of_sws hsol hρ hsub
      (ψ := ψ) hψ hψc hψB
    filter_upwards [hidentity, hLp, hlocalCoeffs] with s hid hs hcoeff
    intro hn
    have hpLoc : LocallyIntegrableOn (fun x : Vec3 => p (x, s)) B volume := by
      have hpOn : IntegrableOn (fun x : Vec3 => p (x, s)) Ω' volume := hs.2.1
      have hpB : IntegrableOn (fun x : Vec3 => p (x, s)) B volume :=
        hpOn.mono_set hBΩ'
      exact hpB.locallyIntegrableOn
    have hULoc (i j : Fin 3) : LocallyIntegrableOn
        (fun x : Vec3 => utensor u x₀ ρ s i j x) B volume := by
      have huComp (k : Fin 3) : MemLp (fun x : Vec3 => u (x, s) k) 2
          (volume.restrict Ω') :=
        hs.1.continuousLinearMap_comp
          (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)
      have huInt (k : Fin 3) : IntegrableOn
          (fun x : Vec3 => u (x, s) k) Ω' volume :=
        (huComp k).integrable (by norm_num)
      have huuInt : IntegrableOn
          (fun x : Vec3 => u (x, s) i * u (x, s) j) Ω' volume :=
        (huComp i).integrable_mul (huComp j)
      have huB (k : Fin 3) : IntegrableOn
          (fun x : Vec3 => u (x, s) k) B volume :=
        (huInt k).mono_set hBΩ'
      have huAvg (k : Fin 3) (c : ℝ) : IntegrableOn
          (fun x : Vec3 => u (x, s) k * c) B volume := by
        have h := (huB k).const_mul c
        exact h.congr (Filter.Eventually.of_forall fun x => by ring)
      have hproduct : IntegrableOn
          (fun x : Vec3 => -(u (x, s) i * u (x, s) j) +
            u (x, s) i * average (volume.restrict B)
              (fun y : Vec3 => u (y, s) j)) B volume := by
        exact (huuInt.mono_set hBΩ').neg.add
          (huAvg i (average (volume.restrict B)
            (fun y : Vec3 => u (y, s) j)))
      have hU : IntegrableOn (fun x => utensor u x₀ ρ s i j x) B volume :=
        hproduct.congr (Filter.Eventually.of_forall fun x => by
          simp only [utensor, meanFreeComponent]
          ring)
      exact hU.locallyIntegrableOn
    have hloc (a : DeltaPMeanFreeTestIndex) :
        LocallyIntegrableOn
          (fun x => deltaPMeanFreeCoeff u p f x₀ ρ s x a) B volume := hcoeff a
    have hpLap : IntegrableOn
        (fun x => p (x, s) * spatialLaplacian ψ x) B volume :=
      hprodInt hpLoc (contDiff_spatialLaplacian_smooth hψ).continuous
        (pressureCutoff_hasCompactSupport_spatialLaplacian hψc)
        (pressureCutoff_tsupport_spatialLaplacian_subset ψ |>.trans hψB)
    have hUterms (i j : Fin 3) : IntegrableOn
        (fun x => utensor u x₀ ρ s i j x * mixedSecond ψ i j x) B volume :=
      hprodInt (hULoc i j)
        (contDiff_mixedSecond_smooth hψ i j).continuous
        (pressureCutoff_hasCompactSupport_mixedSecond hψc i j)
        (pressureCutoff_tsupport_mixedSecond_subset ψ i j |>.trans hψB)
    have hUsum : IntegrableOn
        (fun x => ∑ i, ∑ j,
          utensor u x₀ ρ s i j x * mixedSecond ψ i j x) B volume := by
      change Integrable (∑ i, ∑ j,
        (fun x => utensor u x₀ ρ s i j x * mixedSecond ψ i j x))
        (volume.restrict B)
      exact integrable_finsetSum' Finset.univ fun i _ =>
        integrable_finsetSum' Finset.univ fun j _ => hUterms i j
    have hFterms (i : Fin 3) : IntegrableOn
        (fun x => f (x, s) i * spatialDeriv ψ i x) B volume :=
      hprodInt (hcoeff (Sum.inr i))
        (contDiff_spatialDeriv_smooth hψ i).continuous
        (pressureCutoff_hasCompactSupport_spatialDeriv hψc i)
        (pressureCutoff_tsupport_spatialDeriv_subset ψ i |>.trans hψB)
    have hFsum : IntegrableOn
        (fun x => ∑ i, f (x, s) i * spatialDeriv ψ i x) B volume := by
      change Integrable (∑ i,
        (fun x => f (x, s) i * spatialDeriv ψ i x)) (volume.restrict B)
      exact integrable_finsetSum' Finset.univ fun i _ => hFterms i
    have hpoint (x : Vec3) :
        (∑ a : DeltaPMeanFreeTestIndex,
          deltaPMeanFreeCoeff u p f x₀ ρ s x a *
            deltaPMeanFreeTransform ψ a x) =
          p (x, s) * spatialLaplacian ψ x -
            (∑ i, ∑ j,
              utensor u x₀ ρ s i j x * mixedSecond ψ i j x) +
          ∑ i, f (x, s) i * spatialDeriv ψ i x := by
      classical
      have hdiag (i : Fin 3) :
          ∑ j : Fin 3,
            (if i = j then p (x, s) else 0) * mixedSecond ψ i j x =
            p (x, s) * mixedSecond ψ i i x := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j hj hji
          have hne : i ≠ j := fun h => hji h.symm
          simp [hne]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      simp only [deltaPMeanFreeCoeff, deltaPMeanFreeTransform,
        Fintype.sum_sum_type, Fintype.sum_prod_type, sub_mul,
        Finset.sum_sub_distrib]
      simp_rw [hdiag]
      simp [spatialLaplacian, mixedSecond, Finset.mul_sum]
    have hsumInt :
        ∫ x in B, (∑ a : DeltaPMeanFreeTestIndex,
          deltaPMeanFreeCoeff u p f x₀ ρ s x a *
            deltaPMeanFreeTransform ψ a x) =
          (∫ x in B, p (x, s) * spatialLaplacian ψ x) -
            (∫ x in B, ∑ i, ∑ j,
              utensor u x₀ ρ s i j x * mixedSecond ψ i j x) +
            ∫ x in B, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
      calc
        _ = ∫ x in B, (p (x, s) * spatialLaplacian ψ x -
            (∑ i, ∑ j,
              utensor u x₀ ρ s i j x * mixedSecond ψ i j x) +
            ∑ i, f (x, s) i * spatialDeriv ψ i x) := by
              apply integral_congr_ae
              filter_upwards [] with x
              exact hpoint x
        _ = _ := by
          let gP : Vec3 → ℝ := fun x =>
            p ((x, s) : ParabolicPoint) * spatialLaplacian ψ x
          let gU : Vec3 → ℝ := fun x => ∑ i, ∑ j,
            utensor u x₀ ρ s i j x * mixedSecond ψ i j x
          let gF : Vec3 → ℝ := fun x => ∑ i,
            f ((x, s) : ParabolicPoint) i * spatialDeriv ψ i x
          have hadd :
              ∫ x in B, (gP x - gU x + gF x) =
                (∫ x in B, (gP x - gU x)) + ∫ x in B, gF x :=
            integral_add (hpLap.sub hUsum) hFsum
          have hsub : ∫ x in B, (gP x - gU x) =
              (∫ x in B, gP x) - ∫ x in B, gU x :=
            integral_sub hpLap hUsum
          simpa [gP, gU, gF] using hsub ▸ hadd
    have hsumZero :
        ∫ x in B, (∑ a : DeltaPMeanFreeTestIndex,
          deltaPMeanFreeCoeff u p f x₀ ρ s x a *
            deltaPMeanFreeTransform ψ a x) = 0 := by
      rw [hsumInt]
      linarith only [hid]
    have hkernelTransform : ∀ a : DeltaPMeanFreeTestIndex, ∀ x : Vec3,
        deltaPMeanFreeTransform ψ a x =
          deltaPMeanFreeKernel n a (x - y) := by
      have hψeq : ψ = fun z : Vec3 =>
          mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n) (z - y) := by
        simp [ψ, hn]
      intro a x
      cases a with
      | inl ij =>
          rw [hψeq]
          exact mixedSecond_sub_const (mollifier_contDiff (d := 3)
            (n := ⊤) (sliceRadius_pos n)) y x ij.1 ij.2
      | inr i =>
          rw [hψeq]
          exact spatialDeriv_sub_const
            (mollifier_contDiff (d := 3) (n := ⊤) (sliceRadius_pos n)
              |>.differentiable (by simp)) y x i
    have hKernelSum :
        ∫ x in B, (∑ a : DeltaPMeanFreeTestIndex,
          deltaPMeanFreeCoeff u p f x₀ ρ s x a *
            deltaPMeanFreeKernel n a (x - y)) = 0 := by
      calc
        _ = ∫ x in B, (∑ a : DeltaPMeanFreeTestIndex,
            deltaPMeanFreeCoeff u p f x₀ ρ s x a *
              deltaPMeanFreeTransform ψ a x) := by
              apply integral_congr_ae
              filter_upwards [] with x
              apply Finset.sum_congr rfl
              intro a ha
              rw [hkernelTransform a x]
        _ = 0 := hsumZero
    exact hKernelSum
  filter_upwards [hlocalCoeffs, hzeroFamily, hLp] with s hcoeff hzero hs
  intro ψ hψ hψc hψB
  have hcoeffSlice (a : DeltaPMeanFreeTestIndex) :
      LocallyIntegrableOn (fun x => deltaPMeanFreeCoeff u p f x₀ ρ s x a)
        B volume := hcoeff a
  have hpair := slice_pairing_zero_of_mollifier_family
    (d := 3) (ι := DeltaPMeanFreeTestIndex) (Ω := B) (Q := Q)
    (g := fun x a => deltaPMeanFreeCoeff u p f x₀ ρ s x a)
    (κ := deltaPMeanFreeKernel) (ψ := ψ)
    (T := deltaPMeanFreeTransform ψ)
    (hΩ := hBopen) (hQ := hQdense) (hg := hcoeffSlice)
    (hκcont := deltaPMeanFreeKernel_continuous)
    (hκzero := deltaPMeanFreeKernel_eq_zero)
    (hψcont := hψ.continuous) (hψc := hψc) (hψΩ := hψB)
    (hTcont := fun a => by
      cases a with
      | inl ij => exact (contDiff_mixedSecond_smooth hψ ij.1 ij.2).continuous
      | inr i => exact (contDiff_spatialDeriv_smooth hψ i).continuous)
    (hTsupp := fun a x hx => by
      cases a with
      | inl ij =>
          exact image_eq_zero_of_notMem_tsupport
            (fun h => hx (pressureCutoff_tsupport_mixedSecond_subset ψ
              ij.1 ij.2 h))
      | inr i =>
          exact image_eq_zero_of_notMem_tsupport
            (fun h => hx (pressureCutoff_tsupport_spatialDeriv_subset ψ i h)))
    (hid := fun (n : ℕ) (a : DeltaPMeanFreeTestIndex) (x : Vec3) =>
      deltaPMeanFree_mollify_identity hψ n a x)
    (hzero := fun y hy n hn => hzero ⟨⟨y, hy⟩, n⟩ hn)
  have hwhole : ∫ x in B, ∑ a : DeltaPMeanFreeTestIndex,
      deltaPMeanFreeCoeff u p f x₀ ρ s x a *
        deltaPMeanFreeTransform ψ a x = 0 := hpair
  have hpOn : IntegrableOn (fun x : Vec3 => p (x, s)) Ω' volume := hs.2.1
  have hpLoc : LocallyIntegrableOn (fun x : Vec3 => p (x, s)) B volume :=
    (hpOn.mono_set hBΩ').locallyIntegrableOn
  have hlocalIntegrability : ∀ i j : Fin 3,
      LocallyIntegrableOn (fun x : Vec3 => utensor u x₀ ρ s i j x) B volume := by
    intro i j
    have huComp (k : Fin 3) : MemLp (fun x : Vec3 => u (x, s) k) 2
        (volume.restrict Ω') :=
      hs.1.continuousLinearMap_comp
        (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)
    have huInt (k : Fin 3) : IntegrableOn
        (fun x : Vec3 => u (x, s) k) Ω' volume :=
      (huComp k).integrable (by norm_num)
    have huuInt : IntegrableOn
        (fun x : Vec3 => u (x, s) i * u (x, s) j) Ω' volume :=
      (huComp i).integrable_mul (huComp j)
    have huB (k : Fin 3) : IntegrableOn
        (fun x : Vec3 => u (x, s) k) B volume := (huInt k).mono_set hBΩ'
    have huAvg (k : Fin 3) (c : ℝ) : IntegrableOn
        (fun x : Vec3 => u (x, s) k * c) B volume := by
      have h := (huB k).const_mul c
      exact h.congr (Filter.Eventually.of_forall fun x => by ring)
    have hproduct : IntegrableOn
        (fun x : Vec3 => -(u (x, s) i * u (x, s) j) +
          u (x, s) i * average (volume.restrict B)
            (fun y : Vec3 => u (y, s) j)) B volume := by
      exact (huuInt.mono_set hBΩ').neg.add
        (huAvg i (average (volume.restrict B)
          (fun y : Vec3 => u (y, s) j)))
    have hU : IntegrableOn (fun x => utensor u x₀ ρ s i j x) B volume :=
      hproduct.congr (Filter.Eventually.of_forall fun x => by
        simp only [utensor, meanFreeComponent]
        ring)
    exact hU.locallyIntegrableOn
  have hpLap : IntegrableOn
      (fun x => p (x, s) * spatialLaplacian ψ x) B volume :=
    hprodInt hpLoc (contDiff_spatialLaplacian_smooth hψ).continuous
      (pressureCutoff_hasCompactSupport_spatialLaplacian hψc)
      (pressureCutoff_tsupport_spatialLaplacian_subset ψ |>.trans hψB)
  have hUterms (i j : Fin 3) : IntegrableOn
      (fun x => utensor u x₀ ρ s i j x * mixedSecond ψ i j x) B volume :=
    hprodInt (hlocalIntegrability i j)
      (contDiff_mixedSecond_smooth hψ i j).continuous
      (pressureCutoff_hasCompactSupport_mixedSecond hψc i j)
      (pressureCutoff_tsupport_mixedSecond_subset ψ i j |>.trans hψB)
  have hUsum : IntegrableOn
      (fun x => ∑ i, ∑ j,
        utensor u x₀ ρ s i j x * mixedSecond ψ i j x) B volume := by
    change Integrable (∑ i, ∑ j,
      (fun x => utensor u x₀ ρ s i j x * mixedSecond ψ i j x))
      (volume.restrict B)
    exact integrable_finsetSum' Finset.univ fun i _ =>
      integrable_finsetSum' Finset.univ fun j _ => hUterms i j
  have hFterms (i : Fin 3) : IntegrableOn
      (fun x => f (x, s) i * spatialDeriv ψ i x) B volume := by
    have h : LocallyIntegrableOn (fun x : Vec3 => f (x, s) i) B volume := by
      exact hcoeffSlice (Sum.inr i)
    exact hprodInt h (contDiff_spatialDeriv_smooth hψ i).continuous
      (pressureCutoff_hasCompactSupport_spatialDeriv hψc i)
      (pressureCutoff_tsupport_spatialDeriv_subset ψ i |>.trans hψB)
  have hFsum : IntegrableOn
      (fun x => ∑ i, f (x, s) i * spatialDeriv ψ i x) B volume := by
    change Integrable (∑ i,
      (fun x => f (x, s) i * spatialDeriv ψ i x)) (volume.restrict B)
    exact integrable_finsetSum' Finset.univ fun i _ => hFterms i
  have hpoint (x : Vec3) :
      (∑ a : DeltaPMeanFreeTestIndex,
        deltaPMeanFreeCoeff u p f x₀ ρ s x a *
          deltaPMeanFreeTransform ψ a x) =
        p (x, s) * spatialLaplacian ψ x -
          (∑ i, ∑ j,
            utensor u x₀ ρ s i j x * mixedSecond ψ i j x) +
          ∑ i, f (x, s) i * spatialDeriv ψ i x := by
    classical
    have hdiag (i : Fin 3) :
        ∑ j : Fin 3,
          (if i = j then p (x, s) else 0) * mixedSecond ψ i j x =
            p (x, s) * mixedSecond ψ i i x := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        have hne : i ≠ j := fun h => hji h.symm
        simp [hne]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    simp only [deltaPMeanFreeCoeff, deltaPMeanFreeTransform,
      Fintype.sum_sum_type, Fintype.sum_prod_type, sub_mul,
      Finset.sum_sub_distrib]
    simp_rw [hdiag]
    simp [spatialLaplacian, mixedSecond, Finset.mul_sum]
  have hsumInt :
      ∫ x in B, (∑ a : DeltaPMeanFreeTestIndex,
        deltaPMeanFreeCoeff u p f x₀ ρ s x a *
          deltaPMeanFreeTransform ψ a x) =
        (∫ x in B, p (x, s) * spatialLaplacian ψ x) -
          (∫ x in B, ∑ i, ∑ j,
            utensor u x₀ ρ s i j x * mixedSecond ψ i j x) +
          ∫ x in B, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
    calc
      _ = ∫ x in B, (p (x, s) * spatialLaplacian ψ x -
          (∑ i, ∑ j,
            utensor u x₀ ρ s i j x * mixedSecond ψ i j x) +
          ∑ i, f (x, s) i * spatialDeriv ψ i x) := by
            apply integral_congr_ae
            filter_upwards [] with x
            exact hpoint x
      _ = _ := by
        let gP : Vec3 → ℝ := fun x =>
          p ((x, s) : ParabolicPoint) * spatialLaplacian ψ x
        let gU : Vec3 → ℝ := fun x => ∑ i, ∑ j,
          utensor u x₀ ρ s i j x * mixedSecond ψ i j x
        let gF : Vec3 → ℝ := fun x => ∑ i,
          f ((x, s) : ParabolicPoint) i * spatialDeriv ψ i x
        have hadd :
            ∫ x in B, (gP x - gU x + gF x) =
              (∫ x in B, (gP x - gU x)) + ∫ x in B, gF x :=
          integral_add (hpLap.sub hUsum) hFsum
        have hsub : ∫ x in B, (gP x - gU x) =
            (∫ x in B, gP x) - ∫ x in B, gU x :=
          integral_sub hpLap hUsum
        simpa [gP, gU, gF] using hsub ▸ hadd
  have hdisplay :
      (∫ x in B, p (x, s) * spatialLaplacian ψ x) =
        (∫ x in B, ∑ i, ∑ j,
          utensor u x₀ ρ s i j x * mixedSecond ψ i j x) -
          ∫ x in B, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
    have hsumZero := hwhole
    rw [hsumInt] at hsumZero
    linarith only [hsumZero]
  exact hdisplay

end CKN

end
