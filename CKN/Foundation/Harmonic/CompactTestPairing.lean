-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.NewtonianRadialSupport
import CKN.Foundation.Euclidean.SmoothIBP

open MeasureTheory
open scoped BigOperators Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Harmonic

/-!
# Harmonic pairing with compactly supported Laplacians

For a globally twice continuously differentiable harmonic function, pairing against the
Laplacian of a smooth compactly supported test function vanishes. The proof uses two
one-coordinate integration-by-parts identities.
-/

private lemma contDiff_spatialDeriv_of_one_more {u : Vec3 → ℝ} {n : ℕ}
    (hu : ContDiff ℝ (n + 1) u) (i : Fin 3) :
    ContDiff ℝ n (CKN.spatialDeriv u i) := by
  have hfd := hu.contDiff_fderiv_apply (m := n)
    (n := ((n + 1 : ℕ) : ℕ∞)) (by simp)
  have hc : ContDiff ℝ n (fun x : Vec3 => (x, CKN.basisVec i)) := by fun_prop
  change ContDiff ℝ n (fun x : Vec3 => (fderiv ℝ u x) (CKN.basisVec i))
  exact hfd.comp hc

private lemma support_spatialDeriv_subset {u : Vec3 → ℝ} (i : Fin 3) :
    Function.support (CKN.spatialDeriv u i) ⊆ tsupport u := by
  intro x hx
  by_contra hxt
  apply hx
  simp [CKN.spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt]

private lemma tsupport_spatialDeriv_subset {u : Vec3 → ℝ} (i : Fin 3) :
    tsupport (CKN.spatialDeriv u i) ⊆ tsupport u :=
  closure_minimal (support_spatialDeriv_subset i) (isClosed_tsupport u)

private lemma hasCompactSupport_spatialDeriv {u : Vec3 → ℝ}
    (hu : HasCompactSupport u) (i : Fin 3) :
    HasCompactSupport (CKN.spatialDeriv u i) :=
  HasCompactSupport.of_support_subset_isCompact hu.isCompact
    (support_spatialDeriv_subset i)

private lemma integral_mul_spatialDeriv_order1 {u φ : Vec3 → ℝ}
    (hu : ContDiff ℝ 1 u) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (i : Fin 3) :
    ∫ x, u x * CKN.spatialDeriv φ i x =
      -∫ x, CKN.spatialDeriv u i x * φ x := by
  have hφd : Continuous (CKN.spatialDeriv φ i) :=
    (contDiff_spatialDeriv_of_one_more hφ i).continuous
  have hud : Continuous (CKN.spatialDeriv u i) :=
    (contDiff_spatialDeriv_of_one_more hu i).continuous
  have hφdc := hasCompactSupport_spatialDeriv hφc i
  have hleft : Integrable (fun x => u x * CKN.spatialDeriv φ i x) volume :=
    (hu.continuous.mul hφd).integrable_of_hasCompactSupport
      (hφdc.mul_left (f := u))
  have hright : Integrable (fun x => CKN.spatialDeriv u i x * φ x) volume :=
    (hud.mul hφ.continuous).integrable_of_hasCompactSupport
      (hφc.mul_left (f := CKN.spatialDeriv u i))
  have hprod : Integrable (fun x => u x * φ x) volume :=
    (hu.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      (hφc.mul_left (f := u))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec3)) (v := CKN.basisVec i)
    hright hleft hprod
    (fun x _ => hu.differentiable (by norm_num) x)
    (fun x _ => hφ.differentiable (by norm_num) x)
  simpa only [CKN.spatialDeriv] using h

/-- A globally `C²` harmonic function pairs to zero with the Laplacian of any smooth
compactly supported test function whose support lies in the harmonic region. -/
theorem harmonic_laplacian_compact_test_pairing
    {H ψ : Vec3 → ℝ} (hH : ContDiff ℝ 2 H)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hHarm : ∀ x ∈ tsupport ψ, CKN.spatialLaplacian H x = 0) :
    ∫ x, H x * CKN.spatialLaplacian ψ x = 0 := by
  let h1 : ContDiff ℝ 1 H := hH.of_le (by norm_num)
  have hd1 (i : Fin 3) : ContDiff ℝ 1 (CKN.spatialDeriv H i) :=
    contDiff_spatialDeriv_of_one_more hH i
  have hψ1 (i : Fin 3) : ContDiff ℝ 1 (CKN.spatialDeriv ψ i) :=
    contDiff_spatialDeriv_of_one_more (hψ.of_le (by norm_num)) i
  have hψc1 (i : Fin 3) : HasCompactSupport (CKN.spatialDeriv ψ i) :=
    hasCompactSupport_spatialDeriv hψc i
  have hψc2 (i : Fin 3) : HasCompactSupport
      (CKN.spatialDeriv (CKN.spatialDeriv ψ i) i) :=
    hasCompactSupport_spatialDeriv (hψc1 i) i
  have hHlapCont : Continuous (CKN.spatialLaplacian H) := by
    unfold CKN.spatialLaplacian
    exact continuous_finsetSum _ (fun i hi =>
      (contDiff_spatialDeriv_of_one_more (hd1 i) i).continuous)
  have hψlapCont : Continuous (CKN.spatialLaplacian ψ) := by
    unfold CKN.spatialLaplacian
    exact continuous_finsetSum _ (fun i hi =>
      (contDiff_spatialDeriv_of_one_more (hψ1 i) i).continuous)
  have hleft : Integrable (fun x => H x * CKN.spatialLaplacian ψ x) volume := by
    apply (hH.continuous.mul hψlapCont).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    intro x hx
    by_contra hxt
    have hzero (i : Fin 3) : CKN.spatialDeriv
        (CKN.spatialDeriv ψ i) i x = 0 := by
      have hxi : x ∉ tsupport (CKN.spatialDeriv ψ i) :=
        fun h => hxt (tsupport_spatialDeriv_subset i h)
      change (fderiv ℝ (CKN.spatialDeriv ψ i) x) (CKN.basisVec i) = 0
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hxi]
      simp
    have hzeroLap : CKN.spatialLaplacian ψ x = 0 := by
      rw [CKN.spatialLaplacian]
      exact Finset.sum_eq_zero (fun i hi => hzero i)
    change H x * CKN.spatialLaplacian ψ x ≠ 0 at hx
    rw [hzeroLap] at hx
    exact hx (by simp)
  have hright : Integrable (fun x => CKN.spatialLaplacian H x * ψ x) volume := by
    exact (hHlapCont.mul hψ.continuous).integrable_of_hasCompactSupport
      (hψc.mul_left (f := CKN.spatialLaplacian H))
  have hterms (i : Fin 3) :
      ∫ x, H x * CKN.spatialDeriv (CKN.spatialDeriv ψ i) i x =
        ∫ x, CKN.spatialDeriv (CKN.spatialDeriv H i) i x * ψ x := by
    have hfirst := integral_mul_spatialDeriv_order1 h1 (hψ1 i) (hψc1 i) i
    have hsecond := integral_mul_spatialDeriv_order1 (hd1 i)
      (hψ.of_le (by norm_num)) hψc i
    -- The first identity moves one derivative; the second moves it back.
    have hsecond' :
        ∫ x, CKN.spatialDeriv H i x * CKN.spatialDeriv ψ i x =
          -∫ x, CKN.spatialDeriv (CKN.spatialDeriv H i) i x * ψ x := by
      simpa using hsecond
    calc
      ∫ x, H x * CKN.spatialDeriv (CKN.spatialDeriv ψ i) i x =
          -∫ x, CKN.spatialDeriv H i x * CKN.spatialDeriv ψ i x := by
            simpa using hfirst
      _ = ∫ x, CKN.spatialDeriv (CKN.spatialDeriv H i) i x * ψ x := by
            rw [hsecond']
            ring
  have hsumHterm (i : Fin 3) : Integrable
      (fun x => CKN.spatialDeriv (CKN.spatialDeriv H i) i x * ψ x) volume := by
    exact ((contDiff_spatialDeriv_of_one_more (hd1 i) i).continuous.mul
      hψ.continuous).integrable_of_hasCompactSupport
        (hψc.mul_left (f := CKN.spatialDeriv (CKN.spatialDeriv H i) i))
  have hsumψterm (i : Fin 3) : Integrable
      (fun x => H x * CKN.spatialDeriv
        (CKN.spatialDeriv ψ i) i x) volume := by
    exact (hH.continuous.mul
      ((contDiff_spatialDeriv_of_one_more (hψ1 i) i).continuous)).integrable_of_hasCompactSupport
        ((hψc2 i).mul_left (f := H))
  have hsumEq :
      ∫ x, (∑ i : Fin 3, H x * CKN.spatialDeriv
        (CKN.spatialDeriv ψ i) i x) =
      ∫ x, (∑ i : Fin 3, CKN.spatialDeriv
        (CKN.spatialDeriv H i) i x * ψ x) := by
    rw [integral_finsetSum (s := Finset.univ)
      (fun i hi => hsumψterm i)]
    rw [integral_finsetSum (s := Finset.univ)
      (fun i hi => hsumHterm i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact hterms i
  have hpoint : (fun x => ∑ i : Fin 3,
      CKN.spatialDeriv (CKN.spatialDeriv H i) i x * ψ x) = fun x => 0 := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · rw [show (∑ i : Fin 3,
        CKN.spatialDeriv (CKN.spatialDeriv H i) i x * ψ x) =
          CKN.spatialLaplacian H x * ψ x by
          simp [CKN.spatialLaplacian, Finset.sum_mul]]
      rw [hHarm x hx]
      simp
    · have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hψx]
  calc
    ∫ x, H x * CKN.spatialLaplacian ψ x =
        ∫ x, (∑ i : Fin 3, H x *
          CKN.spatialDeriv (CKN.spatialDeriv ψ i) i x) := by
            congr 1
            funext x
            simp [CKN.spatialLaplacian, Finset.mul_sum]
    _ = ∫ x, (∑ i : Fin 3,
        CKN.spatialDeriv (CKN.spatialDeriv H i) i x * ψ x) := hsumEq
    _ = 0 := by rw [hpoint]; simp

end CKN.Foundation.Harmonic
