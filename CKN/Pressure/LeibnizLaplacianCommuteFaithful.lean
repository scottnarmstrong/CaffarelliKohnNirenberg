-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.LeibnizLaplacian

/-!
# The commutator identity `eq:commute` for a locally integrable matrix field

`CKN/Pressure/LeibnizLaplacian.lean` proves the Hessian-pairing identity for a
*smooth* matrix field `W`.  The display `eq:commute` of `paper/ckn.tex` is
applied to `U = u ⊗ u ∈ L^{5/3}_loc`, so the matrix field is only locally
integrable.  This file records the identity in that generality: the second-order
Leibniz rule holds pointwise for the smooth pair `η, φ`, and each of the three
resulting blocks is separately integrable against a locally integrable weight
because its smooth factor is compactly supported inside `U`.
-/

open MeasureTheory Set
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

private lemma commute_integrableOn_mul_continuous
    {U : Set Vec3} (hU : IsOpen U)
    {f q : Vec3 → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hq : Continuous q) (hqCompact : HasCompactSupport q)
    (hqU : tsupport q ⊆ U) : IntegrableOn (fun x => f x * q x) U volume := by
  have hfK : IntegrableOn f (tsupport q) volume :=
    hf.integrableOn_compact_subset hqU hqCompact.isCompact
  have hprodK : IntegrableOn (fun x => f x * q x) (tsupport q) volume :=
    hfK.mul_continuousOn hq.continuousOn hqCompact.isCompact
  have hzero : ∀ x ∈ U \ tsupport q, f x * q x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx.2, mul_zero]
  simpa only [IntegrableOn, volumeOn] using
    hprodK.of_forall_sdiff_eq_zero hU.measurableSet hzero

private lemma commute_spatialDeriv_eq_zero {f : Vec3 → ℝ} {x : Vec3} (i : Fin 3)
    (hx : x ∉ tsupport f) : spatialDeriv f i x = 0 := by
  simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]

private lemma commute_support_cross_subset {η φ : Vec3 → ℝ} (i j : Fin 3) :
    Function.support (fun x => spatialDeriv η i x * spatialDeriv φ j x
        + spatialDeriv η j x * spatialDeriv φ i x) ⊆ tsupport η := by
  intro x hx
  by_contra hxt
  exact hx (by
    simp [commute_spatialDeriv_eq_zero (f := η) i hxt,
      commute_spatialDeriv_eq_zero (f := η) j hxt])

/-- `eq:commute`: for a locally integrable matrix field `W` on an open set `U`
and smooth compactly supported `η, φ` with supports in `U`,
`∫ ∑ W_{ij} ∂_i∂_j(ηφ) = ∫ η ∑ W_{ij} ∂_i∂_jφ + ∫ (∑ W_{ij} ∂_i∂_jη) φ
 + ∫ ∑ W_{ij} (∂_iη ∂_jφ + ∂_jη ∂_iφ)`. -/
theorem spatialSecondDeriv_commute_weak
    {U : Set Vec3} (hU : IsOpen U) {W : Vec3 → Fin 3 → Fin 3 → ℝ}
    (hW : ∀ i j, LocallyIntegrableOn (fun x => W x i j) U volume)
    {η φ : Vec3 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    ∫ x in U, (∑ i, ∑ j, W x i j * mixedSecond (fun y => η y * φ y) i j x)
      = (∫ x in U, η x * (∑ i, ∑ j, W x i j * mixedSecond φ i j x))
        + (∫ x in U, (∑ i, ∑ j, W x i j * mixedSecond η i j x) * φ x)
        + (∫ x in U, ∑ i, ∑ j, W x i j *
            (spatialDeriv η i x * spatialDeriv φ j x
              + spatialDeriv η j x * spatialDeriv φ i x)) := by
  have hA : IntegrableOn
      (fun x => η x * ∑ i : Fin 3, ∑ j : Fin 3, W x i j * mixedSecond φ i j x)
      U volume := by
    have heq : (fun x => η x *
          ∑ i : Fin 3, ∑ j : Fin 3, W x i j * mixedSecond φ i j x)
        = fun x => ∑ i : Fin 3, ∑ j : Fin 3,
            W x i j * (η x * mixedSecond φ i j x) := by
      funext x
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    exact commute_integrableOn_mul_continuous hU (hW i j)
      (hη.continuous.mul (contDiff_mixedSecond_smooth hφ i j).continuous)
      (HasCompactSupport.mul_right hηc) (tsupport_mul_subset_left.trans hηU)
  have hB : IntegrableOn
      (fun x => (∑ i : Fin 3, ∑ j : Fin 3, W x i j * mixedSecond η i j x) * φ x)
      U volume := by
    have heq : (fun x =>
          (∑ i : Fin 3, ∑ j : Fin 3, W x i j * mixedSecond η i j x) * φ x)
        = fun x => ∑ i : Fin 3, ∑ j : Fin 3,
            W x i j * (mixedSecond η i j x * φ x) := by
      funext x
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    exact commute_integrableOn_mul_continuous hU (hW i j)
      ((contDiff_mixedSecond_smooth hη i j).continuous.mul hφ.continuous)
      (HasCompactSupport.mul_left hφc) (tsupport_mul_subset_right.trans hφU)
  have hC : IntegrableOn
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3, W x i j *
        (spatialDeriv η i x * spatialDeriv φ j x
          + spatialDeriv η j x * spatialDeriv φ i x)) U volume := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    have hsupp := commute_support_cross_subset (η := η) (φ := φ) i j
    refine commute_integrableOn_mul_continuous hU (hW i j) ?_
      (HasCompactSupport.of_support_subset_isCompact hηc.isCompact hsupp)
      ((closure_minimal hsupp (isClosed_tsupport η)).trans hηU)
    exact (((contDiff_spatialDeriv_smooth hη i).continuous.mul
          (contDiff_spatialDeriv_smooth hφ j).continuous).add
        ((contDiff_spatialDeriv_smooth hη j).continuous.mul
          (contDiff_spatialDeriv_smooth hφ i).continuous))
  have hpt : ∀ x : Vec3,
      (∑ i : Fin 3, ∑ j : Fin 3, W x i j * mixedSecond (fun y => η y * φ y) i j x)
        = (η x * ∑ i : Fin 3, ∑ j : Fin 3, W x i j * mixedSecond φ i j x)
          + ((∑ i : Fin 3, ∑ j : Fin 3, W x i j * mixedSecond η i j x) * φ x)
          + ∑ i : Fin 3, ∑ j : Fin 3, W x i j *
              (spatialDeriv η i x * spatialDeriv φ j x
                + spatialDeriv η j x * spatialDeriv φ i x) := by
    intro x
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [spatialSecondDeriv_mul_smooth hη hφ i j x]
    ring
  calc
    ∫ x in U, (∑ i, ∑ j, W x i j * mixedSecond (fun y => η y * φ y) i j x)
        = ∫ x in U, ((η x * ∑ i : Fin 3, ∑ j : Fin 3,
              W x i j * mixedSecond φ i j x)
            + ((∑ i : Fin 3, ∑ j : Fin 3, W x i j * mixedSecond η i j x) * φ x)
            + ∑ i : Fin 3, ∑ j : Fin 3, W x i j *
                (spatialDeriv η i x * spatialDeriv φ j x
                  + spatialDeriv η j x * spatialDeriv φ i x)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x in U, η x * (∑ i, ∑ j, W x i j * mixedSecond φ i j x))
          + (∫ x in U, (∑ i, ∑ j, W x i j * mixedSecond η i j x) * φ x)
          + (∫ x in U, ∑ i, ∑ j, W x i j *
              (spatialDeriv η i x * spatialDeriv φ j x
                + spatialDeriv η j x * spatialDeriv φ i x)) := by
          have hAB : IntegrableOn
              (fun x => (η x * ∑ i : Fin 3, ∑ j : Fin 3,
                    W x i j * mixedSecond φ i j x)
                + ((∑ i : Fin 3, ∑ j : Fin 3, W x i j * mixedSecond η i j x)
                    * φ x)) U volume := hA.add hB
          rw [integral_add hAB hC, integral_add hA hB]

end CKN
