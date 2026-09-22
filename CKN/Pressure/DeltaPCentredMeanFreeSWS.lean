-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.DeltaPCentred
import CKN.Pressure.SpatialDerivSupport
import CKN.Setting.UTensor

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

private theorem delta_p_setIntegral_eq_of_support_subset
    {A B S : Set Vec3} {g : Vec3 → ℝ}
    (hzero : ∀ x, x ∉ S → g x = 0) (hA : S ⊆ A) (hB : S ⊆ B) :
    (∫ x in A, g x) = ∫ x in B, g x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hzero x (fun hxS => hx (hA hxS))),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hzero x (fun hxS => hx (hB hxS)))]

/-- The pressure slice identity on a ball with the singly centred tensor
`Uᵢⱼ = -uᵢ (uⱼ - ⨍_{Bρ} uⱼ)`, as in `eq:Uij`. -/
theorem pressure_delta_p_meanFree_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (vec3Ball x₀ ρ) ⊆ Ω)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψB : tsupport ψ ⊆ vec3Ball x₀ ρ) :
    ∀ᵐ s ∂volume.restrict I,
      ∫ x in vec3Ball x₀ ρ, p (x, s) * spatialLaplacian ψ x =
        (∫ x in vec3Ball x₀ ρ, ∑ i, ∑ j,
            utensor u x₀ ρ s i j x * mixedSecond ψ i j x) -
          ∫ x in vec3Ball x₀ ρ, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  -- In particular, the singly centred tensor uses the genuine normalized
  -- mean on a positive-volume ball, not the zero-measure convention.
  have _hBpos : 0 < volume B :=
    CKN.Foundation.Parabolic.Integration.volume_vec3Ball_pos hρ
  have hBΩ : B ⊆ Ω := subset_closure.trans hsub
  have hψΩ : tsupport ψ ⊆ Ω := hψB.trans hBΩ
  have hraw := pressure_slice_identity_ae hsol hψ hψc hψΩ
  have hdiv : ∀ᵐ s ∂volume.restrict I, ∀ j : Fin 3,
      ∫ x in Ω, ∑ i, u (x, s) i * mixedSecond ψ i j x = 0 := by
    rw [ae_all_iff]
    intro j
    have hd := divfree_slice_weak_of_suitable hsol
      (spatialDeriv ψ j) (contDiff_spatialDeriv_smooth hψ j)
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j))
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hψΩ)
    filter_upwards [hd] with s hs
    simpa only [mixedSecond, spatialDeriv] using hs
  obtain ⟨Ω', _, _, hψΩ', hΩ'compact, hΩ'Ω, hLp⟩ :=
    decomposition_slice_integrability hsol hψc hψΩ hψc hψΩ
  set_option linter.style.haveILetI false in
    letI : IsFiniteMeasure (volume.restrict Ω') := by
      apply isFiniteMeasure_restrict.mpr
      exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
        hΩ'compact.measure_lt_top).ne
  filter_upwards [hraw, hdiv, hLp] with s hraw_s hdiv_s hLp_s
  have huComp (i : Fin 3) : MemLp (fun x : Vec3 => u (x, s) i) 2
      (volume.restrict Ω') :=
    hLp_s.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have huInt (i : Fin 3) : Integrable (fun x : Vec3 => u (x, s) i)
      (volume.restrict Ω') := huComp i |>.integrable (by norm_num)
  have huScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ' : tsupport g ⊆ Ω') : IntegrableOn
      (fun x => u (x, s) i * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have h' := (huInt i).mul_bdd hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x)
    have h'On : IntegrableOn (fun x => u (x, s) i * g x) Ω' volume := h'
    have hfull : Integrable (fun x => u (x, s) i * g x) volume :=
      h'On.integrable_of_forall_notMem_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hxt => hx (hgΩ' hxt)), mul_zero])
    exact hfull.integrableOn
  have huuScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ' : tsupport g ⊆ Ω') : IntegrableOn
      (fun x => u (x, s) i * u (x, s) j * g x) Ω volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have h' := ((huComp i).integrable_mul (huComp j)).mul_bdd
      hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x)
    have h'On : IntegrableOn
        (fun x => u (x, s) i * u (x, s) j * g x) Ω' volume := h'
    have hfull : Integrable
        (fun x => u (x, s) i * u (x, s) j * g x) volume :=
      h'On.integrable_of_forall_notMem_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hxt => hx (hgΩ' hxt)), mul_zero])
    exact hfull.integrableOn
  have hmixedCont (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have hmixedC (i j : Fin 3) : HasCompactSupport (mixedSecond ψ i j) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  have hmixedΩ' (i j : Fin 3) : tsupport (mixedSecond ψ i j) ⊆ Ω' :=
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hψΩ')
  have hfinite {g : Fin 3 → Fin 3 → Vec3 → ℝ}
      (hg : ∀ i j, IntegrableOn (g i j) Ω volume) : IntegrableOn
      (fun x => ∑ i, ∑ j, g i j x) Ω volume := by
    change Integrable (∑ i, ∑ j, (fun x => g i j x)) (volume.restrict Ω)
    exact integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun i _ => integrable_finsetSum' (Finset.univ : Finset (Fin 3))
        (fun j _ => hg i j))
  have hrawTensor : IntegrableOn
      (fun x => ∑ i, ∑ j,
        u (x, s) i * u (x, s) j * mixedSecond ψ i j x) Ω volume :=
    hfinite (fun i j => huuScalar (hmixedCont i j).continuous
      (hmixedC i j) (hmixedΩ' i j))
  have hcrossScalar {i j : Fin 3} : IntegrableOn
      (fun x => u (x, s) i *
        average (volume.restrict B) (fun y => u (y, s) j) * mixedSecond ψ i j x)
      Ω volume := by
    have h := (huScalar (i := i) (hmixedCont i j).continuous
      (hmixedC i j) (hmixedΩ' i j)).const_mul
        (average (volume.restrict B) (fun y => u (y, s) j))
    exact h.congr (Filter.Eventually.of_forall fun x => by ring)
  have hcross : IntegrableOn
      (fun x => ∑ i, ∑ j,
        u (x, s) i * average (volume.restrict B) (fun y => u (y, s) j) *
          mixedSecond ψ i j x) Ω volume :=
    hfinite (fun i j => hcrossScalar (i := i) (j := j))
  have hrow (j : Fin 3) : IntegrableOn
      (fun x => ∑ i, u (x, s) i * mixedSecond ψ i j x) Ω volume := by
    change Integrable (∑ i, (fun x => u (x, s) i * mixedSecond ψ i j x))
      (volume.restrict Ω)
    exact integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun i _ => huScalar (i := i) (hmixedCont i j).continuous
        (hmixedC i j) (hmixedΩ' i j))
  have hcrossPoint (x : Vec3) :
      (∑ i, ∑ j,
        u (x, s) i * average (volume.restrict B) (fun y => u (y, s) j) *
          mixedSecond ψ i j x) =
        ∑ j, average (volume.restrict B) (fun y => u (y, s) j) *
          (∑ i, u (x, s) i * mixedSecond ψ i j x) := by
    calc
      _ = ∑ j, ∑ i,
          u (x, s) i * average (volume.restrict B) (fun y => u (y, s) j) *
            mixedSecond ψ i j x := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hcrossZero :
      ∫ x in Ω, ∑ i, ∑ j,
        u (x, s) i * average (volume.restrict B) (fun y => u (y, s) j) *
          mixedSecond ψ i j x = 0 := by
    calc
      _ = ∫ x in Ω, ∑ j,
          average (volume.restrict B) (fun y => u (y, s) j) *
            (∑ i, u (x, s) i * mixedSecond ψ i j x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hcrossPoint x
      _ = ∑ j, average (volume.restrict B) (fun y => u (y, s) j) *
          (∫ x in Ω, ∑ i, u (x, s) i * mixedSecond ψ i j x) := by
          have hsum := integral_finsetSum (μ := volume.restrict Ω)
            (Finset.univ : Finset (Fin 3))
            (fun j _ => (hrow j).const_mul
              (average (volume.restrict B) (fun y => u (y, s) j)))
          simpa only [integral_const_mul] using hsum
      _ = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [hdiv_s j, mul_zero]
  have htensorPoint (x : Vec3) :
      (∑ i, ∑ j, utensor u x₀ ρ s i j x * mixedSecond ψ i j x) =
        -(∑ i, ∑ j,
          u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
          ∑ i, ∑ j,
            u (x, s) i * average (volume.restrict B) (fun y => u (y, s) j) *
              mixedSecond ψ i j x := by
    simp only [utensor, meanFreeComponent]
    calc
      _ = ∑ i, ∑ j,
          (-(u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
            u (x, s) i * average (volume.restrict B) (fun y => u (y, s) j) *
              mixedSecond ψ i j x) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have htensorIntegral :
      ∫ x in Ω, ∑ i, ∑ j,
        utensor u x₀ ρ s i j x * mixedSecond ψ i j x =
          -(∫ x in Ω, ∑ i, ∑ j,
            u (x, s) i * u (x, s) j * mixedSecond ψ i j x) := by
    calc
      _ = ∫ x in Ω,
          (-(∑ i, ∑ j,
              u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
            ∑ i, ∑ j,
              u (x, s) i * average (volume.restrict B) (fun y => u (y, s) j) *
                mixedSecond ψ i j x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact htensorPoint x
      _ = -(∫ x in Ω, ∑ i, ∑ j,
          u (x, s) i * u (x, s) j * mixedSecond ψ i j x) +
            ∫ x in Ω, ∑ i, ∑ j,
              u (x, s) i * average (volume.restrict B) (fun y => u (y, s) j) *
                mixedSecond ψ i j x := by
          have hsum := integral_add hrawTensor.neg hcross
          simpa only [Pi.neg_apply, Pi.add_apply, integral_neg] using hsum
      _ = _ := by rw [hcrossZero]; simp
  have hidentityΩ :
      ∫ x in Ω, p (x, s) * spatialLaplacian ψ x =
        (∫ x in Ω, ∑ i, ∑ j,
            utensor u x₀ ρ s i j x * mixedSecond ψ i j x) -
          ∫ x in Ω, ∑ i, f (x, s) i * spatialDeriv ψ i x := by
    rw [hraw_s, ← htensorIntegral]
  have hzeroLhs (x : Vec3) (hx : x ∉ tsupport ψ) :
    p (x, s) * spatialLaplacian ψ x = 0 := by
    have hxLap : x ∉ Function.support (spatialLaplacian ψ) :=
      fun h => hx (support_spatialLaplacian_subset h)
    have hLap : spatialLaplacian ψ x = 0 := by
      change ¬ spatialLaplacian ψ x ≠ 0 at hxLap
      exact not_not.mp hxLap
    rw [hLap, mul_zero]
  have hzeroTensor (x : Vec3) (hx : x ∉ tsupport ψ) :
      (∑ i, ∑ j,
        utensor u x₀ ρ s i j x * mixedSecond ψ i j x) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hxMixed : x ∉ Function.support (mixedSecond ψ i j) :=
      fun h => hx (support_mixedSecond_subset i j h)
    have hMixed : mixedSecond ψ i j x = 0 := by
      change ¬ mixedSecond ψ i j x ≠ 0 at hxMixed
      exact not_not.mp hxMixed
    rw [hMixed, mul_zero]
  have hzeroForce (x : Vec3) (hx : x ∉ tsupport ψ) :
      (∑ i, f (x, s) i * spatialDeriv ψ i x) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hxDeriv : x ∉ Function.support (spatialDeriv ψ i) :=
      fun h => hx (support_spatialDeriv_subset i h)
    have hDeriv : spatialDeriv ψ i x = 0 := by
      change ¬ spatialDeriv ψ i x ≠ 0 at hxDeriv
      exact not_not.mp hxDeriv
    rw [hDeriv, mul_zero]
  rw [← delta_p_setIntegral_eq_of_support_subset hzeroLhs hψΩ hψB,
    ← delta_p_setIntegral_eq_of_support_subset hzeroTensor hψΩ hψB,
    ← delta_p_setIntegral_eq_of_support_subset hzeroForce hψΩ hψB]
  exact hidentityΩ

end CKN
