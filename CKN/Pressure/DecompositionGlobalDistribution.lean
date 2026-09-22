-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.DecompositionAllSpaceTests

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN

private theorem pressureGlobal_ts_support_spatialDeriv_subset {g : Vec3 → ℝ}
    (i : Fin 3) : tsupport (spatialDeriv g i) ⊆ tsupport g := by
  apply closure_minimal
  · intro x hx
    by_contra hxt
    exact hx (by simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt])
  · exact isClosed_tsupport g

private theorem pressureGlobal_ts_support_mixedSecond_subset {g : Vec3 → ℝ}
    (i j : Fin 3) : tsupport (mixedSecond g i j) ⊆ tsupport g := by
  apply closure_minimal
  · intro x hx
    by_contra hxt
    have hnot : x ∉ tsupport (spatialDeriv g j) := fun h =>
      hxt (pressureGlobal_ts_support_spatialDeriv_subset j h)
    exact hx (by simp [mixedSecond, spatialDeriv,
      fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot])
  · exact isClosed_tsupport g

private theorem pressureGlobal_ts_support_spatialLaplacian_subset {g : Vec3 → ℝ} :
    tsupport (spatialLaplacian g) ⊆ tsupport g := by
  apply closure_minimal
  · intro x hx
    by_contra hxt
    have hsecond (i : Fin 3) : spatialDeriv (spatialDeriv g i) i x = 0 := by
      have hnot : x ∉ tsupport (spatialDeriv g i) := fun h =>
        hxt (pressureGlobal_ts_support_spatialDeriv_subset i h)
      simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]
    apply hx
    simp only [spatialLaplacian]
    rw [Finset.sum_eq_zero fun i _ => hsecond i]
  · exact isClosed_tsupport g

/-- The cutoff Laplacian identity tested against every smooth compactly
supported function on space, written as whole-space integrals. -/
theorem pressure_laplace_cutoff_identity_global_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∀ᵐ s ∂volume.restrict I,
      ∫ x, p (x, s) * (η x * spatialLaplacian ψ x) =
        (∫ x, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) +
        (∫ x, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) +
        (∫ x, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j *
            (spatialDeriv η i x * spatialDeriv ψ j x)) +
        (∫ x, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) -
        (∫ x, p (x, s) * (ψ x * spatialLaplacian η x)) -
        2 * (∫ x, (spatialGradDot η ψ x) * p (x, s)) -
        (∫ x, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) -
        (∫ x, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)) := by
  have hlocal := pressure_laplace_cutoff_identity_ae_all_tests
    hsol hη hηc hηΩ (c := c) hψ hψc
  have hη0 : ∀ x, x ∉ Ω → η x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hxη => hx (hηΩ hxη))
  have hηd0 (i : Fin 3) : ∀ x, x ∉ Ω → spatialDeriv η i x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxηd
    exact hx (hηΩ (pressureGlobal_ts_support_spatialDeriv_subset i hxηd))
  have hηm0 (i j : Fin 3) : ∀ x, x ∉ Ω → mixedSecond η i j x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxηm
    exact hx (hηΩ (pressureGlobal_ts_support_mixedSecond_subset i j hxηm))
  have hηLap0 : ∀ x, x ∉ Ω → spatialLaplacian η x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxηL
    exact hx (hηΩ (pressureGlobal_ts_support_spatialLaplacian_subset hxηL))
  filter_upwards [hlocal] with s hs
  have hleft := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := Ω)
      (f := fun x => p (x, s) * (η x * spatialLaplacian ψ x))
      (fun x hx => by rw [hη0 x hx]; simp)
  have hterm0 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := Ω)
      (f := fun x => ∑ i, ∑ j,
        pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x))
      (fun x hx => by rw [hη0 x hx]; simp)
  have hterm1 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := Ω)
      (f := fun x => ∑ i, ∑ j,
        pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x))
      (fun x hx => by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        rw [hηm0 i j x hx]
        simp)
  have hterm2 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := Ω)
      (f := fun x => ∑ i, ∑ j,
        pressureUTensor u c (x, s) i j *
          (spatialDeriv η i x * spatialDeriv ψ j x))
      (fun x hx => by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        rw [hηd0 i x hx]
        simp)
  have hterm3 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := Ω)
      (f := fun x => ∑ i, ∑ j,
        pressureUTensor u c (x, s) i j *
          (spatialDeriv η j x * spatialDeriv ψ i x))
      (fun x hx => by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        rw [hηd0 j x hx]
        simp)
  have hterm4 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := Ω)
      (f := fun x => p (x, s) * (ψ x * spatialLaplacian η x))
      (fun x hx => by rw [hηLap0 x hx]; simp)
  have hterm5 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := Ω)
      (f := fun x => spatialGradDot η ψ x * p (x, s))
      (fun x hx => by
        have hgrad : spatialGradDot η ψ x = 0 := by
          simp only [spatialGradDot]
          apply Finset.sum_eq_zero
          intro i hi
          rw [hηd0 i x hx]
          simp
        rw [hgrad]
        simp)
  have hterm6 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := Ω)
      (f := fun x => ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x))
      (fun x hx => by rw [hη0 x hx]; simp)
  have hterm7 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := Ω)
      (f := fun x => ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x))
      (fun x hx => by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hηd0 i x hx]
        simp)
  simpa only [hleft, hterm0, hterm1, hterm2, hterm3, hterm4,
    hterm5, hterm6, hterm7] using hs

end CKN

end
