-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.CoordinateMultiplierBridge
import CKN.Core.Endgame.CausalGradientMorrey
import CKN.Core.Endgame.CausalDerivativeSource
import CKN.Core.Endgame.CausalPressureExtension
import CKN.Core.Endgame.ForceSlotNumericalSupport
import CKN.Foundation.Parabolic.Covering

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Endgame

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4

private lemma indicator_indicator_local {α β : Type} [Zero β]
    (S T : Set α) (hST : S ⊆ T) (g : α → β) :
    T.indicator (S.indicator g) = S.indicator g := by
  funext z
  by_cases hzS : z ∈ S
  · simp only [indicator_of_mem hzS, indicator_of_mem (hST hzS)]
  · simp [hzS]

private lemma morrey_norm_neg_local {P τ : ℝ} (g : ParabolicPoint → ℝ) :
    morreyNorm P τ (fun z => -g z) = morreyNorm P τ g := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

private lemma morrey_norm_sub_local {P τ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) :
    morreyNorm P τ (fun z => f z - g z) ≤
      morreyNorm P τ f + morreyNorm P τ g := by
  have h := morrey_norm_add_le (τ := τ) hP hf hg.neg
  change morreyNorm P τ (fun z => f z + -g z) ≤
    morreyNorm P τ f + morreyNorm P τ (fun z => -g z) at h
  rw [morrey_norm_neg_local] at h
  simpa only [sub_eq_add_neg] using h

theorem causal_gradient_source_local_of_step2
    (q ε₀ C : ℝ) (KU KD KP : ℝ≥0∞)
    (hq : 5 / 2 < q) (hC : 0 ≤ C)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    {φ : Vec3 × ℝ → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hφrange : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (33 / 64))
    (hder : ∀ z : Vec3 × ℝ, z.2 ≤ 0 →
      |timePartial φ z| ≤ C ∧ (∀ j, |spatialPartial φ j z| ≤ C) ∧
        |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C)
    (hU : ∀ i, morreyNorm 3 25
      ((parabolicCylinder (0 : Vec3) 0 (9 / 16)).indicator (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8)
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
        (fun z => Du z i j)) ≤ KD)
    (hDp : ∀ i, AEMeasurable
      ((parabolicCylinder (0 : Vec3) 0 (17 / 32)).indicator
        (fun z => Dp z i)) volume)
    (hP : ∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      ((parabolicCylinder (0 : Vec3) 0 (17 / 32)).indicator
        (fun z => Dp z i)) ≤ KP)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀) :
    ∀ i, AEMeasurable (causalGradientSourceComponent φ u Du f Dp i) volume ∧
      morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
        (causalGradientSourceComponent φ u Du f Dp i) ≤
          causalGradientMorreyBound q ε₀ C KU KD KP := by
  let S₉ := parabolicCylinder (0 : Vec3) 0 (9 / 16)
  let S₅ := parabolicCylinder (0 : Vec3) 0 (5 / 8)
  let S₁₇ := parabolicCylinder (0 : Vec3) 0 (17 / 32)
  let Sb := parabolicCylinder (0 : Vec3) 0 (33 / 64)
  have hSb9 : Sb ⊆ S₉ := by
    exact parabolicCylinder_mono (by norm_num) (by norm_num)
  have hSb5 : Sb ⊆ S₅ := by
    exact parabolicCylinder_mono (by norm_num) (by norm_num)
  have hSb17 : Sb ⊆ S₁₇ := by
    exact parabolicCylinder_mono (by norm_num) (by norm_num)
  have hS9S5 : S₉ ⊆ S₅ := by
    exact parabolicCylinder_mono (by norm_num) (by norm_num)
  have hS17S5 : S₁₇ ⊆ S₅ := by
    exact parabolicCylinder_mono (by norm_num) (by norm_num)
  have hdata := one_sided_indicated_components_aemeasurable hsol hdom
  have hφAE : AEMeasurable (φ : ParabolicPoint → ℝ) volume :=
    (hφ.1.continuous.comp continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have hsupp5 : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8) := by
    intro z hz ht
    exact parabolicCylinder_mono (by norm_num) (by norm_num) (hsupp z hz ht)
  have hzero := fun z ht hz =>
    cutoff_coefficients_zero_on_past_outside_intermediate hφ.1 hsupp5 (z := z) ht hz
  have hφzero (z : ParabolicPoint) (hz : z ∉ Sb) (ht : z.2 ≤ 0) : φ z = 0 := by
    have hraw : (z.1, z.2) ∉ tsupport (φ : Vec3 × ℝ → ℝ) := by
      intro hm
      apply hz
      have hs := hsupp (z.1, z.2) hm ht
      rw [parabolicHomeomorph_symm_apply] at hs
      change z ∈ Sb at hs
      exact hs
    have hv := image_eq_zero_of_notMem_tsupport (f := φ) hraw
    change φ z = 0 at hv
    exact hv
  have hcoeffzero (z : ParabolicPoint) (hz : z ∉ Sb) (ht : z.2 ≤ 0) :
      timePartial φ z = 0 ∧
      (∀ j, spatialPartial φ j z = 0) ∧
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
    have hraw : (z.1, z.2) ∉ tsupport (φ : Vec3 × ℝ → ℝ) := by
      intro hm
      apply hz
      have hs := hsupp (z.1, z.2) hm ht
      rw [parabolicHomeomorph_symm_apply] at hs
      change z ∈ Sb at hs
      exact hs
    have ht0 := timePartial_zero_of_not_mem_tsupport_public hφ.1 hraw
    change timePartial φ z = 0 at ht0
    refine ⟨ht0, ?_, ?_⟩
    · intro j
      have hj := spatialPartial_zero_of_not_mem_tsupport_public hφ.1 hraw j
      change spatialPartial φ j z = 0 at hj
      exact hj
    · change (∑ j : Fin 3, spatialSecondPartial φ j j z) = 0
      exact Finset.sum_eq_zero (fun j _ =>
        by
          have hj := spatialSecondPartial_zero_of_not_mem_tsupport_public
            hφ.1 hraw j j
          change spatialSecondPartial φ j j z = 0 at hj
          exact hj)
  have hφsupp5 : ∀ z ∈ tsupport φ, z.2 ≤ 0 → z ∈ S₅ := by
    intro z hz ht
    exact parabolicCylinder_mono (by norm_num) (by norm_num) (hsupp z hz ht)
  have hφsupp17 : ∀ z ∈ tsupport φ, z.2 ≤ 0 → z ∈ S₁₇ := by
    intro z hz ht
    exact parabolicCylinder_mono (by norm_num) (by norm_num) (hsupp z hz ht)
  have hφunit : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 1 → φ z = 0 := by
    intro z ht hz
    exact hφzero z (fun hz' => hz (parabolicCylinder_mono (by norm_num) (by norm_num) hz')) ht
  have hUa : ∀ i, AEMeasurable (S₅.indicator (fun z => u z i)) volume := hdata.1
  have hDa : ∀ i j, AEMeasurable (S₅.indicator (fun z => Du z i j)) volume := hdata.2.1
  have hS₉meas : MeasurableSet S₉ := measurableSet_parabolicCylinder _ _ _
  have hS₅meas : MeasurableSet S₅ := measurableSet_parabolicCylinder _ _ _
  have hS₁₇meas : MeasurableSet S₁₇ := measurableSet_parabolicCylinder _ _ _
  have hU9ae : ∀ i, AEMeasurable (S₉.indicator (fun z => u z i)) volume := by
    intro i
    have hae := (hUa i).indicator hS₉meas
    have heq : S₉.indicator (S₅.indicator (fun z => u z i)) =
        S₉.indicator (fun z => u z i) := by
      funext z
      by_cases hz : z ∈ S₉
      · simp only [indicator_of_mem hz, indicator_of_mem (hS9S5 hz)]
      · simp only [indicator_of_notMem hz]
    rw [← heq]
    exact hae
  have hD17ae : ∀ i j, AEMeasurable (S₁₇.indicator (fun z => Du z i j)) volume := by
    intro i j
    have hae := (hDa i j).indicator hS₁₇meas
    have heq : S₁₇.indicator (S₅.indicator (fun z => Du z i j)) =
        S₁₇.indicator (fun z => Du z i j) := by
      funext z
      by_cases hz : z ∈ S₁₇
      · simp only [indicator_of_mem hz, indicator_of_mem (hS17S5 hz)]
      · simp only [indicator_of_notMem hz]
    rw [← heq]
    exact hae
  have hU5ae : ∀ i, AEMeasurable
      (S₅.indicator (fun z => S₉.indicator (fun w => u w i) z)) volume := by
    intro i
    exact (hU9ae i).indicator hS₅meas
  have hD5ae : ∀ i j, AEMeasurable
      (S₅.indicator (fun z => S₅.indicator (fun w => Du w i j) z)) volume := by
    intro i j
    exact (hDa i j).indicator hS₅meas
  have hP5ae : ∀ i, AEMeasurable
      (S₅.indicator (fun z => S₁₇.indicator (fun w => Dp w i) z)) volume := by
    intro i
    exact (hDp i).indicator hS₅meas
  have hU5 : ∀ i, morreyNorm 3 25
      (S₅.indicator (fun z => S₉.indicator (fun w => u w i) z)) ≤ KU := by
    intro i
    rw [indicator_indicator_local S₉ S₅ hS9S5]
    exact hU i
  have hD5 : ∀ i j, morreyNorm 2 (25 / 8)
      (S₅.indicator (fun z => S₅.indicator (fun w => Du w i j) z)) ≤ KD := by
    intro i j
    rw [indicator_indicator_local S₅ S₅ subset_rfl]
    exact hD i j
  have hP5 : ∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      (S₅.indicator (fun z => S₁₇.indicator (fun w => Dp w i) z)) ≤ KP := by
    intro i
    rw [indicator_indicator_local S₁₇ S₅ hS17S5]
    exact hP i
  have hmul_eq {a g : ParabolicPoint → ℝ}
      (ha : ∀ z, z.2 ≤ 0 → z ∉ S₉ → a z = 0) :
      pastMultiplierSource a (fun z => S₉.indicator g z) =
        pastMultiplierSource a g := by
    funext z
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · simp only [pastMultiplierSource, indicator_of_mem ht]
      by_cases hz : z ∈ S₉
      · simp only [indicator_of_mem hz]
      · simp only [indicator_of_notMem hz, ha z ht hz, zero_mul]
    · simp only [pastMultiplierSource, indicator_of_notMem ht]
  have hmul_eq17 {a g : ParabolicPoint → ℝ}
      (ha : ∀ z, z.2 ≤ 0 → z ∉ S₁₇ → a z = 0) :
      pastMultiplierSource a (fun z => S₁₇.indicator g z) =
        pastMultiplierSource a g := by
    funext z
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · simp only [pastMultiplierSource, indicator_of_mem ht]
      by_cases hz : z ∈ S₁₇
      · simp only [indicator_of_mem hz]
      · simp only [indicator_of_notMem hz, ha z ht hz, zero_mul]
    · simp only [pastMultiplierSource, indicator_of_notMem ht]
  intro i
  let A := pastMultiplierSource (fun z => timePartial φ z)
    (fun z => u z i)
  let B := pastMultiplierSource
    (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1) (fun z => u z i)
  let N := {z : ParabolicPoint | z.2 ≤ 0}.indicator
    (fun z => φ z * localizedConvection u Du z i)
  let F := causalForceComponent φ f i
  let P := pastMultiplierSource φ (fun z => Dp z i)
  have hA0 : ∀ z, z.2 ≤ 0 → z ∉ S₉ → timePartial φ z = 0 :=
    fun z ht hz => (hcoeffzero z (fun hm => hz (hSb9 hm)) ht).1
  have hB0 : ∀ z, z.2 ≤ 0 → z ∉ S₉ →
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 :=
    fun z ht hz => (hcoeffzero z (fun hm => hz (hSb9 hm)) ht).2.2
  have hA := causal_linear_velocity_source_morrey_le q C KU hq hC
    (fun z => timePartial φ z) (fun z => S₉.indicator (fun w => u w i) z)
    ((timePartial_contDiff_full hφ.1).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
    (hU5ae i) (fun z ht => (hder z ht).1)
    (fun z ht hz => hA0 z ht (fun hm => hz (hS9S5 hm))) (hU5 i)
  have hB := causal_linear_velocity_source_morrey_le q C KU hq hC
    (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1)
    (fun z => S₉.indicator (fun w => u w i) z)
    (by
      have hlapcont : Continuous
          (fun z : Vec3 × ℝ => spatialLaplacian (fun x => φ (x, z.2)) z.1) := by
        change Continuous (fun z : Vec3 × ℝ => ∑ j, spatialSecondPartial φ j j z)
        exact continuous_finsetSum _ (fun j _ =>
          (spatialSecondPartial_contDiff_full hφ.1 j j).continuous)
      exact (hlapcont.comp continuous_parabolicPoint_to_prod).measurable.aemeasurable)
    (hU5ae i) (fun z ht => (hder z ht).2.2)
    (fun z ht hz => hB0 z ht (fun hm => hz (hS9S5 hm))) (hU5 i)
  let u₉ : ParabolicPoint → Vec3 := fun z j => S₉.indicator
    (fun w => u w j) z
  let Du₅ : ParabolicPoint → Fin 3 → Vec3 := fun z i =>
    fun j => S₅.indicator (fun w => Du w i j) z
  have hφzero5 : ∀ z, z.2 ≤ 0 → z ∉ S₅ → φ z = 0 := by
    intro z ht hz
    exact hφzero z (fun hm => hz (hSb5 hm)) ht
  have hN := past_convection_source_morrey_le q KU KD hq φ
    u₉ Du₅ i hφAE
    (fun z ht => by
      change |φ (z.1, z.2)| ≤ 1
      rw [abs_of_nonneg (hφrange (z.1, z.2)).1]
      exact (hφrange (z.1, z.2)).2)
    hφzero5 (fun j => by simpa [u₉] using hU5ae j)
      (fun j => by simpa [Du₅] using hD5ae i j)
    (fun j => by simpa [u₉] using hU5 j)
      (fun j => by simpa [Du₅] using hD5 i j)
  have hF := causal_force_source_of_suitableWeakSolution q ε₀ hq hsol hdom
    hφAE (fun z _ => hφrange (z.1, z.2)) hφunit hsmall i
  have hP := causal_linear_pressure_source_morrey_le q KP φ
    (fun z => S₁₇.indicator (fun w => Dp w i) z) hφAE
    (hP5ae i) (fun z ht => by
      change |φ (z.1, z.2)| ≤ 1
      rw [abs_of_nonneg (hφrange (z.1, z.2)).1]
      exact (hφrange (z.1, z.2)).2)
    (fun z ht hz => by exact hφzero z (fun hm => hz (hSb5 hm)) ht) (hP5 i)
  have hAeq : A = pastMultiplierSource
      (fun z => timePartial φ z) (fun z => S₉.indicator (fun w => u w i) z) := by
    dsimp [A]
    exact (hmul_eq hA0).symm
  have hBeq : B = pastMultiplierSource
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1)
        (fun z => S₉.indicator (fun w => u w i) z) := by
    dsimp [B]
    exact (hmul_eq hB0).symm
  have hAmeas : AEMeasurable A volume := by
    rw [hAeq]
    exact hA.1
  have hBmeas : AEMeasurable B volume := by
    rw [hBeq]
    exact hB.1
  have hNmeas : AEMeasurable N volume := by
    have heq : N = {z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => φ z * localizedConvection u₉ Du₅ z i) := by
      funext z
      by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
      · simp only [N, indicator_of_mem ht]
        by_cases hz : z ∈ Sb
        · have hu : u₉ z = u z := by
            funext j
            simp only [u₉, indicator_of_mem (hSb9 hz)]
          have hdu : Du₅ z i = Du z i := by
            funext j
            simp only [Du₅, indicator_of_mem (hSb5 hz)]
          change φ (z.1, z.2) * localizedConvection u Du z i =
            φ (z.1, z.2) * localizedConvection u₉ Du₅ z i
          simp only [localizedConvection]
          rw [hu, hdu]
        · rw [hφzero z hz ht]
          simp only [zero_mul]
      · simp only [N, indicator_of_notMem ht]
    rw [heq]
    exact hN.1
  have hNbound : morreyNorm (6 / 5) (min q (25 / 9)) N ≤ 3 * KU * KD := by
    have heq : N = {z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => φ z * localizedConvection u₉ Du₅ z i) := by
      funext z
      by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
      · simp only [N, indicator_of_mem ht]
        by_cases hz : z ∈ Sb
        · have hu : u₉ z = u z := by
            funext j
            simp only [u₉, indicator_of_mem (hSb9 hz)]
          have hdu : Du₅ z i = Du z i := by
            funext j
            simp only [Du₅, indicator_of_mem (hSb5 hz)]
          change φ (z.1, z.2) * localizedConvection u Du z i =
            φ (z.1, z.2) * localizedConvection u₉ Du₅ z i
          simp only [localizedConvection]
          rw [hu, hdu]
        · rw [hφzero z hz ht]
          simp only [zero_mul]
      · simp only [N, indicator_of_notMem ht]
    rw [heq]
    exact hN.2
  have hP0 : ∀ z, z.2 ≤ 0 → z ∉ S₁₇ → φ z = 0 := by
    intro z ht hz
    exact hφzero z (fun hm => hz (hSb17 hm)) ht
  have hPeq : P = pastMultiplierSource φ
      (fun z => S₁₇.indicator (fun w => Dp w i) z) := by
    dsimp [P]
    exact (hmul_eq17 hP0).symm
  have hPmeas : AEMeasurable P volume := by
    rw [hPeq]
    exact hP.1
  have hPbound : morreyNorm (6 / 5) (min q (25 / 9)) P ≤ KP := by
    rw [hPeq]
    exact hP.2
  have hsource : causalGradientSourceComponent φ u Du f Dp i =
      fun z => A z + B z - N z + F z - P z := by
    funext z
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · simp only [causalGradientSourceComponent, A, B, N, F, P,
        pastMultiplierSource, causalForceComponent, indicator_of_mem ht,
        CKN.Core.Step4.localizedGradientSourceG, localizedEquationG]
    · simp only [causalGradientSourceComponent, A, B, N, F, P,
        pastMultiplierSource, causalForceComponent, indicator_of_notMem ht,
        add_zero, sub_zero]
  rw [hsource]
  refine ⟨(((hAmeas.add hBmeas).sub hNmeas).add hF.1).sub hPmeas, ?_⟩
  have hAB := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6 / 5)
      hAmeas hBmeas).trans (add_le_add (by simpa only [hAeq] using hA.2)
        (by simpa only [hBeq] using hB.2))
  have hABN := (morrey_norm_sub_local (by norm_num : (1 : ℝ) ≤ 6 / 5)
      (hAmeas.add hBmeas) hNmeas).trans (add_le_add hAB hNbound)
  have hABNF := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6 / 5)
      ((hAmeas.add hBmeas).sub hNmeas) hF.1).trans
    (add_le_add hABN hF.2)
  exact (morrey_norm_sub_local (by norm_num : (1 : ℝ) ≤ 6 / 5)
      (((hAmeas.add hBmeas).sub hNmeas).add hF.1) hPmeas).trans
    (add_le_add hABNF hPbound)

end CKN.Core.Endgame
