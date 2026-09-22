-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientOriginClauseDerivativeShared
import CKN.Core.Endgame.TheoremACarrierTime
import CKN.Core.Endgame.TheoremABudgetBridge
import CKN.Witnesses.PressureGradientOriginCellInstanceCarrier
import CKN.Core.Step4.PressureGradientHGCloserCellsRemainderGlobal

/-! # Origin budgets from the fixed derivative decomposition

The derivative construction supplies clipped growth and a whole-carrier
integral for one selected field. The location of the coefficient quantifiers
is retained: finite solution-dependent coefficients are not numerical
bounds uniform over the suitable solutions of `prop:bootstrap`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Core.Step4
noncomputable section
namespace CKN.Core.Endgame

/-- The derivative route gives both clipped growth and the whole-carrier
budget without a pressure-mass exponent conversion. -/
theorem theoremA_derivative_clipped_budgets
    (hRemainderMajorant :
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}, 5 / 2 < q →
        ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
            closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
            ∃ M : ℝ → ℝ≥0∞,
              AEMeasurable M (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) ∧
              (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
              ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
                ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
                  ‖classicalGradient
                    (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                      (sourceSliceCentredMean z.1 ρ u) p s +
                      pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s)
    {q τ R₀ R₁ : ℝ} {KU KD : ℝ≥0∞}
    (hq : 5/2 < q) (hτ : 25/3 ≤ τ) (hτhi : τ ≤ 25)
    (hR₁ : 0 < R₁) (hgap : R₁ < R₀) (hR₀ : R₀ < 1)
    (hKU : KU < ⊤) (hKD : KD < ⊤)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => u w i)) ≤ KU)
    (hDu : ∀ i j, morreyNorm 2 (25/8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => Du w i j)) ≤ KD) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y,s)) (fun y => Dp (y,s) i)) ∧
      ∃ A B : ℝ≥0∞, A < ⊤ ∧ B < ⊤ ∧ (∀ (i : Fin 3) (z : ParabolicPoint) (r : ℝ), 0 < r →
        (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-R₁^2) 0,
          eLpNorm (fun y => Dp (y,s) i) (ENNReal.ofReal (6/5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6/5 : ℝ)) ≤
          A * ENNReal.ofReal (r ^ (5 * (1 - (6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q)))) ∧
        (∀ i : Fin 3, (∫⁻ s in Ioc (-R₁^2) 0,
          eLpNorm (fun y => Dp (y,s) i) (ENNReal.ofReal (6/5 : ℝ))
            (volume.restrict (vec3Ball (0 : Vec3) R₁)) ^ (6/5 : ℝ)) ≤ B) := by
  obtain ⟨Dp, hm, hw, A, hA, hgrowth⟩ :=
    originClause_clipped_growth_of_temporal_majorant hRemainderMajorant
      hq hτ hτhi hR₁ hgap hR₀ hKU hKD hsol hdom hU hDu
  let B := A * ENNReal.ofReal
    (R₁ ^ (5 * (1 - (6/5 : ℝ) / min ((1/τ+8/25)⁻¹) q)))
  refine ⟨Dp, hm, hw, A, B, hA,
    ENNReal.mul_lt_top hA ENNReal.ofReal_lt_top, hgrowth, ?_⟩
  intro i
  simpa only [zero_sub, Set.inter_self] using hgrowth i ((0 : Vec3), 0) R₁ hR₁

/-- A finite spatial cover controls the carrier norm by the sum of the
norms on its source half-balls, with no loss depending on the field. -/
theorem theoremA_slice_norm_le_finite_cover
    {n : ℕ} {R ρ : ℝ} {x : Fin n → Vec3}
    (hcover : vec3Ball (0 : Vec3) R ⊆ ⋃ j, vec3Ball (x j) (ρ / 2))
    {g : Vec3 → ℝ} (hg : Measurable g) :
    eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball (0 : Vec3) R)) ≤
      ∑ j, eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball (x j) (ρ / 2))) := by
  classical
  let U := fun j : Fin n => vec3Ball (x j) (ρ / 2)
  let K := vec3Ball (0 : Vec3) R
  have hK : MeasurableSet K := (isOpen_vec3Ball _ _).measurableSet
  have hU (j : Fin n) : MeasurableSet (U j) := (isOpen_vec3Ball _ _).measurableSet
  have hmono : eLpNorm (K.indicator g) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      eLpNorm (fun y => ∑ j, |(U j).indicator g y|) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    apply eLpNorm_mono (hg.indicator hK).aestronglyMeasurable
    intro y
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (show 0 ≤ ∑ j, |(U j).indicator g y| from
      Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
    by_cases hy : y ∈ K
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hy)
      rw [indicator_of_mem hy]
      calc
        |g y| = |(U j).indicator g y| := by rw [indicator_of_mem hj]
        _ ≤ ∑ k, |(U k).indicator g y| := Finset.single_le_sum
          (f := fun k => |(U k).indicator g y|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    · rw [indicator_of_notMem hy, abs_zero]
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hK] at hmono
  apply hmono.trans
  have hsum := eLpNorm_sum_le (μ := (volume : Measure Vec3))
    (f := fun j : Fin n => fun y => |(U j).indicator g y|)
    (s := Finset.univ) (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6 / 5 : ℝ))
  simp only [Finset.sum_fn] at hsum
  apply hsum.trans
  apply Finset.sum_le_sum
  intro j _
  have hn := eLpNorm_norm (p := ENNReal.ofReal (6 / 5 : ℝ)) (μ := volume) ((U j).indicator g) (hg.indicator (hU j)).aestronglyMeasurable
  simpa only [Real.norm_eq_abs, eLpNorm_indicator_eq_eLpNorm_restrict (hU j)] using hn.le

/-- A prescribed temporal moment bound gives a prescribed remainder Morrey
constant. The moment bound, not merely its finiteness, is retained explicitly. -/
theorem theoremA_remainder_bound_of_temporal_budget
    (Kmoment : ℝ≥0∞) {κ : ℝ} (hκlo : 3 / 2 ≤ κ) (hκhi : κ ≤ 25 / 9)
    {F : ParabolicPoint → ℝ} {H : ℝ → ℝ≥0∞} {S : Set Vec3}
    (hF : AEMeasurable F volume) (hH : AEMeasurable H volume)
    (hS : MeasurableSet S)
    (hsupport : ∀ x ∉ S, ∀ t : ℝ, F (x, t) = 0)
    (hbound : ∀ᵐ s ∂volume, ∀ x : Vec3, ‖F (x, s)‖ₑ ≤ H s)
    (hbudget : (∫⁻ s, H s ^ (3 / 2 : ℝ)) ≤ Kmoment) :
    morreyNorm (6 / 5 : ℝ) κ F ≤
      (ENNReal.ofReal (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) + volume S ^ (5 / 6 : ℝ)) *
        Kmoment ^ (2 / 3 : ℝ) := by
  apply (pressure_remainder_morreyNorm_bound hκlo hκhi hF hH hS hsupport hbound).trans
  exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hbudget (by norm_num))

/-- A translated weak derivative estimate controls any weak derivative on
its overlap with the original spatial carrier. -/
theorem theoremA_translated_slice_bound_on_intersection
    {x : Vec3} {r : ℝ} {B : Set Vec3} (hB : IsOpen B)
    {p g D : Vec3 → ℝ} {K : ℝ≥0∞} (i : Fin 3)
    (hpm : AEStronglyMeasurable (fun y => p (x + y))
      (volume.restrict (vec3Ball (0 : Vec3) r)))
    (hg : MemLp g (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball (0 : Vec3) r)))
    (hgw : HasWeakPartialDerivOn (vec3Ball (0 : Vec3) r) i (fun y => p (x + y)) g)
    (hgK : eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball (0 : Vec3) r)) ≤ K)
    (hDloc : LocallyIntegrableOn D B volume) (hDw : HasWeakPartialDerivOn B i p D) :
    eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball x r ∩ B)) ≤ K := by
  have hpre : (fun y : Vec3 => y - x) ⁻¹' vec3Ball (0 : Vec3) r = vec3Ball x r := by
    ext y
    simp only [mem_preimage, mem_vec3Ball, sub_zero]
  have hmp : MeasurePreserving (fun y : Vec3 => y - x)
      (volume.restrict (vec3Ball x r)) (volume.restrict (vec3Ball (0 : Vec3) r)) := by
    have h := (measurePreserving_sub_right (volume : Measure Vec3) x).restrict_preimage
      (isOpen_vec3Ball (0 : Vec3) r).measurableSet
    rwa [hpre] at h
  have hback := hg.comp_measurePreserving hmp
  have hbackloc : LocallyIntegrableOn (fun y => g (y - x)) (vec3Ball x r) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hback.locallyIntegrable (by norm_num))
  have himage : vec3Ball (0 : Vec3) r = scalingSpace 1 (-x) '' vec3Ball x r := by
    ext y
    constructor
    · intro hy
      refine ⟨x + y, ?_, ?_⟩
      · simpa only [mem_vec3Ball, add_sub_cancel_left, sub_zero] using hy
      · simp [scalingSpace]
    · rintro ⟨z, hz, rfl⟩
      simpa [scalingSpace, mem_vec3Ball, sub_eq_add_neg, add_comm] using hz
  have hbw := hasWeakPartialDerivOn_scaling 1 (by norm_num) (-x)
    (isOpen_vec3Ball (0 : Vec3) r).measurableSet i himage hgw hpm hg.aestronglyMeasurable
  have hbackw : HasWeakPartialDerivOn (vec3Ball x r) i p (fun y => g (y - x)) := by
    simpa [scalingSpace, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbw
  have heq := HasWeakPartialDerivOn.ae_eq ((isOpen_vec3Ball x r).inter hB)
    (hDloc.mono_set inter_subset_right) (hbackloc.mono_set inter_subset_left)
    (hDw.restrict ((isOpen_vec3Ball x r).inter hB) inter_subset_right)
    (hbackw.restrict ((isOpen_vec3Ball x r).inter hB) inter_subset_left)
  rw [eLpNorm_congr_ae heq]
  apply (eLpNorm_mono_measure _ (Measure.restrict_mono inter_subset_left le_rfl)).trans
  exact (eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hmp).le.trans hgK

private theorem fixed_window_cover {I : Set ℝ} (hI : IsOpen I) (hc : I.OrdConnected)
    (hunit : Icc (-1 : ℝ) 0 ⊆ I) {l : ℝ} (hl : 0 < l) (hlone : l < 1)
    {s : ℝ} (hs : s ∈ I) :
    ∃ t : ℚ, Icc ((t : ℝ) - l) t ⊆ I ∧ s ∈ Ioc ((t : ℝ) - l) t := by
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp hI s hs
  have hleft : s - ε / 2 ∈ I := by
    apply he
    rw [Metric.mem_ball, Real.dist_eq]
    have hh : s - ε / 2 - s = -(ε / 2) := by ring
    rw [hh, abs_neg, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith only [hε]
  have hright : s + ε / 2 ∈ I := by
    apply he
    rw [Metric.mem_ball, Real.dist_eq]
    have hh : s + ε / 2 - s = ε / 2 := by ring
    rw [hh, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith only [hε]
  let a := min (s - ε / 2) (-1)
  let b := max (s + ε / 2) 0
  have ha : a ∈ I := by
    dsimp [a]
    rcases le_total (s - ε / 2) (-1) with h | h
    · simpa only [min_eq_left h] using hleft
    · simpa only [min_eq_right h] using hunit (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 0)
  have hb : b ∈ I := by
    dsimp [b]
    rcases le_total 0 (s + ε / 2) with h | h
    · simpa only [max_eq_left h] using hright
    · simpa only [max_eq_right h] using hunit (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 0)
  have has : a < s := (min_le_left _ _).trans_lt (by linarith only [hε])
  have hsb : s < b := (show s < s + ε / 2 by linarith only [hε]).trans_le (le_max_left _ _)
  have hab : a + l < b := by
    have hamin : a ≤ -1 := min_le_right _ _
    have hbmax : 0 ≤ b := le_max_right _ _
    linarith only [hamin, hbmax, hlone]
  have hgap : max (a + l) s < min b (s + l) := by
    exact max_lt (lt_min hab (by linarith only [has]))
      (lt_min hsb (by linarith only [hl]))
  obtain ⟨t, htlo, hthi⟩ := exists_rat_btwn hgap
  have hat : a < (t : ℝ) - l := by
    have hh := (le_max_left (a + l) s).trans_lt htlo
    linarith only [hh]
  have htb : (t : ℝ) < b := hthi.trans_le (min_le_left _ _)
  refine ⟨t, ?_, ?_, ?_⟩
  · intro y hy
    exact hc.out ha hb ⟨(hat.trans_le hy.1).le, (hy.2.trans_lt htb).le⟩
  · have hh := hthi.trans_le (min_le_right _ _)
    linarith only [hh]
  · exact ((le_max_right (a + l) s).trans_lt htlo).le

/-- Estimates on all contained windows of one fixed length hold almost
everywhere on the entire solution interval containing the unit window. -/
theorem theoremA_ae_of_fixed_windows {I : Set ℝ} (hI : IsOpen I) (hc : I.OrdConnected)
    (hunit : Icc (-1 : ℝ) 0 ⊆ I) {l : ℝ} (hl : 0 < l) (hlone : l < 1)
    {P : ℝ → Prop}
    (hlocal : ∀ t : ℝ, Icc (t - l) t ⊆ I → ∀ᵐ s ∂volume.restrict (Ioc (t - l) t), P s) :
    ∀ᵐ s ∂volume.restrict I, P s := by
  have hf (t : ℚ) : ∀ᵐ s ∂volume.restrict I,
      Icc ((t : ℝ) - l) t ⊆ I → s ∈ Ioc ((t : ℝ) - l) t → P s := by
    by_cases ht : Icc ((t : ℝ) - l) t ⊆ I
    · exact ae_restrict_of_ae ((ae_imp_of_ae_restrict (hlocal t ht)).mono (fun _ h _ => h))
    · exact Eventually.of_forall (fun _ h => absurd h ht)
  filter_upwards [ae_all_iff.mpr hf, ae_restrict_mem hI.measurableSet] with s hs hsI
  obtain ⟨t, htI, hst⟩ := fixed_window_cover hI hc hunit hl hlone hsI
  exact hs t htI hst

/-- A fixed translated source ball controls the carrier overlap for almost
every time in the entire suitable-solution interval. -/
theorem theoremA_carrier_overlap_slice_bound
    {Ω : Set Vec3} {I : Set ℝ} {q ρ R : ℝ} {x : Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hunit : Icc (-1 : ℝ) 0 ⊆ I) (hρ : 0 < ρ) (hρone : ρ < 1)
    (hball : closure (vec3Ball x ρ) ⊆ Ω)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R) i
        (fun y => p (y,s)) (fun y => Dp (y,s) i)) :
    ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      eLpNorm (fun y => Dp (y,s) i) (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball x (ρ/2) ∩ vec3Ball (0 : Vec3) R)) ≤
          theoremATranslatedSliceMajorant u Du p f x hρ s := by
  apply theoremA_ae_of_fixed_windows hsol.2.1 hsol.2.2.1 hunit
    (sq_pos_of_pos hρ) (by nlinarith only [hρ, hρone])
  intro t ht
  have htime : Ioc (t - ρ^2) t ⊆ I := Ioc_subset_Icc_self.trans ht
  have htshift : rescaledTime 1 0 I = I := by ext s; simp [rescaledTime, scalingTime]
  have hshift := isSuitableWeakSolutionIntegrable_rescale hsol (x, 0) (by norm_num : (0 : ℝ) < 1)
  rw [htshift] at hshift
  have hsub : closure (parabolicCylinder (0 : Vec3) t ρ) ⊆
      spaceTimeSet (rescaledSpace 1 x Ω) I := by
    rw [closure_parabolicCylinder hρ]
    intro w hw
    refine ⟨?_, ht hw.2⟩
    apply hball
    rw [closure_vec3Ball hρ]
    simpa [scalingSpace] using hw.1
  have hlocal := origin_local_slice_gradient_bound_ae_of_sws (z := ((0 : Vec3), t)) hshift hρ hsub
  have hpressure := sws_pressure_memLp_slice_ae (z := ((0 : Vec3), t)) hshift hρ hsub
  filter_upwards [hlocal, hpressure, ae_restrict_of_ae_restrict_of_subset htime hfield]
    with s hs hp hf
  obtain ⟨D, hloc, hmem, hweak, hnorm⟩ := hs
  have hhalf := CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
    (x₀ := (0 : Vec3)) (by positivity : 0 < ρ / 2)
  rw [hhalf] at hloc hmem hweak hnorm
  have hp' := hp.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono (vec3Ball_mono (x := (0 : Vec3))
      (by linarith only [hρ] : ρ / 2 ≤ ρ)) le_rfl)
  intro i
  have hw : HasWeakPartialDerivOn (vec3Ball (0 : Vec3) (ρ / 2)) i
      (fun y => p (x + y,s)) (fun y => D y i) := by
    simpa [rescalePressure, parabolicTranslate, parabolicScale] using hweak i
  have hpm : AEStronglyMeasurable (fun y => p (x + y,s))
      (volume.restrict (vec3Ball (0 : Vec3) (ρ/2))) := by
    simpa [rescalePressure, parabolicTranslate, parabolicScale] using hp'
  exact theoremA_translated_slice_bound_on_intersection (isOpen_vec3Ball _ _) i
    hpm (hmem.eval i) hw (hnorm i) (hf i).1 (hf i).2

private theorem source_radius_lt_one {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closure (vec3Ball x ρ) ⊆ vec3Ball (0 : Vec3) 1) : ρ < 1 := by
  let v : Vec3 := fun k => if k = 0 then ρ else 0
  have hv : vec3EuclideanNorm v = ρ := by
    simp [vec3EuclideanNorm, v, Real.sqrt_sq_eq_abs, abs_of_pos hρ]
  have hp : x + v ∈ closure (vec3Ball x ρ) := by
    rw [closure_vec3Ball hρ]
    change vec3EuclideanNorm (x + v - x) ≤ ρ
    simp only [add_sub_cancel_left, hv, le_refl]
  have hm : x - v ∈ closure (vec3Ball x ρ) := by
    rw [closure_vec3Ball hρ]
    have he : x - v - x = -v := by abel
    change vec3EuclideanNorm (x - v - x) ≤ ρ
    simp only [he, vec3EuclideanNorm_neg, hv, le_refl]
  have hpn : vec3EuclideanNorm (x + v) < 1 := by
    simpa only [mem_vec3Ball, sub_zero] using hball hp
  have hmn : vec3EuclideanNorm (x - v) < 1 := by
    simpa only [mem_vec3Ball, sub_zero] using hball hm
  have hsub := vec3EuclideanNorm_sub_le (x + v) (x - v)
  have he : x + v - (x - v) = (2 : ℝ) • v := by module
  rw [he, vec3EuclideanNorm_smul, hv] at hsub
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsub
  linarith only [hsub, hpn, hmn]

/-- Suitability supplies the fixed finite-cover slice estimate. All source
centres and the common radius are selected before the solution fields. -/
theorem theoremA_carrier_finite_cover_estimate :
      ∀ R₁ : ℝ, 0 < R₁ → R₁ < 3 / 4 →
      ∃ (n : ℕ) (x : Fin n → Vec3) (ρ : ℝ) (hρ : 0 < ρ),
        (∀ j, closure (vec3Ball (x j) ρ) ⊆ vec3Ball (0 : Vec3) 1) ∧
        ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
          {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
          {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
          ∀ Dp : ParabolicPoint → Vec3, Measurable Dp →
          (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
            LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
            HasWeakPartialDerivOn (vec3Ball 0 R₁) i
              (fun y => p (y, s)) (fun y => Dp (y, s) i)) →
          ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict I,
            eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
                (volume.restrict (vec3Ball 0 R₁)) ≤
              ∑ j, theoremATranslatedSliceMajorant u Du p f (x j) hρ s := by
  intro R₁ hR₁ hR₁upper
  obtain ⟨n, x, ρ, hρ, hballs, hcover⟩ := originCarrier_exists_finite_spatial_cover
    hR₁ (by linarith only [hR₁upper])
  have hzero : (0 : Vec3) ∈ closure (vec3Ball (0 : Vec3) R₁) :=
    subset_closure (by simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using hR₁)
  obtain ⟨j₀, _⟩ := mem_iUnion.mp (hcover hzero)
  have hρone := source_radius_lt_one hρ (hballs j₀)
  refine ⟨n, x, ρ, hρ, hballs, ?_⟩
  intro Ω I q u Du p f hsol hdom Dp hDp hfield
  obtain ⟨hΩ, hI⟩ := OriginInstance.originUnitBall_subset_of_dom hdom
  have hb (j : Fin n) : closure (vec3Ball (x j) ρ) ⊆ Ω := by
    intro y hy
    apply hΩ
    exact (show vec3EuclideanNorm (y - 0) < 1 from hballs j hy).le
  have hl (j : Fin n) := theoremA_carrier_overlap_slice_bound hsol hI hρ hρone (hb j) hfield
  intro i
  filter_upwards [ae_all_iff.mpr hl] with s hs
  let g : Vec3 → ℝ := (vec3Ball (0 : Vec3) R₁).indicator (fun y => Dp (y,s) i)
  have hK := (isOpen_vec3Ball (0 : Vec3) R₁).measurableSet
  have hg : Measurable g := (((measurable_pi_apply i).comp hDp).comp
    (measurable_id.prodMk measurable_const)).indicator hK
  have hn := theoremA_slice_norm_le_finite_cover (subset_closure.trans hcover) hg
  have hn' : eLpNorm (fun y => Dp (y,s) i) (ENNReal.ofReal (6/5 : ℝ))
      (volume.restrict (vec3Ball (0 : Vec3) R₁)) ≤
      ∑ j, eLpNorm (fun y => Dp (y,s) i) (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball (x j) (ρ/2) ∩ vec3Ball (0 : Vec3) R₁)) := by
    simpa only [g, eLpNorm_indicator_eq_eLpNorm_restrict hK,
      Measure.restrict_restrict hK, inter_self, inter_comm] using hn
  exact hn'.trans (Finset.sum_le_sum (fun j _ => hs j i))

/-- The explicit moment budget for the sum of the harmonic and far-force
majorants, in terms of numerical bounds on their input moments. -/
def theoremARemainderMomentBudget (Ch Cf E Kp Kf timeVolume : ℝ≥0∞) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
    (Ch ^ (3 / 2 : ℝ) * ((2 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
      (E ^ (3 / 2 : ℝ) * timeVolume + Kp)) + Cf ^ (3 / 2 : ℝ) * Kf)

private theorem add_moment_bound {J : Set ℝ} {P F : ℝ → ℝ≥0∞}
    (hP : AEMeasurable P (volume.restrict J))
    (hF : AEMeasurable F (volume.restrict J)) :
    (∫⁻ s in J, (P s + F s) ^ (3 / 2 : ℝ)) ≤
      (2 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
        ((∫⁻ s in J, P s ^ (3 / 2 : ℝ)) + ∫⁻ s in J, F s ^ (3 / 2 : ℝ)) := by
  calc
    _ ≤ ∫⁻ s in J, (2 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
        (P s ^ (3 / 2 : ℝ) + F s ^ (3 / 2 : ℝ)) :=
      lintegral_mono (fun s => ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ (by norm_num))
    _ = _ := by
      have hm : AEMeasurable (fun s => P s ^ (3 / 2 : ℝ) + F s ^ (3 / 2 : ℝ))
          (volume.restrict J) := (hP.pow_const _).add (hF.pow_const _)
      rw [lintegral_const_mul'' _ hm, lintegral_add_left' (hP.pow_const (3 / 2 : ℝ))]

/-- Numerical bounds for pressure, force and energy give an explicit
`3/2` moment bound for the concrete derivative remainder envelope. -/
theorem theoremA_remainder_moment_le_budget
    (Ch Cf E Kp Kf timeVolume : ℝ≥0∞) {J : Set ℝ} {P F : ℝ → ℝ≥0∞}
    (hP : AEMeasurable P (volume.restrict J))
    (hF : AEMeasurable F (volume.restrict J))
    (hJ : volume J ≤ timeVolume)
    (hpressure : (∫⁻ s in J, P s ^ (3 / 2 : ℝ)) ≤ Kp)
    (hforce : (∫⁻ s in J, F s ^ (3 / 2 : ℝ)) ≤ Kf) :
    (∫⁻ s in J, (Ch * (E + P s) + Cf * F s) ^ (3 / 2 : ℝ)) ≤
      theoremARemainderMomentBudget Ch Cf E Kp Kf timeVolume := by
  have he := add_moment_bound (J := J) (P := fun _ => E) aemeasurable_const hP
  rw [lintegral_const, Measure.restrict_apply_univ] at he
  have he' : (∫⁻ s in J, (E + P s) ^ (3 / 2 : ℝ)) ≤
      (2 : ℝ≥0∞) ^ (3 / 2 : ℝ) * (E ^ (3 / 2 : ℝ) * timeVolume + Kp) :=
    he.trans (mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hJ) hpressure))
  have hh := add_moment_bound
    (aemeasurable_const.mul (aemeasurable_const.add hP)) (aemeasurable_const.mul hF)
    (P := fun s => Ch * (E + P s)) (F := fun s => Cf * F s)
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2)] at hh
  have hm : AEMeasurable (fun s => (E + P s) ^ (3 / 2 : ℝ)) (volume.restrict J) :=
    (aemeasurable_const.add hP).pow_const _
  rw [lintegral_const_mul'' _ hm,
    lintegral_const_mul'' _ (hF.pow_const (3 / 2 : ℝ))] at hh
  exact hh.trans (mul_le_mul' le_rfl
    (add_le_add (mul_le_mul' le_rfl he') (mul_le_mul' le_rfl hforce)))

/-- Every source box inside the unit cylinder inherits uniform pressure and
force time-moment bounds from the original data size. -/
theorem theoremA_patch_pressure_force_moments
    (q ε : ℝ) (hq : 5 / 2 < q) {B : Set Vec3} {J : Set ℝ}
    (hpatch : B ×ˢ J ⊆ parabolicCylinder (0 : Vec3) 0 1)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
      ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
      ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    ((∫⁻ s in J, eLpNorm (fun y => p (y,s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict B) ^ (3 / 2 : ℝ)) ≤ ENNReal.ofReal ε) ∧
    ((∫⁻ s in J, eLpNorm (fun y => vec3EuclideanNorm (f (y,s)))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B) ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal ε ^ ((3 / 2 : ℝ) / q) *
        volume (parabolicCylinder (0 : Vec3) 0 1) ^ (1 - (3 / 2 : ℝ) / q)) := by
  let Q := parabolicCylinder (0 : Vec3) 0 1
  obtain ⟨U,T,hbox,hQT⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1
    (by norm_num : (0 : ℝ) < 1) hdom
  have hd := hsol.2.2.2.2.2.1 U T hbox
  have hp := hd.2.2.1.aemeasurable.mono_measure
    (Measure.restrict_mono_set volume (hpatch.trans hQT))
  have hf : AEMeasurable (fun z : ParabolicPoint => vec3EuclideanNorm (f z))
      (volume.restrict Q) :=
    continuous_vec3EuclideanNorm.measurable.comp_aemeasurable
      (hd.2.2.2.1.aemeasurable.mono_measure (Measure.restrict_mono_set volume hQT))
  have hFpatch := hf.mono_measure (Measure.restrict_mono_set volume hpatch)
  constructor
  · rw [origin_time_slice_norm_power_eq (by norm_num : (0 : ℝ) < 3/2) hp]
    apply (lintegral_mono_set hpatch).trans
    apply le_trans _ hsize
    exact lintegral_mono (fun _ => (le_add_left le_rfl).trans (le_add_right le_rfl))
  · have hq0 : 0 < q := by linarith only [hq]
    have hexp : 0 < (3 / 2 : ℝ) / q := div_pos (by norm_num) hq0
    have hexp1 : (3 / 2 : ℝ) / q < 1 := (div_lt_one hq0).mpr (by linarith only [hq])
    have hmass : (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
        ENNReal.ofReal ε := (lintegral_mono (fun _ => le_add_left le_rfl)).trans hsize
    have hh := lintegral_rpow_le_rpow_lintegral_mul_measure
      (hf.ennreal_ofReal.pow_const q) hexp hexp1
    simp only [Measure.restrict_apply_univ, ← ENNReal.rpow_mul,
      show q * ((3 / 2 : ℝ) / q) = 3 / 2 by field_simp] at hh
    rw [origin_time_slice_norm_power_eq (by norm_num : (0 : ℝ) < 3/2) hFpatch]
    simp only [abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact (lintegral_mono_set hpatch).trans
      (hh.trans (mul_le_mul' (ENNReal.rpow_le_rpow hmass hexp.le) le_rfl))

end CKN.Core.Endgame
