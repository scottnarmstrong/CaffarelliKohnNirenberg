-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.CoordinateMultiplierBridge
import CKN.Core.HeatPotential.PastSourcesBridge
import CKN.Core.HeatPotential.PastSourcesSourceAdapter
import CKN.Core.Step4.InteriorGradientProducerStep2
import CKN.Core.Endgame.NestedCutoffs
import CKN.Core.Endgame.ForceSlotNumericalSupport
import CKN.Core.Endgame.CausalGradientMorrey
import CKN.Core.Endgame.CausalDerivativeSource
import CKN.Core.Endgame.CausalPressureExtension
import CKN.Core.Endgame.CausalBootstrap
import CKN.Core.Endgame.SourceExponents
import CKN.Core.Endgame.LocalBoxRestriction
import CKN.Core.Step3.GradientSlotDuhamel

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Endgame

open CKN.Core.HeatPotential
open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame CKN.Core.Step3 CKN.Core.Step4

private theorem past_sources_step2_compact_unit_cylinder :
    IsCompact (closure (parabolicCylinder (0 : Vec3) 0 1)) := by
  have hspace : IsCompact {x : Vec3 | vec3EuclideanNorm (x - 0) ≤ 1} := by
    have hcompact := vec3Homeomorph.isCompact_preimage.mpr
      (isCompact_closedBall (vec3Homeomorph (0 : Vec3)) 1)
    convert hcompact using 1
    ext x
    simp only [mem_ofPred_eq, mem_preimage, Metric.mem_closedBall,
      vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
      vec3EuclideanNorm_eq_l2]
  apply parabolicHomeomorph.symm.isCompact_preimage.mp
  rw [closure_parabolicCylinder one_pos]
  exact hspace.prod isCompact_Icc

private theorem past_sources_step2_compact_of_unit_zero
    {g : ParabolicPoint → ℝ}
    (hzero : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 1, g z = 0) :
    HasCompactSupport g := by
  apply HasCompactSupport.of_support_subset_isCompact
    past_sources_step2_compact_unit_cylinder
  intro z hz
  apply subset_closure
  by_contra hnot
  exact hz (hzero z hnot)

theorem exists_past_heat_sources_of_step2
    (q : ℝ) (hq : 5 / 2 < q) (ε₀ K : ℝ) (hε₀ : 0 ≤ ε₀) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∃ σ : Fin N → Vec3 → ℂ, ∃ KF KG : ℝ≥0∞,
      (∀ k, SmoothOffOrigin (σ k)) ∧
      (∀ k, IsDegreeOneHomogeneous (σ k)) ∧
      KF < ⊤ ∧ KG < ⊤ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        let Q₂s : Set ParabolicPoint :=
          vec3Ball 0 (5 / 8) ×ˢ Ioc (-(25 / 64 : ℝ)) 0
        (∀ i : Fin 3,
          morreyBallNorm 3 stepTau₂ (Q₂s.indicator (fun z => u z i)) ≤
            ENNReal.ofReal K) →
        (∀ i j : Fin 3,
          morreyBallNorm 2 stepTau₃ (Q₂s.indicator (fun z => Du z i j)) ≤
            ENNReal.ofReal K) →
        morreyBallNorm (3 / 2) stepTauP (Q₂s.indicator p) ≤ ENNReal.ofReal K →
        ∃ Fminus : ParabolicPoint → Vec3,
        ∃ Gminus : Fin N → ParabolicPoint → Vec3,
          (∀ i : Fin 3, AEMeasurable (fun z => Fminus z i) volume) ∧
          (∀ (j : Fin N) (i : Fin 3), AEMeasurable (fun z => Gminus j z i) volume) ∧
          (∀ i : Fin 3,
            morreyNorm (6 / 5) (stepTheta₀ (stepGamma₀ q))
              (fun z => Fminus z i) ≤ KF) ∧
          (∀ (j : Fin N) (i : Fin 3),
            morreyNorm (6 / 5) (stepTheta₁ (stepGamma₀ q))
              (fun z => Gminus j z i) ≤ KG) ∧
          (∀ i : Fin 3, HasCompactSupport (fun z => Fminus z i)) ∧
          (∀ (j : Fin N) (i : Fin 3), HasCompactSupport (fun z => Gminus j z i)) ∧
          (∀ z : ParabolicPoint, z ∉ Q₂s → Fminus z = 0) ∧
          (∀ j : Fin N, ∀ z : ParabolicPoint, z ∉ Q₂s → Gminus j z = 0) ∧
          (∀ i : Fin 3,
            (fun z => (u z i : ℂ)) =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))]
              multiplierHeatPotential σ (fun y => Fminus y i)
                (fun k y => Gminus k y i)) ∧
          (∀ i : Fin 3, ∀ᵐ w ∂volume,
            Integrable (fun v =>
              (heatKernelPlus (pointSub w v) : ℂ) * (Fminus v i : ℂ)) volume ∧
            ∀ k, Integrable (fun v =>
              spatialMultiplierHeatKernel (σ k) (pointSub w v).1
                (pointSub w v).2 * (Gminus k v i : ℂ)) volume) ∧
          (∀ i : Fin 3, ∀ᵐ w ∂volume,
            multiplierHeatPotential σ (fun y => Fminus y i)
                (fun k y => Gminus k y i) w =
              (∫ s : ℝ, spatialHeatConv (w.2 - s)
                (fun y : Vec3 => (Fminus (y, s) i : ℂ)) w.1) +
              ∑ k, ∫ s : ℝ, spatialMultiplierApply (σ k)
                (spatialHeatConv (w.2 - s)
                  (fun y : Vec3 => (Gminus k (y, s) i : ℂ))) w.1) := by
  have _hK : 0 ≤ K := hK
  let σ : Fin 3 → Vec3 → ℂ := fun k => coordinateMultiplierSymbol k
  have hσ : ∀ k, SmoothOffOrigin (σ k) := by
    intro k
    exact coordinateMultiplierSymbol_smoothOffOrigin k
  have hhom : ∀ k, IsDegreeOneHomogeneous (σ k) := by
    intro k
    exact coordinateMultiplierSymbol_isDegreeOneHomogeneous k
  obtain ⟨ψ, C, hC, hψsmooth, hψcompact, hcut⟩ :=
    exists_uniform_nested_cutoff_derivative_bound
      (1 / 2) (33 / 64) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨KU, KP, hKU, hKP, hround⟩ :=
    exists_interior_first_round_of_step2_data q ε₀ K hq hε₀
  let Csrc : ℝ≥0∞ :=
    causalGradientMorreyBound q ε₀ C KU (ENNReal.ofReal K) KP
  let Cder : ℝ≥0∞ := causalDerivativeMorreyBound C (ENNReal.ofReal K)
  have hCsrc : Csrc < ⊤ := by
    dsimp [Csrc]
    exact causalGradientMorreyBound_lt_top q ε₀ C hq hKU
      ENNReal.ofReal_lt_top hKP
  have hCder : Cder < ⊤ := by
    dsimp [Cder]
    exact causalDerivativeMorreyBound_lt_top C ENNReal.ofReal_lt_top
  refine ⟨3, σ, Csrc, Cder, ?_, ?_, hCsrc, hCder, ?_⟩
  · intro k
    simpa [σ] using hσ k
  · intro k
    simpa [σ] using hhom k
  · intro Ω I u Du p f hsol hdom hsmall Q₂s hUball hDball hpball
    dsimp only [Q₂s] at hUball hDball hpball ⊢
    have hUball' := hUball
    have hDball' := hDball
    rw [pastCarrier_eq_parabolicCylinder] at hUball' hDball'
    have hUinitial : ∀ i : Fin 3, morreyNorm 3 (25 / 3 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
          (fun z => u z i)) ≤ ENNReal.ofReal K := by
      intro i
      exact (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans
        (hUball' i)
    have hD : ∀ i j : Fin 3, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
          (fun z => Du z i j)) ≤ ENNReal.ofReal K := by
      intro i j
      exact (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans
        (hDball' i j)
    obtain ⟨hU, ⟨Dp, hDpAE, hDpInt, hDpWeak, hDpNorm⟩⟩ :=
      hround Ω I u Du p f hsol hdom hsmall hUball hDball
    obtain ⟨φ, Ω', J, hφ, hbox, hφbox, hφrange, hφone, hφsupp,
      hφspace, hφgerm, hφder⟩ := hcut Ω I hsol.1 hsol.2.1 hdom
    have hDpSub : parabolicCylinder (0 : Vec3) 0 (17 / 32) ⊆
        spaceTimeSet (vec3Ball (0 : Vec3) (17 / 32)) I := by
      intro z hz
      exact ⟨hz.1, (hdom (subset_closure
        (parabolicCylinder_mono (by norm_num) (by norm_num) hz))).2⟩
    have hDpAE' : ∀ i, AEMeasurable
        ((parabolicCylinder (0 : Vec3) 0 (17 / 32)).indicator
          (fun z => Dp z i)) volume := by
      intro i
      apply (aemeasurable_indicator_iff
        ((vec3Ball_measurable _ _).prod measurableSet_Ioc)).mpr
      exact (hDpAE i).mono_measure
        (Measure.restrict_mono (μ := volume) hDpSub le_rfl)
    let Fminus : ParabolicPoint → Vec3 := fun z i =>
      causalGradientSourceComponent φ u Du f Dp i z
    let Gminus : Fin 3 → ParabolicPoint → Vec3 := fun j z i =>
      causalDerivativeComponent φ u j i z
    have hsource := causal_gradient_source_local_of_step2
      q ε₀ C KU (ENNReal.ofReal K) KP hq hC.le hsol hdom hφ hφrange
      hφsupp
      (fun z ht => ⟨(hφder z ht).2.1,
        (hφder z ht).2.2.1, (hφder z ht).2.2.2⟩)
      hU hD hDpAE' hDpNorm hsmall
    have hderiv := causal_derivative_source_of_suitableWeakSolution
      C (ENNReal.ofReal K) hC.le hsol hdom hφ
      (fun z hz ht => parabolicCylinder_mono (by norm_num) (by norm_num)
        (hφsupp z hz ht))
      (fun z hz j => (hφder z hz).2.2.1 j) hUinitial
    have hφsupp5 : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
        parabolicHomeomorph.symm z ∈
          parabolicCylinder (0 : Vec3) 0 (5 / 8) := by
      intro z hz ht
      exact parabolicCylinder_mono (by norm_num) (by norm_num)
        (hφsupp z hz ht)
    have hFzero : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8),
        Fminus z = 0 := by
      intro z hz
      funext i
      exact causalGradientSourceComponent_zero_outside_intermediate
        hφ.1 hφsupp5 u Du f Dp i hz
    have hGzero : ∀ j z, z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) →
        Gminus j z = 0 := by
      intro j z hz
      funext i
      exact causalDerivativeComponent_zero_outside_intermediate
        (u := u) hφ.1 hφsupp5 j i hz
    have hFunit : ∀ z, z ∉ parabolicCylinder (0 : Vec3) 0 1 →
        Fminus z = 0 := by
      intro z hz
      exact hFzero z (fun hz' => hz (parabolicCylinder_mono
        (by norm_num) (by norm_num) hz'))
    have hGunit : ∀ j z, z ∉ parabolicCylinder (0 : Vec3) 0 1 →
        Gminus j z = 0 := by
      intro j z hz
      exact hGzero j z (fun hz' => hz (parabolicCylinder_mono
        (by norm_num) (by norm_num) hz'))
    have hFae : ∀ i, AEMeasurable (fun z => Fminus z i) volume := by
      intro i
      simpa [Fminus] using (hsource i).1
    have hGae : ∀ j i, AEMeasurable (fun z => Gminus j z i) volume := by
      intro j i
      simpa [Gminus] using (hderiv j i).1
    have hFraw : ∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
        (fun z => Fminus z i) ≤ Csrc := by
      intro i
      simpa [Csrc, Fminus] using (hsource i).2
    have hGraw : ∀ j i, morreyNorm (6 / 5) (25 / 3 : ℝ)
        (fun z => Gminus j z i) ≤ Cder := by
      intro j i
      simpa [Cder, Gminus, causalDerivativeMorreyBound] using (hderiv j i).2
    have hGunitComp : ∀ j i z,
        z ∉ parabolicCylinder (0 : Vec3) 0 1 → Gminus j z i = 0 := by
      intro j i z hz
      exact congrFun (hGunit j z hz) i
    obtain ⟨hFbound, hGbound⟩ := source_norm_bounds_at_holder_exponents_unit
      q Csrc Cder hq hFraw hGraw hGunitComp
    have hFcompact : ∀ i, HasCompactSupport (fun z => Fminus z i) := by
      intro i
      exact past_sources_step2_compact_of_unit_zero
        (fun z hz => congrFun (hFunit z hz) i)
    have hGcompact : ∀ j i, HasCompactSupport (fun z => Gminus j z i) := by
      intro j i
      exact past_sources_step2_compact_of_unit_zero
        (fun z hz => congrFun (hGunit j z hz) i)
    have hFfinite : ∀ i, morreyNorm (6 / 5)
        (stepTheta₀ (stepGamma₀ q)) (fun z => Fminus z i) < ∞ := by
      intro i
      exact (hFbound i).trans_lt hCsrc
    have hGfinite : ∀ j i, morreyNorm (6 / 5)
        (stepTheta₁ (stepGamma₀ q)) (fun z => Gminus j z i) < ∞ := by
      intro j i
      exact (hGbound j i).trans_lt hCder
    have hP : (1 : ℝ) ≤ 6 / 5 := by norm_num
    have hPθ₀ : (6 / 5 : ℝ) ≤ stepTheta₀ (stepGamma₀ q) := by
      linarith only [stepTheta₀_gt_half (stepGamma₀_pos hq) (stepGamma₀_lt_one q)]
    have hPθ₁ : (6 / 5 : ℝ) ≤ stepTheta₁ (stepGamma₀ q) := by
      linarith only [stepTheta₁_gt_five (stepGamma₀_pos hq) (stepGamma₀_lt_one q)]
    have hclauses := past_source_kernel_clauses_of_morrey_data
      hP hPθ₀ hPθ₁ σ hσ hhom hFae hGae hFfinite hGfinite
        hFcompact hGcompact
    have hbox' := localBox_inter_spatial_open hbox
      (isOpen_vec3Ball (0 : Vec3) (17 / 32))
    have hφspace' : ∀ z ∈ tsupport φ,
        z.1 ∈ vec3Ball (0 : Vec3) (17 / 32) := by
      intro z hz
      exact vec3Ball_mono (by norm_num) (hφspace z hz)
    have hφbox' := support_subset_inter_spatial_box hφbox hφspace'
    have hDpInt' := fun i => hDpInt _ J hbox' inter_subset_right i
    have hDpWeak' : ∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
        tsupport ψ ⊆ (Ω' ∩ vec3Ball (0 : Vec3) (17 / 32)) ×ˢ J →
        (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
          -(∫ z : ParabolicPoint, Dp z i * ψ z) := by
      intro i ψ hψ hψbox
      apply hDpWeak i ψ hψ
      intro z hz
      have hm := hψbox hz
      exact ⟨hm.1.2, hbox.2.2.2.2.2 (subset_closure hm.2)⟩
    have hrepHeat := localized_gradient_slot_duhamel_of_sws
      hsol hφ hbox' hφbox' hDpInt' hDpWeak'
    have hplateau : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (1 / 2),
        φ z = 1 := by
      intro z hz
      have hnear := hφone (z.1, z.2) (subset_closure hz)
      exact hnear.eq_of_nhds
    have hQhalf : MeasurableSet (parabolicCylinder (0 : Vec3) 0 (1 / 2)) :=
      measurableSet_parabolicCylinder _ _ _
    have hrepLocal : u =ᵐ[volume.restrict (parabolicCylinder (0 : Vec3) 0 (1 / 2))]
        vectorHeatPotential (fun z i => Fminus z i)
          (fun j z i => Gminus j z i) := by
      have hrepHeat' : localizedVelocity φ u =ᵐ[
          volume.restrict (parabolicCylinder (0 : Vec3) 0 (1 / 2))]
          (fun z i => heatPotential
            (fun w => localizedGradientSourceG φ u Du f Dp w i)
            (fun j w => localizedGradientSourceH φ u j w i) z) := by
        exact hrepHeat.filter_mono (ae_mono Measure.restrict_le_self)
      filter_upwards [hrepHeat', ae_restrict_mem hQhalf] with z hz hzQ
      have hφz := hplateau z hzQ
      funext i
      have hz_i := congrFun hz i
      have htime := heatPotential_time_truncation
        (fun y => localizedGradientSourceG φ u Du f Dp y i)
        (fun k y => localizedGradientSourceH φ u k y i) hzQ.2.2
      change u z i = heatPotential (fun y => Fminus y i)
        (fun k y => Gminus k y i) z
      simpa only [localizedVelocity, hφz, one_smul, vectorHeatPotential,
        Fminus, Gminus, causalGradientSourceComponent,
        causalDerivativeComponent] using hz_i.trans htime.symm
    have hQeq : (vec3Ball (0 : Vec3) (5 / 8) ×ˢ Ioc
        (-(25 / 64 : ℝ)) 0 : Set ParabolicPoint) =
        parabolicCylinder (0 : Vec3) 0 (5 / 8) := by
      rw [parabolicCylinder]
      norm_num
    refine ⟨Fminus, Gminus, hFae, hGae, hFbound, hGbound, hFcompact,
      hGcompact, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      change z ∉ (vec3Ball (0 : Vec3) (5 / 8) ×ˢ Ioc
        (-(25 / 64 : ℝ)) 0 : Set ParabolicPoint) at hz
      exact hFzero z (fun hz' => hz (hQeq.symm ▸ hz'))
    · intro j z hz
      change z ∉ (vec3Ball (0 : Vec3) (5 / 8) ×ˢ Ioc
        (-(25 / 64 : ℝ)) 0 : Set ParabolicPoint) at hz
      exact hGzero j z (fun hz' => hz (hQeq.symm ▸ hz'))
    · intro i
      filter_upwards [hrepLocal,
        ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)] with z hz hzQ
      have hcoord := multiplierHeatPotential_coordinate_eq_heatPotential
        (F := fun y => Fminus y i) (G := fun k y => Gminus k y i) z
      change u z i = multiplierHeatPotential σ
        (fun y => Fminus y i) (fun k y => Gminus k y i) z
      rw [hcoord]
      exact congrArg Complex.ofReal (congrFun hz i)
    · exact hclauses.1
    · exact hclauses.2

end CKN.Core.Endgame
