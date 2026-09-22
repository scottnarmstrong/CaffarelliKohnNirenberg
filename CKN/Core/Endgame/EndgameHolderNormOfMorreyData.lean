-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumericalClosure
import CKN.Core.Endgame.TheoremAClosersInstancesQ
import CKN.Core.Step4.PressureGradientOriginASlotFinal
import CKN.Core.Step4.PressureGradientOriginBSlotInstances

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Endgame

/-- Paper theorem `thm:endgame` and its proof: the finite
quantitative Holder representative obtained from the Step 2 decay data and
the three displayed local norms.  The pressure-gradient producer is
assembled from the two established Theorem A instance slots before the solution
quantifiers are entered. -/
theorem endgame_holder_norm_of_morrey_data
    (q M r₂ r₃ U P F : ℝ)
    (hq : 5 / 2 < q) (hM : 1 ≤ M) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hU : 0 ≤ U) (hP : 0 ≤ P) (hF : 0 ≤ F)
    :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
        (z₀ : ParabolicPoint),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
        (∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
          max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
            M * r ^ (2 / 5 : ℝ)) →
        eLpNorm (fun z => vec3EuclideanNorm (u z)) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal U →
        eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal P →
        eLpNorm (fun z => vec3EuclideanNorm (f z)) (ENNReal.ofReal q)
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal F →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (Metric.closedBall z₀ r₃)] u ∧
          ParabolicHolderVecNormLE (Metric.closedBall z₀ r₃) w (stepGamma₀ q) C ∧
          ∀ z ∈ Metric.ball z₀ r₃, IsRegularPoint Ω I u z := by
  let Cstar : ℝ → ℝ := fun q =>
    max (originASlotCorrectionThreshold originASlotM2Threshold q) bslotThresholdB
  let hGAInst := theoremA_hGA_of_integral_slots_instances_q Cstar
    (by
      intro q τ C_CZ R₀ R₁ ε KU KD hq' hτ hτhi hC hthreshold hinstances
        hR₁ hR₁R₀ hR₀ hε hKU hKD
      exact theoremA_aSlot_integral_instances q τ C_CZ R₀ R₁ ε KU KD hq' hτ hτhi hC
        ((le_max_left _ _).trans hthreshold) hinstances hR₁ hR₁R₀ hR₀ hε hKU hKD)
    (by
      intro q τ C_CZ R₀ R₁ ε KU KD hq' hτ hτhi hC hthreshold hinstances
        hR₁ hR₁R₀ hR₀ hε hKU hKD
      exact theoremA_bslot_integral_instances q τ C_CZ R₀ R₁ ε KU KD hq' hτ hτhi hC
        ((le_max_right _ _).trans hthreshold) hinstances hR₁ hR₁R₀ hR₀ hε hKU hKD)
  have hLSelected :
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u f Dp : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ), IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (φ : Vec3 × ℝ → ℝ) (U : Set Vec3) (J : Set ℝ),
        φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
        localBox Ω I U J → tsupport φ ⊆ U ×ˢ J →
        (∀ i, Integrable (fun z => Dp z i)
          (volume.restrict (spaceTimeSet U J))) →
        (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ U ×ˢ J →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
        localizedVelocity φ u =ᵐ[volume] (fun z i => heatPotential
          (fun w => localizedGradientSourceG φ u Du f Dp w i)
          (fun j w => localizedGradientSourceH φ u j w i) z) := by
    intro Ω I u f Dp Du p hsol φ U J hφ hbox hsupp hInt hweak
    exact CKN.Core.Step3.localized_gradient_slot_duhamel_of_sws
      hsol hφ hbox hsupp hInt hweak
  have hInitial :
      ∀ (q₀ C_CZ ε₀ : ℝ) (KU KD : ℝ≥0∞),
        5 / 2 < q₀ → 0 ≤ C_CZ → 0 ≤ ε₀ → KU < ⊤ → KD < ⊤ →
        Cstar q₀ ≤ C_CZ →
        ∃ KP : ℝ≥0∞, KP < ⊤ ∧
          ∀ {Ω : Set Vec3} {I : Set ℝ}
            {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
            {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
            IsSuitableWeakSolutionIntegrable Ω I q₀ u Du p f →
            closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
            (∀ i, morreyNorm 3 (25 / 3)
              ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
                (fun z => u z i)) ≤ KU) →
            (∀ i j, morreyNorm 2 (25 / 8)
              ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
                (fun z => Du z i j)) ≤ KD) →
            ((∫⁻ z in parabolicCylinder 0 0 1,
              ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q₀) ≤
              ENNReal.ofReal ε₀) →
            ∃ Dp : ParabolicPoint → Vec3,
              (∀ i, AEMeasurable (fun z => Dp z i)
                (volume.restrict (vec3Ball 0 (43 / 64) ×ˢ I))) ∧
              (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
                U ⊆ vec3Ball 0 (43 / 64) → ∀ i,
                Integrable (fun z => Dp z i)
                  (volume.restrict (spaceTimeSet U J))) ∧
              (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
                ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
                tsupport ψ ⊆ vec3Ball 0 (43 / 64) ×ˢ I →
                (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
                  -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
              (∀ i, morreyNorm (6 / 5) (25 / 11 : ℝ)
                ((parabolicCylinder (0 : Vec3) 0 (43 / 64)).indicator
                  (fun z => Dp z i)) ≤ KP) := by
    intro q₀ C_CZ ε₀ KU KD hq₀ hC hε hKU hKD hthreshold
    let KP := oneSidedPressureGradientKPAffine q₀ (25 / 3) C_CZ
      (11 / 16) (43 / 64) ε₀ KU KD
    obtain ⟨hKP, hout⟩ := hGAInst q₀ (25 / 3) C_CZ (11 / 16) (43 / 64)
      ε₀ KU KD hq₀ (by norm_num) (by norm_num) hC hthreshold
      (Or.inl ⟨rfl, rfl, rfl⟩) (by norm_num) (by norm_num) (by norm_num)
      hε hKU hKD
    refine ⟨KP, ?_, ?_⟩
    · simpa only [KP] using hKP
    · intro Ω I u Du p f hsol hdom hU hD hsmall
      obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hout hsol hdom hU hD hsmall
      refine ⟨Dp, hAE, hInt, hweak, ?_⟩
      intro i
      have hmin : min (((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹) q₀ = 25 / 11 := by
        rw [show ((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹ = 25 / 11 by norm_num]
        exact min_eq_left (by linarith only [hq₀])
      simpa only [KP, hmin] using hN i
  have hFinal :
      ∀ (q₀ C_CZ ε₀ : ℝ) (KU KD : ℝ≥0∞),
        5 / 2 < q₀ → 0 ≤ C_CZ → 0 ≤ ε₀ → KU < ⊤ → KD < ⊤ →
        Cstar q₀ ≤ C_CZ →
        ∃ KP : ℝ≥0∞, KP < ⊤ ∧
          ∀ {Ω : Set Vec3} {I : Set ℝ}
            {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
            {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
            IsSuitableWeakSolutionIntegrable Ω I q₀ u Du p f →
            closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
            (∀ i, morreyNorm 3 25
              ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
                (fun z => u z i)) ≤ KU) →
            (∀ i j, morreyNorm 2 (25 / 8)
              ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
                (fun z => Du z i j)) ≤ KD) →
            ((∫⁻ z in parabolicCylinder 0 0 1,
              ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q₀) ≤
              ENNReal.ofReal ε₀) →
            ∃ Dp : ParabolicPoint → Vec3,
              (∀ i, AEMeasurable (fun z => Dp z i)
                (volume.restrict (vec3Ball 0 (19 / 32) ×ˢ I))) ∧
              (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
                U ⊆ vec3Ball 0 (19 / 32) → ∀ i,
                Integrable (fun z => Dp z i)
                  (volume.restrict (spaceTimeSet U J))) ∧
              (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
                ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
                tsupport ψ ⊆ vec3Ball 0 (19 / 32) ×ˢ I →
                (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
                  -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
              (∀ i, morreyNorm (6 / 5) (min q₀ (25 / 9 : ℝ))
                ((parabolicCylinder (0 : Vec3) 0 (19 / 32)).indicator
                  (fun z => Dp z i)) ≤ KP) := by
    intro q₀ C_CZ ε₀ KU KD hq₀ hC hε hKU hKD hthreshold
    let KP := oneSidedPressureGradientKPAffine q₀ 25 C_CZ
      (5 / 8) (19 / 32) ε₀ KU KD
    obtain ⟨hKP, hout⟩ := hGAInst q₀ 25 C_CZ (5 / 8) (19 / 32)
      ε₀ KU KD hq₀ (by norm_num) (by norm_num) hC hthreshold
      (Or.inr ⟨rfl, rfl, rfl⟩) (by norm_num) (by norm_num) (by norm_num)
      hε hKU hKD
    refine ⟨KP, ?_, ?_⟩
    · simpa only [KP] using hKP
    · intro Ω I u Du p f hsol hdom hU hD hsmall
      obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hout hsol hdom hU hD hsmall
      refine ⟨Dp, hAE, hInt, hweak, ?_⟩
      intro i
      simpa only [KP, show (1 / (25 : ℝ) + 8 / 25)⁻¹ = 25 / 9 by norm_num,
        min_comm] using hN i
  have hUnit :
      ∀ (C_CZ ε : ℝ) (KU KD : ℝ≥0∞),
        0 ≤ C_CZ → 0 ≤ ε → KU < ⊤ → KD < ⊤ →
        Cstar q ≤ C_CZ →
        ∃ KU25 KP : ℝ≥0∞, KU25 < ⊤ ∧ KP < ⊤ ∧
          ∀ {Ω : Set Vec3} {I : Set ℝ}
            {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
            {p : ParabolicPoint → ℝ},
            IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
            closure (parabolicCylinder (0 : Vec3) 0 1) ⊆
              spaceTimeSet Ω I →
            (∀ i, morreyNorm 3 (25 / 3)
              ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
                (fun w => u w i)) ≤ KU) →
            (∀ i j, morreyNorm 2 (25 / 8)
              ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
                (fun w => Du w i j)) ≤ KD) →
            ((∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
              ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤
              ENNReal.ofReal ε) →
            (∀ i, morreyNorm 3 25
              ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
                (fun w => u w i)) ≤ KU25) ∧
            ∃ Dp : ParabolicPoint → Vec3,
              (∀ i, AEMeasurable (fun w => Dp w i)
                (volume.restrict (vec3Ball 0 (19 / 32) ×ˢ I))) ∧
              (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
                U ⊆ vec3Ball 0 (19 / 32) → ∀ i,
                Integrable (fun w => Dp w i)
                  (volume.restrict (spaceTimeSet U J))) ∧
              (∀ i (ψ : Vec3 × ℝ → ℝ),
                ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
                tsupport ψ ⊆ vec3Ball 0 (19 / 32) ×ˢ I →
                (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
                  -(∫ w : ParabolicPoint, Dp w i * ψ w)) ∧
              (∀ i, morreyNorm (6 / 5) (min q (25 / 9))
                ((parabolicCylinder (0 : Vec3) 0 (19 / 32)).indicator
                  (fun w => Dp w i)) ≤
                KP) := by
    intro C_CZ ε KU KD hC hε hKU hKD hthreshold
    obtain ⟨KI, hKI, hInitialPressure⟩ := hInitial q C_CZ ε KU KD
      hq hC hε hKU hKD hthreshold
    obtain ⟨KU25, hKU25, hboot⟩ := exists_uniform_bootstrap_of_initial_pressure
      q ε KU KD hq hKU hKD
      ⟨KI, hKI, by
        intro Ω I u f Du p hsol hdom hsmall hU hD
        exact hInitialPressure hsol hdom hU hD hsmall⟩
      hLSelected
    obtain ⟨KP, hKP, hFinalPressure⟩ := hFinal q C_CZ ε KU25 KD
      hq hC hε hKU25 hKD hthreshold
    refine ⟨KU25, KP, hKU25, hKP, ?_⟩
    intro Ω I u f Du p hsol hdom hU hD hsmall
    have hImproved := hboot Ω I u f Du p hsol hdom hU hD hsmall
    have hDsmall (i j : Fin 3) : morreyNorm 2 (25 / 8)
        ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
          (fun w => Du w i j)) ≤ KD := by
      apply le_trans (morreyNorm_mono (by norm_num) ?_) (hD i j)
      intro w
      by_cases hw : w ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8)
      · rw [indicator_of_mem hw, indicator_of_mem
          (parabolicCylinder_mono (by norm_num) (by norm_num) hw)]
      · rw [indicator_of_notMem hw, abs_zero]
        exact abs_nonneg _
    obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := hFinalPressure hsol hdom
      hImproved hDsmall hsmall
    refine ⟨hImproved, Dp, hAE, hInt, hweak, ?_⟩
    intro i
    simpa only [show ((1 / (25 : ℝ) + 8 / 25)⁻¹) = 25 / 9 by norm_num,
      min_comm] using hN i
  have hSelected :
      ∃ KU KD KU25 KP : ℝ≥0∞,
        KU < ⊤ ∧ KD < ⊤ ∧ KU25 < ⊤ ∧ KP < ⊤ ∧
        ∀ (Ω : Set Vec3) (I : Set ℝ)
          (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
          (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) (z₀ : ParabolicPoint),
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
          (∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
            max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
              M * r ^ (2 / 5 : ℝ)) →
          eLpNorm (fun w => vec3EuclideanNorm (u w)) (ENNReal.ofReal (10 / 3 : ℝ))
            (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal U →
          eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal P →
          eLpNorm (fun w => vec3EuclideanNorm (f w)) (ENNReal.ofReal q)
            (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal F →
          ∀ z ∈ Metric.closedBall z₀ r₃,
            (∀ i, morreyNorm 3 (25 / 3)
              ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
                (fun w => u w i)) ≤ KU) ∧
            (∀ i j, morreyNorm 2 (25 / 8)
              ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
                (fun w => Du w i j)) ≤ KD) ∧
            (∀ i, morreyNorm 3 25
              ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
                (fun w => u w i)) ≤ KU25) ∧
            ∃ Dp : ParabolicPoint → Vec3,
              (∀ i, Integrable (fun w => Dp w i)
                (volume.restrict (Metric.ball z (4 * endgameLocalRadius r₂ r₃)))) ∧
              (∀ i (ψ : Vec3 × ℝ → ℝ),
                ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
                tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹'
                  Metric.ball z (4 * endgameLocalRadius r₂ r₃) →
                (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
                  -(∫ w : ParabolicPoint, Dp w i * ψ w)) ∧
              (∀ i, morreyNorm (6 / 5) (min q (25 / 9))
                ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
                  (fun w => Dp w i)) ≤ KP) := by
    have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
    let a := endgameLocalRadius r₂ r₃
    let μ := 32 * a
    have ha : 0 < a := by
      dsimp [a, endgameLocalRadius]
      linarith only [hrr]
    have hμ : 0 < μ := by dsimp [μ]; positivity
    obtain ⟨KU, KD, Kpressure, hKU, hKD, _hKpressure, hstep⟩ :=
      step2_morrey_form_uniform M r₂ hM hr₂
    let KUn := ENNReal.ofReal |μ| *
      (ENNReal.ofReal μ ^ (-5 / (25 / 3) : ℝ) * KU)
    let KDn := ENNReal.ofReal |μ ^ 2| *
      (ENNReal.ofReal μ ^ (-5 / (25 / 8) : ℝ) * KD)
    let ε := (forceSlotEnergy q r₂ r₃ U P F).toReal
    have hKUn : KUn < ⊤ := force_slot_scaling_bound_lt_top _ _ _ hμ hKU
    have hKDn : KDn < ⊤ := force_slot_scaling_bound_lt_top _ _ _ hμ hKD
    let C_CZ := max (Cstar q) 0
    have hC_CZ : 0 ≤ C_CZ := le_max_right _ _
    have hthreshold : Cstar q ≤ C_CZ := le_max_left _ _
    obtain ⟨KU25n, KPn, hKU25n, hKPn, hboot⟩ := hUnit C_CZ ε KUn KDn
      hC_CZ ENNReal.toReal_nonneg hKUn hKDn hthreshold
    let KP := forceSlotUnscaledBound μ (μ ^ 3) (min q (25 / 9)) KPn
    refine ⟨KU, KD, forceSlotUnscaledBound μ μ 25 KU25n, KP,
      hKU, hKD, forceSlotUnscaledBound_lt_top _ _ _ hμ hKU25n,
      forceSlotUnscaledBound_lt_top _ _ _ hμ hKPn, ?_⟩
    intro Ω I u Du p f z₀ hsol hdom hdec hU hP hF z hz
    obtain ⟨hUb, hDb, _hPb⟩ := hstep hsol z₀ hdom hdec
    let b : ParabolicPoint := (z.1, z.2 + 16 * a ^ 2)
    have hsoln := isSuitableWeakSolutionIntegrable_rescale hsol b hμ
    have hdomn : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆
        spaceTimeSet (rescaledSpace μ b.1 Ω) (rescaledTime μ b.2 I) := by
      rw [rescaledSpaceTimeSet_eq_preimage]
      intro w hw
      apply hdom
      apply Metric.ball_subset_ball (by linarith only [hr₂] : r₂ / 4 ≤ 2 * r₂)
      exact force_slot_normalized_unit_subset_step2 hrr hz ⟨w, hw, rfl⟩
    have hUn (i : Fin 3) : morreyNorm 3 (25 / 3)
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
          (fun w => rescaleVelocity μ b u w i)) ≤ KUn :=
      force_slot_normalized_morrey_le 3 (25 / 3) μ (11 / 16) KU
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrr hz
        (fun w => u w i) (hUb i)
    have hDn (i j : Fin 3) : morreyNorm 2 (25 / 8)
        ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
          (fun w => rescaleGradient μ b Du w i j)) ≤ KDn :=
      force_slot_normalized_morrey_le 2 (25 / 8) (μ ^ 2) (11 / 16) KD
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrr hz
        (fun w => Du w i j) (hDb i j)
    have hE := force_slot_rescaled_energy_le hq hr₃ hrr hsol hdom hz hU hP hF
    obtain ⟨hU25n, Dn, _hAE, hInt, hweak, hPN⟩ := hboot hsoln hdomn hUn hDn hE
    obtain ⟨Dp, hamp, hDpInt, hDpweak⟩ := force_slot_pressure_transport a ha z
      hsoln.1 hsoln.2.1 hdomn p Dn hInt hweak
    have hsub := force_slot_carrier_subset hrr hz
    have hrestrict (s t : ℝ) (K : ℝ≥0∞) (hs : 0 < s) (hst : s ≤ t)
        (v : ParabolicPoint → ℝ)
        (hv : morreyBallNorm s t ((Metric.ball z₀ (r₂ / 4)).indicator v) ≤ K) :
        morreyNorm s t ((Metric.ball z (2 * a)).indicator v) ≤ K := by
      apply (morreyNorm_le_morreyBallNorm hs.le hst _).trans
      apply le_trans (morreyBallNorm_mono hs.le ?_) hv
      intro w
      by_cases hw : w ∈ Metric.ball z (2 * a)
      · rw [indicator_of_mem hw, indicator_of_mem (hsub hw)]
      · rw [indicator_of_notMem hw, abs_zero]
        exact abs_nonneg _
    refine ⟨fun i => hrestrict 3 (25 / 3) KU (by norm_num) (by norm_num) _ (hUb i),
      fun i j => hrestrict 2 (25 / 8) KD (by norm_num) (by norm_num) _ (hDb i j),
      ?_, Dp, hDpInt, hDpweak, ?_⟩
    · intro i
      apply force_slot_source_morrey_of_normalized 3 25 μ KU25n (by norm_num)
        hμ.ne' a ha z
      apply le_trans (morreyNorm_mono (by norm_num) ?_) (hU25n i)
      intro w
      by_cases hw : w ∈ parabolicCylinder (0 : Vec3) 0 (19 / 32)
      · rw [indicator_of_mem hw, indicator_of_mem
          (parabolicCylinder_mono (by norm_num) (by norm_num) hw)]
        exact le_rfl
      · rw [indicator_of_notMem hw, abs_zero]
        exact abs_nonneg _
    · intro i
      apply force_slot_source_morrey_of_normalized (6 / 5) (min q (25 / 9))
        (μ ^ 3) KPn (by norm_num) (pow_ne_zero _ hμ.ne') a ha z
      simpa only [μ, hamp] using hPN i
  obtain ⟨KU, KD, KU25, KP, hKU, hKD, hKU25, hKP, hselected⟩ := hSelected
  have hr₂ : 0 < r₂ := by linarith only [hr₃, hrr]
  have ha : 0 < endgameLocalRadius r₂ r₃ := by
    unfold endgameLocalRadius
    linarith only [hrr]
  let C₁₀ := forceSlotCutoffConstant (endgameLocalRadius r₂ r₃)
  have hC₁₀ : 0 ≤ C₁₀ := (forceSlotCutoffConstant_pos ha).le
  have hKF₀ : endgameForceSlotBound q C₁₀ r₂ r₃ KU KU25 KD KP
      (ENNReal.ofReal F) < ⊤ := by
    exact forceSlotNumericalBound_lt_top q C₁₀ _ hq (by positivity)
      hKU hKU25 hKD hKP ENNReal.ofReal_lt_top
  obtain ⟨hCcut, hcut⟩ := exists_force_slot_cutoff_family r₂ r₃ hr₃ hrr
  have hforce :
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
        (z₀ : ParabolicPoint),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
        (∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
          max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
            M * r ^ (2 / 5 : ℝ)) →
        eLpNorm (fun z => vec3EuclideanNorm (u z)) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal U →
        eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal P →
        eLpNorm (fun z => vec3EuclideanNorm (f z)) (ENNReal.ofReal q)
          (volume.restrict (Metric.ball z₀ r₂)) ≤ ENNReal.ofReal F →
        ∀ z ∈ Metric.closedBall z₀ r₃,
        ∀ (φ : Vec3 × ℝ → ℝ),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
          tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹'
            Metric.ball z (2 * endgameLocalRadius r₂ r₃) →
          (∀ w : Vec3 × ℝ, |φ w| ≤ C₁₀ ∧
            |timePartial φ w| ≤ C₁₀ ∧
            (∀ j, |spatialPartial φ j w| ≤ C₁₀) ∧
            |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C₁₀) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, Integrable (fun w => Dp w i)
            (volume.restrict (Metric.ball z (4 * endgameLocalRadius r₂ r₃)))) ∧
          (∀ i (ψ : Vec3 × ℝ → ℝ),
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹'
              Metric.ball z (4 * endgameLocalRadius r₂ r₃) →
            (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
              -(∫ w : ParabolicPoint, Dp w i * ψ w)) ∧
          (∀ i, AEMeasurable
            (fun w => localizedGradientSourceG φ u Du f Dp w i) volume) ∧
          (∀ j i, AEMeasurable
            (fun w => localizedGradientSourceH φ u j w i) volume) ∧
          (∀ i, HasCompactSupport
            (fun w => localizedGradientSourceG φ u Du f Dp w i)) ∧
          (∀ j i, HasCompactSupport
            (fun w => localizedGradientSourceH φ u j w i)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
            (fun w => localizedGradientSourceG φ u Du f Dp w i) ≤
              endgameForceSlotBound q C₁₀ r₂ r₃ KU KU25 KD KP
                (ENNReal.ofReal F)) := by
    intro Ω I u Du p f z₀ hsol hdom hdec hUnorm hPnorm hFnorm z hz φ hφ hsupp hcoeff
    let a := endgameLocalRadius r₂ r₃
    have ha' : 0 < a := by dsimp [a]; exact ha
    let B := vec3Ball z.1 (3 * a)
    let J := Ioo (z.2 - (3 * a) ^ 2) (z.2 + (3 * a) ^ 2)
    have hbox : localBox Ω I B J := (force_slot_cutoff_local_box hr₃ hrr hdom hz ha').1
    have hB : spaceTimeSet B J ⊆ Metric.ball z (4 * a) := by
      intro w hw
      apply Metric.ball_subset_ball (by linarith only [ha'] : 3 * a ≤ 4 * a)
      rw [metricBall_eq_parabolicBall]
      exact hw
    have hφbox : tsupport φ ⊆ B ×ˢ J := by
      intro w hw
      have hm := Metric.ball_subset_ball (by linarith only [ha'] : 2 * a ≤ 3 * a)
        (hsupp hw)
      rw [metricBall_eq_parabolicBall] at hm
      exact hm
    obtain ⟨hUi, hDi, hU25, Dp, hDp, hweak, hPN⟩ :=
      hselected Ω I u Du p f z₀ hsol hdom hdec hUnorm hPnorm hFnorm z hz
    have hDpBox (i : Fin 3) := (hDp i).mono_measure
      (Measure.restrict_mono_set volume hB)
    have hcarrier : Metric.ball z (2 * (2 * a)) ⊆ spaceTimeSet Ω I := by
      apply Set.Subset.trans ?_ hdom
      apply parabolic_ball_subset_ball_of_center_mem_closedBall hz
      dsimp [a, endgameLocalRadius]
      linarith only [hr₃, hrr]
    have hN := force_slot_numerical_bound_of_selected_gradient q C₁₀ (2 * a)
      KU KU25 KD KP (ENNReal.ofReal F) hq (by positivity) hC₁₀ hsol hφ hbox hφbox hcoeff
      z hcarrier hsupp hUi hU25 hDi hPN hDpBox
      ((eLpNorm_mono_measure _
        (Measure.restrict_mono_set volume
          ((force_slot_carrier_subset hrr hz).trans
            (Metric.ball_subset_ball (by linarith only [hr₂]))))).trans hFnorm)
    obtain ⟨hGae, hHae, hGc, hHc⟩ :=
      force_slot_sources_measurable_compact hsol hφ hbox hφbox hDpBox
    refine ⟨Dp, hDp, hweak, hGae, hHae, hGc, hHc, ?_⟩
    intro i
    simpa only [endgameForceSlotBound,
      show 2 * (2 * a) = 4 * endgameLocalRadius r₂ r₃ by dsimp [a]; ring] using hN i
  exact endgame_holder_norm_of_force_producer q M r₂ r₃ U P F C₁₀
    (endgameForceSlotBound q C₁₀ r₂ r₃ KU KU25 KD KP (ENNReal.ofReal F))
    hq hM hr₃ hrr hU hP hF hC₁₀ hKF₀
    CKN.Core.Step3.localized_gradient_slot_duhamel_of_sws hcut hforce

end CKN.Core.Endgame
