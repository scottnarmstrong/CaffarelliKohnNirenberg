-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumericalBootstrap
import CKN.Core.Endgame.ForceSlotNumericalNormalizedData
import CKN.Core.Endgame.ForceSlotNumericalPressureTransport

/-!
# Uniform velocity and pressure bounds on the physical source collar

The two normalized pressure estimates and the intervening velocity bootstrap
are transported back to the fixed endgame radius. Every numerical bound is
chosen before the domain, fields, and localization centre.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- The inverse scaling loss for a field of amplitude `c`. -/
def forceSlotUnscaledBound (a c τ : ℝ) (K : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal a ^ (5 / τ : ℝ) * (ENNReal.ofReal |c⁻¹| * K)

/-- The inverse scaling loss preserves finiteness for every exponent. -/
theorem forceSlotUnscaledBound_lt_top (a c τ : ℝ) (ha : 0 < a)
    {K : ℝ≥0∞} (hK : K < ⊤) : forceSlotUnscaledBound a c τ K < ⊤ := by
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top))
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK)

/-- Uniform improved velocity and selected pressure-gradient bounds on the
physical endgame carrier, from the quantitative one-sided pressure estimate. -/
theorem exists_force_slot_uniform_selected_gradient
    (hGA : oneSidedPressureGradientQuantitative)
    (q M r₂ r₃ U P F C_CZ : ℝ)
    (hq : 5 / 2 < q) (hM : 1 ≤ M) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hC : 0 ≤ C_CZ)
    (hL : ∀ (Ω : Set Vec3) (I : Set ℝ)
      (u f Dp : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ), IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ (φ : Vec3 × ℝ → ℝ) (U : Set Vec3) (J : Set ℝ),
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      localBox Ω I U J → tsupport φ ⊆ U ×ˢ J →
      (∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) →
      (∀ (i : Fin 3) (ψ : Vec3 × ℝ → ℝ),
        ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ → tsupport ψ ⊆ U ×ˢ J →
        (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
          -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
      localizedVelocity φ u =ᵐ[volume] (fun z i => heatPotential
        (fun w => localizedGradientSourceG φ u Du f Dp w i)
        (fun j w => localizedGradientSourceH φ u j w i) z)) :
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
            ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator (fun w => u w i)) ≤ KU) ∧
          (∀ i j, morreyNorm 2 (25 / 8)
            ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator
              (fun w => Du w i j)) ≤ KD) ∧
          (∀ i, morreyNorm 3 25
            ((Metric.ball z (2 * endgameLocalRadius r₂ r₃)).indicator (fun w => u w i)) ≤ KU25) ∧
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
  have ha : 0 < a := by dsimp [a, endgameLocalRadius]; linarith only [hrr]
  have hμ : 0 < μ := by dsimp [μ]; positivity
  obtain ⟨KU, KD, Kpressure, hKU, hKD, _hKpressure, hstep⟩ :=
    step2_morrey_form_uniform M r₂ hM hr₂
  let KUn := ENNReal.ofReal |μ| * (ENNReal.ofReal μ ^ (-5 / (25 / 3) : ℝ) * KU)
  let KDn := ENNReal.ofReal |μ ^ 2| * (ENNReal.ofReal μ ^ (-5 / (25 / 8) : ℝ) * KD)
  let ε := (forceSlotEnergy q r₂ r₃ U P F).toReal
  have hKUn : KUn < ⊤ := force_slot_scaling_bound_lt_top _ _ _ hμ hKU
  have hKDn : KDn < ⊤ := force_slot_scaling_bound_lt_top _ _ _ hμ hKD
  obtain ⟨KU25n, hKU25n, hKPn, hboot⟩ := force_slot_unit_bootstrap_of_GA_and_representation
    hGA q C_CZ ε KUn KDn hq hC ENNReal.toReal_nonneg hKUn hKDn hL
  let KPn := oneSidedPressureGradientKP q 25 C_CZ (5 / 8) (19 / 32) ε KU25n KDn
  refine ⟨KU, KD, forceSlotUnscaledBound μ μ 25 KU25n,
    forceSlotUnscaledBound μ (μ ^ 3) (min q (25 / 9)) KPn,
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
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrr hz (fun w => u w i) (hUb i)
  have hDn (i j : Fin 3) : morreyNorm 2 (25 / 8)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
        (fun w => rescaleGradient μ b Du w i j)) ≤ KDn :=
    force_slot_normalized_morrey_le 2 (25 / 8) (μ ^ 2) (11 / 16) KD
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrr hz (fun w => Du w i j) (hDb i j)
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
    apply force_slot_source_morrey_of_normalized 3 25 μ KU25n (by norm_num) hμ.ne' a ha z
    apply le_trans (morreyNorm_mono (by norm_num) ?_) (hU25n i)
    intro w
    by_cases hw : w ∈ parabolicCylinder (0 : Vec3) 0 (19 / 32)
    · rw [indicator_of_mem hw, indicator_of_mem
        (parabolicCylinder_mono (by norm_num) (by norm_num) hw)]
      exact le_rfl
    · rw [indicator_of_notMem hw, abs_zero]
      exact abs_nonneg _
  · intro i
    apply force_slot_source_morrey_of_normalized (6 / 5) (min q (25 / 9)) (μ ^ 3) KPn
      (by norm_num) (pow_ne_zero _ hμ.ne') a ha z
    simpa only [μ, hamp] using hPN i

end CKN.Core.Endgame
