-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Iteration.ThetaUpperSemicontinuity
import CKN.Setting.CombinedMonotonicity

/-!
# Fixed-scale neighbourhood transfer for the iteration quantity

Once the descent has made `θ` small at one centre and one radius `R₀`, the
same bound at the smaller fixed radius `ρ` persists on a whole neighbourhood of
that centre.  The two ingredients are the radius comparison of the scale
quantities and the base-point semicontinuity of `α`, `β`, `δ`.

`CKN/Core/Step2/MorreyDecay.lean` performs this transfer inside the proof of
`morreyDecay_of_thetaDecay`, at the iteration constants and at one specific
radius ratio `7/5`; the statement here is the transfer itself, for arbitrary
positive `κ`, `η` and any radius ratio admitted by the displayed power bound.
-/

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology

open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Fixed-scale transfer: smallness of `θ` at `(z₀, R₀)` together with the
radius-ratio bound gives one radius `r₂ < ρ / 4` whose doubled parabolic ball
lies in the domain and on whose `r₂`-ball every centre satisfies
`θ (z, ρ) ≤ η`. -/
theorem morrey_fixed_scale_transfer_source
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η)
    (z₀ : ParabolicPoint) (R₀ ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ < R₀)
    (hdom : closure (parabolicCylinder z₀.1 z₀.2 R₀) ⊆ spaceTimeSet Ω I)
    (hsmall : theta κ u Du p z₀ R₀ ≤ η / 4)
    (hratio : (R₀ / ρ) ^ (4 / 3 + 2 / 5 : ℝ) ≤ 2) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ r₂ < ρ / 4 ∧
      Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I ∧
      ∀ z ∈ Metric.ball z₀ r₂, theta κ u Du p z ρ ≤ η := by
  have hR₀ : 0 < R₀ := hρ.trans hρR
  have hone_le : 1 ≤ R₀ / ρ := (one_le_div hρ).2 hρR.le
  have hfac : ∀ e : ℝ, e ≤ 4 / 3 + 2 / 5 → (R₀ / ρ) ^ e ≤ 2 := by
    intro e he
    exact (Real.rpow_le_rpow_of_exponent_le hone_le he).trans hratio
  have hhalf : (R₀ / ρ) ^ (1 / 2 : ℝ) ≤ 2 := hfac _ (by norm_num)
  have hfour : (R₀ / ρ) ^ (4 / 3 : ℝ) ≤ 2 := hfac _ (by norm_num)
  have hlin : R₀ / ρ ≤ 2 := by
    have h := hfac 1 (by norm_num)
    rwa [Real.rpow_one] at h
  have hκinv : 0 < κ ^ (-4 : ℝ) := Real.rpow_pos_of_pos hκ _
  have hκprod : κ ^ (-4 : ℝ) * κ ^ (4 : ℝ) = 1 := by
    rw [← Real.rpow_add hκ]
    norm_num
  have hαR : 0 ≤ alpha u z₀ R₀ := by unfold alpha; positivity
  have hβR : 0 ≤ beta u Du z₀ R₀ := by unfold beta; positivity
  have hαρ : 0 ≤ alpha u z₀ ρ := by unfold alpha; positivity
  have hβρ : 0 ≤ beta u Du z₀ ρ := by unfold beta; positivity
  obtain ⟨hαmono, hβmono, -, hδmono, -⟩ :=
    scale_quantities_mono_radius_of_sws hsol z₀ hρ hρR.le hdom
  have hAle : alpha u z₀ R₀ ≤ theta κ u Du p z₀ R₀ := by
    have hpos : 0 ≤ κ ^ (-4 : ℝ) * delta p z₀ R₀ ^ 2 := by positivity
    unfold theta
    linarith only [hβR, hpos]
  have hA4 : alpha u z₀ R₀ ≤ η / 4 := hAle.trans hsmall
  have hθρ : theta κ u Du p z₀ ρ ≤ η / 2 := by
    have h1 : alpha u z₀ ρ ≤ 2 * alpha u z₀ R₀ :=
      hαmono.trans (mul_le_mul_of_nonneg_right hhalf hαR)
    have h2 : beta u Du z₀ ρ ≤ 2 * beta u Du z₀ R₀ :=
      hβmono.trans (mul_le_mul_of_nonneg_right hhalf hβR)
    have h3 : κ ^ (-4 : ℝ) * delta p z₀ ρ ^ 2 ≤
        2 * (κ ^ (-4 : ℝ) * delta p z₀ R₀ ^ 2) := by
      have hδ2 : delta p z₀ ρ ^ 2 ≤ 2 * delta p z₀ R₀ ^ 2 :=
        hδmono.trans (mul_le_mul_of_nonneg_right hfour (sq_nonneg _))
      calc κ ^ (-4 : ℝ) * delta p z₀ ρ ^ 2 ≤
            κ ^ (-4 : ℝ) * (2 * delta p z₀ R₀ ^ 2) :=
            mul_le_mul_of_nonneg_left hδ2 hκinv.le
        _ = 2 * (κ ^ (-4 : ℝ) * delta p z₀ R₀ ^ 2) := by ring
    have hsmall' : theta κ u Du p z₀ R₀ ≤ η / 4 := hsmall
    unfold theta at hsmall' ⊢
    linarith only [h1, h2, h3, hsmall']
  have hz₀mem : z₀ ∈ spaceTimeSet Ω I := by
    apply hdom
    rw [closure_parabolicCylinder hR₀]
    refine ⟨?_, ?_, le_rfl⟩
    · change vec3EuclideanNorm (z₀.1 - z₀.1) ≤ R₀
      simpa only [sub_self, vec3EuclideanNorm_zero] using hR₀.le
    · have : 0 < R₀ ^ 2 := by positivity
      linarith only [this]
  have hrect : euclideanClosedBall z₀.1 R₀ ×ˢ Icc (z₀.2 - R₀ ^ 2) z₀.2 ⊆
      spaceTimeSet Ω I := by
    intro y hy
    apply hdom
    rw [closure_parabolicCylinder hR₀]
    refine ⟨?_, hy.2⟩
    change vec3EuclideanNorm (y.1 - z₀.1) ≤ R₀
    have heq : CKN.vecEuclideanNorm (y.1 - z₀.1) =
        vec3EuclideanNorm (y.1 - z₀.1) := by
      simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot, pow_two]
    rw [← heq]
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR₀.le).1 hy.1
  have husc := theta_usc_of_sws_with_alpha_bound hsol hρ hρR hrect hz₀mem.2
  have hlimsup : Filter.limsup (fun z : ParabolicPoint => alpha u z ρ ^ 2)
      (𝓝 z₀) < 9 * η ^ 2 / 64 := by
    have hA2 : alpha u z₀ R₀ ^ 2 ≤ (η / 4) ^ 2 := by
      nlinarith only [hA4, hαR]
    have hprod : (R₀ / ρ) * alpha u z₀ R₀ ^ 2 ≤ 2 * (η / 4) ^ 2 := by
      have h1 : (R₀ / ρ) * alpha u z₀ R₀ ^ 2 ≤ 2 * alpha u z₀ R₀ ^ 2 :=
        mul_le_mul_of_nonneg_right hlin (sq_nonneg _)
      linarith only [h1, hA2]
    calc Filter.limsup (fun z : ParabolicPoint => alpha u z ρ ^ 2) (𝓝 z₀) ≤
          (R₀ / ρ) * alpha u z₀ R₀ ^ 2 := husc.1
      _ ≤ 2 * (η / 4) ^ 2 := hprod
      _ < 9 * η ^ 2 / 64 := by nlinarith only [hη]
  have hαevent : ∀ᶠ z : ParabolicPoint in 𝓝 z₀, alpha u z ρ < 3 * η / 8 := by
    have h := eventually_lt_of_limsup_lt hlimsup husc.2.2.2
    filter_upwards [h] with z hz
    by_contra hcon
    have hcon' : 3 * η / 8 ≤ alpha u z ρ := not_lt.mp hcon
    nlinarith only [hz, hcon', hη]
  have hβevent : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      beta u Du z ρ < beta u Du z₀ ρ + η / 32 :=
    husc.2.1.eventually (eventually_lt_nhds (by linarith only [hη]))
  have hδevent : ∀ᶠ z : ParabolicPoint in 𝓝 z₀,
      delta p z ρ ^ 2 < delta p z₀ ρ ^ 2 + κ ^ (4 : ℝ) * η / 32 := by
    have hpos : 0 < κ ^ (4 : ℝ) * η / 32 := by positivity
    exact (husc.2.2.1.pow 2).eventually
      (eventually_lt_nhds (by linarith only [hpos]))
  have htransfer : ∀ᶠ z : ParabolicPoint in 𝓝 z₀, theta κ u Du p z ρ ≤ η := by
    filter_upwards [hαevent, hβevent, hδevent] with z hαz hβz hδz
    have hδterm : κ ^ (-4 : ℝ) * delta p z ρ ^ 2 ≤
        κ ^ (-4 : ℝ) * delta p z₀ ρ ^ 2 + η / 32 := by
      calc κ ^ (-4 : ℝ) * delta p z ρ ^ 2 ≤
            κ ^ (-4 : ℝ) * (delta p z₀ ρ ^ 2 + κ ^ (4 : ℝ) * η / 32) :=
            mul_le_mul_of_nonneg_left hδz.le hκinv.le
        _ = κ ^ (-4 : ℝ) * delta p z₀ ρ ^ 2 +
            (κ ^ (-4 : ℝ) * κ ^ (4 : ℝ)) * (η / 32) := by ring
        _ = κ ^ (-4 : ℝ) * delta p z₀ ρ ^ 2 + η / 32 := by
            rw [hκprod]; ring
    have hsplit : beta u Du z₀ ρ + κ ^ (-4 : ℝ) * delta p z₀ ρ ^ 2 ≤ η / 2 := by
      unfold theta at hθρ
      linarith only [hθρ, hαρ]
    unfold theta
    linarith only [hαz, hβz, hδterm, hsplit, hη]
  obtain ⟨rE, hrE, hballE⟩ := Metric.mem_nhds_iff.mp htransfer
  obtain ⟨Ropen, hRopen, hRopenSub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1).mem_nhds hz₀mem)
  refine ⟨min (rE / 2) (min (ρ / 8) (Ropen / 4)), ?_, ?_, ?_, ?_⟩
  · exact lt_min (by linarith only [hrE])
      (lt_min (by linarith only [hρ]) (by linarith only [hRopen]))
  · have h : min (rE / 2) (min (ρ / 8) (Ropen / 4)) ≤ ρ / 8 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith only [h, hρ]
  · have h : min (rE / 2) (min (ρ / 8) (Ropen / 4)) ≤ Ropen / 4 :=
      (min_le_right _ _).trans (min_le_right _ _)
    refine (Metric.ball_subset_ball ?_).trans hRopenSub
    linarith only [h, hRopen]
  · intro z hz
    have h : min (rE / 2) (min (ρ / 8) (Ropen / 4)) ≤ rE / 2 := min_le_left _ _
    exact hballE (Metric.ball_subset_ball (by linarith only [h, hrE]) hz)

end CKN

end
