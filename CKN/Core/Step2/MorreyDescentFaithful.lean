-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Iteration.Arithmetic
import CKN.Core.Iteration.UpperSemicontinuity
import CKN.Core.Iteration.ThetaUpperSemicontinuity
import CKN.Core.Step2.MorreyDecayAux
import CKN.Core.Step2.Iteration
import CKN.Setting.SliceNormBounds
import CKN.Setting.Energy.PointwiseEnergy

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The descent-radius conclusion in Step 2, at the constants fixed by
`conv:kappa` and from the first one-step decay estimate. -/
theorem morrey_descent_of_thetaDecay
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} (hz₀ : z₀ ∈ spaceTimeSet Ω I)
    {C₂₇ C₂₈ : ℝ} (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hThetaDecay₁ : ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
        C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p z ρ +
          C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
            (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
            theta (iterationKappa C₂₇) u Du p z ρ +
          C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
            theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
            lambda q f z ρ ^ (1 / 2 : ℝ) +
          C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ)
    (hβlim : Filter.limsup (fun r : ℝ => (ENNReal.ofReal r)⁻¹ *
        ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
          ENNReal.ofReal (spatialGradientSq u Du w))
      (𝓝[>] (0 : ℝ)) <
        ENNReal.ofReal ((iterationEpsilonStar C₂₇) ^ (2 : ℕ)))
    {rbar : ℝ} (hrbar : 0 < rbar) :
    ∃ (r₄ : ℝ) (n₀ : ℕ), 0 < r₄ ∧ r₄ ≤ rbar ∧
      closure (Metric.ball z₀ (4 * r₄)) ⊆ spaceTimeSet Ω I ∧
      theta (iterationKappa C₂₇) u Du p z₀
          (iterationKappa C₂₇ ^ n₀ * r₄) ≤
        iterationEta C₂₇ * iterationKappa C₂₇ ^ ((n₀ : ℝ) * iterationEpsilon) / 4 := by
  let κ : ℝ := iterationKappa C₂₇
  let η : ℝ := iterationEta C₂₇
  let εStar : ℝ := iterationEpsilonStar C₂₇
  let ε : ℝ := iterationEpsilon
  let C₂₉ : ℝ := iterationC₂₉ C₂₇ C₂₈
  let Λ₀ : ℝ := iterationLambda₀ C₂₇ C₂₈
  let ηd : ℝ := min η (min (η ^ 2 / 8) (κ ^ 4 * η / 8))
  have hκ : 0 < κ := by dsimp [κ]; exact iterationKappa_pos hC₂₇
  have hκle : κ ≤ 1 / 2 := by dsimp [κ]; exact iterationKappa_le_half C₂₇
  have hκone : κ ≤ 1 := hκle.trans (by norm_num)
  have hη : 0 < η := by dsimp [η]; exact iterationEta_pos hC₂₇
  have hεStar : 0 < εStar := by
    dsimp [εStar]
    exact iterationEpsilonStar_pos hC₂₇
  have hηd : 0 < ηd := by
    dsimp [ηd]
    exact lt_min hη (lt_min (by positivity) (by positivity))
  have hε : 0 < ε := by dsimp [ε]; norm_num [iterationEpsilon]
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have hσ : 1 < 3 - 5 / q := by
    have hfive : 5 / q < (2 : ℝ) := by
      apply (div_lt_iff₀ hqpos).2
      nlinarith only [hq]
    linarith only [hfive]
  have hεσ : ε ≤ 3 - 5 / q := by
    dsimp [ε, iterationEpsilon]
    nlinarith only [hσ]
  have hC₂₉ : 0 < C₂₉ := by
    dsimp [C₂₉]
    exact iterationC₂₉_pos hC₂₇ hC₂₈
  have hΛ : C₂₉ * Λ₀ = η / 2 := by
    dsimp [C₂₉, Λ₀, η]
    exact iterationC₂₉_mul_Lambda₀ hC₂₇ hC₂₈
  obtain ⟨Ropen, hRopen, hRopenSub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1).mem_nhds hz₀)
  have hquotEvent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
            ENNReal.ofReal (spatialGradientSq u Du w) <
        ENNReal.ofReal (εStar ^ (2 : ℕ)) := by
    exact eventually_lt_of_limsup_lt (by simpa [εStar] using hβlim)
  have hβevent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), beta u Du z₀ r < εStar := by
    have hRopenEvent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < Ropen :=
      (eventually_lt_nhds hRopen).filter_mono nhdsWithin_le_nhds
    filter_upwards [hquotEvent, eventually_mem_nhdsWithin, hRopenEvent]
      with r hqLim hr hRr
    change 0 < r at hr
    have hsubr : closure (parabolicCylinder z₀.1 z₀.2 r) ⊆
        spaceTimeSet Ω I := by
      intro y hy
      have hyc := step2_closure_cylinder_subset_closedBall hr hy
      apply hRopenSub
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hyc) hRr
    have heq := sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq
      hsol z₀ hr hsubr
    rw [heq] at hqLim
    rw [← ENNReal.ofReal_inv_of_pos hr,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ r⁻¹)] at hqLim
    have hqLim' : ENNReal.ofReal (beta u Du z₀ r ^ 2) <
        ENNReal.ofReal (εStar ^ (2 : ℕ)) := by
      convert hqLim using 1
      congr 1
      field_simp
    have hroot : beta u Du z₀ r ^ 2 < εStar ^ (2 : ℕ) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hqLim'
    have hβnonneg : 0 ≤ beta u Du z₀ r := by
      unfold beta
      positivity
    nlinarith only [hroot, hβnonneg, hεStar]
  obtain ⟨U, hU, h0U, hUsub⟩ := mem_nhdsWithin.1 hβevent
  obtain ⟨Rβ, hRβ, hRβsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  let rbase : ℝ := min (Ropen / 8) (min (Rβ / 2) rbar)
  have hrbase : 0 < rbase := by
    dsimp [rbase]
    positivity
  have hrbaseR : rbase < Ropen := by
    dsimp [rbase]
    have hle : min (Ropen / 8) (min (Rβ / 2) rbar) ≤ Ropen / 8 :=
      min_le_left _ _
    linarith only [hle, hRopen]
  have hrbaseβ : rbase < Rβ := by
    dsimp [rbase]
    have hle₁ : min (Ropen / 8) (min (Rβ / 2) rbar) ≤
        min (Rβ / 2) rbar := min_le_right _ _
    have hle₂ : min (Rβ / 2) rbar ≤ Rβ / 2 := min_le_left _ _
    linarith only [hle₁, hle₂, hRβ]
  have hrbasebar : rbase ≤ rbar := by
    dsimp [rbase]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hbaseSub : closure (parabolicCylinder z₀.1 z₀.2 rbase) ⊆
      spaceTimeSet Ω I := by
    intro y hy
    have hyc := step2_closure_cylinder_subset_closedBall hrbase hy
    apply hRopenSub
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hyc) hrbaseR
  have hβsmall : ∀ {r : ℝ}, 0 < r → r ≤ rbase →
      beta u Du z₀ r ≤ εStar := by
    intro r hr hrb
    apply le_of_lt
    apply hUsub
    exact ⟨hRβsub (by
      rw [Metric.mem_ball]
      simpa [Real.dist_eq, abs_of_pos hr] using
        lt_of_le_of_lt hrb hrbaseβ), hr⟩
  have hforceBase : (∫⁻ w in parabolicCylinder z₀.1 z₀.2 rbase,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) < ⊤ :=
    sws_force_integral_lt_top hsol hrbase hbaseSub
  let lambdaBase := lambda q f z₀ rbase
  have hlambdaBase : 0 ≤ lambdaBase := by
    dsimp [lambdaBase, lambda]
    positivity
  let lambdaSmall : ℝ := min Λ₀ (ηd / (16 * C₂₉))
  have hlambdaSmall : 0 < lambdaSmall := by
    dsimp [lambdaSmall]
    exact lt_min (by dsimp [Λ₀]; exact iterationLambda₀_pos hC₂₇ hC₂₈)
      (by positivity)
  have hκlt : κ < 1 := lt_of_le_of_lt hκle (by norm_num)
  let a : ℝ := κ ^ (3 - 5 / q)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    exact Real.rpow_lt_one hκ.le hκlt (by linarith only [hσ])
  have hlambdaTendsto : Tendsto (fun n : ℕ => a ^ n * lambdaBase)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).mul_const lambdaBase
  have hlambdaEvent : ∀ᶠ n : ℕ in atTop, a ^ n * lambdaBase < lambdaSmall :=
    (tendsto_order.1 hlambdaTendsto).2 _ hlambdaSmall
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlambdaEvent
  let r₄ : ℝ := κ ^ N * rbase
  have hr₄ : 0 < r₄ := by dsimp [r₄]; positivity
  have hr₄base : r₄ ≤ rbase := by
    dsimp [r₄]
    simpa [mul_comm] using
      (mul_le_of_le_one_right hrbase.le (pow_le_one₀ hκ.le hκone) :
        rbase * κ ^ N ≤ rbase)
  have hr₄bar : r₄ ≤ rbar := hr₄base.trans hrbasebar
  have hsub₄ : closure (parabolicCylinder z₀.1 z₀.2 r₄) ⊆
      spaceTimeSet Ω I :=
    (closure_parabolicCylinder_mono hr₄.le hr₄base).trans hbaseSub
  have hball₄ : closure (Metric.ball z₀ (4 * r₄)) ⊆
      spaceTimeSet Ω I := by
    have hrad : 4 * r₄ < Ropen := by
      have hle : r₄ ≤ Ropen / 8 := hr₄base.trans
        (min_le_left (Ropen / 8) (min (Rβ / 2) rbar))
      nlinarith only [hle, hRopen]
    exact Metric.closure_ball_subset_closedBall.trans
      ((Metric.closedBall_subset_ball hrad).trans hRopenSub)
  have hmono₄ := lambda_mono_radius_of_sws hsol z₀ hr₄ hr₄base hbaseSub
  have hratio₄ : r₄ / rbase = κ ^ N := by
    dsimp [r₄]
    field_simp
  have hpow₄ : (κ ^ N) ^ (3 - 5 / q) = a ^ N := by
    dsimp [a]
    calc
      (κ ^ N) ^ (3 - 5 / q) = (κ ^ (N : ℝ)) ^ (3 - 5 / q) := by
        rw [Real.rpow_natCast]
      _ = κ ^ ((N : ℝ) * (3 - 5 / q)) := by
        rw [Real.rpow_mul hκ.le]
      _ = (κ ^ (3 - 5 / q)) ^ N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
        congr 1
        ring_nf
  rw [hratio₄, hpow₄] at hmono₄
  have hlambda₄ : lambda q f z₀ r₄ ≤ lambdaSmall :=
    hmono₄.trans (le_of_lt (hN N le_rfl))
  let Θ : ℕ → ℝ := fun n => theta κ u Du p z₀ (κ ^ n * r₄)
  let Lraw : ℕ → ℝ := fun n => lambda q f z₀ (κ ^ n * r₄)
  let T : ℕ → ℝ := fun n => Θ n / κ ^ ((n : ℝ) * ε)
  let L : ℕ → ℝ := fun n => Lraw n / κ ^ ((n : ℝ) * ε)
  have hΘnonneg : ∀ n, 0 ≤ Θ n := by
    intro n
    dsimp [Θ]
    unfold theta alpha beta delta
    positivity
  have hTnonneg : ∀ n, 0 ≤ T n := by
    intro n
    dsimp [T]
    exact div_nonneg (hΘnonneg n) (by positivity)
  have hLrawdecay : ∀ n, 0 ≤ Lraw n ∧ Lraw n ≤
      κ ^ ((n : ℝ) * (3 - 5 / q)) * Lraw 0 := by
    intro n
    have hρ : 0 < κ ^ n * r₄ := by positivity
    have hρr : κ ^ n * r₄ ≤ r₄ := by
      simpa [mul_comm] using
        (mul_le_of_le_one_right hr₄.le (pow_le_one₀ hκ.le hκone) :
          r₄ * κ ^ n ≤ r₄)
    have hmono := lambda_mono_radius_of_sws hsol z₀ hρ hρr hsub₄
    have hratio : (κ ^ n * r₄) / r₄ = κ ^ n := by field_simp
    have hpow : (κ ^ n) ^ (3 - 5 / q) =
        κ ^ ((n : ℝ) * (3 - 5 / q)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
    have hnonneg : 0 ≤ Lraw n := by
      dsimp [Lraw, lambda]
      positivity
    refine ⟨hnonneg, ?_⟩
    rw [hratio, hpow] at hmono
    simpa [Lraw] using hmono
  have hLnonneg : ∀ n, 0 ≤ L n := by
    intro n
    dsimp [L]
    exact div_nonneg (hLrawdecay n).1 (by positivity)
  have hLzero : Lraw 0 ≤ lambdaSmall := by simpa [Lraw] using hlambda₄
  have hLbound : ∀ n, L n ≤ lambdaSmall := by
    change ∀ n, Lraw n / κ ^ ((n : ℝ) * ε) ≤ lambdaSmall
    exact force_normalized_bound hκ hκone hεσ (hLrawdecay 0).1 hLzero
      hLrawdecay
  have hsource : ∀ n, C₂₉ * L n ≤ ηd / 16 := by
    intro n
    have hsmall : C₂₉ * lambdaSmall ≤ ηd / 16 := by
      dsimp [lambdaSmall]
      have hmin := min_le_right Λ₀ (ηd / (16 * C₂₉))
      have hmul := mul_le_mul_of_nonneg_left hmin hC₂₉.le
      convert hmul using 1
      field_simp
    exact (mul_le_mul_of_nonneg_left (hLbound n) hC₂₉.le).trans hsmall
  have hrec : ∀ n, T (n + 1) ≤ (3 / 8 : ℝ) * T n + C₂₉ * L n := by
    intro n
    have hρ : 0 < κ ^ n * r₄ := by positivity
    have hρr : κ ^ n * r₄ ≤ r₄ := by
      simpa [mul_comm] using
        (mul_le_of_le_one_right hr₄.le (pow_le_one₀ hκ.le hκone) :
          r₄ * κ ^ n ≤ r₄)
    have hρsub : closure (parabolicCylinder z₀.1 z₀.2 (κ ^ n * r₄)) ⊆
        spaceTimeSet Ω I :=
      (closure_parabolicCylinder_mono hρ.le hρr).trans hsub₄
    have hb : beta u Du z₀ (κ ^ n * r₄) ≤ εStar :=
      hβsmall hρ (hρr.trans hr₄base)
    have hdec := hThetaDecay₁ hρ hρsub
    have hnext : κ ^ (n + 1) * r₄ = κ * (κ ^ n * r₄) := by
      rw [pow_succ]
      ring_nf
    have hnextTheta : Θ (n + 1) =
        theta κ u Du p z₀ (κ * (κ ^ n * r₄)) := by
      dsimp [Θ]
      rw [hnext]
    have hscale : ∀ m, Θ m = T m * κ ^ ((m : ℝ) * ε) := by
      intro m
      dsimp [T]
      field_simp
    have hLrawscale : ∀ m, Lraw m = L m * κ ^ ((m : ℝ) * ε) := by
      intro m
      dsimp [L]
      field_simp
    have hpow : κ ^ (((n + 1 : ℕ) : ℝ) * ε) =
        κ ^ ((n : ℝ) * ε) * κ ^ ε := by
      rw [← Real.rpow_add hκ]
      congr 1
      push_cast
      ring_nf
    have hdec' : theta κ u Du p z₀ (κ * (κ ^ n * r₄)) ≤
        C₂₇ * κ ^ (2 / 3 : ℝ) * Θ n +
          C₂₇ * κ ^ (-5 : ℝ) *
            (beta u Du z₀ (κ ^ n * r₄) ^ (1 / 2 : ℝ) +
              beta u Du z₀ (κ ^ n * r₄)) * Θ n +
          C₂₈ * κ ^ (-1 / 2 : ℝ) * Θ n ^ (1 / 2 : ℝ) *
            Lraw n ^ (1 / 2 : ℝ) + C₂₈ * κ ^ (-3 : ℝ) * Lraw n := by
      simpa [κ, Θ, Lraw] using hdec
    have hΘpow : (T n * κ ^ ((n : ℝ) * ε)) ^ (1 / 2 : ℝ) =
        T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2) := by
      rw [Real.mul_rpow (hTnonneg n) (Real.rpow_nonneg hκ.le _)]
      congr 1
      rw [← Real.rpow_mul hκ.le]
      ring_nf
    have hLpow : (L n * κ ^ ((n : ℝ) * ε)) ^ (1 / 2 : ℝ) =
        L n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2) := by
      rw [Real.mul_rpow (hLnonneg n) (Real.rpow_nonneg hκ.le _)]
      congr 1
      rw [← Real.rpow_mul hκ.le]
      ring_nf
    have hhalf : κ ^ ((n : ℝ) * ε / 2) * κ ^ ((n : ℝ) * ε / 2) =
        κ ^ ((n : ℝ) * ε) := by
      rw [← Real.rpow_add hκ]
      congr 1
      ring_nf
    have hhalfSq : (κ ^ (ε * (n : ℝ) * (1 / 2 : ℝ))) ^ 2 =
        κ ^ (ε * (n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
      congr 1
      ring_nf
    have h₁ : κ ^ (2 / 3 - ε : ℝ) * κ ^ ε = κ ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hκ]
      congr 1
      ring_nf
    have h₂ : κ ^ (-5 - ε : ℝ) * κ ^ ε = κ ^ (-5 : ℝ) := by
      rw [← Real.rpow_add hκ]
      congr 1
      ring_nf
    have h₃ : κ ^ (-1 / 2 - ε : ℝ) * κ ^ ε = κ ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add hκ]
      congr 1
      ring_nf
    have h₄ : κ ^ (-3 - ε : ℝ) * κ ^ ε = κ ^ (-3 : ℝ) := by
      rw [← Real.rpow_add hκ]
      congr 1
      ring_nf
    let b : ℝ := beta u Du z₀ (κ ^ n * r₄)
    have hscaled :
        (C₂₇ * κ ^ (2 / 3 - ε : ℝ) * T n +
          C₂₇ * κ ^ (-5 - ε : ℝ) * (b ^ (1 / 2 : ℝ) + b) * T n +
          C₂₈ * κ ^ (-1 / 2 - ε : ℝ) * T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ) +
          C₂₈ * κ ^ (-3 - ε : ℝ) * L n) *
            (κ ^ ((n : ℝ) * ε) * κ ^ ε) =
        C₂₇ * κ ^ (2 / 3 : ℝ) * (T n * κ ^ ((n : ℝ) * ε)) +
          C₂₇ * κ ^ (-5 : ℝ) * (b ^ (1 / 2 : ℝ) + b) *
            (T n * κ ^ ((n : ℝ) * ε)) +
          C₂₈ * κ ^ (-1 / 2 : ℝ) *
            (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
            (L n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) +
          C₂₈ * κ ^ (-3 : ℝ) * (L n * κ ^ ((n : ℝ) * ε)) := by
      calc
        _ = C₂₇ * (κ ^ (2 / 3 - ε : ℝ) * κ ^ ε) *
              (T n * κ ^ ((n : ℝ) * ε)) +
            C₂₇ * (κ ^ (-5 - ε : ℝ) * κ ^ ε) *
              (b ^ (1 / 2 : ℝ) + b) * (T n * κ ^ ((n : ℝ) * ε)) +
            C₂₈ * (κ ^ (-1 / 2 - ε : ℝ) * κ ^ ε) *
              (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
              (L n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) +
            C₂₈ * (κ ^ (-3 - ε : ℝ) * κ ^ ε) * (L n * κ ^ ((n : ℝ) * ε)) := by
          ring_nf
          rw [hhalfSq]
          ring
        _ = _ := by
          rw [h₁, h₂, h₃, h₄]
    have hscaledBound : T (n + 1) ≤
        C₂₇ * κ ^ (2 / 3 - ε : ℝ) * T n +
          C₂₇ * κ ^ (-5 - ε : ℝ) * (b ^ (1 / 2 : ℝ) + b) * T n +
          C₂₈ * κ ^ (-1 / 2 - ε : ℝ) * T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ) +
          C₂₈ * κ ^ (-3 - ε : ℝ) * L n := by
      rw [show T (n + 1) = Θ (n + 1) /
          κ ^ (((n + 1 : ℕ) : ℝ) * ε) by rfl, hnextTheta]
      have hden : 0 < κ ^ (((n + 1 : ℕ) : ℝ) * ε) := by positivity
      apply (div_le_iff₀ hden).2
      rw [hpow]
      rw [hscale n, hLrawscale n, hΘpow, hLpow] at hdec'
      calc
        theta κ u Du p z₀ (κ * (κ ^ n * r₄)) ≤
            C₂₇ * κ ^ (2 / 3 : ℝ) * (T n * κ ^ ((n : ℝ) * ε)) +
              C₂₇ * κ ^ (-5 : ℝ) * (b ^ (1 / 2 : ℝ) + b) *
                (T n * κ ^ ((n : ℝ) * ε)) +
              C₂₈ * κ ^ (-1 / 2 : ℝ) *
                (T n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) *
                (L n ^ (1 / 2 : ℝ) * κ ^ ((n : ℝ) * ε / 2)) +
              C₂₈ * κ ^ (-3 : ℝ) * (L n * κ ^ ((n : ℝ) * ε)) := by
          simpa only [b] using hdec'
        _ = _ := hscaled.symm
    have hfirst : C₂₇ * κ ^ (2 / 3 - ε : ℝ) * T n ≤
        (1 / 8 : ℝ) * T n := by
      exact mul_le_mul_of_nonneg_right
        (by simpa [κ, ε] using iterationKappa_prop₁ hC₂₇) (hTnonneg n)
    have hbnonneg : 0 ≤ b := by dsimp [b, beta]; positivity
    have hbsqrt : b ^ (1 / 2 : ℝ) ≤ εStar ^ (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow hbnonneg hb (by norm_num)
    have hbsum : b ^ (1 / 2 : ℝ) + b ≤
        εStar ^ (1 / 2 : ℝ) + εStar := by
      linarith only [hbsqrt, hb]
    have hcoef : C₂₇ * κ ^ (-5 - ε : ℝ) *
        (b ^ (1 / 2 : ℝ) + b) ≤ (1 / 16 : ℝ) := by
      have hbase : C₂₇ * κ ^ (-5 - ε : ℝ) *
          (b ^ (1 / 2 : ℝ) + b) ≤
          C₂₇ * κ ^ (-5 - ε : ℝ) *
            (εStar ^ (1 / 2 : ℝ) + εStar) :=
        mul_le_mul_of_nonneg_left hbsum
          (mul_nonneg hC₂₇.le (Real.rpow_nonneg hκ.le _))
      have hprop := iterationKappa_prop₃ hC₂₇
      have hprop' : 2 * C₂₇ * κ ^ (-5 - ε : ℝ) *
          (εStar ^ (1 / 2 : ℝ) + εStar) ≤ (1 / 8 : ℝ) := by
        simpa [κ, ε, εStar] using hprop
      exact hbase.trans (by nlinarith only [hprop'])
    have hsecond : C₂₇ * κ ^ (-5 - ε : ℝ) *
        (b ^ (1 / 2 : ℝ) + b) * T n ≤ (1 / 16 : ℝ) * T n :=
      mul_le_mul_of_nonneg_right hcoef (hTnonneg n)
    have hTsq : (T n ^ (1 / 2 : ℝ)) ^ 2 = T n := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (hTnonneg n)]
    have hLsq : (L n ^ (1 / 2 : ℝ)) ^ 2 = L n := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (hLnonneg n)]
    have hκsq : (κ ^ (-1 / 2 - ε : ℝ)) ^ 2 = κ ^ (-1 - 2 * ε : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
      congr 1
      ring_nf
    have hyoung : C₂₈ * κ ^ (-1 / 2 - ε : ℝ) *
        T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ) ≤
        (1 / 8 : ℝ) * T n + 2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε : ℝ) * L n := by
      calc
        C₂₈ * κ ^ (-1 / 2 - ε : ℝ) * T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ) =
            T n ^ (1 / 2 : ℝ) *
              (C₂₈ * κ ^ (-1 / 2 - ε : ℝ) * L n ^ (1 / 2 : ℝ)) := by ring
        _ ≤ (1 / 8 : ℝ) * (T n ^ (1 / 2 : ℝ)) ^ 2 +
              2 * (C₂₈ * κ ^ (-1 / 2 - ε : ℝ) * L n ^ (1 / 2 : ℝ)) ^ 2 := by
          nlinarith only [sq_nonneg (T n ^ (1 / 2 : ℝ) -
            4 * (C₂₈ * κ ^ (-1 / 2 - ε : ℝ) * L n ^ (1 / 2 : ℝ)))]
        _ = (1 / 8 : ℝ) * T n +
              2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε : ℝ) * L n := by
          rw [hTsq]
          simp only [mul_pow, hκsq, hLsq]
          ring
    have hC₂₉formula : C₂₉ =
        2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε : ℝ) +
          C₂₈ * κ ^ (-3 - ε : ℝ) := rfl
    have htail : 2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε : ℝ) * L n +
        C₂₈ * κ ^ (-3 - ε : ℝ) * L n ≤ C₂₉ * L n := by
      calc
        2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε : ℝ) * L n +
            C₂₈ * κ ^ (-3 - ε : ℝ) * L n =
            (2 * C₂₈ ^ 2 * κ ^ (-1 - 2 * ε : ℝ) +
              C₂₈ * κ ^ (-3 - ε : ℝ)) * L n := by ring
        _ = C₂₉ * L n := by rw [← hC₂₉formula]
        _ ≤ C₂₉ * L n := le_rfl
    calc
      T (n + 1) ≤
          C₂₇ * κ ^ (2 / 3 - ε : ℝ) * T n +
            C₂₇ * κ ^ (-5 - ε : ℝ) * (b ^ (1 / 2 : ℝ) + b) * T n +
            C₂₈ * κ ^ (-1 / 2 - ε : ℝ) * T n ^ (1 / 2 : ℝ) * L n ^ (1 / 2 : ℝ) +
            C₂₈ * κ ^ (-3 - ε : ℝ) * L n := hscaledBound
      _ ≤ (1 / 8 : ℝ) * T n + (1 / 16 : ℝ) * T n +
            (1 / 8 : ℝ) * T n + C₂₉ * L n := by
          nlinarith only [hfirst, hsecond, hyoung, htail]
      _ ≤ (3 / 8 : ℝ) * T n + C₂₉ * L n := by
          nlinarith only [hTnonneg n]
  obtain ⟨n₀, hn₀⟩ := MorreyDecayAux.exists_small_normalized hηd hrec hsource
  have hθscale : Θ n₀ = T n₀ * κ ^ ((n₀ : ℝ) * ε) := by
    dsimp [T]
    field_simp
  refine ⟨r₄, n₀, hr₄, hr₄bar, hball₄, ?_⟩
  change Θ n₀ ≤ η * κ ^ ((n₀ : ℝ) * ε) / 4
  rw [hθscale]
  calc
    T n₀ * κ ^ ((n₀ : ℝ) * ε) ≤
        (ηd / 4) * κ ^ ((n₀ : ℝ) * ε) :=
      mul_le_mul_of_nonneg_right hn₀ (Real.rpow_nonneg hκ.le _)
    _ ≤ (η / 4) * κ ^ ((n₀ : ℝ) * ε) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (min_le_left η _) (by norm_num))
        (Real.rpow_nonneg hκ.le _)
    _ = η * κ ^ ((n₀ : ℝ) * ε) / 4 := by ring

end CKN
