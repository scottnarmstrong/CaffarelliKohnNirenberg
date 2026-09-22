-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Cylinders
import CKN.Foundation.Parabolic.Morrey.Zero

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

private theorem morreyBallCell_lower_exponent_of_ediam
    {P κ τ D : ℝ} (hP : 1 ≤ P) (hPκ : P ≤ κ) (hκτ : κ ≤ τ)
    (hD : 0 < D) {g : ParabolicPoint → ℝ} {E : Set ParabolicPoint}
    (hsupp : ∀ w ∉ E, g w = 0)
    (hdiam : Metric.ediam E ≤ ENNReal.ofReal D)
    (hE : E.Nonempty) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    morreyBallCell P κ g z r ≤
      ENNReal.ofReal (max 1 (D ^ (5 * (1 / κ - 1 / τ)))) *
        morreyBallNorm P τ g := by
  classical
  obtain ⟨w₀, hw₀⟩ := hE
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hκ0 : 0 < κ := lt_of_lt_of_le hP0 hPκ
  have hτ0 : 0 < τ := lt_of_lt_of_le hκ0 hκτ
  let aκ : ℝ := 5 * (1 / P - 1 / κ)
  let aτ : ℝ := 5 * (1 / P - 1 / τ)
  let δ : ℝ := 5 * (1 / κ - 1 / τ)
  have haκ : 0 ≤ aκ := by
    dsimp [aκ]
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_div_le_one_div_of_le hP0 hPκ))
  have haτ : 0 ≤ aτ := by
    dsimp [aτ]
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_div_le_one_div_of_le hP0 (hPκ.trans hκτ)))
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_div_le_one_div_of_le hκ0 hκτ))
  have hακ : -(5 * (1 - P / κ) / P) = -aκ := by
    dsimp [aκ]
    field_simp [hP0.ne', hκ0.ne']
  have hατ : -(5 * (1 - P / τ) / P) = -aτ := by
    dsimp [aτ]
    field_simp [hP0.ne', hτ0.ne']
  have hαrel : aτ = aκ + δ := by
    dsimp [aτ, aκ, δ]
    ring
  have hexp : -(5 * (1 - P / κ) / P) =
      δ + -(5 * (1 - P / τ) / P) := by
    rw [hακ, hατ]
    rw [hαrel]
    ring
  rcases le_or_gt r D with hsmall | hlarge
  · let A : ℝ≥0∞ := ENNReal.ofReal r
    have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
    have hAtop : A ≠ ∞ := ENNReal.ofReal_ne_top
    have hcell : morreyBallCell P κ g z r =
        A ^ δ * morreyBallCell P τ g z r := by
      unfold morreyBallCell
      rw [hexp, ENNReal.rpow_add _ _ hA0 hAtop]
      ac_rfl
    have hscale : A ^ δ ≤
        ENNReal.ofReal (max 1 (D ^ (5 * (1 / κ - 1 / τ)))) := by
      calc
        A ^ δ ≤ (ENNReal.ofReal D) ^ δ :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hsmall) hδ
        _ = ENNReal.ofReal (D ^ δ) :=
          ENNReal.ofReal_rpow_of_nonneg hD.le hδ
        _ ≤ ENNReal.ofReal (max 1 (D ^ δ)) :=
          ENNReal.ofReal_le_ofReal (le_max_right _ _)
    calc
      morreyBallCell P κ g z r = A ^ δ * morreyBallCell P τ g z r := hcell
      _ ≤ ENNReal.ofReal (max 1 (D ^ δ)) * morreyBallNorm P τ g :=
        (mul_le_mul_right (by
          unfold morreyBallNorm
          exact le_iSup_of_le z (le_iSup_of_le ⟨r, hr⟩ le_rfl)) _).trans
          (mul_le_mul_left hscale _)
  ·
    let R : ℕ → ℝ := fun n => D + (1 : ℝ) / ((n : ℝ) + 1)
    let T : ℕ → Set ParabolicPoint := fun n =>
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace w₀ (R n)
    let S : Set ParabolicPoint :=
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r
    let F : ParabolicPoint → ℝ≥0∞ := fun w => ENNReal.ofReal |g w| ^ P
    have hEdist (w : ParabolicPoint) (hw : w ∈ E) :
        edist w₀ w ≤ ENNReal.ofReal D := by
      exact Metric.edist_le_of_ediam_le hw₀ hw hdiam
    have hdist (w : ParabolicPoint) (hw : w ∈ E) : dist w₀ w ≤ D := by
      have hEd := hEdist w hw
      rw [edist_dist] at hEd
      exact (ENNReal.ofReal_le_ofReal_iff hD.le).mp hEd
    have hRlim : Tendsto R atTop (𝓝 D) := by
      dsimp [R]
      simpa using tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hRpowlim : Tendsto (fun n => R n ^ δ) atTop (𝓝 (D ^ δ)) := by
      have hpair : Tendsto (fun n => (R n, δ)) atTop (𝓝 (D, δ)) := by
        simpa only [nhds_prod_eq] using hRlim.prodMk
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ))
      exact (Real.continuousAt_rpow (D, δ) (Or.inl hD.ne')).tendsto.comp hpair
    have hTmeas (n : ℕ) : MeasurableSet (T n) :=
      Metric.isOpen_ball.measurableSet
    have hSmeas : MeasurableSet S := Metric.isOpen_ball.measurableSet
    have hEt (n : ℕ) : E ⊆ T n := by
      intro w hw
      have hRn : D < R n := by
        dsimp [R]
        exact lt_add_of_pos_right _ (by positivity)
      exact Metric.mem_ball'.mpr ((hdist w hw).trans_lt hRn)
    have hglobal (n : ℕ) :
        ballPowerIntegral P g z r ≤ ballPowerIntegral P g w₀ (R n) := by
      have hpoint : ∀ w, S.indicator F w ≤ (T n).indicator F w := by
        intro w
        by_cases hsw : w ∈ S
        · by_cases htw : w ∈ T n
          · simp [hsw, htw]
          · have hFzero : F w = 0 := by
              have hnotE : w ∉ E := by
                intro hw
                exact htw (hEt n hw)
              simp [F, hsupp w hnotE, ENNReal.zero_rpow_of_pos hP0]
            simp [hsw, htw, hFzero]
        · simp [hsw]
      unfold ballPowerIntegral
      rw [← lintegral_indicator hSmeas, ← lintegral_indicator (hTmeas n)]
      exact lintegral_mono hpoint
    have hlargeBound (n : ℕ) (hRn : R n ≤ r) :
        morreyBallCell P κ g z r ≤
          ENNReal.ofReal (R n ^ δ) * morreyBallNorm P τ g := by
      let A : ℝ≥0∞ := ENNReal.ofReal r
      let B : ℝ≥0∞ := ENNReal.ofReal (R n)
      have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
      have hAtop : A ≠ ∞ := ENNReal.ofReal_ne_top
      have hB0 : B ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_trans hD (by
        dsimp [R]
        exact lt_add_of_pos_right _ (by positivity)))).ne'
      have hBtop : B ≠ ∞ := ENNReal.ofReal_ne_top
      have hBA : B ≤ A := ENNReal.ofReal_le_ofReal hRn
      have hroot : (ballPowerIntegral P g z r) ^ (1 / P) ≤
          B ^ aτ * morreyBallNorm P τ g := by
        have hroot' := ENNReal.rpow_le_rpow (hglobal n)
          (one_div_nonneg.mpr hP0.le)
        have hRnpos : 0 < R n := lt_trans hD (by
          dsimp [R]
          exact lt_add_of_pos_right _ (by positivity))
        have hcellτ : morreyBallCell P τ g w₀ (R n) ≤ morreyBallNorm P τ g := by
          unfold morreyBallNorm
          exact le_iSup_of_le w₀ (le_iSup_of_le ⟨R n, hRnpos⟩ le_rfl)
        have hcellτ' : B ^ (-aτ) *
            (ballPowerIntegral P g w₀ (R n)) ^ (1 / P) ≤
              morreyBallNorm P τ g := by
          simpa only [morreyBallCell, hατ, B] using hcellτ
        have hcancel : B ^ aτ * B ^ (-aτ) = 1 := by
          rw [← ENNReal.rpow_add _ _ hB0 hBtop, add_neg_cancel, ENNReal.rpow_zero]
        calc
          (ballPowerIntegral P g z r) ^ (1 / P) ≤
              (ballPowerIntegral P g w₀ (R n)) ^ (1 / P) := hroot'
          _ = B ^ aτ * (B ^ (-aτ) *
              (ballPowerIntegral P g w₀ (R n)) ^ (1 / P)) := by
                rw [← mul_assoc, hcancel, one_mul]
          _ ≤ B ^ aτ * morreyBallNorm P τ g := mul_le_mul_right hcellτ' _
      have hratio : A ^ (-aκ) * B ^ aκ ≤ 1 := by
        calc
          A ^ (-aκ) * B ^ aκ ≤ A ^ (-aκ) * A ^ aκ :=
            mul_le_mul_right (ENNReal.rpow_le_rpow hBA haκ) _
          _ = 1 := by
            rw [← ENNReal.rpow_add _ _ hA0 hAtop, neg_add_cancel,
              ENNReal.rpow_zero]
      have hcoef : A ^ (-aκ) * B ^ aτ ≤ B ^ δ := by
        calc
          A ^ (-aκ) * B ^ aτ = B ^ δ * (A ^ (-aκ) * B ^ aκ) := by
            rw [hαrel, ENNReal.rpow_add _ _ hB0 hBtop]
            ac_rfl
          _ ≤ B ^ δ * 1 := mul_le_mul_right hratio (B ^ δ)
          _ = B ^ δ := mul_one _
      calc
        morreyBallCell P κ g z r ≤ A ^ (-aκ) *
            (B ^ aτ * morreyBallNorm P τ g) := by
          simpa only [morreyBallCell, hακ, A] using
            (mul_le_mul_right hroot _)
        _ = (A ^ (-aκ) * B ^ aτ) * morreyBallNorm P τ g := by ac_rfl
        _ ≤ B ^ δ * morreyBallNorm P τ g := mul_le_mul_left hcoef _
        _ = ENNReal.ofReal (R n ^ δ) * morreyBallNorm P τ g := by
          rw [ENNReal.ofReal_rpow_of_nonneg
            (lt_trans hD (by
              dsimp [R]
              exact lt_add_of_pos_right _ (by positivity))).le hδ]
    by_cases hNtop : morreyBallNorm P τ g = ∞
    · have hcoefpos : 0 < ENNReal.ofReal (max 1 (D ^ δ)) :=
        ENNReal.ofReal_pos.mpr (lt_of_lt_of_le (by norm_num)
          (le_max_left _ _))
      rw [hNtop, ENNReal.mul_top hcoefpos.ne']
      exact le_top
    · have hRnear : ∀ᶠ n : ℕ in atTop, R n ≤ r := by
        filter_upwards [hRlim.eventually (Iio_mem_nhds hlarge)] with n hn
        exact hn.le
      have hbound : ∀ᶠ n : ℕ in atTop,
          morreyBallCell P κ g z r ≤ ENNReal.ofReal (R n ^ δ) *
            morreyBallNorm P τ g :=
        hRnear.mono fun n hn => hlargeBound n hn
      have hright : Tendsto
          (fun n : ℕ => ENNReal.ofReal (R n ^ δ) * morreyBallNorm P τ g)
          atTop (𝓝 (ENNReal.ofReal (D ^ δ) * morreyBallNorm P τ g)) := by
        exact (ENNReal.continuous_mul_const hNtop).tendsto _ |>.comp
          ((ENNReal.continuous_ofReal.tendsto (D ^ δ)).comp hRpowlim)
      have hlim := le_of_tendsto_of_tendsto tendsto_const_nhds hright hbound
      calc
        morreyBallCell P κ g z r ≤
            ENNReal.ofReal (D ^ δ) * morreyBallNorm P τ g := hlim
        _ ≤ ENNReal.ofReal (max 1 (D ^ δ)) * morreyBallNorm P τ g :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _

/-- A function supported in a set of parabolic diameter at most `D` has its
lower-exponent ball-Morrey norm bounded by the `D`-scale cost. -/
theorem morreyBallNorm_lower_morrey_exponent_of_ediam
    (P κ τ D : ℝ) (hP : 1 ≤ P) (hPκ : P ≤ κ) (hκτ : κ ≤ τ) (hD : 0 < D)
    (g : ParabolicPoint → ℝ) (E : Set ParabolicPoint)
    (hsupp : ∀ w ∉ E, g w = 0)
    (hdiam : Metric.ediam E ≤ ENNReal.ofReal D) :
    morreyBallNorm P κ g ≤
      ENNReal.ofReal (max 1 (D ^ (5 * (1 / κ - 1 / τ)))) * morreyBallNorm P τ g := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  classical
  by_cases hE : E.Nonempty
  · obtain ⟨w₀, hw₀⟩ := hE
    have hEnonempty : E.Nonempty := ⟨w₀, hw₀⟩
    unfold morreyBallNorm
    refine iSup_le fun z => iSup_le fun r => ?_
    exact morreyBallCell_lower_exponent_of_ediam hP hPκ hκτ hD hsupp hdiam
      hEnonempty z r.2
  · have hgzero : g = fun _ => 0 := by
      funext w
      by_cases hw : w ∈ E
      · exact (hE ⟨w, hw⟩).elim
      · exact hsupp w hw
    rw [hgzero, morreyBallNorm_zero hP0, morreyBallNorm_zero hP0]
    simp

end CKN.Foundation.Parabolic.Morrey

end
