-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.NewtonianDerivativeLocalLp
import CKN.Foundation.Euclidean.RieszSecondAllExponentsPaper
import CKN.Foundation.Euclidean.PotentialLocalLpGrowth
import CKN.Foundation.Euclidean.PotentialLocalLpKernel
import CKN.Pressure.PotentialDecayPotentials
import CKN.Pressure.Potentials
import CKN.Pressure.IdentificationExtension
import CKN.Pressure.SpatialDerivSupport
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

private def convMaj (f g : Vec3 → ℝ≥0∞) (x : Vec3) : ℝ≥0∞ :=
  ∫⁻ y : Vec3, f y * g (x-y)

private theorem convMaj_integral {f g : Vec3 → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : Vec3, convMaj f g x) = (∫⁻ y, f y) * (∫⁻ z, g z) := by
  unfold convMaj
  rw [lintegral_lintegral_swap
    ((hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))).aemeasurable]
  have hinner (y : Vec3) : (∫⁻ x : Vec3, f y * g (x-y)) = f y * (∫⁻ x : Vec3, g x) := by
    rw [lintegral_const_mul (f y) (by fun_prop), lintegral_sub_right_eq_self]
  simp_rw [hinner]
  exact lintegral_mul_const _ hf

private theorem convMaj_measurable {f g : Vec3 → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) : Measurable (convMaj f g) := by
  apply Measurable.lintegral_prod_right
  exact ((hf.comp measurable_snd).mul
    (hg.comp (measurable_fst.sub measurable_snd)))

private theorem convMaj_young_3halves
    {p q : ℝ} (hp1 : 1 < p) (hp3 : p < 3 / 2)
    (hq1 : 1 < q) (hq3 : q < 3 / 2)
    (hpq : 1 / p + 1 / q = 5 / 3)
    {f g : Vec3 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x : Vec3, convMaj f g x ^ (3 / 2 : ℝ) ≤
      (∫⁻ y, f y ^ p) ^ ((3 / 2 : ℝ) / p) *
        (∫⁻ y, g y ^ q) ^ ((3 / 2 : ℝ) / q) := by
  let a : ℝ := p / (3 / 2 : ℝ)
  let b : ℝ := q / (3 / 2 : ℝ)
  let α : ℝ := (3 - 2 * p) / (2 * p)
  let β : ℝ := (3 - 2 * q) / (2 * q)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by dsimp [a]; rw [div_lt_one (by norm_num)]; exact hp3
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by dsimp [b]; rw [div_lt_one (by norm_num)]; exact hq3
  have hα : 0 ≤ 1 - a := by linarith only [ha1]
  have hβ : 0 ≤ 1 - b := by linarith only [hb1]
  have hα0 : 0 ≤ α := by
    dsimp [α]
    have hp0 : 0 < p := lt_trans (by norm_num) hp1
    have hp3' : 2 * p < 3 := by linarith only [hp3]
    exact div_nonneg (by linarith only [hp3'] : 0 ≤ 3 - 2 * p)
      (mul_nonneg (by norm_num) hp0.le)
  have hβ0 : 0 ≤ β := by
    dsimp [β]
    have hq0 : 0 < q := lt_trans (by norm_num) hq1
    have hq3' : 2 * q < 3 := by linarith only [hq3]
    exact div_nonneg (by linarith only [hq3'] : 0 ≤ 3 - 2 * q)
      (mul_nonneg (by norm_num) hq0.le)
  have hαid : α + 1 = (3 / 2 : ℝ) / p := by
    dsimp [α]
    field_simp; ring
  have hβid : β + 1 = (3 / 2 : ℝ) / q := by
    dsimp [β]
    field_simp; ring
  have hpne : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp1)
  have hqne : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq1)
  have hweights : (3 - 2 * p) / p + (3 - 2 * q) / q = 1 := by
    calc
      (3 - 2 * p) / p + (3 - 2 * q) / q = 3 * (1 / p + 1 / q) - 4 := by
        field_simp [hpne, hqne]
        ring
      _ = 1 := by rw [hpq]; norm_num
  have hsplit (u v : ℝ≥0∞) :
      (u ^ a * v ^ b) * (u ^ (1-a) * v ^ (1-b)) = u * v := by
    calc
      _ = (u ^ a * u ^ (1-a)) * (v ^ b * v ^ (1-b)) := by ac_rfl
      _ = u * v := by
        rw [← ENNReal.rpow_add_of_nonneg a (1-a) ha0.le hα,
          ← ENNReal.rpow_add_of_nonneg b (1-b) hb0.le hβ]
        simp only [add_sub_cancel, ENNReal.rpow_one]
  have hpowFirst (u v : ℝ≥0∞) :
      (u ^ a * v ^ b) ^ (3 / 2 : ℝ) = u ^ p * v ^ q := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 1 <;> dsimp [a, b] <;> field_simp
  have hpowSecond (u v : ℝ≥0∞) :
      (u ^ (1-a) * v ^ (1-b)) ^ (3 : ℝ) = u ^ (3 - 2*p) * v ^ (3 - 2*q) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 1 <;> dsimp [a, b] <;> field_simp
  have hconj : (3/2 : ℝ).HolderConjugate 3 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hpoint : ∀ x : Vec3,
      convMaj f g x ^ (3 / 2 : ℝ) ≤
        convMaj (fun y => f y ^ p) (fun y => g y ^ q) x *
          ((∫⁻ y, f y ^ p) ^ α * (∫⁻ y, g y ^ q) ^ β) := by
    intro x
    let sh : Vec3 → Vec3 := fun y => x - y
    have hsh : Measurable sh := by fun_prop
    have hHolder₁ := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Vec3)
      hconj
      (f := fun y => f y ^ a * g (x - y) ^ b)
      (g := fun y => f y ^ (1-a) * g (x-y) ^ (1-b)) (by fun_prop) (by fun_prop)
    have hHolder₂ := ENNReal.lintegral_mul_norm_pow_le
      (μ := (volume : Measure Vec3))
      (hf.pow_const p).aemeasurable
      ((hg.comp hsh).pow_const q).aemeasurable
      (p := (3 - 2*p)/p) (q := (3 - 2*q)/q)
      (div_nonneg (by linarith only [hp3] : 0 ≤ 3 - 2*p)
        (lt_trans (by norm_num) hp1).le)
      (div_nonneg (by linarith only [hq3] : 0 ≤ 3 - 2*q)
        (lt_trans (by norm_num) hq1).le) hweights
    have hHolder₂' :
        (∫⁻ y : Vec3, f y ^ (3 - 2*p) * g (x-y) ^ (3 - 2*q)) ≤
          (∫⁻ y, f y ^ p) ^ ((3 - 2*p)/p) *
            (∫⁻ y, g y ^ q) ^ ((3 - 2*q)/q) := by
      calc
        _ = ∫⁻ y : Vec3, (f y ^ p) ^ ((3-2*p)/p) *
            (g (x-y) ^ q) ^ ((3-2*q)/q) := by
          apply lintegral_congr
          intro y
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          congr 1 <;> field_simp
        _ ≤ (∫⁻ y, f y ^ p) ^ ((3-2*p)/p) *
            (∫⁻ y, g (x-y) ^ q) ^ ((3-2*q)/q) := hHolder₂
        _ = _ := by
          rw [show (∫⁻ y : Vec3, g (x-y) ^ q) = ∫⁻ y : Vec3, g y ^ q by
            exact lintegral_sub_left_eq_self (fun y : Vec3 => g y ^ q) x]
    have hleft : convMaj f g x = ∫⁻ y : Vec3,
        (f y ^ a * g (x-y) ^ b) * (f y ^ (1-a) * g (x-y) ^ (1-b)) := by
      unfold convMaj
      apply lintegral_congr
      intro y
      exact (hsplit (f y) (g (x-y))).symm
    have hfirst : (∫⁻ y : Vec3,
        (f y ^ a * g (x-y) ^ b) ^ (3/2 : ℝ)) =
        convMaj (fun y => f y ^ p) (fun y => g y ^ q) x := by
      unfold convMaj
      apply lintegral_congr
      intro y
      exact hpowFirst (f y) (g (x-y))
    have hsecond : (∫⁻ y : Vec3,
        (f y ^ (1-a) * g (x-y) ^ (1-b)) ^ (3:ℝ)) =
        ∫⁻ y : Vec3, f y ^ (3-2*p) * g (x-y) ^ (3-2*q) := by
      apply lintegral_congr
      intro y
      exact hpowSecond (f y) (g (x-y))
    have hpointHolder : convMaj f g x ≤
        convMaj (fun y => f y ^ p) (fun y => g y ^ q) x ^ (2/3 : ℝ) *
          (∫⁻ y : Vec3, f y ^ (3-2*p) * g (x-y) ^ (3-2*q)) ^ (1/3 : ℝ) := by
      calc
        convMaj f g x = _ := hleft
        _ ≤ (∫⁻ y : Vec3, (f y ^ a * g (x-y) ^ b) ^ (3/2 : ℝ)) ^ (1/(3/2 : ℝ)) *
            (∫⁻ y : Vec3, (f y ^ (1-a) * g (x-y) ^ (1-b)) ^ (3:ℝ)) ^ (1/3 : ℝ) := hHolder₁
        _ = _ := by rw [hfirst, hsecond]; norm_num
    calc
      convMaj f g x ^ (3/2 : ℝ) ≤
          (convMaj (fun y => f y ^ p) (fun y => g y ^ q) x ^ (2/3 : ℝ) *
            (∫⁻ y : Vec3, f y ^ (3-2*p) * g (x-y) ^ (3-2*q)) ^ (1/3 : ℝ)) ^ (3/2 : ℝ) :=
          ENNReal.rpow_le_rpow hpointHolder (by norm_num)
      _ = convMaj (fun y => f y ^ p) (fun y => g y ^ q) x *
          (∫⁻ y : Vec3, f y ^ (3-2*p) * g (x-y) ^ (3-2*q)) ^ (1/2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1 <;> norm_num
      _ ≤ convMaj (fun y => f y ^ p) (fun y => g y ^ q) x *
          ((∫⁻ y, f y ^ p) ^ α * (∫⁻ y, g y ^ q) ^ β) := by
        have hpow := ENNReal.rpow_le_rpow hHolder₂' (by norm_num : (0:ℝ) ≤ 1/2)
        have hsplitPow :
            ((∫⁻ y : Vec3, f y ^ p) ^ ((3-2*p)/p) *
              (∫⁻ y : Vec3, g y ^ q) ^ ((3-2*q)/q)) ^ (1/2 : ℝ) =
            (∫⁻ y : Vec3, f y ^ p) ^ (((3-2*p)/p)/2) *
              (∫⁻ y : Vec3, g y ^ q) ^ (((3-2*q)/q)/2) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          congr 1 <;> ring_nf
        have hαid : α = ((3-2*p)/p) / 2 := by dsimp [α]; ring
        have hβid : β = ((3-2*q)/q) / 2 := by dsimp [β]; ring
        rw [hαid, hβid]
        rw [hsplitPow] at hpow
        exact mul_le_mul_right hpow _
  have hHmeas : Measurable (fun y : Vec3 => f y ^ p) := hf.pow_const p
  have hGmeas : Measurable (fun y : Vec3 => g y ^ q) := hg.pow_const q
  have hlin :
      (∫⁻ x : Vec3, convMaj (fun y => f y ^ p) (fun y => g y ^ q) x) =
        (∫⁻ y, f y ^ p) * (∫⁻ y, g y ^ q) := convMaj_integral hHmeas hGmeas
  calc
    (∫⁻ x : Vec3, convMaj f g x ^ (3/2 : ℝ)) ≤
      ∫⁻ x : Vec3, convMaj (fun y => f y ^ p) (fun y => g y ^ q) x *
        ((∫⁻ y, f y ^ p) ^ α * (∫⁻ y, g y ^ q) ^ β) := by
          exact lintegral_mono hpoint
    _ = ((∫⁻ y, f y ^ p) ^ α * (∫⁻ y, g y ^ q) ^ β) *
        ((∫⁻ y, f y ^ p) * (∫⁻ y, g y ^ q)) := by
          have hconst : (fun x : Vec3 =>
              convMaj (fun y => f y ^ p) (fun y => g y ^ q) x *
                ((∫⁻ y, f y ^ p) ^ α * (∫⁻ y, g y ^ q) ^ β)) =
              fun x => ((∫⁻ y, f y ^ p) ^ α * (∫⁻ y, g y ^ q) ^ β) *
                convMaj (fun y => f y ^ p) (fun y => g y ^ q) x := by
            funext x
            ring
          rw [hconst,
            lintegral_const_mul _ (convMaj_measurable hHmeas hGmeas), hlin]
    _ = (∫⁻ y, f y ^ p) ^ ((3/2 : ℝ)/p) *
        (∫⁻ y, g y ^ q) ^ ((3/2 : ℝ)/q) := by
          calc
            _ = ((∫⁻ y, f y ^ p) ^ α * (∫⁻ y, f y ^ p)) *
                ((∫⁻ y, g y ^ q) ^ β * (∫⁻ y, g y ^ q)) := by ac_rfl
            _ = ((∫⁻ y, f y ^ p) ^ α * (∫⁻ y, f y ^ p) ^ (1 : ℝ)) *
                ((∫⁻ y, g y ^ q) ^ β * (∫⁻ y, g y ^ q) ^ (1 : ℝ)) := by
                  rw [ENNReal.rpow_one, ENNReal.rpow_one]
            _ = (∫⁻ y, f y ^ p) ^ (α + 1) *
                (∫⁻ y, g y ^ q) ^ (β + 1) := by
                  rw [← ENNReal.rpow_add_of_nonneg α 1 hα0 (by norm_num),
                    ← ENNReal.rpow_add_of_nonneg β 1 hβ0 (by norm_num)]
            _ = _ := by rw [hαid, hβid]

private theorem eLpNorm_scalarConvolution_young_3halves
    {p q : ℝ} (hp1 : 1 < p) (hp3 : p < 3 / 2)
    (hq1 : 1 < q) (hq3 : q < 3 / 2)
    (hpq : 1 / p + 1 / q = 5 / 3)
    {f g : Vec3 → ℝ} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (scalarConvolution f g) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume * eLpNorm g (ENNReal.ofReal q) volume := by
  let F : Vec3 → ℝ≥0∞ := fun y => ‖f y‖ₑ
  let G : Vec3 → ℝ≥0∞ := fun y => ‖g y‖ₑ
  have hmaj := convMaj_young_3halves hp1 hp3 hq1 hq3 hpq hf.enorm hg.enorm
  have hpoint (x : Vec3) :
      ‖scalarConvolution f g x‖ₑ ≤ convMaj F G x := by
    simpa only [scalarConvolution, convMaj, F, G, enorm_mul] using
      (enorm_integral_le_lintegral_enorm
        (fun y : Vec3 => f y * g (x-y)))
  have hbase :
      (∫⁻ x : Vec3, ‖scalarConvolution f g x‖ₑ ^ (3/2 : ℝ)) ≤
        (∫⁻ y : Vec3, F y ^ p) ^ ((3/2 : ℝ)/p) *
          (∫⁻ y : Vec3, G y ^ q) ^ ((3/2 : ℝ)/q) := by
    refine (lintegral_mono fun x => ?_).trans hmaj
    exact ENNReal.rpow_le_rpow (hpoint x) (by norm_num)
  have hfLp : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hgLp : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  have hconvLp : AEStronglyMeasurable (scalarConvolution f g) volume := by
    exact ((hf.comp measurable_snd).mul
      (hg.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable.integral_prod_right'
  have hfFormula := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (p := ENNReal.ofReal p) (by positivity) ENNReal.ofReal_ne_top hfLp
  have hgFormula := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (p := ENNReal.ofReal q) (by positivity) ENNReal.ofReal_ne_top hgLp
  have hconvFormula := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (p := ENNReal.ofReal (3/2 : ℝ)) (by positivity) ENNReal.ofReal_ne_top hconvLp
  have hfFormula' : eLpNorm f (ENNReal.ofReal p) volume =
      (∫⁻ y : Vec3, F y ^ p) ^ (1/p : ℝ) := by
    simpa only [F, ENNReal.toReal_ofReal (le_of_lt (lt_trans (by norm_num) hp1))] using
      hfFormula
  have hgFormula' : eLpNorm g (ENNReal.ofReal q) volume =
      (∫⁻ y : Vec3, G y ^ q) ^ (1/q : ℝ) := by
    simpa only [G, ENNReal.toReal_ofReal (le_of_lt (lt_trans (by norm_num) hq1))] using
      hgFormula
  have hconvFormula' : eLpNorm (scalarConvolution f g) (ENNReal.ofReal (3/2 : ℝ)) volume =
      (∫⁻ x : Vec3, ‖scalarConvolution f g x‖ₑ ^ (3/2 : ℝ)) ^ (2/3 : ℝ) := by
    calc
      _ = (∫⁻ x : Vec3, ‖scalarConvolution f g x‖ₑ ^ (3/2 : ℝ)) ^
          (1 / (3/2 : ℝ)) := by
        simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 3/2)] using hconvFormula
      _ = _ := by congr 1; norm_num
  have hroot := ENNReal.rpow_le_rpow hbase (by norm_num : (0:ℝ) ≤ 2/3)
  calc
    eLpNorm (scalarConvolution f g) (ENNReal.ofReal (3/2 : ℝ)) volume =
        (∫⁻ x : Vec3, ‖scalarConvolution f g x‖ₑ ^ (3/2 : ℝ)) ^ (2/3 : ℝ) :=
          hconvFormula'
    _ ≤ ((∫⁻ y : Vec3, F y ^ p) ^ ((3/2 : ℝ)/p) *
        (∫⁻ y : Vec3, G y ^ q) ^ ((3/2 : ℝ)/q)) ^ (2/3 : ℝ) := hroot
    _ = (∫⁻ y : Vec3, F y ^ p) ^ (1/p : ℝ) *
        (∫⁻ y : Vec3, G y ^ q) ^ (1/q : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 1 <;> field_simp
    _ = eLpNorm f (ENNReal.ofReal p) volume * eLpNorm g (ENNReal.ofReal q) volume := by
      rw [← hfFormula', ← hgFormula']

end CKN.Foundation.Euclidean


namespace CKN.Foundation.Euclidean

open CKN
open CKN.Foundation.Parabolic

private theorem exists_young_partner_of_one_lt_lt_six_fifths {p : ℝ}
    (hp1 : 1 < p) (hp65 : p < 6 / 5) :
    ∃ q : ℝ, 1 < q ∧ q < 3 / 2 ∧ 1 / p + 1 / q = 5 / 3 := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp1
  have hinvlt1 : 1 / p < 1 := by
    rw [div_lt_one hp0]
    exact hp1
  have hinvgt23 : 2 / 3 < 1 / p := by
    rw [lt_div_iff₀ hp0]
    nlinarith only [hp65]
  let q : ℝ := 1 / (5 / 3 - 1 / p)
  have hdpos : 0 < 5 / 3 - 1 / p := by linarith only [hinvlt1]
  have hq1 : 1 < q := by
    dsimp [q]
    rw [one_lt_div hdpos]
    linarith only [hinvgt23]
  have hq3 : q < 3 / 2 := by
    dsimp [q]
    rw [div_lt_iff₀ hdpos]
    have h : 2 / 3 < 5 / 3 - 1 / p := by linarith only [hinvlt1]
    nlinarith only [h]
  have hpq : 1 / p + 1 / q = 5 / 3 := by
    dsimp [q]
    have hne : 5 / 3 - 1 / p ≠ 0 := ne_of_gt hdpos
    field_simp
    ring
  exact ⟨q, hq1, hq3, hpq⟩

/-- The Newtonian potential of compactly supported `L^p` data is locally `L^{3/2}` for every
exponent `p > 1`. The lower range uses the matching truncated-kernel Young exponent; above
`6/5`, finite support reduces the datum to the established `L^{6/5}` estimate. -/
theorem pressureNewtonianPotential_memLp_ball_of_memLp_gt_one
    {g : Vec3 → ℝ} {p R ρ : ℝ} (hp1 : 1 < p) (hR : 0 < R) (hρ : 0 < ρ)
    (hgmeas : Measurable g) (hg : MemLp g (ENNReal.ofReal p) volume)
    (hgzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → g y = 0) :
    MemLp (pressureNewtonianPotential g) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) ρ)) := by
  by_cases hp65 : p < 6 / 5
  · obtain ⟨q, hq1, hq3, hpq⟩ :=
      exists_young_partner_of_one_lt_lt_six_fifths hp1 hp65
    let k : Vec3 → ℝ := fun z => -truncatedNewtonianPotentialKernel (R + ρ) z
    have hkmeas : Measurable k :=
      (measurable_truncatedNewtonianPotentialKernel (R + ρ)).neg
    have hk : MemLp k (ENNReal.ofReal q) volume := by
      have hk' := truncatedNewtonianPotentialKernel_memLp (R := R + ρ) (s := q)
        (by linarith only [hR, hρ])
        (by linarith only [hq1]) (lt_trans hq3 (by norm_num : (3 / 2 : ℝ) < 3))
      convert hk'.neg using 1
    have hconv : MemLp (scalarConvolution g k) (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      rw [memLp_iff]
      refine lt_of_le_of_lt
        (eLpNorm_scalarConvolution_young_3halves hp1
          (lt_trans hp65 (by norm_num)) hq1 hq3 hpq hgmeas hkmeas)
        (ENNReal.mul_lt_top hg.eLpNorm_lt_top hk.eLpNorm_lt_top)
    have heq : pressureNewtonianPotential g =ᵐ[
        volume.restrict (Metric.ball (0 : Vec3) ρ)] scalarConvolution g k := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hxnorm : ‖x‖ < ρ := mem_ball_zero_iff.mp hx
      rw [pressureNewtonianPotential, scalarConvolution]
      refine integral_congr_ae ?_
      filter_upwards [] with y
      by_cases hgy : g y = 0
      · simp [hgy]
      · have hy : y ∈ Metric.closedBall (0 : Vec3) R := by
          by_contra hy
          exact hgy (hgzero y hy)
        have hynorm : ‖y‖ ≤ R := mem_closedBall_zero_iff.mp hy
        have hxy : ‖x-y‖ < R+ρ := by
          have hsum : ‖x‖+‖y‖ < ρ+R := add_lt_add_of_lt_of_le hxnorm hynorm
          exact (lt_of_le_of_lt (norm_sub_le x y) hsum).trans_eq (by ring)
        simp only [k, truncatedNewtonianPotentialKernel, hxy, ite_true]
        ring
    exact (hconv.restrict (Metric.ball (0 : Vec3) ρ)).ae_eq heq.symm
  · have hp65' : 6 / 5 ≤ p := le_of_not_gt hp65
    have hg65 := memLp_six_fifths_of_memLp_ofReal hp65' hg hgzero
    exact pressureNewtonianPotential_memLp_ball (by linarith only [hR, hρ])
      hgmeas hg65 hgzero

/-- The first-derivative Newtonian potential of compactly supported `L^p` data is locally
`L^{3/2}` for every exponent `p > 1`. -/
theorem pressureNewtonianDerivativePotential_memLp_ball_of_memLp_gt_one
    {g : Vec3 → ℝ} (i : Fin 3) {p R ρ : ℝ} (hp1 : 1 < p)
    (hR : 0 < R) (hρ : 0 < ρ) (hgmeas : Measurable g)
    (hg : MemLp g (ENNReal.ofReal p) volume)
    (hgzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → g y = 0) :
    MemLp (pressureNewtonianDerivativePotential i g) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) ρ)) := by
  by_cases hp65 : p < 6 / 5
  · obtain ⟨q, hq1, hq3, hpq⟩ :=
      exists_young_partner_of_one_lt_lt_six_fifths hp1 hp65
    let k : Vec3 → ℝ := truncatedNewtonianDerivative (R + ρ) i
    have hkmeas : Measurable k := measurable_truncatedNewtonianDerivative (R + ρ) i
    have hk : MemLp k (ENNReal.ofReal q) volume :=
      truncatedNewtonianDerivative_memLp_of_lt_three_halves
        (by linarith only [hR, hρ]) (by linarith only [hq1]) hq3 i
    have hconv : MemLp (scalarConvolution g k) (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      rw [memLp_iff]
      refine lt_of_le_of_lt
        (eLpNorm_scalarConvolution_young_3halves hp1
          (lt_trans hp65 (by norm_num)) hq1 hq3 hpq hgmeas hkmeas)
        (ENNReal.mul_lt_top hg.eLpNorm_lt_top hk.eLpNorm_lt_top)
    have heq : pressureNewtonianDerivativePotential i g =ᵐ[
        volume.restrict (Metric.ball (0 : Vec3) ρ)] scalarConvolution g k := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hxnorm : ‖x‖ < ρ := mem_ball_zero_iff.mp hx
      rw [pressureNewtonianDerivativePotential, scalarConvolution]
      refine integral_congr_ae ?_
      filter_upwards [] with y
      by_cases hgy : g y = 0
      · simp [hgy]
      · have hy : y ∈ Metric.closedBall (0 : Vec3) R := by
          by_contra hy
          exact hgy (hgzero y hy)
        have hynorm : ‖y‖ ≤ R := mem_closedBall_zero_iff.mp hy
        have hxy : ‖x-y‖ < R+ρ := by
          have hsum : ‖x‖+‖y‖ < ρ+R := add_lt_add_of_lt_of_le hxnorm hynorm
          exact (lt_of_le_of_lt (norm_sub_le x y) hsum).trans_eq (by ring)
        simp only [k, truncatedNewtonianDerivative, hxy, ite_true]
        ring
    exact (hconv.restrict (Metric.ball (0 : Vec3) ρ)).ae_eq heq.symm
  · have hp65' : 6 / 5 ≤ p := le_of_not_gt hp65
    have hg65 := memLp_six_fifths_of_memLp_ofReal hp65' hg hgzero
    exact pressureNewtonianDerivativePotential_memLp_ball i hR hρ hgmeas hg65 hgzero

end CKN.Foundation.Euclidean

namespace CKN.Foundation.Euclidean

open CKN
open CKN.Foundation.Parabolic

/-- Compactly supported `L^p` data, `p > 1`, gives the Liouville local-membership and linear-
growth hypotheses for its Newtonian potential. The displayed constant is the tree's explicit
`newtonianPotentialGrowthConstant`. -/
theorem pressureNewtonianPotential_growth_of_memLp_gt_one
    {g : Vec3 → ℝ} {p R : ℝ} (hp1 : 1 < p) (hR : 0 < R)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Vec3) R)
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianPotential g)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
    ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianPotential g)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        newtonianPotentialGrowthConstant g R * (1 + ρ) := by
  have hzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → g y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun hs => hy (hSupp hs))
  obtain ⟨g', hg'meas, hgg', hg'zero⟩ :=
    exists_measurable_representative_of_support_closedBall hg.aestronglyMeasurable hzero
  have hg' : MemLp g' (ENNReal.ofReal p) volume := hg.ae_eq hgg'
  have hnear' := pressureNewtonianPotential_memLp_ball_of_memLp_gt_one hp1 hR
    (by linarith only [hR] : 0 < 2 * R) hg'meas hg' hg'zero
  have hnear : MemLp (pressureNewtonianPotential g') (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) := hnear'
  have hg'int : Integrable g' volume :=
    integrable_of_memLp_ofReal_of_support (by linarith only [hp1]) hg' hg'zero
  have hzero :=
    CKN.memLp_and_lpNorm_linear_growth_of_inv_norm_decay
      (newtonianPotentialDecayConstant_nonneg g')
      (aestronglyMeasurable_pressureNewtonianPotential hg'meas) hnear
      (pressureNewtonianPotential_inv_norm_decay hR hg'int hg'zero)
  have hpot : pressureNewtonianPotential g = pressureNewtonianPotential g' :=
    pressureNewtonianPotential_congr_of_ae_eq hgg'
  have hconst : newtonianPotentialGrowthConstant g R =
      newtonianPotentialGrowthConstant g' R := by
    rw [newtonianPotentialGrowthConstant, newtonianPotentialGrowthConstant, hpot,
      newtonianPotentialDecayConstant_congr hgg']
  rw [hpot, hconst]
  exact hzero

/-- Compactly supported `L^p` data, `p > 1`, gives the Liouville local-membership and linear-
growth hypotheses for its first-derivative Newtonian potential. -/
theorem pressureNewtonianDerivativePotential_growth_of_memLp_gt_one
    {g : Vec3 → ℝ} (i : Fin 3) {p R : ℝ} (hp1 : 1 < p) (hR : 0 < R)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Vec3) R)
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianDerivativePotential i g)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
    ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianDerivativePotential i g)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        newtonianDerivativePotentialGrowthConstant i g R * (1 + ρ) := by
  have hzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → g y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hSupp h))
  obtain ⟨g', hg'meas, hgg', hg'zero⟩ :=
    exists_measurable_representative_of_support_closedBall hg.aestronglyMeasurable hzero
  have hg' : MemLp g' (ENNReal.ofReal p) volume := hg.ae_eq hgg'
  have hnear' := pressureNewtonianDerivativePotential_memLp_ball_of_memLp_gt_one i hp1
    hR (by linarith only [hR] : 0 < 2 * R) hg'meas hg' hg'zero
  have hnear : MemLp (pressureNewtonianDerivativePotential i g')
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (Metric.ball (0 : Vec3) (2 * R))) := hnear'
  have hg'int : Integrable g' volume :=
    integrable_of_memLp_ofReal_of_support (by linarith only [hp1]) hg' hg'zero
  have hzero' :=
    CKN.memLp_and_lpNorm_linear_growth_of_inv_norm_decay
      (newtonianDerivativePotentialDecayConstant_nonneg hR g')
      (aestronglyMeasurable_pressureNewtonianDerivativePotential i hg'meas) hnear
      (pressureNewtonianDerivativePotential_inv_norm_decay i hR hg'int hg'zero)
  have hpot : pressureNewtonianDerivativePotential i g =
      pressureNewtonianDerivativePotential i g' :=
    pressureNewtonianDerivativePotential_congr_of_ae_eq i hgg'
  have hconst : newtonianDerivativePotentialGrowthConstant i g R =
      newtonianDerivativePotentialGrowthConstant i g' R := by
    rw [newtonianDerivativePotentialGrowthConstant,
      newtonianDerivativePotentialGrowthConstant, hpot,
      newtonianDerivativePotentialDecayConstant_congr R hgg']
  rw [hpot, hconst]
  exact hzero'

