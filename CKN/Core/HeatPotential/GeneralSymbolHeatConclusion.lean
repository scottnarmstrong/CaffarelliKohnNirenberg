-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbolHeatNearProof
import CKN.Core.HeatPotential.Campanato
import CKN.Foundation.Parabolic.BallDisplays
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.Prod

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Parabolic.Morrey

private lemma add_rpow_le_two_rpow_mul {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 ≤ p) :
    (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow ⟨a, ha⟩ ⟨b, hb⟩ hp
  have hℝ : ((⟨a, ha⟩ : ℝ≥0) + (⟨b, hb⟩ : ℝ≥0) : ℝ) ^ p ≤
      ((2 : ℝ≥0) : ℝ) ^ (p - 1) * (((⟨a, ha⟩ : ℝ≥0) : ℝ) ^ p +
        ((⟨b, hb⟩ : ℝ≥0) : ℝ) ^ p) := by
    exact_mod_cast h
  simpa using hℝ

theorem multiplier_pairAverage_add_le
    {E : Type*} [NormedAddCommGroup E]
    {h k : ParabolicPoint → E} {B : Set ParabolicPoint} {p : ℝ}
    (hp : 1 ≤ p) (hBpos : 0 < volume B) (hBtop : volume B < ∞)
    (hh : MemLp h (ENNReal.ofReal p) (volume.restrict B))
    (hkAEM : AEStronglyMeasurable k (volume.restrict B))
    (hkp : Integrable (fun xy : ParabolicPoint × ParabolicPoint =>
      ‖k xy.1 - k xy.2‖ ^ p)
      ((volume.restrict B).prod (volume.restrict B))) :
    (⨍ x in B, ⨍ y in B, ‖(h + k) x - (h + k) y‖ ^ p) ≤
      (2 : ℝ) ^ (p - 1) *
        ((⨍ x in B, ⨍ y in B, ‖h x - h y‖ ^ p) +
          (⨍ x in B, ⨍ y in B, ‖k x - k y‖ ^ p)) := by
  let μ : Measure ParabolicPoint := volume.restrict B
  let ν : Measure (ParabolicPoint × ParabolicPoint) := μ.prod μ
  let a : ParabolicPoint × ParabolicPoint → ℝ := fun xy =>
    ‖h xy.1 - h xy.2‖ ^ p
  let b : ParabolicPoint × ParabolicPoint → ℝ := fun xy =>
    ‖k xy.1 - k xy.2‖ ^ p
  let c : ParabolicPoint × ParabolicPoint → ℝ := fun xy =>
    ‖(h + k) xy.1 - (h + k) xy.2‖ ^ p
  have hμpos : 0 < μ Set.univ := by simpa [μ] using hBpos
  have hμtop : μ Set.univ < ∞ := by simpa [μ] using hBtop
  let _ : IsFiniteMeasure μ := ⟨by simpa [μ] using hBtop⟩
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hhpow : Integrable (fun x => ‖h x‖ ^ p) μ := by
    simpa [μ, ENNReal.toReal_ofReal hp0.le] using hh.integrable_norm_rpow'
  have hhaem : AEStronglyMeasurable h μ := hh.aestronglyMeasurable
  have hhaem1 : AEStronglyMeasurable (fun xy : ParabolicPoint × ParabolicPoint =>
      h xy.1 - h xy.2) ν := by
    exact (hhaem.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).sub
      (hhaem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have haem : AEStronglyMeasurable a ν := by
    dsimp [a]
    exact (Real.continuous_rpow_const (zero_le_one.trans hp)).comp_aestronglyMeasurable
      hhaem1.norm
  have hleft : Integrable (fun xy : ParabolicPoint × ParabolicPoint =>
      ‖h xy.1‖ ^ p) ν := hhpow.comp_fst μ
  have hright : Integrable (fun xy : ParabolicPoint × ParabolicPoint =>
      ‖h xy.2‖ ^ p) ν := hhpow.comp_snd μ
  have hmajor : Integrable (fun xy : ParabolicPoint × ParabolicPoint =>
      (2 : ℝ) ^ (p - 1) * (‖h xy.1‖ ^ p + ‖h xy.2‖ ^ p)) ν := by
    exact (hleft.add hright).const_mul _
  have ha : Integrable a ν := by
    apply hmajor.mono haem
    filter_upwards [] with xy
    dsimp [a]
    have hcalc :
        ‖h xy.1 - h xy.2‖ ^ p ≤
          (2 : ℝ) ^ (p - 1) * (‖h xy.1‖ ^ p + ‖h xy.2‖ ^ p) := by
      calc
      ‖h xy.1 - h xy.2‖ ^ p ≤
          (‖h xy.1‖ + ‖h xy.2‖) ^ p := by
        exact Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le _ _) hp0.le
      _ ≤ (2 : ℝ) ^ (p - 1) * (‖h xy.1‖ ^ p + ‖h xy.2‖ ^ p) :=
        add_rpow_le_two_rpow_mul (norm_nonneg _) (norm_nonneg _) hp
    have hmaj0 : 0 ≤ (2 : ℝ) ^ (p - 1) *
        (‖h xy.1‖ ^ p + ‖h xy.2‖ ^ p) := by positivity
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      abs_of_nonneg hmaj0] using hcalc
  have hb : Integrable b ν := hkp
  have hkaem : AEStronglyMeasurable (fun xy : ParabolicPoint × ParabolicPoint =>
      k xy.1 - k xy.2) ν := by
    exact (hkAEM.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).sub
      (hkAEM.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have haemc : AEStronglyMeasurable c ν := by
    dsimp [c]
    have hsum : (fun xy : ParabolicPoint × ParabolicPoint =>
        ‖h xy.1 + k xy.1 - (h xy.2 + k xy.2)‖ ^ p) =
        (fun xy => ‖(h xy.1 - h xy.2) + (k xy.1 - k xy.2)‖ ^ p) := by
      funext xy
      congr 2
      abel
    have hmeas := (Real.continuous_rpow_const (zero_le_one.trans hp)).comp_aestronglyMeasurable
      ((hhaem1.add hkaem).norm)
    rw [hsum]
    exact hmeas
  have hc : Integrable c ν := by
    have hmaj : Integrable (fun xy : ParabolicPoint × ParabolicPoint =>
        (2 : ℝ) ^ (p - 1) * (a xy + b xy)) ν :=
      (ha.add hb).const_mul _
    apply hmaj.mono haemc
    filter_upwards [] with xy
    have hcalc :
        ‖(h + k) xy.1 - (h + k) xy.2‖ ^ p ≤
          (2 : ℝ) ^ (p - 1) *
            (‖h xy.1 - h xy.2‖ ^ p + ‖k xy.1 - k xy.2‖ ^ p) := by
      calc
      ‖(h + k) xy.1 - (h + k) xy.2‖ ^ p ≤
          (‖h xy.1 - h xy.2‖ + ‖k xy.1 - k xy.2‖) ^ p := by
        exact Real.rpow_le_rpow (norm_nonneg _) (by
          rw [show (h + k) xy.1 - (h + k) xy.2 =
          (h xy.1 - h xy.2) + (k xy.1 - k xy.2) by
            simp only [Pi.add_apply]
            abel]
          exact norm_add_le _ _) hp0.le
      _ ≤ (2 : ℝ) ^ (p - 1) *
          (‖h xy.1 - h xy.2‖ ^ p + ‖k xy.1 - k xy.2‖ ^ p) :=
        add_rpow_le_two_rpow_mul (norm_nonneg _) (norm_nonneg _) hp
    change ‖‖h xy.1 + k xy.1 - (h xy.2 + k xy.2)‖ ^ p‖ ≤
      ‖(2 : ℝ) ^ (p - 1) *
        (‖h xy.1 - h xy.2‖ ^ p + ‖k xy.1 - k xy.2‖ ^ p)‖
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.norm_eq_abs,
      abs_of_nonneg (by positivity :
        0 ≤ (2 : ℝ) ^ (p - 1) *
          (‖h xy.1 - h xy.2‖ ^ p + ‖k xy.1 - k xy.2‖ ^ p))]
    simpa only [Pi.add_apply] using hcalc
  have hineq' : ∫ xy, c xy ∂ν ≤
      ∫ xy, (2 : ℝ) ^ (p - 1) * (a xy + b xy) ∂ν := by
    have hmaj : Integrable (fun xy : ParabolicPoint × ParabolicPoint =>
        (2 : ℝ) ^ (p - 1) * (a xy + b xy)) ν :=
      (ha.add hb).const_mul _
    refine integral_mono hc hmaj ?_
    intro xy
    have hcalc :
        ‖(h + k) xy.1 - (h + k) xy.2‖ ^ p ≤
          (2 : ℝ) ^ (p - 1) *
            (‖h xy.1 - h xy.2‖ ^ p + ‖k xy.1 - k xy.2‖ ^ p) := by
      calc
      ‖(h + k) xy.1 - (h + k) xy.2‖ ^ p ≤
          (‖h xy.1 - h xy.2‖ + ‖k xy.1 - k xy.2‖) ^ p := by
        exact Real.rpow_le_rpow (norm_nonneg _) (by
          rw [show (h + k) xy.1 - (h + k) xy.2 =
          (h xy.1 - h xy.2) + (k xy.1 - k xy.2) by
            simp only [Pi.add_apply]
            abel]
          exact norm_add_le _ _) hp0.le
      _ ≤ (2 : ℝ) ^ (p - 1) *
          (‖h xy.1 - h xy.2‖ ^ p + ‖k xy.1 - k xy.2‖ ^ p) :=
        add_rpow_le_two_rpow_mul (norm_nonneg _) (norm_nonneg _) hp
    change ‖h xy.1 + k xy.1 - (h xy.2 + k xy.2)‖ ^ p ≤
      (2 : ℝ) ^ (p - 1) *
        (‖h xy.1 - h xy.2‖ ^ p + ‖k xy.1 - k xy.2‖ ^ p)
    simpa only [Pi.add_apply] using hcalc
  have hineq : ∫ xy, c xy ∂ν ≤
      (2 : ℝ) ^ (p - 1) * (∫ xy, a xy ∂ν + ∫ xy, b xy ∂ν) := by
    calc
      _ ≤ ∫ xy, (2 : ℝ) ^ (p - 1) * (a xy + b xy) ∂ν := hineq'
      _ = _ := by rw [integral_const_mul, integral_add ha hb]
  have hdouble : ∀ {f : ParabolicPoint × ParabolicPoint → ℝ},
      Integrable f ν →
      (⨍ x in B, ⨍ y in B, f (x, y)) =
        (μ Set.univ).toReal⁻¹ ^ (2 : ℕ) * ∫ xy, f xy ∂ν := by
    intro f hf
    change (⨍ x, ⨍ y, f (x, y) ∂μ ∂μ) = _
    rw [MeasureTheory.average_eq]
    have hi : (fun x : ParabolicPoint => ⨍ y, f (x, y) ∂μ) =
        (fun x => (μ.real Set.univ)⁻¹ * ∫ y, f (x, y) ∂μ) := by
      funext x
      rw [MeasureTheory.average_eq]
      simp only [smul_eq_mul]
    rw [hi, integral_const_mul]
    have hf' : Integrable (Function.uncurry (fun x y => f (x, y))) (μ.prod μ) := by
      change Integrable f (μ.prod μ)
      simpa [ν] using hf
    rw [MeasureTheory.integral_integral hf']
    simp only [smul_eq_mul, MeasureTheory.measureReal_def]
    ring
  have hdoublea := hdouble (f := a) ha
  have hdoubleb := hdouble (f := b) hb
  have hdoublec := hdouble (f := c) hc
  rw [hdoublec, hdoublea, hdoubleb]
  have hnorm : 0 ≤ (μ Set.univ).toReal⁻¹ ^ (2 : ℕ) := by positivity
  calc
    _ ≤ (μ Set.univ).toReal⁻¹ ^ (2 : ℕ) *
        ((2 : ℝ) ^ (p - 1) *
          (∫ xy, a xy ∂ν + ∫ xy, b xy ∂ν)) :=
      mul_le_mul_of_nonneg_left hineq hnorm
    _ = (2 : ℝ) ^ (p - 1) *
        ((μ Set.univ).toReal⁻¹ ^ (2 : ℕ) * ∫ xy, a xy ∂ν +
          (μ Set.univ).toReal⁻¹ ^ (2 : ℕ) * ∫ xy, b xy ∂ν) := by ring

private lemma multiplier_spatial_sphere_null (x : Vec3) (r : ℝ) :
    volume {y : Vec3 | vec3EuclideanNorm (y - x) = r} = 0 := by
  let e : Vec3 → _ := WithLp.toLp 2
  let S := Metric.sphere (e x) r
  have hS : MeasurableSet S := isClosed_sphere.measurableSet
  have hzero : volume S = 0 := Measure.addHaar_sphere volume (e x) r
  have heq : {y : Vec3 | vec3EuclideanNorm (y - x) = r} = e ⁻¹' S := by
    ext y
    change vec3EuclideanNorm (y - x) = r ↔ dist (e y) (e x) = r
    rw [dist_eq_norm]
    change vec3EuclideanNorm (y - x) = r ↔
      ‖WithLp.toLp 2 y - WithLp.toLp 2 x‖ = r
    rw [← WithLp.toLp_sub, vec3EuclideanNorm_eq_l2]
  rw [heq]
  exact (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hS.nullMeasurableSet |>.trans hzero

private lemma parabolic_closedBall_eq_product (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    Metric.closedBall z r =
      {y : Vec3 | vec3EuclideanNorm (y - z.1) ≤ r} ×ˢ
        Icc (z.2 - r ^ 2) (z.2 + r ^ 2) := by
  ext p
  rw [Metric.mem_closedBall, dist_eq_parabolicDist]
  change max (vec3EuclideanNorm (p.1 - z.1)) (Real.sqrt |p.2 - z.2|) ≤ r ↔ _
  rw [max_le_iff, Real.sqrt_le_iff]
  constructor
  · rintro ⟨hspace, htime, htime'⟩
    have habs : |p.2 - z.2| ≤ r ^ 2 := htime'
    have hlow : z.2 - r ^ 2 ≤ p.2 := by
      have habs' := (abs_le.mp habs)
      linarith only [habs'.1]
    have hhigh : p.2 ≤ z.2 + r ^ 2 := by
      have habs' := (abs_le.mp habs)
      linarith only [habs'.2]
    exact ⟨hspace, hlow, hhigh⟩
  · rintro ⟨hspace, hlow, hhigh⟩
    have habs : |p.2 - z.2| ≤ r ^ 2 := by
      rw [abs_le]
      constructor <;> linarith only [hlow, hhigh]
    exact ⟨hspace, hr.le, habs⟩

theorem multiplier_closedBall_diff_ball_null (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    volume (Metric.closedBall z r \ Metric.ball z r) = 0 := by
  rw [show Metric.closedBall z r =
      {y : Vec3 | vec3EuclideanNorm (y - z.1) ≤ r} ×ˢ
        Icc (z.2 - r ^ 2) (z.2 + r ^ 2) by
      exact parabolic_closedBall_eq_product z hr,
    metricBall_eq_parabolicBall]
  let S : Set Vec3 := {y | vec3EuclideanNorm (y - z.1) ≤ r}
  let T : Set ℝ := Icc (z.2 - r ^ 2) (z.2 + r ^ 2)
  let sS : Set Vec3 := {y | vec3EuclideanNorm (y - z.1) = r}
  let tL : Set ℝ := {z.2 - r ^ 2}
  let tR : Set ℝ := {z.2 + r ^ 2}
  have hsub : (S ×ˢ T) \ (vec3Ball z.1 r ×ˢ Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)) ⊆
      (sS ×ˢ T) ∪ (S ×ˢ (tL ∪ tR)) := by
    intro p hp
    rcases p with ⟨y, s⟩
    simp only [Set.mem_sdiff, Set.mem_prod, S, T] at hp
    rcases hp with ⟨⟨hys, hst⟩, hnot⟩
    by_cases hysphere : vec3EuclideanNorm (y - z.1) = r
    · exact Or.inl ⟨hysphere, hst⟩
    · right
      have hspace_lt : vec3EuclideanNorm (y - z.1) < r := lt_of_le_of_ne hys hysphere
      have htime : s = z.2 - r ^ 2 ∨ s = z.2 + r ^ 2 := by
        by_contra hn
        have hlow : z.2 - r ^ 2 < s := lt_of_le_of_ne hst.1 (by
          intro heq
          exact hn (Or.inl heq.symm))
        have hhigh : s < z.2 + r ^ 2 := lt_of_le_of_ne hst.2 (by
          intro heq
          exact hn (Or.inr heq))
        exact hnot ⟨hspace_lt, hlow, hhigh⟩
      rcases htime with htime | htime
      · exact ⟨hys, Or.inl htime⟩
      · exact ⟨hys, Or.inr htime⟩
  apply measure_mono_null hsub
  rw [Integration.volume_parabolicPoint_eq_prod]
  apply measure_union_null
  · change ((volume : Measure Vec3).prod (volume : Measure ℝ)) (sS ×ˢ T) = 0
    rw [Measure.prod_prod, multiplier_spatial_sphere_null, zero_mul]
  · change ((volume : Measure Vec3).prod (volume : Measure ℝ)) (S ×ˢ (tL ∪ tR)) = 0
    rw [Measure.prod_prod]
    have ht : volume (tL ∪ tR) = 0 :=
      measure_union_null (by simp [tL]) (by simp [tR])
    rw [ht, mul_zero]

theorem multiplier_pairOscillation_sub_const {k : ParabolicPoint → ℂ} {c : ℂ}
    {z : ParabolicPoint} {r p : ℝ} :
    multiplierHeatPairOscillation (fun w => k w - c) z r p =
      multiplierHeatPairOscillation k z r p := by
  unfold multiplierHeatPairOscillation
  congr 4
  funext w
  congr 2
  funext w'
  congr 1
  simp only [sub_sub_sub_cancel_right]

theorem multiplier_rpow_shell_bound {γ r C S : ℝ} (hr : 0 < r) (n : ℕ) :
    C * (2 * r) * ((2 : ℝ) ^ (n : ℝ) * r) ^ (γ - 1) * S =
      (2 * C * S) * (2 : ℝ) ^ ((n : ℝ) * (γ - 1)) * r ^ γ := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h2p : 0 < (2 : ℝ) ^ (n : ℝ) := by positivity
  have hpow : ((2 : ℝ) ^ (n : ℝ) * r) ^ (γ - 1) =
      (2 : ℝ) ^ ((n : ℝ) * (γ - 1)) * r ^ (γ - 1) := by
    rw [Real.mul_rpow h2p.le hr.le, ← Real.rpow_mul h2]
  have hrpow : r ^ (γ - 1) * r = r ^ γ := by
    calc
      r ^ (γ - 1) * r = r ^ (γ - 1) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = r ^ ((γ - 1) + 1) := (Real.rpow_add hr _ _).symm
      _ = r ^ γ := by congr 1; ring
  rw [hpow]
  calc
    C * (2 * r) * (2 ^ ((n : ℝ) * (γ - 1)) * r ^ (γ - 1)) * S =
        (2 * C * S) * 2 ^ ((n : ℝ) * (γ - 1)) *
          (r ^ (γ - 1) * r) := by ring
    _ = _ := by rw [hrpow]

end CKN.Core.HeatPotential
