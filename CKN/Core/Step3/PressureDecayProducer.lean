-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step3.PressureDecayTShape
import CKN.Pressure.CZP1Closer
import CKN.Pressure.ForceCancellationSolenoidalDisplay
import CKN.Pressure.PressureDecompositionFull
import CKN.Pressure.PkConstantsNonneg

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step3

open CKN

private lemma pressure_delta_sq_eq_scale_producer
    {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) :
    delta p z r ^ 2 = r ^ (-4 / 3 : ℝ) *
      (eLpNorm' p (3 / 2 : ℝ)
        (volume.restrict (parabolicCylinder z.1 z.2 r))).toReal := by
  unfold delta
  have hnonneg : 0 ≤ (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal := ENNReal.toReal_nonneg
  have hbase : 0 ≤ r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
  norm_num only [Nat.cast_ofNat]
  have hpow : (r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^ (2 / 3 : ℝ) =
      r ^ (-4 / 3 : ℝ) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal ^ (2 / 3 : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt hr) _) hnonneg]
    rw [← Real.rpow_mul hr.le]
    norm_num
  rw [hpow]
  have heq : eLpNorm' p (3 / 2 : ℝ)
      (volume.restrict (parabolicCylinder z.1 z.2 r)) =
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
    rw [eLpNorm'_eq_lintegral_enorm]
    norm_num only [Nat.cast_ofNat]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [] with w
    rw [← ofReal_norm, Real.norm_eq_abs]
  rw [heq, ← ENNReal.toReal_rpow]
  ring_nf

private lemma eLpNorm_le_fin_six
    {p : ParabolicPoint → ℝ} {g : Fin 6 → ParabolicPoint → ℝ}
    {E : Set ParabolicPoint}
    (hrep : ∀ᵐ w ∂(volume.restrict E), p w = ∑ k : Fin 6, g k w)
    (hmeas : ∀ k : Fin 6,
      AEStronglyMeasurable (g k) (volume.restrict E)) :
    eLpNorm' p (3 / 2 : ℝ) (volume.restrict E) ≤
      ∑ k : Fin 6, eLpNorm' (g k) (3 / 2 : ℝ)
        (volume.restrict E) := by
  have hmono : eLpNorm' p (3 / 2 : ℝ) (volume.restrict E) ≤
      eLpNorm' (fun w => ∑ k : Fin 6, g k w) (3 / 2 : ℝ)
        (volume.restrict E) := by
    apply eLpNorm'_mono_ae (by norm_num)
    filter_upwards [hrep] with w hw
    rw [hw]
  have hsum := eLpNorm'_sum_le
    (s := (Finset.univ : Finset (Fin 6))) (f := g)
    (by intro k hk; exact hmeas k)
    (by norm_num : (1 : ℝ) ≤ 3 / 2)
  simpa [Finset.sum_apply] using hmono.trans hsum

private lemma pressure_decay_force_free_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {z : ParabolicPoint} {ρ r C₁₂ : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hC₁₂ : 0 ≤ C₁₂)
    (hP12C : pressureP12Constant ≤ C₁₂)
    (hCZ_p1 : ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
      eLpNorm' (fun w : ParabolicPoint => pressureP1
        (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
        p f w.2 w.1) (3 / 2 : ℝ)
        (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
      ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ))
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
        (tsupport ψ) volume ∧
      ∫ w in spaceTimeSet Ω I,
        ∑ i : Fin 3, f w i * spatialPartial ψ i w = 0) :
    delta p z r ≤
      Real.sqrt (2 * C₁₂) * (r / ρ) ^ (-1 / 2 : ℝ) *
          Real.sqrt (alpha u z ρ) * Real.sqrt (beta u Du z ρ) +
        Real.sqrt (2 * C₁₂) * (r / ρ) ^ (1 / 3 : ℝ) *
          delta p z ρ +
        Real.sqrt 0 * (r / ρ) ^ (1 / 2 : ℝ) *
          Real.sqrt (lambda q f z ρ) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun t j => MeasureTheory.average
    (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)
  obtain ⟨B, T, η', c', hB, hT, hη', hc', hP1, hP2, hP3, hP4, hP5, hP6,
    hP7, hP8⟩ := pressure_source_measurable_on_cylinder hsol hρ hsub
  subst B
  subst T
  subst η'
  have hc_eq : c' = c := by
    funext t
    simpa [c] using hc' t
  subst c'
  let E : Set ParabolicPoint := parabolicCylinder z.1 z.2 ρ
  let Bρ : Set Vec3 := vec3Ball z.1 ρ
  let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  have hET : volume.restrict E =
      (volume.restrict Bρ).prod (volume.restrict Tρ) := by
    rw [show E = Bρ ×ˢ Tρ by
      ext w
      rfl, Measure.prod_restrict,
      CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    rfl
  have hP7a : AEMeasurable (fun v : ParabolicPoint =>
      pressureP7 η f v.2 v.1) (volume.restrict E) := hP7.aemeasurable
  have hP8a : AEMeasurable (fun v : ParabolicPoint =>
      pressureP8 η f v.2 v.1) (volume.restrict E) := hP8.aemeasurable
  let P7m : ParabolicPoint → ℝ := fun w =>
    AEMeasurable.mk (fun v : ParabolicPoint =>
      pressureP7 η f v.2 v.1) hP7a w
  let P8m : ParabolicPoint → ℝ := fun w =>
    AEMeasurable.mk (fun v : ParabolicPoint =>
      pressureP8 η f v.2 v.1) hP8a w
  have hP7eq : (fun w : ParabolicPoint => pressureP7 η f w.2 w.1) =ᵐ[
      volume.restrict E] P7m := by
    exact hP7a.ae_eq_mk
  have hP8eq : (fun w : ParabolicPoint => pressureP8 η f w.2 w.1) =ᵐ[
      volume.restrict E] P8m := by
    exact hP8a.ae_eq_mk
  have hP7prod :
      (fun w : ParabolicPoint => pressureP7 η f w.2 w.1) =ᵐ[
        (volume.restrict Bρ).prod (volume.restrict Tρ)] P7m := by
    rw [← hET]
    exact hP7eq
  have hP8prod :
      (fun w : ParabolicPoint => pressureP8 η f w.2 w.1) =ᵐ[
        (volume.restrict Bρ).prod (volume.restrict Tρ)] P8m := by
    rw [← hET]
    exact hP8eq
  have hP7slices : ∀ᵐ s ∂volume.restrict Tρ, ∀ᵐ x ∂volume.restrict Bρ,
      pressureP7 η f s x = P7m (x, s) := by
    have hswap :=
      MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
        hP7prod
    exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap
  have hP8slices : ∀ᵐ s ∂volume.restrict Tρ, ∀ᵐ x ∂volume.restrict Bρ,
      pressureP8 η f s x = P8m (x, s) := by
    have hswap :=
      MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
        hP8prod
    exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap
  have hforce := pressure_force_cancellation_of_sws hsol hρ hsub hdiv
  have hforce_rep_slices : ∀ᵐ s ∂volume.restrict Tρ, ∀ᵐ x ∂volume.restrict Bρ,
      P7m (x, s) + P8m (x, s) = 0 := by
    filter_upwards [hforce, hP7slices, hP8slices] with s hs h7 h8
    filter_upwards [ae_restrict_of_ae hs, h7, h8] with x hx h7x h8x
    rw [← h7x, ← h8x]
    exact hx
  have hP7m_meas : Measurable P7m := hP7a.measurable_mk
  have hP8m_meas : Measurable P8m := hP8a.measurable_mk
  have hforce_set : MeasurableSet
      {w : ParabolicPoint | P7m w + P8m w = 0} := by
    exact measurableSet_eq_fun (hP7m_meas.add hP8m_meas) measurable_const
  have hforce_set_prod : MeasurableSet
      {w : Vec3 × ℝ | P7m w + P8m w = 0} := by
    exact hforce_set
  have hforce_prod :
      ∀ᵐ w : Vec3 × ℝ ∂((volume.restrict Bρ).prod (volume.restrict Tρ)),
        P7m w + P8m w = 0 := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hforce_set_prod]
    exact (MeasureTheory.Measure.ae_ae_comm hforce_set_prod).mpr hforce_rep_slices
  have hforce_E : ∀ᵐ w ∂volume.restrict E,
      pressureP7 η f w.2 w.1 + pressureP8 η f w.2 w.1 = 0 := by
    rw [hET]
    filter_upwards [hforce_prod, hP7prod, hP8prod] with w hw h7 h8
    rw [h7, h8]
    exact hw
  let Er : Set ParabolicPoint := parabolicCylinder z.1 z.2 r
  have hEr : Er ⊆ E := by
    exact parabolicCylinder_mono (by positivity)
      (by nlinarith only [hhalf, hρ])
  have hforce_Er := ae_restrict_of_ae_restrict_of_subset hEr hforce_E
  have hηinner : ∀ x, x ∈ vec3Ball z.1 r → η x = 1 := by
    intro x hx
    apply mollifiedBallCutoff_eq_one_on_inner z.1 hρ
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)]
    have hx' := mem_vec3Ball.mp hx
    have hrinner : r < 13 * ρ / 20 := by
      nlinarith only [hhalf, hρ]
    have hx'' : vecEuclideanNorm (x - z.1) < r := by
      simpa [vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot, pow_two]
        using hx'
    exact lt_of_lt_of_le hx'' hrinner.le
  let g : Fin 6 → ParabolicPoint → ℝ := fun k w => match k with
    | 0 => pressureP1 η u c p f w.2 w.1
    | 1 => pressureP2 η u c w.2 w.1
    | 2 => pressureP3 η u c w.2 w.1
    | 3 => pressureP4 η u c w.2 w.1
    | 4 => pressureP5 η p w.2 w.1
    | 5 => pressureP6 η p w.2 w.1
  have hrep : ∀ᵐ w ∂volume.restrict Er, p w = ∑ k : Fin 6, g k w := by
    filter_upwards [hforce_Er,
      ae_restrict_mem (measurableSet_parabolicCylinder z.1 z.2 r)] with w hw hmem
    rcases w with ⟨x, s⟩
    have hx := (mem_parabolicCylinder.mp hmem).1
    have hpoint := pressure_decomposition_pointwise η u c p f s x
    have hpoint' : p (x, s) =
        pressureP1 η u c p f s x + pressureP2 η u c s x +
          pressureP3 η u c s x + pressureP4 η u c s x +
          pressureP5 η p s x + pressureP6 η p s x := by
      have hηx := hηinner x hx
      have hfull := hpoint
      rw [hηx] at hfull
      calc
        p (x, s) = (1 : ℝ) * p (x, s) := by ring
        _ = pressureP1 η u c p f s x + pressureP2 η u c s x +
            pressureP3 η u c s x + pressureP4 η u c s x +
            pressureP5 η p s x + pressureP6 η p s x +
            (pressureP7 η f s x + pressureP8 η f s x) := by
              rw [one_mul]
              linear_combination hfull
        _ = _ := by rw [hw]; ring
    calc
      p (x, s) =
          pressureP1 η u c p f s x + pressureP2 η u c s x +
            pressureP3 η u c s x + pressureP4 η u c s x +
            pressureP5 η p s x + pressureP6 η p s x := hpoint'
      _ = ∑ k : Fin 6, g k (x, s) := by
        simp [g, Fin.sum_univ_succ]
        ring
  have hmeas (k : Fin 6) :
      AEStronglyMeasurable (g k) (volume.restrict Er) := by
    fin_cases k
    · simpa [g] using hP1.mono_measure (Measure.restrict_mono_set volume hEr)
    · simpa [g] using hP2.mono_measure (Measure.restrict_mono_set volume hEr)
    · simpa [g] using hP3.mono_measure (Measure.restrict_mono_set volume hEr)
    · simpa [g] using hP4.mono_measure (Measure.restrict_mono_set volume hEr)
    · simpa [g] using hP5.mono_measure (Measure.restrict_mono_set volume hEr)
    · simpa [g] using hP6.mono_measure (Measure.restrict_mono_set volume hEr)
  have hnorm := eLpNorm_le_fin_six hrep hmeas
  let N : ℝ≥0∞ := ENNReal.ofReal (r ^ (-4 / 3 : ℝ))
  let μ : Measure ParabolicPoint := volume.restrict Er
  have hP234 := pressureP234_bound hsol hρ hr hhalf hsub
  have hP56 := pressureP56_bound hsol hρ hr hhalf hsub
  have hCZ : N * eLpNorm' (g 0) (3 / 2 : ℝ) μ ≤
      ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ) := by
    simpa [N, μ, g, η, c] using hCZ_p1
  have hP234' : N * (eLpNorm' (g 1) (3 / 2 : ℝ) μ +
      eLpNorm' (g 2) (3 / 2 : ℝ) μ +
      eLpNorm' (g 3) (3 / 2 : ℝ) μ) ≤
      ENNReal.ofReal (C₁₂ * (r / ρ) * alpha u z ρ * beta u Du z ρ) := by
    have h := hP234
    have hbase : N * (eLpNorm' (g 1) (3 / 2 : ℝ) μ +
        eLpNorm' (g 2) (3 / 2 : ℝ) μ +
        eLpNorm' (g 3) (3 / 2 : ℝ) μ) ≤
        ENNReal.ofReal (pressureP12Constant * (r / ρ) *
          alpha u z ρ * beta u Du z ρ) := by
      simpa [N, μ, g, η, c] using h
    exact hbase.trans (ENNReal.ofReal_mono (by
      have hP12 : pressureP12Constant ≤ C₁₂ := by
        exact hP12C
      have hratio : 0 ≤ r / ρ := (div_nonneg hr.le hρ.le)
      have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
      have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP12 hratio) hα)
        hβ))
  have hP56' : N * (eLpNorm' (g 4) (3 / 2 : ℝ) μ +
      eLpNorm' (g 5) (3 / 2 : ℝ) μ) ≤
      ENNReal.ofReal (C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) *
        (delta p z ρ) ^ 2) := by
    have h := hP56
    have hbase : N * (eLpNorm' (g 4) (3 / 2 : ℝ) μ +
        eLpNorm' (g 5) (3 / 2 : ℝ) μ) ≤
        ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
          (delta p z ρ) ^ 2) := by
      simpa [N, μ, g, η, c] using h
    exact hbase.trans (ENNReal.ofReal_mono (by
      have hP12 : pressureP12Constant ≤ C₁₂ := by
        exact hP12C
      have hratio : 0 ≤ r / ρ := (div_nonneg hr.le hρ.le)
      have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
      have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
      have hδ : 0 ≤ (delta p z ρ) ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hP12
          (Real.rpow_nonneg hratio (2 / 3 : ℝ))) hδ))
  have hnorm_mul : N * eLpNorm' p (3 / 2 : ℝ) μ ≤
      N * ∑ k : Fin 6, eLpNorm' (g k) (3 / 2 : ℝ) μ :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hsum_rewrite :
      (∑ k : Fin 6, eLpNorm' (g k) (3 / 2 : ℝ) μ) =
        eLpNorm' (g 0) (3 / 2 : ℝ) μ +
          (eLpNorm' (g 1) (3 / 2 : ℝ) μ +
            eLpNorm' (g 2) (3 / 2 : ℝ) μ +
            eLpNorm' (g 3) (3 / 2 : ℝ) μ) +
          (eLpNorm' (g 4) (3 / 2 : ℝ) μ +
            eLpNorm' (g 5) (3 / 2 : ℝ) μ) := by
    simp [Fin.sum_univ_succ]
    ring
  have hgroup : N * eLpNorm' p (3 / 2 : ℝ) μ ≤
      ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (C₁₂ * (r / ρ) *
          alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) *
          (delta p z ρ) ^ 2) := by
    calc
      _ ≤ N * ∑ k : Fin 6, eLpNorm' (g k) (3 / 2 : ℝ) μ := hnorm_mul
      _ = N * eLpNorm' (g 0) (3 / 2 : ℝ) μ +
          N * (eLpNorm' (g 1) (3 / 2 : ℝ) μ +
            eLpNorm' (g 2) (3 / 2 : ℝ) μ +
            eLpNorm' (g 3) (3 / 2 : ℝ) μ) +
          N * (eLpNorm' (g 4) (3 / 2 : ℝ) μ +
            eLpNorm' (g 5) (3 / 2 : ℝ) μ) := by rw [hsum_rewrite]; ring
      _ ≤ _ := by
        exact add_le_add (add_le_add hCZ hP234') hP56'
  have hrightfin :
      (ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
          alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (C₁₂ * (r / ρ) *
          alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) *
          (delta p z ρ) ^ 2)) ≠ ∞ := by
    exact ENNReal.add_ne_top.mpr ⟨
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
      ENNReal.ofReal_ne_top⟩
  have hA : ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
      alpha u z ρ * beta u Du z ρ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hB : ENNReal.ofReal (C₁₂ * (r / ρ) *
      alpha u z ρ * beta u Du z ρ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hC : ENNReal.ofReal (C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) *
      (delta p z ρ) ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hA0 : 0 ≤ C₁₂ * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC₁₂ (inv_nonneg.mpr (div_nonneg hr.le hρ.le)))
        (by unfold alpha; positivity))
      (by unfold beta; positivity)
  have hB0 : 0 ≤ C₁₂ * (r / ρ) * alpha u z ρ * beta u Du z ρ := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC₁₂ (div_nonneg hr.le hρ.le))
        (by unfold alpha; positivity))
      (by unfold beta; positivity)
  have hC0 : 0 ≤ C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) *
      (delta p z ρ) ^ 2 := by
    positivity
  have hAB : (ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
      alpha u z ρ * beta u Du z ρ) +
      ENNReal.ofReal (C₁₂ * (r / ρ) *
        alpha u z ρ * beta u Du z ρ)) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hA, hB⟩
  have hright_toReal :
      (ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
          alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (C₁₂ * (r / ρ) *
          alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) *
          (delta p z ρ) ^ 2)).toReal =
      C₁₂ * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ +
        C₁₂ * (r / ρ) * alpha u z ρ * beta u Du z ρ +
        C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) * (delta p z ρ) ^ 2 := by
    rw [ENNReal.toReal_add hAB hC, ENNReal.toReal_add hA hB,
      ENNReal.toReal_ofReal hA0, ENNReal.toReal_ofReal hB0,
      ENNReal.toReal_ofReal hC0]
  have hleft : N * eLpNorm' p (3 / 2 : ℝ) μ ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hgroup (lt_top_iff_ne_top.mpr hrightfin))
  have hnormR := (ENNReal.toReal_le_toReal hleft hrightfin).2 hgroup
  have hscale : 0 ≤ r ^ (-4 / 3 : ℝ) := by positivity
  simp only [N, ENNReal.toReal_mul, ENNReal.toReal_ofReal hscale] at hnormR
  rw [hright_toReal] at hnormR
  have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
  have hδ : 0 ≤ delta p z ρ := by unfold delta; positivity
  have hδr : 0 ≤ delta p z r := by unfold delta; positivity
  have hsq : (delta p z r) ^ 2 ≤
      C₁₂ * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ +
        C₁₂ * (r / ρ) * alpha u z ρ * beta u Du z ρ +
        C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) * (delta p z ρ) ^ 2 := by
    rw [pressure_delta_sq_eq_scale_producer hr]
    calc
      _ ≤ C₁₂ * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ +
          C₁₂ * (r / ρ) * alpha u z ρ * beta u Du z ρ +
          C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) * (delta p z ρ) ^ 2 := hnormR
      _ = _ := by rfl
  apply pressureDecay_algebra
  · exact div_pos hr hρ
  · exact (div_le_iff₀ hρ).2 (by nlinarith only [hhalf])
  · exact hC₁₂
  · exact (by norm_num)
  · exact hα
  · exact hβ
  · exact hδ
  · unfold lambda
    positivity
  · exact hδr
  · simpa only [zero_mul, add_zero] using hsq

/-- Pressure decay with a common absolute constant for the general-force and
local spacetime-solenoidal branches, and a force coefficient depending only on q. -/
theorem repair_step_pressure_decay :
∃ C₁₄ : ℝ, 0 ≤ C₁₄ ∧ ∀ q : ℝ, ∃ C₁₅ : ℝ, 0 ≤ C₁₅ ∧
∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ r : ℝ}, 0 < ρ → 0 < r → r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      delta p z r ≤
        C₁₄ * (r / ρ) ^ (-1 / 2 : ℝ)
            * Real.sqrt (alpha u z ρ) * Real.sqrt (beta u Du z ρ)
          + C₁₄ * (r / ρ) ^ (1 / 3 : ℝ) * delta p z ρ
          + C₁₅ * (r / ρ) ^ (1 / 2 : ℝ)
              * Real.sqrt (lambda q f z ρ) ∧
      ((∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
          IntegrableOn (fun w => ∑ i : Fin 3, f w i * spatialPartial ψ i w)
            (tsupport ψ) volume ∧
          ∫ w in spaceTimeSet Ω I,
            ∑ i : Fin 3, f w i * spatialPartial ψ i w = 0) →
        delta p z r ≤
          C₁₄ * (r / ρ) ^ (-1 / 2 : ℝ)
              * Real.sqrt (alpha u z ρ) * Real.sqrt (beta u Du z ρ)
            + C₁₄ * (r / ρ) ^ (1 / 3 : ℝ) * delta p z ρ) := by
  let C₁₂ : ℝ := max pressureP12Constant czP1ThetaDecayConstant
  let C₁₄ : ℝ := Real.sqrt (2 * C₁₂)
  have hP12 : 0 ≤ pressureP12Constant := pressureP12Constant_nonneg
  have hCZ : 0 ≤ czP1ThetaDecayConstant := czP1ThetaDecayConstant_nonneg
  have hC₁₂ : 0 ≤ C₁₂ := by
    dsimp [C₁₂]
    exact hP12.trans (le_max_left _ _)
  have hC₁₄ : 0 ≤ C₁₄ := by
    dsimp [C₁₄]
    positivity
  refine ⟨C₁₄, hC₁₄, ?_⟩
  intro q
  let C₁₅ : ℝ := Real.sqrt
    (2 * max (pressureP13Constant q) (pressureP7SolutionConstant q).toReal)
  have hP13 : 0 ≤ pressureP13Constant q :=
    pressureP13Constant_nonneg (x₀ := (0 : Vec3)) (ρ := 1) (by norm_num)
  have hP7 : 0 ≤ (pressureP7SolutionConstant q).toReal :=
    ENNReal.toReal_nonneg
  have hC₁₅ : 0 ≤ C₁₅ := by
    dsimp [C₁₅]
    positivity
  refine ⟨C₁₅, hC₁₅, ?_⟩
  intro Ω I u Du p f hsol z ρ r hρ hr hhalf hsub
  constructor
  · have hCZ_p1 := pressureP1_thetaDecay_hCZ_unconditional q Ω I u Du p f
      hsol hρ hr hhalf hsub
    have hgeneral := pressureDecay_one_scale_T czP1ThetaDecayConstant hsol
      hρ hr hhalf hsub hCZ_p1
    simpa [C₁₄, C₁₅, C₁₂] using hgeneral
  · intro hdiv
    have hCZ_p1 := pressureP1_thetaDecay_hCZ_unconditional q Ω I u Du p f
      hsol hρ hr hhalf hsub
    have hCZ_p1' : ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint => pressureP1
          (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
          p f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        ENNReal.ofReal (C₁₂ * (r / ρ)⁻¹ *
          alpha u z ρ * beta u Du z ρ) := by
      exact hCZ_p1.trans (ENNReal.ofReal_mono (by
        have hratio : 0 ≤ (r / ρ)⁻¹ := by positivity
        have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
        have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hratio) hα) hβ))
    have hP12C : pressureP12Constant ≤ C₁₂ := by
      dsimp [C₁₂]
      exact le_max_left _ _
    simpa only [Real.sqrt_zero, zero_mul, add_zero] using
      (pressure_decay_force_free_bound hsol hρ hr hhalf hsub hC₁₂ hP12C
        hCZ_p1' hdiv)

end CKN.Core.Step3
