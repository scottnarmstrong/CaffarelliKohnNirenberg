-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Energy.AELocalEnergy
import CKN.Setting.Energy.PointwiseEnergy

/-!
# The fixed-scale local energy inequality against the affine backward ramp

This module proves the affine-ramp energy estimate of `eq:lei-h` in `paper/ckn.tex`:
for every nonnegative space-time test function `φ`, every time `t` and every
`h > 0`, the dissipation and the right-hand side weighted by the piecewise
affine backward ramp

`χ(s) = 1` for `s ≤ t - h`, `(t - s)/h` for `t - h < s < t`, `0` for `s ≥ t`

satisfy the energy inequality, with the extra window average
`h⁻¹ ∫_{(t-h,t]} ∫ |u|² φ` on the left produced by the ramp derivative.

The route replaces the paper's mollification of `χ` by an exact averaging
identity: the ramp is the mean over `τ ∈ (t-h, t]` of the indicators
`1_{s < τ}`, so Tonelli turns the ramp-weighted integrals into window averages
of the half-line integrals, and the conclusion is the window average of the
already available almost-every-time inequality
`CKN.suitableWeakSolution_localEnergyInequality_ae`.

Two things have to be supplied for that averaging.  First the space-time
integrals are reduced to the time integrals of the spatial slice integrals,
which needs the integrability of the three densities and the fact that `φ`
vanishes off the space-time carrier, so the spatial integrals over `Ω` are
integrals over the whole space.  Second, the almost-every-time inequality is
only stated on the time domain `I`, while the window `(t-h, t]` is arbitrary;
since `I` is open and order connected, a time outside it lies either below all
of `I`, where every term vanishes, or above all of `I`, where the half-line
integrals are the full ones and the inequality is the global energy inequality
`CKN.suitableWeakSolution_energyInequality` for `φ` itself.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN

/-- The piecewise affine backward ramp of `eq:time-cutoff`. -/
def affineTimeRamp (t h : ℝ) : ℝ → ℝ :=
  fun s => if s ≤ t - h then 1 else if s < t then (t - s) / h else 0

private theorem affineTimeRamp_linear_lipschitzWith {t h : ℝ} (hh : 0 < h) :
    LipschitzWith (Real.toNNReal h⁻¹) (fun s : ℝ => (t - s) / h) := by
  apply LipschitzWith.of_le_add_mul'
  intro x y
  rw [Real.dist_eq]
  field_simp [ne_of_gt hh]
  have hxy : y - x ≤ |x - y| := by
    simpa only [abs_sub_comm] using (le_abs_self (y - x))
  linarith only [hxy]

private theorem affineTimeRamp_eq_clamp {t h : ℝ} (hh : 0 < h) :
    affineTimeRamp t h = fun s : ℝ => max 0 (min ((t - s) / h) 1) := by
  funext s
  unfold affineTimeRamp
  by_cases hs₁ : s ≤ t - h
  · have hq : 1 ≤ (t - s) / h := by
      apply (le_div_iff₀ hh).2
      linarith only [hs₁]
    rw [ite_eq_left hs₁, min_eq_right hq, max_eq_right (by norm_num)]
  · by_cases hs₂ : s < t
    · have hq₀ : 0 ≤ (t - s) / h :=
        div_nonneg (by linarith only [hs₂]) hh.le
      have hq₁ : (t - s) / h ≤ 1 := by
        apply (div_le_iff₀ hh).2
        linarith only [hs₁]
      rw [ite_eq_right hs₁, ite_eq_left hs₂, min_eq_left hq₁, max_eq_right hq₀]
    · have hq₀ : (t - s) / h ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (not_lt.mp hs₂)) hh.le
      have hq₁ : (t - s) / h ≤ 1 := hq₀.trans (by norm_num)
      rw [ite_eq_right hs₁, ite_eq_right hs₂, min_eq_left hq₁, max_eq_left hq₀]

/-- The affine backward ramp is Lipschitz with the reciprocal transition width. -/
theorem affineTimeRamp_lipschitzWith {t h : ℝ} (hh : 0 < h) :
    LipschitzWith (Real.toNNReal h⁻¹) (affineTimeRamp t h) := by
  rw [affineTimeRamp_eq_clamp hh]
  exact (affineTimeRamp_linear_lipschitzWith hh).min_const 1 |>.const_max 0

private theorem affineTimeRamp_hasDerivAt_of_lt {t h s : ℝ}
    (hs : s < t - h) : HasDerivAt (affineTimeRamp t h) 0 s := by
  have hev : affineTimeRamp t h =ᶠ[𝓝 s] (fun _ : ℝ => 1) := by
    filter_upwards [Iio_mem_nhds hs] with y hy
    have hy' : y < t - h := hy
    exact by simp only [affineTimeRamp, ite_eq_left hy'.le]
  exact (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq hev

private theorem affineTimeRamp_hasDerivAt_of_mem {t h s : ℝ}
    (hs₁ : t - h < s) (hs₂ : s < t) :
    HasDerivAt (affineTimeRamp t h) (-(h⁻¹)) s := by
  have hev : affineTimeRamp t h =ᶠ[𝓝 s] (fun y : ℝ => (t - y) / h) := by
    filter_upwards [Ioo_mem_nhds hs₁ hs₂] with y hy
    simp only [affineTimeRamp, ite_eq_right (not_le.mpr hy.1), ite_eq_left hy.2]
  have hlin : HasDerivAt (fun y : ℝ => (t - y) / h) (-(h⁻¹)) s := by
    have hbase := ((hasDerivAt_const s t).sub (hasDerivAt_id s)).div_const h
    convert hbase using 1
    · funext y
      rfl
    · ring
  exact hlin.congr_of_eventuallyEq hev

private theorem affineTimeRamp_hasDerivAt_of_gt {t h s : ℝ} (hh : 0 < h) (hs : t < s) :
    HasDerivAt (affineTimeRamp t h) 0 s := by
  have hev : affineTimeRamp t h =ᶠ[𝓝 s] (fun _ : ℝ => 0) := by
    filter_upwards [Ici_mem_nhds hs] with y hy
    have hy' : t ≤ y := hy
    have hnot : ¬ y ≤ t - h := by linarith only [hy', hs, hh]
    simp only [affineTimeRamp, ite_eq_right hnot, ite_eq_right (not_lt_of_ge hy')]
  exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev

/-- Away from the two corners, the ramp derivative is `-h⁻¹` on its affine
transition interval and zero elsewhere. -/
theorem affineTimeRamp_hasDerivAt_ae {t h : ℝ} (hh : 0 < h) :
    ∀ᵐ s : ℝ, HasDerivAt (affineTimeRamp t h)
      (-(h⁻¹) * Set.indicator (Set.Ioo (t - h) t) 1 s) s := by
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) (t - h),
    Measure.ae_ne (volume : Measure ℝ) t] with s hs₁ hs₂
  by_cases hleft : s < t - h
  · have hderiv := affineTimeRamp_hasDerivAt_of_lt hleft
    have hnot : s ∉ Set.Ioo (t - h) t := by
      intro hs
      exact (not_lt_of_ge (le_of_lt hleft)) hs.1
    rw [Set.indicator_of_notMem hnot]
    simpa using hderiv
  · have hleft' : t - h < s := by
      exact lt_of_le_of_ne (le_of_not_gt hleft) hs₁.symm
    by_cases hmid : s < t
    · have hderiv := affineTimeRamp_hasDerivAt_of_mem hleft' hmid
      have hmem : s ∈ Set.Ioo (t - h) t := ⟨hleft', hmid⟩
      rw [Set.indicator_of_mem hmem]
      simpa using hderiv
    · have hright : t < s := lt_of_le_of_ne (le_of_not_gt hmid) hs₂.symm
      have hderiv := affineTimeRamp_hasDerivAt_of_gt hh hright
      have hnot : s ∉ Set.Ioo (t - h) t := by
        intro hs
        exact (not_lt_of_ge (le_of_not_gt hmid)) hs.2
      rw [Set.indicator_of_notMem hnot]
      simpa using hderiv

private theorem affineTimeRamp_measurable (t h : ℝ) : Measurable (affineTimeRamp t h) := by
  unfold affineTimeRamp
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    ((measurable_const.sub measurable_id).div_const h) measurable_const

private theorem affineTimeRamp_abs_le_one {t h : ℝ} (hh : 0 < h) (s : ℝ) :
    |affineTimeRamp t h s| ≤ 1 := by
  unfold affineTimeRamp
  split_ifs with h₁ h₂
  · norm_num
  · have h₁' : t - h < s := not_le.mp h₁
    rw [abs_of_nonneg (div_nonneg (by linarith only [h₂]) hh.le), div_le_one hh]
    linarith only [h₁']
  · norm_num

private theorem finiteMeasure_restrict_Ioc (a b : ℝ) :
    IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc a b)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩

/-- The backward ramp is the average of the indicators `1_{s < τ}` over the
window `τ ∈ (t-h, t]`. -/
private theorem measure_window_gt (t h : ℝ) (hh : 0 < h) (s : ℝ) :
    (volume (Ioc (t - h) t ∩ Ioi s)).toReal = h * affineTimeRamp t h s := by
  have hset : Ioc (t - h) t ∩ Ioi s = Ioc (max (t - h) s) t := by
    ext τ
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]
    tauto
  rw [hset, Real.volume_Ioc, ENNReal.toReal_ofReal']
  unfold affineTimeRamp
  split_ifs with h₁ h₂
  · rw [max_eq_left h₁, max_eq_left (by linarith only [hh] : (0 : ℝ) ≤ t - (t - h))]
    ring
  · have h₁' : t - h ≤ s := (not_le.mp h₁).le
    rw [max_eq_right h₁', max_eq_left (by linarith only [h₂] : (0 : ℝ) ≤ t - s)]
    field_simp
  · have h₁' : t - h ≤ s := (not_le.mp h₁).le
    have h₂' : t ≤ s := not_lt.mp h₂
    rw [max_eq_right h₁', max_eq_right (by linarith only [h₂'] : t - s ≤ 0)]
    ring

private theorem integrable_indicator_Iio_prod {G : ℝ → ℝ} (hG : Integrable G volume)
    (a b : ℝ) :
    Integrable (fun z : ℝ × ℝ => Set.indicator (Iio z.1) G z.2)
      (((volume : Measure ℝ).restrict (Ioc a b)).prod volume) := by
  have := finiteMeasure_restrict_Ioc a b
  have hdom : Integrable (fun z : ℝ × ℝ => G z.2)
      (((volume : Measure ℝ).restrict (Ioc a b)).prod volume) := hG.comp_snd _
  have hset : MeasurableSet {z : ℝ × ℝ | z.2 < z.1} :=
    measurableSet_lt measurable_snd measurable_fst
  have heq : (fun z : ℝ × ℝ => Set.indicator (Iio z.1) G z.2) =
      Set.indicator {z : ℝ × ℝ | z.2 < z.1} (fun z : ℝ × ℝ => G z.2) := by
    funext z
    simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_ofPred_eq]
  rw [heq]
  exact hdom.indicator hset

/-- Averaging the backward half-line integrals over the window `(t-h, t]` gives the
ramp-weighted integral. -/
private theorem integral_window_Iio {G : ℝ → ℝ} (hG : Integrable G volume) (t h : ℝ)
    (hh : 0 < h) :
    ∫ τ in Ioc (t - h) t, (∫ s in Iio τ, G s) =
      h * ∫ s : ℝ, G s * affineTimeRamp t h s := by
  have := finiteMeasure_restrict_Ioc (t - h) t
  have hint := integrable_indicator_Iio_prod hG (t - h) t
  have hswap := MeasureTheory.integral_integral_swap
    (μ := (volume : Measure ℝ).restrict (Ioc (t - h) t)) (ν := (volume : Measure ℝ))
    (f := fun τ s => Set.indicator (Iio τ) G s) hint
  have hinner : ∀ s : ℝ,
      ∫ τ in Ioc (t - h) t, Set.indicator (Iio τ) G s =
        h * (G s * affineTimeRamp t h s) := by
    intro s
    have h1 : (fun τ : ℝ => Set.indicator (Iio τ) G s) =
        Set.indicator (Ioi s) (fun _ : ℝ => G s) := by
      funext τ
      simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ioi]
    rw [h1, setIntegral_indicator measurableSet_Ioi, setIntegral_const,
      measureReal_def, measure_window_gt t h hh s, smul_eq_mul]
    ring
  rw [show (∫ τ in Ioc (t - h) t, ∫ s in Iio τ, G s) =
      ∫ τ, ∫ s, Set.indicator (Iio τ) G s ∂volume
        ∂(volume : Measure ℝ).restrict (Ioc (t - h) t) by
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [integral_indicator measurableSet_Iio]]
  rw [hswap]
  simp_rw [hinner]
  rw [integral_const_mul]

/-- A space-time integral against a bounded time weight is the time integral of
the weighted spatial slice integrals. -/
private theorem integral_mul_time_weight {F : Vec3 × ℝ → ℝ} (hF : Integrable F volume)
    {c : ℝ → ℝ} (hc : Measurable c) (hc1 : ∀ s, |c s| ≤ 1) :
    ∫ z : ParabolicPoint, F z * c z.2 = ∫ s : ℝ, (∫ x : Vec3, F (x, s)) * c s := by
  have hcm : AEStronglyMeasurable (fun z : Vec3 × ℝ => c z.2) volume :=
    (hc.comp measurable_snd).aestronglyMeasurable
  have hFc : Integrable (fun z : Vec3 × ℝ => F z * c z.2) volume := by
    refine Integrable.mono' hF.norm (hF.1.mul hcm) ?_
    filter_upwards with z
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    simpa only [Real.norm_eq_abs] using hc1 z.2
  have hprod : Integrable (fun z : Vec3 × ℝ => F z * c z.2)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := hFc
  calc ∫ z : ParabolicPoint, F z * c z.2
      = ∫ x : Vec3, ∫ s : ℝ, F (x, s) * c s := integral_prod _ hprod
    _ = ∫ s : ℝ, ∫ x : Vec3, F (x, s) * c s :=
        integral_integral_swap (f := fun (x : Vec3) (s : ℝ) => F (x, s) * c s) hprod
    _ = ∫ s : ℝ, (∫ x : Vec3, F (x, s)) * c s := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        exact integral_mul_const _ _

private theorem test_eq_zero_of_notMem {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) {z : Vec3 × ℝ}
    (hz : z ∉ spaceTimeSet Ω I) : φ z = 0 := by
  by_contra hne
  exact hz (hφ.2.2 (subset_tsupport (f := φ) (Function.mem_support.mpr hne)))

private theorem rhs_eq_zero_of_notMem {Ω : Set Vec3} {I : Set ℝ}
    {u : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ} {f : Vec3 × ℝ → Vec3} {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) {z : Vec3 × ℝ}
    (hz : z ∉ spaceTimeSet Ω I) : localEnergyRhs u p f φ z = 0 :=
  localEnergyRhs_eq_zero_of_not_mem_tsupport_public hφ.1 (fun hmem => hz (hφ.2.2 hmem))

private theorem integral_slice_eq {F : Vec3 × ℝ → ℝ} (hF : Integrable F volume) :
    ∫ z : ParabolicPoint, F z = ∫ s : ℝ, ∫ x : Vec3, F (x, s) := by
  have hbase := integral_mul_time_weight hF (c := fun _ : ℝ => (1 : ℝ))
    measurable_const (by intro s; norm_num)
  simpa using hbase

/-- Off an open order-connected time interval the slice inequality is either
trivial or the global energy inequality, so the almost-everywhere statement on
the interval upgrades to one on the whole line. -/
private theorem ae_extend_off_interval {I : Set ℝ} (hIopen : IsOpen I)
    (hIord : OrdConnected I) {E G K : ℝ → ℝ}
    (hE0 : ∀ τ, τ ∉ I → E τ = 0) (hG0 : ∀ s, s ∉ I → G s = 0)
    (hK0 : ∀ s, s ∉ I → K s = 0)
    (htotal : 2 * ∫ s : ℝ, G s ≤ ∫ s : ℝ, K s)
    (hland : ∀ᵐ τ ∂(volume : Measure ℝ).restrict I,
      E τ + 2 * ∫ s in Iio τ, G s ≤ ∫ s in Iio τ, K s) :
    ∀ᵐ τ : ℝ, E τ + 2 * ∫ s in Iio τ, G s ≤ ∫ s in Iio τ, K s := by
  rw [ae_restrict_iff' hIopen.measurableSet] at hland
  filter_upwards [hland] with τ hτ
  by_cases hmem : τ ∈ I
  · exact hτ hmem
  have hcase : (∀ s ∈ I, τ < s) ∨ (∀ s ∈ I, s < τ) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨s₁, hs₁I, hs₁⟩, ⟨s₂, hs₂I, hs₂⟩⟩ := hcon
    exact hmem (hIord.out hs₁I hs₂I ⟨hs₁, hs₂⟩)
  rcases hcase with hleft | hright
  · have hG : ∫ s in Iio τ, G s = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      exact hG0 s fun hsI => absurd hs (not_lt.mpr (hleft s hsI).le)
    have hK : ∫ s in Iio τ, K s = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      exact hK0 s fun hsI => absurd hs (not_lt.mpr (hleft s hsI).le)
    rw [hG, hK, hE0 τ hmem]
    norm_num
  · have hG : ∫ s in Iio τ, G s = ∫ s : ℝ, G s := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
      exact hG0 s fun hsI => hs (hright s hsI)
    have hK : ∫ s in Iio τ, K s = ∫ s : ℝ, K s := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
      exact hK0 s fun hsI => hs (hright s hsI)
    rw [hG, hK, hE0 τ hmem, zero_add]
    exact htotal

/-- Averaging the almost-everywhere slice inequality over the window `(t-h, t]`. -/
private theorem ramp_inequality_of_ae {E G K : ℝ → ℝ} (hEint : Integrable E volume)
    (hGint : Integrable G volume) (hKint : Integrable K volume)
    (hae : ∀ᵐ τ : ℝ, E τ + 2 * ∫ s in Iio τ, G s ≤ ∫ s in Iio τ, K s)
    (t h : ℝ) (hh : 0 < h) :
    2 * (∫ s : ℝ, G s * affineTimeRamp t h s) + h⁻¹ * (∫ s in Ioc (t - h) t, E s)
      ≤ ∫ s : ℝ, K s * affineTimeRamp t h s := by
  have hfin := finiteMeasure_restrict_Ioc (t - h) t
  have hEres : IntegrableOn E (Ioc (t - h) t) volume := hEint.integrableOn
  have hΦG : Integrable (fun τ => ∫ s in Iio τ, G s)
      ((volume : Measure ℝ).restrict (Ioc (t - h) t)) := by
    have hbase := (integrable_indicator_Iio_prod hGint (t - h) t).integral_prod_left
    simpa only [integral_indicator measurableSet_Iio] using hbase
  have hΦK : Integrable (fun τ => ∫ s in Iio τ, K s)
      ((volume : Measure ℝ).restrict (Ioc (t - h) t)) := by
    have hbase := (integrable_indicator_Iio_prod hKint (t - h) t).integral_prod_left
    simpa only [integral_indicator measurableSet_Iio] using hbase
  have hmono : ∫ τ in Ioc (t - h) t, (E τ + 2 * ∫ s in Iio τ, G s)
      ≤ ∫ τ in Ioc (t - h) t, (∫ s in Iio τ, K s) :=
    integral_mono_ae (hEres.add (hΦG.const_mul 2)) hΦK (ae_restrict_of_ae hae)
  rw [integral_add hEres (hΦG.const_mul 2), integral_const_mul,
    integral_window_Iio hGint t h hh, integral_window_Iio hKint t h hh] at hmono
  have hrw : 2 * (∫ s : ℝ, G s * affineTimeRamp t h s) +
      h⁻¹ * (∫ s in Ioc (t - h) t, E s) =
      h⁻¹ * ((∫ s in Ioc (t - h) t, E s) +
        2 * (h * ∫ s : ℝ, G s * affineTimeRamp t h s)) := by
    field_simp
    ring
  rw [hrw]
  calc h⁻¹ * ((∫ s in Ioc (t - h) t, E s) +
        2 * (h * ∫ s : ℝ, G s * affineTimeRamp t h s))
      ≤ h⁻¹ * (h * ∫ s : ℝ, K s * affineTimeRamp t h s) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ∫ s : ℝ, K s * affineTimeRamp t h s := by
        field_simp

/-- The local energy inequality in slice form, for almost every time of the whole
line rather than of the time domain only. -/
private theorem local_energy_slice_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ} (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hφpos : ∀ z, 0 ≤ φ z) :
    ∀ᵐ τ : ℝ,
      (∫ x : Vec3, vec3EuclideanNorm (u (x, τ)) ^ 2 * φ (x, τ))
        + 2 * ∫ s in Iio τ, (∫ x : Vec3, spatialGradientSq u Du (x, s) * φ (x, s))
        ≤ ∫ s in Iio τ, (∫ x : Vec3, localEnergyRhs u p f φ (x, s)) := by
  obtain ⟨hDint, hKint, hEint⟩ := suitableWeakSolution_energy_integrable hsol hφ hφpos
  have hΩg : ∀ s : ℝ, ∫ x in Ω, spatialGradientSq u Du (x, s) * φ (x, s)
      = ∫ x : Vec3, spatialGradientSq u Du (x, s) * φ (x, s) := by
    intro s
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [test_eq_zero_of_notMem hφ (z := (x, s)) (fun hmem => hx hmem.1), mul_zero]
  have hΩe : ∀ s : ℝ, ∫ x in Ω, vec3EuclideanNorm (u (x, s)) ^ 2 * φ (x, s)
      = ∫ x : Vec3, vec3EuclideanNorm (u (x, s)) ^ 2 * φ (x, s) := by
    intro s
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [test_eq_zero_of_notMem hφ (z := (x, s)) (fun hmem => hx hmem.1), mul_zero]
  have hΩk : ∀ s : ℝ, ∫ x in Ω, localEnergyRhs u p f φ (x, s)
      = ∫ x : Vec3, localEnergyRhs u p f φ (x, s) := by
    intro s
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    exact rhs_eq_zero_of_notMem hφ (z := (x, s)) (fun hmem => hx hmem.1)
  have hland := suitableWeakSolution_localEnergyInequality_ae hsol hφ hφpos
  simp_rw [hΩg, hΩe, hΩk] at hland
  have hE0 : ∀ τ : ℝ, τ ∉ I →
      (∫ x : Vec3, vec3EuclideanNorm (u (x, τ)) ^ 2 * φ (x, τ)) = 0 := by
    intro τ hτ
    have hzero : ∀ x : Vec3, vec3EuclideanNorm (u (x, τ)) ^ 2 * φ (x, τ) = 0 := by
      intro x
      rw [test_eq_zero_of_notMem hφ (z := (x, τ)) (fun hmem => hτ hmem.2), mul_zero]
    simp only [hzero, integral_zero]
  have hG0 : ∀ s : ℝ, s ∉ I →
      (∫ x : Vec3, spatialGradientSq u Du (x, s) * φ (x, s)) = 0 := by
    intro s hs
    have hzero : ∀ x : Vec3, spatialGradientSq u Du (x, s) * φ (x, s) = 0 := by
      intro x
      rw [test_eq_zero_of_notMem hφ (z := (x, s)) (fun hmem => hs hmem.2), mul_zero]
    simp only [hzero, integral_zero]
  have hK0 : ∀ s : ℝ, s ∉ I → (∫ x : Vec3, localEnergyRhs u p f φ (x, s)) = 0 := by
    intro s hs
    have hzero : ∀ x : Vec3, localEnergyRhs u p f φ (x, s) = 0 := fun x =>
      rhs_eq_zero_of_notMem hφ (z := (x, s)) (fun hmem => hs hmem.2)
    simp only [hzero, integral_zero]
  have htotal : 2 * ∫ s : ℝ, (∫ x : Vec3, spatialGradientSq u Du (x, s) * φ (x, s))
      ≤ ∫ s : ℝ, (∫ x : Vec3, localEnergyRhs u p f φ (x, s)) := by
    have hg := suitableWeakSolution_energyInequality hsol hφ hφpos
    have hgu : ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * φ z
        = ∫ z : ParabolicPoint, spatialGradientSq u Du z * φ z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [test_eq_zero_of_notMem hφ hz, mul_zero]
    have hku : ∫ z in spaceTimeSet Ω I, localEnergyRhs u p f φ z
        = ∫ z : ParabolicPoint, localEnergyRhs u p f φ z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        rhs_eq_zero_of_notMem hφ hz
    rw [hgu, hku, integral_slice_eq hDint, integral_slice_eq hKint] at hg
    exact hg
  exact ae_extend_off_interval hsol.2.1 hsol.2.2.1 hE0 hG0 hK0 htotal hland

/-- The fixed-`h` local energy inequality of `eq:lei-h`: the affine backward ramp
`χ` of `eq:time-cutoff` weights the dissipation and the right-hand side, and the
ramp derivative contributes the window average of the velocity energy. -/
theorem local_energy_affine_ramp_source
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ} (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hφpos : ∀ z, 0 ≤ φ z) (t h : ℝ) (hh : 0 < h) :
    let χ : ℝ → ℝ := fun s => if s ≤ t-h then 1 else if s < t then (t-s)/h else 0
    2 * (∫ z : ParabolicPoint, spatialGradientSq u Du z * φ z * χ z.2) +
      h⁻¹ * (∫ s in Ioc (t-h) t, ∫ x : Vec3, vec3EuclideanNorm (u (x,s))^2 * φ (x,s)) ≤
      ∫ z : ParabolicPoint, localEnergyRhs u p f φ z * χ z.2 := by
  intro χ
  obtain ⟨hDint, hKint, hEint⟩ := suitableWeakSolution_energy_integrable hsol hφ hφpos
  have hGe : Integrable (fun s : ℝ => ∫ x : Vec3,
      vec3EuclideanNorm (u (x, s)) ^ 2 * φ (x, s)) volume := hEint.integral_prod_right
  have hGg : Integrable (fun s : ℝ => ∫ x : Vec3,
      spatialGradientSq u Du (x, s) * φ (x, s)) volume := hDint.integral_prod_right
  have hGk : Integrable (fun s : ℝ => ∫ x : Vec3,
      localEnergyRhs u p f φ (x, s)) volume := hKint.integral_prod_right
  have hmain := ramp_inequality_of_ae hGe hGg hGk
    (local_energy_slice_ae hsol hφ hφpos) t h hh
  have hG : ∫ z : ParabolicPoint, spatialGradientSq u Du z * φ z * affineTimeRamp t h z.2
      = ∫ s : ℝ, (∫ x : Vec3, spatialGradientSq u Du (x, s) * φ (x, s)) *
          affineTimeRamp t h s :=
    integral_mul_time_weight hDint (affineTimeRamp_measurable t h)
      (affineTimeRamp_abs_le_one hh)
  have hK : ∫ z : ParabolicPoint, localEnergyRhs u p f φ z * affineTimeRamp t h z.2
      = ∫ s : ℝ, (∫ x : Vec3, localEnergyRhs u p f φ (x, s)) * affineTimeRamp t h s :=
    integral_mul_time_weight hKint (affineTimeRamp_measurable t h)
      (affineTimeRamp_abs_le_one hh)
  have hχ : χ = affineTimeRamp t h := rfl
  rw [hχ, hG, hK]
  exact hmain

end CKN
end
