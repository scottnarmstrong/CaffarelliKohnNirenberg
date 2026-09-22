-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.SpatialSliceMultiplier
import Mathlib.Analysis.Convolution

/-!
# The multiplier commutes with the heat convolution

The proof of Proposition `prop:heat-morrey-hoelder` in `paper/ckn.tex` (line 2921)
records one exchange and uses it throughout:

> `ς(D)W₊` is a locally integrable function, so `W₊ * ς(D)G = (ς(D)W₊) * G`.

This file proves that exchange where it is an identity between absolutely
convergent integrals: on one spatial slice, for a source `g ∈ L¹(ℝ³)` and a
positive time `t`,

`ς(D)(W(·,t) * g) = (ς(D)W(·,t)) * g`,

with `ς(D)` the operator of `CKN/Foundation/Heat/SpatialSliceMultiplier.lean` and
`ς(D)W(·,t)` the kernel `spatialMultiplierHeatKernel` of
`CKN/Foundation/Euclidean/SpatialMultiplierKernel.lean`.  Both sides are finite:
the Gaussian `e^{-t|ξ|²}` at a fixed positive time beats the linear growth of the
symbol, which is the same estimate that makes the kernel's own defining integral
converge.

Two ingredients are proved on the way and are of independent use: the transform of
a heat convolution is the Gaussian times the transform, and the frequency integrand
of `ς(D)` applied to a heat-smoothed source is absolutely integrable.

What is **not** proved here, and why.  The paper's own placement of the multiplier,
`W₊ * (ς(D)G)`, puts `ς(D)` outside the time integral.  There it is not an
absolutely convergent frequency integral: `∫|ς(ξ)|e^{-τ|ξ|²}dξ` grows like `τ^{-2}`
as `τ ↓ 0`, and `τ^{-2}` is not integrable in `τ` at `0`.  The identity that holds
is therefore the slice-wise one, applied under the time integral, which is what the
space-time statement below records; its Fubini step consumes the local integrability
of `ς(D)W₊` in space-time, the fourth clause of `eq:heat-kernel-bounds`, and that
clause is carried here as an explicit integrability hypothesis rather than assumed.
-/

open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Euclidean CKN.Foundation.Parabolic

/-- The spatial heat convolution at time `t`: `W(·,t) * g`, taken in the space
variable only and extended by the causal value `0` to `t ≤ 0`, as `W` itself is. -/
def spatialHeatConv (t : ℝ) (g : Vec3 → ℂ) (x : Vec3) : ℂ :=
  ∫ y : Vec3, (heatKernel (x - y) t : ℂ) * g y

/-- On the causal side the heat convolution is the zero function. -/
theorem spatialHeatConv_of_nonpos {t : ℝ} (ht : t ≤ 0) (g : Vec3 → ℂ) :
    spatialHeatConv t g = fun _ => 0 := by
  funext x
  rw [spatialHeatConv]
  have hzero : ∀ y : Vec3, (heatKernel (x - y) t : ℂ) * g y = 0 := by
    intro y
    rw [heatKernel_eq_zero_of_nonpos ht]
    norm_num
  simp [hzero]

/-! ### The transform of a heat convolution -/

private theorem phase_sub (a b c : Vec3) :
    Complex.exp (-(Complex.I * ((∑ j : Fin 3, a j * c j : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * ((∑ j : Fin 3, (a - b) j * c j : ℝ) : ℂ))) *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, b j * c j : ℝ) : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  have hsum : (∑ j : Fin 3, a j * c j : ℝ) =
      (∑ j : Fin 3, (a - b) j * c j : ℝ) + (∑ j : Fin 3, b j * c j : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [Pi.sub_apply]
    ring
  rw [hsum]
  push_cast
  ring

private theorem integrable_heatKernel_complex {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : Vec3 => (heatKernel y t : ℂ)) volume :=
  (heatKernel_integrable ht).ofReal

private theorem integrable_heatConv_pair {g : Vec3 → ℂ} (hg : Integrable g volume)
    {t : ℝ} (ht : 0 < t) (ξ : Vec3) :
    Integrable (Function.uncurry fun z y : Vec3 =>
      ((heatKernel (z - y) t : ℂ) * g y) *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, z j * ξ j : ℝ) : ℂ))))
      (volume.prod volume) := by
  have hconv : Integrable (fun p : Vec3 × Vec3 =>
      (ContinuousLinearMap.mul ℂ ℂ) (g p.2) ((heatKernel (p.1 - p.2) t : ℂ)))
      (volume.prod volume) :=
    hg.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
      (integrable_heatKernel_complex ht)
  have hphase : Continuous fun p : Vec3 × Vec3 =>
      Complex.exp (-(Complex.I * ((∑ j : Fin 3, p.1 j * ξ j : ℝ) : ℂ))) := by
    apply Complex.continuous_exp.comp
    apply Continuous.neg
    apply continuous_const.mul
    exact Complex.continuous_ofReal.comp
      (continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp continuous_fst).mul continuous_const)
  refine Integrable.mono' hconv.norm ?_ ?_
  · refine (hconv.aestronglyMeasurable.mul hphase.aestronglyMeasurable).congr ?_
    filter_upwards with p
    simp only [Pi.mul_apply, Function.uncurry, ContinuousLinearMap.mul_apply']
    rw [mul_comm (g p.2) ((heatKernel (p.1 - p.2) t : ℂ))]
  · filter_upwards with p
    have hnorm : ‖Complex.exp (-(Complex.I * ((∑ j : Fin 3, p.1 j * ξ j : ℝ) : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    simp only [Function.uncurry, ContinuousLinearMap.mul_apply', norm_mul, hnorm, mul_one]
    exact le_of_eq (mul_comm _ _)

/-- The transform of a heat convolution is the Gaussian times the transform: the
convolution theorem for `W(·,t)`, in the normalization of `ext:heat-kernel`. -/
theorem spatialFourierIntegral_spatialHeatConv {g : Vec3 → ℂ}
    (hg : Integrable g volume) {t : ℝ} (ht : 0 < t) (ξ : Vec3) :
    spatialFourierIntegral (spatialHeatConv t g) ξ =
      Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) *
        spatialFourierIntegral g ξ := by
  have hstep : spatialFourierIntegral (spatialHeatConv t g) ξ =
      ∫ z : Vec3, ∫ y : Vec3, ((heatKernel (z - y) t : ℂ) * g y) *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, z j * ξ j : ℝ) : ℂ))) := by
    rw [spatialFourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [spatialHeatConv]
    rw [← integral_mul_const]
  rw [hstep, integral_integral_swap (integrable_heatConv_pair hg ht ξ)]
  have hinner : ∀ y : Vec3,
      (∫ z : Vec3, ((heatKernel (z - y) t : ℂ) * g y) *
          Complex.exp (-(Complex.I * ((∑ j : Fin 3, z j * ξ j : ℝ) : ℂ)))) =
        Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) *
          (g y * Complex.exp (-(Complex.I * ((∑ j : Fin 3, y j * ξ j : ℝ) : ℂ)))) := by
    intro y
    have hrw : ∀ z : Vec3, ((heatKernel (z - y) t : ℂ) * g y) *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, z j * ξ j : ℝ) : ℂ))) =
          ((fun u : Vec3 => (heatKernel u t : ℂ) *
            Complex.exp (-(Complex.I * ((∑ j : Fin 3, u j * ξ j : ℝ) : ℂ)))) (z - y)) *
            (g y * Complex.exp (-(Complex.I * ((∑ j : Fin 3, y j * ξ j : ℝ) : ℂ)))) := by
      intro z
      rw [phase_sub z y ξ]
      ring
    simp_rw [hrw]
    rw [integral_mul_const, integral_sub_right_eq_self
      (fun u : Vec3 => (heatKernel u t : ℂ) *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, u j * ξ j : ℝ) : ℂ)))) y]
    rw [show (∫ u : Vec3, (heatKernel u t : ℂ) *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, u j * ξ j : ℝ) : ℂ)))) =
        spatialFourierIntegral (fun u => (heatKernel u t : ℂ)) ξ from rfl,
      spatialFourierIntegral_heatKernel ht]
  simp_rw [hinner]
  rw [integral_const_mul]
  rfl

/-! ### The exchange of the multiplier with the heat convolution -/

private theorem integrable_multiplier_pair {σ : Vec3 → ℂ}
    (hcont : ContinuousOn σ ({0}ᶜ : Set Vec3)) (hhom : IsDegreeOneHomogeneous σ)
    {g : Vec3 → ℂ} (hg : Integrable g volume) {t : ℝ} (ht : 0 < t) (x : Vec3) :
    Integrable (Function.uncurry fun ξ y : Vec3 =>
      spatialMultiplierHeatIntegrand σ (x - y) t ξ * g y) (volume.prod volume) := by
  have hbase := integrable_spatialMultiplierHeatIntegrand hcont hhom x ht
  have hmaj : Integrable (fun p : Vec3 × Vec3 =>
      ‖spatialMultiplierHeatIntegrand σ x t p.1‖ * ‖g p.2‖) (volume.prod volume) :=
    hbase.norm.mul_prod hg.norm
  have hσmeas : AEStronglyMeasurable σ volume := by
    have h := hcont.aestronglyMeasurable (μ := volume)
      (MeasurableSet.compl (measurableSet_singleton (0 : Vec3)))
    rwa [restrict_compl_singleton (0 : Vec3)] at h
  have hmeas : AEStronglyMeasurable (Function.uncurry fun ξ y : Vec3 =>
      spatialMultiplierHeatIntegrand σ (x - y) t ξ * g y) (volume.prod volume) := by
    have hphase : Continuous fun p : Vec3 × Vec3 =>
        Complex.exp (Complex.I *
          ((∑ j : Fin 3, (x - p.2) j * p.1 j : ℝ) : ℂ)) := by
      apply Complex.continuous_exp.comp
      apply continuous_const.mul
      refine Complex.continuous_ofReal.comp (continuous_finsetSum _ fun j _ => ?_)
      exact ((continuous_const.sub ((continuous_apply j).comp continuous_snd)).mul
        ((continuous_apply j).comp continuous_fst))
    have hgauss : Continuous fun p : Vec3 × Vec3 =>
        Complex.exp (-((t * vec3EuclideanNorm p.1 ^ 2 : ℝ) : ℂ)) := by
      apply Complex.continuous_exp.comp
      exact (Complex.continuous_ofReal.comp
        (((continuous_vec3EuclideanNorm.comp continuous_fst).pow 2).const_mul t)).neg
    have hsig : AEStronglyMeasurable (fun p : Vec3 × Vec3 => σ p.1) (volume.prod volume) :=
      hσmeas.comp_fst
    exact ((hphase.aestronglyMeasurable.mul hsig).mul hgauss.aestronglyMeasurable).mul
      hg.aestronglyMeasurable.comp_snd
  have hphasenorm : ∀ a b : Vec3,
      ‖Complex.exp (Complex.I * ((∑ j : Fin 3, a j * b j : ℝ) : ℂ))‖ = 1 := by
    intro a b
    rw [Complex.norm_exp]
    simp
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards with p
  have hval : ‖spatialMultiplierHeatIntegrand σ (x - p.2) t p.1‖ =
      ‖spatialMultiplierHeatIntegrand σ x t p.1‖ := by
    unfold spatialMultiplierHeatIntegrand
    simp only [norm_mul, hphasenorm, one_mul]
  simp only [Function.uncurry, norm_mul, hval]
  exact le_rfl

/-- The inverse phase splits off a translation: `e^{i(a-b)·c} = e^{i a·c} e^{-i b·c}`. -/
private theorem phase_sub_inverse (a b c : Vec3) :
    Complex.exp (Complex.I * ((∑ j : Fin 3, (a - b) j * c j : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((∑ j : Fin 3, a j * c j : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, b j * c j : ℝ) : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  have hsum : (∑ j : Fin 3, (a - b) j * c j : ℝ) =
      (∑ j : Fin 3, a j * c j : ℝ) - (∑ j : Fin 3, b j * c j : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [Pi.sub_apply]
    ring
  rw [hsum]
  push_cast
  ring

/-- **The exchange of `prop:heat-morrey-hoelder`.**  On one spatial slice at a
positive time, the multiplier of a degree-one homogeneous symbol applied to the
heat convolution of an integrable source is the convolution of the same source with
the multiplier kernel `ς(D)W(·,t)`: `ς(D)(W(·,t) * g) = (ς(D)W(·,t)) * g`. -/
theorem spatialMultiplierApply_spatialHeatConv {σ : Vec3 → ℂ}
    (hcont : ContinuousOn σ ({0}ᶜ : Set Vec3)) (hhom : IsDegreeOneHomogeneous σ)
    {g : Vec3 → ℂ} (hg : Integrable g volume) {t : ℝ} (ht : 0 < t) (x : Vec3) :
    spatialMultiplierApply σ (spatialHeatConv t g) x =
      ∫ y : Vec3, spatialMultiplierHeatKernel σ (x - y) t * g y := by
  have hfreq : ∀ ξ : Vec3,
      spatialMultiplierIntegrand σ (spatialHeatConv t g) x ξ =
        ∫ y : Vec3, spatialMultiplierHeatIntegrand σ (x - y) t ξ * g y := by
    intro ξ
    have hpull : (fun y : Vec3 => spatialMultiplierHeatIntegrand σ (x - y) t ξ * g y) =
        fun y : Vec3 =>
          (Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) * σ ξ *
              Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))) *
            (g y * Complex.exp (-(Complex.I * ((∑ j : Fin 3, y j * ξ j : ℝ) : ℂ)))) := by
      funext y
      rw [spatialMultiplierHeatIntegrand, phase_sub_inverse x y ξ]
      ring
    rw [spatialMultiplierIntegrand, spatialFourierIntegral_spatialHeatConv hg ht,
      hpull, integral_const_mul]
    rw [show (∫ y : Vec3, g y *
        Complex.exp (-(Complex.I * ((∑ j : Fin 3, y j * ξ j : ℝ) : ℂ)))) =
        spatialFourierIntegral g ξ from rfl]
    ring
  have hfun : (fun y : Vec3 => spatialMultiplierHeatKernel σ (x - y) t * g y) =
      fun y : Vec3 => (2 * Real.pi : ℂ) ^ (-3 : ℤ) *
        ∫ ξ : Vec3, spatialMultiplierHeatIntegrand σ (x - y) t ξ * g y := by
    funext y
    rw [integral_mul_const, ← mul_assoc]
    congr 1
    simp [spatialMultiplierHeatKernel, ht]
  rw [spatialMultiplierApply]
  simp_rw [hfreq]
  rw [integral_integral_swap (integrable_multiplier_pair hcont hhom hg ht x), hfun,
    integral_const_mul]



/-! ### The slice-wise multiplier of a heat-smoothed source is a function -/

private theorem norm_spatialFourierIntegral_le {g : Vec3 → ℂ}
    (hg : Integrable g volume) (ξ : Vec3) :
    ‖spatialFourierIntegral g ξ‖ ≤ ∫ y : Vec3, ‖g y‖ := by
  rw [spatialFourierIntegral]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => norm_nonneg _) hg.norm ?_
  filter_upwards with y
  rw [norm_mul, Complex.norm_exp]
  simp

private theorem aestronglyMeasurable_spatialFourierIntegral {g : Vec3 → ℂ}
    (hg : Integrable g volume) :
    AEStronglyMeasurable (spatialFourierIntegral g) volume := by
  have hphase : Continuous fun p : Vec3 × Vec3 =>
      Complex.exp (-(Complex.I * ((∑ j : Fin 3, p.2 j * p.1 j : ℝ) : ℂ))) := by
    apply Complex.continuous_exp.comp
    apply Continuous.neg
    apply continuous_const.mul
    exact Complex.continuous_ofReal.comp
      (continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp continuous_snd).mul
          ((continuous_apply j).comp continuous_fst))
  have hpair : AEStronglyMeasurable (fun p : Vec3 × Vec3 =>
      g p.2 * Complex.exp (-(Complex.I * ((∑ j : Fin 3, p.2 j * p.1 j : ℝ) : ℂ))))
      (volume.prod volume) :=
    hg.aestronglyMeasurable.comp_snd.mul hphase.aestronglyMeasurable
  exact hpair.integral_prod_right'

/-- **The slice-wise multiplier of a heat-smoothed source is a continuous function.**
At a positive time, `ς(D)(W(·,t) * g)` of an integrable `g` is continuous, hence locally
integrable, hence a distribution on `ℝ³`; the frequency integral that defines it converges
absolutely and depends continuously on the point. -/
theorem continuous_spatialMultiplierApply_spatialHeatConv {σ : Vec3 → ℂ}
    (hcont : ContinuousOn σ ({0}ᶜ : Set Vec3)) (hhom : IsDegreeOneHomogeneous σ)
    {g : Vec3 → ℂ} (hg : Integrable g volume) {t : ℝ} (ht : 0 < t) :
    Continuous (spatialMultiplierApply σ (spatialHeatConv t g)) := by
  have hσmeas : AEStronglyMeasurable σ volume := by
    have h := hcont.aestronglyMeasurable (μ := volume)
      (MeasurableSet.compl (measurableSet_singleton (0 : Vec3)))
    rwa [restrict_compl_singleton (0 : Vec3)] at h
  have hbase := integrable_spatialMultiplierHeatIntegrand hcont hhom 0 ht
  have hgaussmeas : AEStronglyMeasurable
      (fun ξ : Vec3 => Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))) volume := by
    refine Continuous.aestronglyMeasurable ?_
    apply Complex.continuous_exp.comp
    exact (Complex.continuous_ofReal.comp
      ((continuous_vec3EuclideanNorm.pow 2).const_mul t)).neg
  have hphasenorm : ∀ a b : Vec3,
      ‖Complex.exp (Complex.I * ((∑ j : Fin 3, a j * b j : ℝ) : ℂ))‖ = 1 := by
    intro a b
    rw [Complex.norm_exp]
    simp
  have hrw : spatialMultiplierApply σ (spatialHeatConv t g) =
      fun x : Vec3 => (2 * Real.pi : ℂ) ^ (-3 : ℤ) *
        ∫ ξ : Vec3, Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) * σ ξ *
          (Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ)) *
            spatialFourierIntegral g ξ) := by
    funext x
    rw [spatialMultiplierApply]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    rw [spatialMultiplierIntegrand, spatialFourierIntegral_spatialHeatConv hg ht]
  rw [hrw]
  refine continuous_const.mul (continuous_of_dominated
    (bound := fun ξ : Vec3 => ‖spatialMultiplierHeatIntegrand σ 0 t ξ‖ *
      ∫ y : Vec3, ‖g y‖) ?_ ?_ (hbase.norm.mul_const _) ?_)
  · intro x
    refine AEStronglyMeasurable.mul ?_ (hgaussmeas.mul
      (aestronglyMeasurable_spatialFourierIntegral hg))
    refine Continuous.aestronglyMeasurable ?_ |>.mul hσmeas
    apply Complex.continuous_exp.comp
    apply continuous_const.mul
    exact Complex.continuous_ofReal.comp
      (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))
  · intro x
    filter_upwards with ξ
    have hbnd := norm_spatialFourierIntegral_le hg ξ
    have hkernel : ‖spatialMultiplierHeatIntegrand σ 0 t ξ‖ =
        ‖σ ξ‖ * ‖Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ := by
      unfold spatialMultiplierHeatIntegrand
      rw [norm_mul, norm_mul, hphasenorm, one_mul]
    rw [norm_mul, norm_mul, norm_mul, hphasenorm, one_mul, hkernel]
    have hstep : ‖σ ξ‖ * ‖Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ *
        ‖spatialFourierIntegral g ξ‖ ≤
        ‖σ ξ‖ * ‖Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ *
          ∫ y : Vec3, ‖g y‖ := by
      gcongr
    calc ‖σ ξ‖ * (‖Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ *
            ‖spatialFourierIntegral g ξ‖)
        = ‖σ ξ‖ * ‖Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ *
            ‖spatialFourierIntegral g ξ‖ := by ring
      _ ≤ ‖σ ξ‖ * ‖Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))‖ *
            ∫ y : Vec3, ‖g y‖ := hstep
  · filter_upwards with ξ
    refine Continuous.mul (Continuous.mul ?_ continuous_const) continuous_const
    apply Complex.continuous_exp.comp
    apply continuous_const.mul
    exact Complex.continuous_ofReal.comp
      (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const)

/-! ### The space-time form -/

/-- **The space-time exchange used by `eq:heat-potential`.**  Convolving the source `G`
with the multiplier kernel `ς(D)W₊` over `ℝ³ × ℝ` is the same as applying `ς(D)` in
space to each causal heat slice `W(·, t-s) * G(·,s)` and integrating over `s`.  This is
`W₊ * (ς(D)G) = (ς(D)W₊) * G` with the multiplier under the time integral, which is
where it is an absolutely convergent frequency integral.

The integrability hypothesis is the one the paper discharges in the sentence preceding
the identity — `ς(D)W₊` is locally integrable by the fourth clause of
`eq:heat-kernel-bounds` — and the sources of `prop:heat-morrey-hoelder` have bounded
support.  It is carried explicitly because that clause is not yet available. -/
theorem integral_multiplierHeatKernel_eq_integral_sliceMultiplier
    {σ : Vec3 → ℂ} (hcont : ContinuousOn σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) {G : Vec3 × ℝ → ℂ}
    (hGslice : ∀ᵐ s : ℝ, Integrable (fun y : Vec3 => G (y, s)) volume)
    (w : Vec3 × ℝ)
    (hint : Integrable (fun v : Vec3 × ℝ =>
      spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) * G v) volume) :
    ∫ v : Vec3 × ℝ, spatialMultiplierHeatKernel σ (w.1 - v.1) (w.2 - v.2) * G v =
      ∫ s : ℝ, spatialMultiplierApply σ
        (spatialHeatConv (w.2 - s) (fun y : Vec3 => G (y, s))) w.1 := by
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hGslice] with s hs
  by_cases hts : 0 < w.2 - s
  · exact (spatialMultiplierApply_spatialHeatConv hcont hhom hs hts w.1).symm
  · have hzero : ∀ y : Vec3,
        spatialMultiplierHeatKernel σ (w.1 - y) (w.2 - s) * G (y, s) = 0 := by
      intro y
      rw [spatialMultiplierHeatKernel_of_nonpos σ (w.1 - y) (le_of_not_gt hts)]
      ring
    rw [spatialHeatConv_of_nonpos (le_of_not_gt hts), spatialMultiplierApply_zero_fun]
    simp [hzero]

end CKN.Foundation.Heat
