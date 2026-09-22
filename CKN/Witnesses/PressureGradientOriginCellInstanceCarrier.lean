-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientOriginClauseGrowth
import CKN.Core.Step4.PressureGradientGluedOriginTransfer
import CKN.Core.Step4.PressureGradientLargeCells
import CKN.Foundation.Parabolic.BallBasics

/-!
# Finite-cell bounds on the whole origin carrier

The closed backward carrier admits a finite cover by backward cells of any
fixed positive radius, with all centres still in the closed carrier. At its
top time the cover uses relative neighbourhoods, so no future-time estimate
is needed. Summing the clipped slice inequalities bounds the whole-carrier
integral and hence every large cell of the restricted gradient.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

/-- Finitely many half-balls cover the closed spatial carrier, while the
closures of the full source balls remain strictly inside the unit ball.
The centres and radius depend only on the carrier radius. -/
theorem originCarrier_exists_finite_spatial_cover
    {R : ℝ} (hR : 0 < R) (hRone : R < 1) :
    ∃ (n : ℕ) (x : Fin n → Vec3) (ρ : ℝ), 0 < ρ ∧
      (∀ j, closure (vec3Ball (x j) ρ) ⊆ vec3Ball (0 : Vec3) 1) ∧
      closure (vec3Ball (0 : Vec3) R) ⊆ ⋃ j, vec3Ball (x j) (ρ / 2) := by
  classical
  let ρ := (1 - R) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith only [hRone]
  let K := closure (vec3Ball (0 : Vec3) R)
  have hc : IsCompact K := isCompact_closure_vec3Ball hR
  have hcover : K ⊆ ⋃ x : K, vec3Ball x.1 (ρ / 2) := by
    intro y hy
    refine mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
    simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using
      (show 0 < ρ / 2 by positivity)
  obtain ⟨S, hS⟩ := hc.elim_finite_subcover
    (fun x : K => vec3Ball x.1 (ρ / 2)) (fun _ => isOpen_vec3Ball _ _) hcover
  let x : Fin S.card → Vec3 := fun j => (S.equivFin.symm j).1.1
  refine ⟨S.card, x, ρ, hρ, ?_, ?_⟩
  · intro j y hy
    have hx : x j ∈ K := (S.equivFin.symm j).1.2
    rw [closure_vec3Ball hρ] at hy
    change x j ∈ closure (vec3Ball (0 : Vec3) R) at hx
    rw [closure_vec3Ball hR] at hx
    change vec3EuclideanNorm (y - x j) ≤ ρ at hy
    change vec3EuclideanNorm (x j - 0) ≤ R at hx
    rw [mem_vec3Ball]
    have htriangle : vec3EuclideanNorm (y - 0) ≤
        vec3EuclideanNorm (y - x j) + vec3EuclideanNorm (x j - 0) := by
      convert vec3EuclideanNorm_add_le (y - x j) (x j - 0) using 1
      congr 1
      abel
    have hsum : ρ + R < 1 := by dsimp [ρ]; linarith only [hRone]
    exact (htriangle.trans (add_le_add hy hx)).trans_lt hsum
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hS hy)
    refine mem_iUnion.mpr ⟨S.equivFin ⟨z, hz⟩, ?_⟩
    simpa only [x, Equiv.symm_apply_apply] using hyz

/-- The closed origin carrier has a finite cover by backward cells of any
positive radius, whose centres belong to that same closed carrier. -/
theorem originCarrier_exists_finite_cell_cover
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ S : Finset ParabolicPoint,
      (∀ z ∈ S, z ∈ closure (parabolicCylinder (0 : Vec3) 0 R)) ∧
      closure (parabolicCylinder (0 : Vec3) 0 R) ⊆
        ⋃ z ∈ S, parabolicCylinder z.1 z.2 δ := by
  classical
  let K := closure (parabolicCylinder (0 : Vec3) 0 R)
  have hK : K = closure (vec3Ball (0 : Vec3) R) ×ˢ Icc (-(R ^ 2)) 0 := by
    ext w
    simp only [K, closure_parabolicCylinder hR, closure_vec3Ball hR, zero_sub]
  have hc : IsCompact K := by
    rw [hK]
    exact parabolicHomeomorph.isCompact_preimage.mpr
      ((isCompact_closure_vec3Ball hR).prod isCompact_Icc)
  let U : K → Set ParabolicPoint := fun z =>
    vec3Ball z.1.1 δ ×ˢ Ioo (z.1.2 - δ ^ 2) (if z.1.2 = 0 then 1 else z.1.2)
  have ho (z : K) : IsOpen (U z) :=
    (isOpen_vec3Ball _ _).preimage continuous_fst_parabolicPoint |>.inter
      (isOpen_Ioo.preimage continuous_snd_parabolicPoint)
  have hcover : K ⊆ ⋃ z : K, U z := by
    intro w hw
    have hw' : w ∈ closure (vec3Ball (0 : Vec3) R) ×ˢ Icc (-(R ^ 2)) 0 := by
      rwa [← hK]
    let t := min 0 (w.2 + δ ^ 2 / 2)
    have ht : w.2 ≤ t := le_min hw'.2.2 (by linarith only [sq_nonneg δ])
    have ht0 : t ≤ 0 := min_le_left _ _
    have htd : t - δ ^ 2 < w.2 := by
      have hd : 0 < δ ^ 2 := sq_pos_of_pos hδ
      have ht' : t ≤ w.2 + δ ^ 2 / 2 := min_le_right _ _
      linarith only [hd, ht']
    have hz : (w.1, t) ∈ K := by
      rw [hK]
      exact ⟨hw'.1, hw'.2.1.trans ht, ht0⟩
    refine mem_iUnion.mpr ⟨⟨(w.1, t), hz⟩, ?_⟩
    change w.1 ∈ vec3Ball w.1 δ ∧
      w.2 ∈ Ioo (t - δ ^ 2) (if t = 0 then 1 else t)
    refine ⟨?_, htd, ?_⟩
    · simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using hδ
    · split_ifs with htzero
      · exact lt_of_le_of_lt hw'.2.2 (by norm_num)
      · have ht' : t = w.2 + δ ^ 2 / 2 :=
          min_eq_right (le_of_not_ge (fun hh => htzero (min_eq_left hh)))
        have hd : 0 < δ ^ 2 := sq_pos_of_pos hδ
        linarith only [ht', hd]
  obtain ⟨T, hT⟩ := hc.elim_finite_subcover U ho hcover
  refine ⟨T.image Subtype.val, ?_, ?_⟩
  · intro z hz
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hz
    exact v.2
  · intro w hw
    obtain ⟨z, hzT, hwz⟩ := mem_iUnion₂.mp (hT hw)
    refine mem_iUnion₂.mpr ⟨z.1, Finset.mem_image.mpr ⟨z, hzT, rfl⟩, hwz.1, hwz.2.1, ?_⟩
    by_cases hz0 : z.1.2 = 0
    · have hw' : w ∈ closure (vec3Ball (0 : Vec3) R) ×ˢ Icc (-(R ^ 2)) 0 := by
        rwa [← hK]
      simpa only [hz0] using hw'.2.2
    · have htop := hwz.2.2
      change w.2 < (if z.1.2 = 0 then 1 else z.1.2) at htop
      simpa only [ite_eq_right hz0] using htop.le

private theorem lintegral_finset_cover_le
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Finset ι) (C : ι → Set α) (f : α → ℝ≥0∞) :
    (∫⁻ x in ⋃ j ∈ S, C j, f x ∂μ) ≤ ∑ j ∈ S, ∫⁻ x in C j, f x ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    exact (lintegral_union_le f _ _).trans (add_le_add le_rfl ih)

/-- Summing clipped cell integrals over a finite cover bounds the whole
carrier integral; overlaps need no disjointness assumption. -/
theorem originCarrier_integral_le_finite_cell_sum
    {R δ : ℝ} (S : Finset ParabolicPoint)
    (hcover : parabolicCylinder (0 : Vec3) 0 R ⊆
      ⋃ z ∈ S, parabolicCylinder z.1 z.2 δ)
    (g : ParabolicPoint → ℝ≥0∞) :
    (∫⁻ w in parabolicCylinder (0 : Vec3) 0 R, g w) ≤
      ∑ z ∈ S, ∫⁻ w in parabolicCylinder z.1 z.2 δ ∩
        parabolicCylinder (0 : Vec3) 0 R, g w := by
  have hsub : parabolicCylinder (0 : Vec3) 0 R ⊆
      ⋃ z ∈ S, parabolicCylinder z.1 z.2 δ ∩ parabolicCylinder (0 : Vec3) 0 R := by
    intro w hw
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp (hcover hw)
    exact mem_iUnion₂.mpr ⟨z, hz, hwz, hw⟩
  exact (lintegral_mono_set hsub).trans (lintegral_finset_cover_le volume S _ g)

/-- The fixed-carrier weak gradient is controlled on the whole carrier by
the sum of the mean-subtracted slice majorants on a finite cover. -/
theorem originCarrier_integral_le_finite_gauge_sum
    {Ω : Set Vec3} {I : Set ℝ} {q R δ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR : 0 < R) (hRone : R < 1) (hδ : 0 < δ)
    (hmargin : δ ≤ 2 * ((1 - R) / 4))
    (S : Finset ParabolicPoint)
    (hcentres : ∀ z ∈ S, z ∈ closure (parabolicCylinder (0 : Vec3) 0 R))
    (hcover : parabolicCylinder (0 : Vec3) 0 R ⊆
      ⋃ z ∈ S, parabolicCylinder z.1 z.2 δ)
    {Dp : ParabolicPoint → Vec3} {i : Fin 3}
    (hDm : AEMeasurable (fun w => Dp w i)
      (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ I)))
    (hfield : ∀ᵐ s ∂volume.restrict I,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i)) :
    (∫⁻ w in parabolicCylinder (0 : Vec3) 0 R,
      ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
      ∑ z ∈ S, ∫⁻ s in Ioc (z.2 - δ ^ 2) z.2 ∩ Ioc (-(R ^ 2)) 0,
        originClauseGaugeMajorant R u Du p f z
          (show 0 < 2 * δ by positivity) s ^ (6 / 5 : ℝ) := by
  apply (originCarrier_integral_le_finite_cell_sum S hcover _).trans
  apply Finset.sum_le_sum
  intro z hz
  exact originClauseGaugeCarrierCellIntegral_le_of_sws hsol hdom hR hRone
    hDm hfield hδ hmargin (hcentres z hz)

/-- One measurable carrier gradient and a geometric finite cover satisfy
both the local clipped-cell inequalities and their whole-carrier sum. -/
theorem originCarrier_exists_gradient_and_finite_gauge_bound
    {Ω : Set Vec3} {I : Set ℝ} {q R δ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR : 0 < R) (hRone : R < 1) (hδ : 0 < δ)
    (hmargin : δ ≤ 2 * ((1 - R) / 4)) :
    ∃ S : Finset ParabolicPoint,
      (∀ z ∈ S, z ∈ closure (parabolicCylinder (0 : Vec3) 0 R)) ∧
      (closure (parabolicCylinder (0 : Vec3) 0 R) ⊆
        ⋃ z ∈ S, parabolicCylinder z.1 z.2 δ) ∧
      ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
        (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
          LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R) volume ∧
          HasWeakPartialDerivOn (vec3Ball 0 R) i
            (fun y => p (y, s)) (fun y => Dp (y, s) i)) ∧
        (∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R),
          ∀ (r : ℝ) (hr : 0 < r), r ≤ 2 * ((1 - R) / 4) → ∀ i : Fin 3,
            (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R,
              ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
              ∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R ^ 2)) 0,
                originClauseGaugeMajorant R u Du p f z
                  (show 0 < 2 * r by positivity) s ^ (6 / 5 : ℝ)) ∧
        (∀ i : Fin 3,
          (∫⁻ w in parabolicCylinder (0 : Vec3) 0 R,
            ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
            ∑ z ∈ S, ∫⁻ s in Ioc (z.2 - δ ^ 2) z.2 ∩ Ioc (-(R ^ 2)) 0,
              originClauseGaugeMajorant R u Du p f z
                (show 0 < 2 * δ by positivity) s ^ (6 / 5 : ℝ)) := by
  obtain ⟨S, hcentres, hcover⟩ := originCarrier_exists_finite_cell_cover hR hδ
  obtain ⟨Dp, hDm, hfield, hcell⟩ :=
    originClauseGauge_exists_doubled_cell_bounds_of_sws hsol hdom hR hRone
  refine ⟨S, hcentres, hcover, Dp, hDm, hfield, hcell, ?_⟩
  intro i
  exact originCarrier_integral_le_finite_gauge_sum hsol hdom hR hRone hδ hmargin
    S hcentres (subset_closure.trans hcover)
    (((measurable_pi_apply i).comp hDm).aemeasurable.mono_measure Measure.restrict_le_self)
    (hfield.mono (fun _ hs => hs i))

/-- Every large Morrey cell, at an arbitrary centre, is controlled by the
finite sum of clipped gauge integrals on the origin carrier. -/
theorem originCarrier_large_cell_le_finite_gauge_sum
    {Ω : Set Vec3} {I : Set ℝ} {q R δ κ r₀ r : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR : 0 < R) (hRone : R < 1) (hδ : 0 < δ)
    (hmargin : δ ≤ 2 * ((1 - R) / 4))
    (S : Finset ParabolicPoint)
    (hcentres : ∀ z ∈ S, z ∈ closure (parabolicCylinder (0 : Vec3) 0 R))
    (hcover : parabolicCylinder (0 : Vec3) 0 R ⊆
      ⋃ z ∈ S, parabolicCylinder z.1 z.2 δ)
    {Dp : ParabolicPoint → Vec3} {i : Fin 3}
    (hDm : AEMeasurable (fun w => Dp w i)
      (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ I)))
    (hfield : ∀ᵐ s ∂volume.restrict I,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (hκ : 6 / 5 ≤ κ) (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (z : ParabolicPoint) :
    morreyCell (6 / 5) κ
      ((parabolicCylinder 0 0 R).indicator (fun w => Dp w i)) z r ≤
      ENNReal.ofReal (r₀ ^ (5 / κ - 25 / 6)) *
        (∑ c ∈ S, ∫⁻ s in Ioc (c.2 - δ ^ 2) c.2 ∩ Ioc (-(R ^ 2)) 0,
          originClauseGaugeMajorant R u Du p f c
            (show 0 < 2 * δ by positivity) s ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by
  apply (pressure_gradient_origin_cylinder_large_cell_le hκ hr₀ hr z).trans
  exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (originCarrier_integral_le_finite_gauge_sum hsol hdom hR hRone hδ hmargin
      S hcentres hcover hDm hfield) (by norm_num))

/-- A small cell with an arbitrary centre that meets the carrier is bounded
by a doubled cell centred inside the carrier, and thus by its gauge integral. -/
theorem originCarrier_small_cell_le_recentered_gauge
    {Ω : Set Vec3} {I : Set ℝ} {q R r : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR : 0 < R) (hRone : R < 1)
    {Dp : ParabolicPoint → Vec3} {i : Fin 3}
    (hDm : AEMeasurable (fun w => Dp w i)
      (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ I)))
    (hfield : ∀ᵐ s ∂volume.restrict I,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (z : ParabolicPoint) (hr : 0 < r) (hmargin : r ≤ (1 - R) / 4)
    (hmeet : (parabolicCylinder z.1 z.2 r ∩
      parabolicCylinder (0 : Vec3) 0 R).Nonempty) :
    ∃ c ∈ parabolicCylinder (0 : Vec3) 0 R,
      (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R,
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
        ∫⁻ s in Ioc (c.2 - (2 * r) ^ 2) c.2 ∩ Ioc (-(R ^ 2)) 0,
          originClauseGaugeMajorant R u Du p f c
            (show 0 < 2 * (2 * r) by positivity) s ^ (6 / 5 : ℝ) := by
  obtain ⟨c, hc, hsub⟩ := exists_one_sided_covering_cylinder_on_carrier hmeet
  refine ⟨c, hc, ?_⟩
  have hclip : parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R ⊆
      parabolicCylinder c.1 c.2 (2 * r) ∩ parabolicCylinder (0 : Vec3) 0 R := by
    intro w hw
    exact ⟨hsub ⟨hw.1, hw.2.2.2⟩, hw.2⟩
  exact (lintegral_mono_set hclip).trans
    (originClauseGaugeCarrierCellIntegral_le_of_sws hsol hdom hR hRone hDm hfield
      (by positivity : 0 < 2 * r) (by linarith only [hmargin]) (subset_closure hc))

/-- The pressure contribution to a finite covering sum has the exact
growth coefficient supplied by the fixed-carrier pressure mass estimate.
This statement concerns only the pressure contribution, not the full majorant. -/
theorem originCarrier_pressure_cover_sum_le
    {Ω : Set Vec3} {I : Set ℝ} {q R κ δ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (Kp : ℝ≥0∞) (hKp : Kp < ⊤)
    (hpressure : ∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R),
      ∀ r : ℝ, 0 < r → r ≤ (1 - R) / 4 →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R ^ 2)) 0,
          ∫⁻ y in vec3Ball z.1 (2 * r),
            ‖p (y, s) - average (volume.restrict (vec3Ball (0 : Vec3) R))
              (fun v => p (v, s))‖ₑ ^ (3 / 2 : ℝ)) ≤
          Kp * ENNReal.ofReal (r ^ (13 / 2 - 15 / (2 * κ))))
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR : 0 < R) (hRone : R < 1) (hδ : 0 < δ) (hmargin : δ ≤ (1 - R) / 4)
    (S : Finset ParabolicPoint)
    (hcentres : ∀ z ∈ S, z ∈ closure (parabolicCylinder (0 : Vec3) 0 R)) :
    (∑ z ∈ S, ∫⁻ s in Ioc (z.2 - δ ^ 2) z.2 ∩ Ioc (-(R ^ 2)) 0,
      (ENNReal.ofReal ((2 * δ) ^ (-1 / 2 : ℝ)) *
        eLpNorm (fun y => p (y, s) -
          average (volume.restrict (vec3Ball (0 : Vec3) R)) (fun v => p (v, s)))
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (vec3Ball z.1 (2 * δ)))) ^ (6 / 5 : ℝ)) ≤
      (S.card : ℝ≥0∞) *
        ((ENNReal.ofReal ((2 : ℝ) ^ (-3 / 5 : ℝ)) * Kp ^ (4 / 5 : ℝ)) *
          ENNReal.ofReal (δ ^ (5 * (1 - (6 / 5 : ℝ) / κ)))) := by
  have hg := (originClauseGauge_pressure_growth_of_sws Kp hKp hpressure
    hsol hdom hR hRone).2
  calc
    _ ≤ ∑ _z ∈ S,
        (ENNReal.ofReal ((2 : ℝ) ^ (-3 / 5 : ℝ)) * Kp ^ (4 / 5 : ℝ)) *
          ENNReal.ofReal (δ ^ (5 * (1 - (6 / 5 : ℝ) / κ))) :=
      Finset.sum_le_sum (fun z hz => hg z (hcentres z hz) δ hδ hmargin)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end CKN.Core.Step4
