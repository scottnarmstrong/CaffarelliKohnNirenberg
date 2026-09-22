-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step3.GradientSlotDuhamel
import CKN.Core.Step4.PressureGradientOriginCellInstanceAssembly
import CKN.Core.Step4.PressureGradientOriginCellInstanceSlice
import CKN.Core.Step4.PressureGradientGluedSlice
import CKN.Core.Step4.SliceSelectedGradientSymmetricBox
import CKN.Core.Step4.WeakGradientGluingTFixedPairing
import CKN.Core.Endgame.TheoremACarrierTime
import CKN.Foundation.Parabolic.BallBasics
import CKN.Foundation.Measure.SliceGradientSelection
import CKN.Foundation.Sobolev.WeakGradientGluingTMeasurable
import CKN.Statements.SpaceTimeSet
import CKN.Setting.ScalingInvariance
import Mathlib.Topology.Metrizable.Basic

/-! # Producing the localized Duhamel pressure gradient

The pressure of a suitable weak solution is locally integrable in space-time.
Fubini therefore gives locally integrable pressure slices on every compact
local box.  This is the starting point for selecting its spatial weak gradient.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Core.Step3
open CKN.Core.HeatPotential
open CKN.Core.Step4


private theorem exists_strict_backward_patch
    {Ω : Set Vec3} {I : Set ℝ} (hI : IsOpen I)
    {V : Set Vec3} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {x : Vec3} (hx : x ∈ V) {s : ℝ} (hs : s ∈ I) :
    ∃ c : Vec3, ∃ t₀ r : ℝ, 0 < r ∧
      vec3Ball c (r / 2) ⊆ V ∧
      closure (parabolicCylinder c t₀ r) ⊆ CKN.spaceTimeSet Ω I ∧
      (x, s) ∈ vec3Ball c (r / 2) ×ˢ Ioo (t₀ - r ^ 2) t₀ := by
  classical
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hx
  have hballV : vec3Ball x δ ⊆ V := by
    intro y hy
    apply hδV
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (norm_le_vec3EuclideanNorm (y - x)) hy
  have hxball : x ∈ vec3Ball x δ := by
    rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
    exact hδ
  obtain ⟨c, tQ, rQ, hc, hrQ, hxb, hsmall, hclose, htime⟩ :=
    exists_small_cylinder_of_mem hI
      (dense_univ : Dense (Set.univ : Set Vec3)) hxball hs
  let r : ℝ := rQ
  let t : ℝ := tQ
  have hr : 0 < r := hrQ
  have hballspace : closure (vec3Ball c r) ⊆ vec3Ball x δ := by
    rw [closure_vec3Ball hr]
    intro y hy
    have hz : (y, t) ∈ closure (parabolicCylinder c t r) := by
      rw [closure_parabolicCylinder hr]
      exact ⟨hy, ⟨by dsimp [t]; nlinarith only [hr], le_rfl⟩⟩
    have hh := hclose hz
    exact hh.1
  have hsmallV : vec3Ball c (r / 2) ⊆ V := by simpa [r] using hsmall.trans hballV
  have hcloseΩ : closure (parabolicCylinder c t r) ⊆ CKN.spaceTimeSet Ω I := by
    intro z hz
    rcases hclose hz with ⟨hzx, hzt⟩
    exact ⟨hVΩ (hballV hzx), hzt⟩
  have htI : t ∈ I := by
    have hcyl : (c, t) ∈ closure (parabolicCylinder c t r) := by
      rw [closure_parabolicCylinder hr]
      refine ⟨?_, ?_⟩
      · simpa [vec3EuclideanNorm_zero] using le_of_lt hr
      · exact ⟨by nlinarith only [hr], le_rfl⟩
    exact (hcloseΩ hcyl).2
  rcases lt_or_eq_of_le htime.2 with hst | hst
  · refine ⟨c, t, r, hr, hsmallV, hcloseΩ, ?_⟩
    simpa [r, t] using ⟨hxb, ⟨htime.1, hst⟩⟩
  · subst s
    obtain ⟨ε₀, hε₀, hε₀I⟩ := Metric.isOpen_iff.mp hI t htI
    let ε := min (ε₀ / 2) (r ^ 2 / 2)
    have hε : 0 < ε := lt_min (by linarith only [hε₀]) (by positivity)
    have hεsmall : ε < r ^ 2 := (min_le_right _ _).trans_lt (by nlinarith only [hr])
    have hεtime : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith only [hε₀])
    let T := t + ε
    have hcloseT : closure (parabolicCylinder c T r) ⊆ CKN.spaceTimeSet Ω I := by
      rw [closure_parabolicCylinder hr]
      intro z hz
      rcases hz with ⟨hzx, hztlo, hzthi⟩
      refine ⟨?_, ?_⟩
      · have hzx' : z.1 ∈ closure (vec3Ball c r) := by
          rw [closure_vec3Ball hr]
          exact hzx
        exact hVΩ (hballV (hballspace hzx'))
      · by_cases hle : z.2 ≤ t
        · have hzold : (c, z.2) ∈ closure (parabolicCylinder c t r) := by
            rw [closure_parabolicCylinder hr]
            refine ⟨by simpa [vec3EuclideanNorm_zero] using le_of_lt hr, ?_, hle⟩
            dsimp [T] at hztlo
            linarith only [hztlo, hε]
          exact (hclose hzold).2
        · apply hε₀I
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          have hzthi' := hzthi
          dsimp [T] at hzthi'
          have hupper : z.2 - t < ε₀ := by
            linarith only [hzthi', hεtime]
          have hlower : -(ε₀) < z.2 - t := by
            nlinarith only [hle, hε₀]
          exact ⟨hlower, hupper⟩
    refine ⟨c, T, r, hr, hsmallV, hcloseT, ?_⟩
    refine ⟨hxb, ?_⟩
    constructor
    · dsimp [T]
      linarith only [hεsmall, htime.1]
    · dsimp [T]
      dsimp [t]
      exact lt_add_of_pos_right _ hε

private theorem translated_spatial_ball_measure_preserving
    (x : Vec3) {r : ℝ} :
    MeasurePreserving (fun y : Vec3 => -x + y)
      (volume.restrict (vec3Ball x r)) (volume.restrict (vec3Ball 0 r)) := by
  have hpre : (fun y : Vec3 => -x + y) ⁻¹' vec3Ball 0 r = vec3Ball x r := by
    ext y
    simp [mem_preimage, mem_vec3Ball, neg_add_eq_sub]
  have hm := (measurePreserving_add_left (volume : Measure Vec3) (-x)).restrict_preimage
    (isOpen_vec3Ball (0 : Vec3) r).measurableSet
  rwa [hpre] at hm

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step3

/-- Pressure is locally integrable on almost every spatial slice of any
compact local box. -/
theorem pressure_locallyIntegrableOn_slice_of_localBox
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B : Set Vec3} (hbox : localBox Ω I B J) :
    ∀ᵐ t ∂(volume.restrict J),
      LocallyIntegrableOn (fun x => p (x, t)) B volume := by
  have hp : IntegrableOn p (B ×ˢ J) volume :=
    pressure_integrable_on_of_suitable_local_box hsol hbox subset_rfl
  have hpProd : Integrable p
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hp
  filter_upwards [hpProd.prod_left_ae] with t ht
  have htOn : IntegrableOn (fun x => p (x, t)) B volume := ⟨ht.1, ht.2⟩
  exact htOn.locallyIntegrableOn

/-- Small-cylinder weak gradients glue to a slice weak gradient on any open
spatial carrier. -/
theorem ae_exists_pressure_slice_weakGradient_of_small_cylinders
    {Ω : Set Vec3} {I T : Set ℝ} (hI : IsOpen I)
    (hTI : T ⊆ I) (hTmeas : MeasurableSet T)
    {B : Set Vec3} (hB : IsOpen B) (hBΩ : B ⊆ Ω) (k : Fin 3)
    {p : ParabolicPoint → ℝ}
    (hp : ∀ᵐ t ∂(volume.restrict T),
      LocallyIntegrableOn (fun x => p (x, t)) B volume)
    (hslice : ∀ (c : Vec3) (t₀ ρ : ℝ), 0 < ρ →
      closure (parabolicCylinder c t₀ ρ) ⊆ CKN.spaceTimeSet Ω I →
      ∀ᵐ s ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)),
        ∃ g : Vec3 → ℝ,
          LocallyIntegrableOn g (vec3Ball c (ρ / 2)) volume ∧
          HasWeakPartialDerivOn (vec3Ball c (ρ / 2)) k (fun x => p (x, s)) g) :
    ∀ᵐ t ∂(volume.restrict T),
      ∃ G : Vec3 → ℝ,
        LocallyIntegrableOn G B volume ∧
        HasWeakPartialDerivOn B k (fun x => p (x, t)) G := by
  classical
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense Vec3
  have hS : Countable ↥S := hScount.to_subtype
  have hfam : ∀ a : ↥S × ℚ × ℚ, ∀ᵐ t ∂(volume.restrict T),
      0 < ((a.2.2 : ℚ) : ℝ) →
      closure (parabolicCylinder (a.1 : Vec3) ((a.2.1 : ℚ) : ℝ)
        ((a.2.2 : ℚ) : ℝ)) ⊆ CKN.spaceTimeSet Ω I →
      t ∈ Ioc (((a.2.1 : ℚ) : ℝ) - ((a.2.2 : ℚ) : ℝ) ^ 2)
        ((a.2.1 : ℚ) : ℝ) →
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g
          (vec3Ball (a.1 : Vec3) (((a.2.2 : ℚ) : ℝ) / 2)) volume ∧
        HasWeakPartialDerivOn
          (vec3Ball (a.1 : Vec3) (((a.2.2 : ℚ) : ℝ) / 2))
          k (fun x => p (x, t)) g := by
    intro a
    by_cases hρ : 0 < ((a.2.2 : ℚ) : ℝ)
    · by_cases hsub : closure (parabolicCylinder (a.1 : Vec3)
          ((a.2.1 : ℚ) : ℝ) ((a.2.2 : ℚ) : ℝ)) ⊆ CKN.spaceTimeSet Ω I
      · have h := hslice (a.1 : Vec3) ((a.2.1 : ℚ) : ℝ)
          ((a.2.2 : ℚ) : ℝ) hρ hsub
        have h2 := ae_imp_of_ae_restrict h
        refine ae_restrict_of_ae h2 |>.mono ?_
        intro t ht _ _ hmem
        exact ht hmem
      · exact Filter.Eventually.of_forall fun _ _ h => absurd h hsub
    · exact Filter.Eventually.of_forall fun _ h => absurd h hρ
  have hall : ∀ᵐ t ∂(volume.restrict T), ∀ a : ↥S × ℚ × ℚ,
      0 < ((a.2.2 : ℚ) : ℝ) →
      closure (parabolicCylinder (a.1 : Vec3) ((a.2.1 : ℚ) : ℝ)
        ((a.2.2 : ℚ) : ℝ)) ⊆ CKN.spaceTimeSet Ω I →
      t ∈ Ioc (((a.2.1 : ℚ) : ℝ) - ((a.2.2 : ℚ) : ℝ) ^ 2)
        ((a.2.1 : ℚ) : ℝ) →
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g
          (vec3Ball (a.1 : Vec3) (((a.2.2 : ℚ) : ℝ) / 2)) volume ∧
        HasWeakPartialDerivOn
          (vec3Ball (a.1 : Vec3) (((a.2.2 : ℚ) : ℝ) / 2))
          k (fun x => p (x, t)) g := ae_all_iff.mpr hfam
  filter_upwards [hp, hall,
    ae_restrict_of_forall_mem (μ := (volume : Measure ℝ)) hTmeas hTI]
    with t htp htall htI
  refine exists_weakPartialDerivOn_of_local hB htp ?_
  intro x hx
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hB x hx
  have hball : vec3Ball x ε ⊆ B := by
    intro y hy
    have hnorm : ‖y - x‖ < ε := (norm_le_vec3EuclideanNorm (y - x)).trans_lt hy
    exact hεB hnorm
  have hxball : x ∈ vec3Ball x ε := by
    rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
    exact hε
  obtain ⟨c, t₀, ρ, hcS, hρ, hxmem, hsub, hclos, hmem⟩ :=
    exists_small_cylinder_of_mem hI hSdense hxball htI
  refine ⟨vec3Ball c (ρ / 2), isOpen_vec3Ball _ _, hxmem,
    hsub.trans hball, ?_⟩
  exact htall (⟨c, hcS⟩, t₀, ρ) hρ
    (hclos.trans (Set.prod_mono (hball.trans hBΩ) (Subset.rfl))) hmem

/-- A suitable weak solution supplies a slice-wise weak pressure gradient on
every localizing spatial box, with no gradient field assumed. -/
theorem pressure_slice_weakGradient_ae_of_suitable_localBox
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B : Set Vec3} (hbox : localBox Ω I B J) :
    ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g B volume ∧
        HasWeakPartialDerivOn B i (fun x => p (x, t)) g := by
  have hp := pressure_locallyIntegrableOn_slice_of_localBox hsol hbox
  have hJmeas : MeasurableSet J := hbox.2.2.2.1.measurableSet
  have hJI : J ⊆ I := subset_trans subset_closure hbox.2.2.2.2.2
  have hslice (i : Fin 3) (c : Vec3) (t₀ ρ : ℝ) (hρ : 0 < ρ)
      (hsub : closure (parabolicCylinder c t₀ ρ) ⊆ CKN.spaceTimeSet Ω I) :
      ∀ᵐ s ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)),
        ∃ g : Vec3 → ℝ,
          LocallyIntegrableOn g (vec3Ball c (ρ / 2)) volume ∧
          HasWeakPartialDerivOn (vec3Ball c (ρ / 2)) i
            (fun x => p (x, s)) g := by
    have hball := origin_local_slice_gradient_ae_of_sws
      (Ω := Ω) (I := I) (q := q) (u := u) (Du := Du) (p := p) (f := f)
      (z := (c, t₀)) (ρ := ρ) hsol hρ hsub
    have heq : euclideanBall c (ρ / 2) = vec3Ball c (ρ / 2) :=
      euclideanBall_eq_vec3Ball (by positivity : 0 < ρ / 2)
    filter_upwards [hball] with s hs
    obtain ⟨D, hloc, _hmem, hweak⟩ := hs
    exact ⟨fun x => D x i, by simpa only [heq] using hloc i,
      by simpa only [heq] using hweak i⟩
  have hweak (i : Fin 3) :=
    ae_exists_pressure_slice_weakGradient_of_small_cylinders hsol.2.1
      hJI hJmeas hbox.1 (subset_closure.trans hbox.2.2.1) i hp (hslice i)
  have hweakall : ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g B volume ∧
        HasWeakPartialDerivOn B i (fun x => p (x, t)) g := ae_all_iff.mpr hweak
  exact hweakall

/-- Suitability selects one measurable representative of the pressure slice
derivative on a neighbourhood of the spatial factor of a local box. -/
theorem exists_measurable_pressure_slice_gradient_on_neighborhood
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B : Set Vec3} (hbox : localBox Ω I B J) :
    ∃ V : Set Vec3, IsOpen V ∧ closure B ⊆ V ∧ V ⊆ Ω ∧
      ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
        (∀ᵐ t ∂(volume.restrict I),
          LocallyIntegrableOn (fun x => p (x, t)) V volume) ∧
        ∀ᵐ t ∂(volume.restrict I), ∀ i : Fin 3,
          LocallyIntegrableOn (fun x => Dp (x, t) i) V volume ∧
          HasWeakPartialDerivOn V i (fun x => p (x, t))
            (fun x => Dp (x, t) i) := by
  obtain ⟨V, δ, hδ, hVopen, hBV, hVcpt, hVΩ, _hballs⟩ :=
    CKN.exists_open_between_of_isCompact hbox.2.1 hsol.1 hbox.2.2.1
  obtain ⟨W, δ', hδ', hWopen, hVW, hWcpt, hWΩ, _hballs'⟩ :=
    CKN.exists_open_between_of_isCompact hVcpt hsol.1 hVΩ
  obtain ⟨T, _hTmono, hTord, hTcpt, hTI, hTunion, _hTcover⟩ :=
    OriginInstance.exists_compact_ordConnected_exhaustion hsol.2.1 hsol.2.2.1
  have hboxW (n : ℕ) : localBox Ω I W (T n) := by
    refine ⟨hWopen, hWcpt, hWΩ, hTord n, ?_, ?_⟩
    · rw [(hTcpt n).isClosed.closure_eq]
      exact hTcpt n
    · rw [(hTcpt n).isClosed.closure_eq]
      exact hTI n
  have hslice : ∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict I), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g W volume ∧
      HasWeakPartialDerivOn W i (fun x => p (x, t)) g := by
    intro i
    rw [← hTunion, ae_restrict_iUnion_iff]
    intro n
    have hs := pressure_slice_weakGradient_ae_of_suitable_localBox hsol (hboxW n)
    filter_upwards [hs] with t ht
    exact ht i
  have hJmeas : ∀ n, MeasurableSet (T n) := fun n => (hTcpt n).isClosed.measurableSet
  have hpV : ∀ᵐ t ∂(volume.restrict I),
      LocallyIntegrableOn (fun x => p (x, t)) W volume := by
    rw [← hTunion, ae_restrict_iUnion_iff]
    intro n
    exact pressure_locallyIntegrableOn_slice_of_localBox hsol (hboxW n)
  have hpV' : ∀ᵐ t ∂(volume.restrict I),
      LocallyIntegrableOn (fun x => p (x, t)) V volume := by
    filter_upwards [hpV] with t ht
    exact ht.mono_set (subset_closure.trans hVW)
  obtain ⟨Dp, hmeas, hweak⟩ := exists_measurable_weakGradient_on_time_union
    hWopen hVopen hVcpt hVW hJmeas hTunion
    (fun n => pressure_integrable_on_of_suitable_local_box hsol (hboxW n) subset_rfl) hslice
  exact ⟨V, hVopen, hBV, subset_closure.trans hVΩ, Dp, hmeas, hpV',
    hweak.mono (fun _ hs i => ⟨(hs i).1, (hs i).2.1⟩)⟩

/-- A slice gradient selected on a neighbourhood inherits the translated
quantitative cell estimate on every admissible backward time window. -/
private theorem translated_solution_cell
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x : Vec3} {t₀ r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder x t₀ r) ⊆ CKN.spaceTimeSet Ω I) :
    IsSuitableWeakSolutionIntegrable (rescaledSpace 1 x Ω) I q
      (rescaleVelocity 1 (x, 0) u) (rescaleGradient 1 (x, 0) Du)
      (rescalePressure 1 (x, 0) p) (rescaleForce 1 (x, 0) f) ∧
    closure (parabolicCylinder 0 t₀ r) ⊆
      CKN.spaceTimeSet (rescaledSpace 1 x Ω) I := by
  have ht : rescaledTime 1 0 I = I := by
    ext s
    simp [rescaledTime, scalingTime]
  have hshift := isSuitableWeakSolutionIntegrable_rescale hsol (x, 0)
    (by norm_num : (0 : ℝ) < 1)
  rw [ht] at hshift
  refine ⟨hshift, ?_⟩
  rw [closure_parabolicCylinder hr]
  intro z hz
  have hzorig : (x + z.1, z.2) ∈ closure (parabolicCylinder x t₀ r) := by
    rw [closure_parabolicCylinder hr]
    refine ⟨?_, hz.2⟩
    simpa [add_sub_cancel_left] using hz.1
  have hout := hsub hzorig
  rcases hout with ⟨houtΩ, houtI⟩
  change scalingSpace 1 x z.1 ∈ Ω ∧ z.2 ∈ I
  exact ⟨by simpa [scalingSpace] using houtΩ, houtI⟩

private theorem translated_fixed_gradient_bound_of_origin_slice
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {Dp : ParabolicPoint → Vec3} {x : Vec3} {t₀ r s : ℝ}
    (hr : 0 < r) {V : Set Vec3}
    (hball : vec3Ball x (r / 2) ⊆ V)
    (hp : MemLp (fun y => rescalePressure 1 (x, 0) p (y, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 r)))
    (hfield : ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) V volume ∧
      HasWeakPartialDerivOn V i (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (hs : ∃ D : Vec3 → Vec3,
      (∀ k : Fin 3, LocallyIntegrableOn (fun y => D y k)
        (euclideanBall 0 (r / 2)) volume) ∧
      MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall 0 (r / 2))) ∧
      (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall 0 (r / 2)) k
        (fun y => rescalePressure 1 (x, 0) p (y, s)) (fun y => D y k)) ∧
      (∀ k : Fin 3, eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall 0 (r / 2))) ≤
          originSliceGradientMajorant
            (rescaleVelocity 1 (x, 0) u) (rescaleGradient 1 (x, 0) Du)
            (rescalePressure 1 (x, 0) p) (rescaleForce 1 (x, 0) f)
            ((0 : Vec3), t₀) hr s)) :
    ∀ i : Fin 3,
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x (r / 2))) ≤
          CKN.Core.Endgame.theoremATranslatedSliceMajorant u Du p f x hr s := by
  obtain ⟨D, _hDloc, hDmem, hDweak, hDbound⟩ := hs
  have hhalf : euclideanBall (0 : Vec3) (r / 2) = vec3Ball 0 (r / 2) :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by linarith only [hr])
  rw [hhalf] at hDmem hDweak hDbound
  have houter : vec3Ball 0 (r / 2) ⊆ vec3Ball 0 r := by
    intro y hy
    rw [mem_vec3Ball] at hy ⊢
    exact hy.trans_le (by linarith only [hr])
  have hp0 : AEStronglyMeasurable
      (fun y => rescalePressure 1 (x, 0) p (y, s))
      (volume.restrict (vec3Ball 0 (r / 2))) :=
    hp.aestronglyMeasurable.mono_measure (Measure.restrict_mono houter le_rfl)
  have hm := translated_spatial_ball_measure_preserving x (r := r / 2)
  let _ : IsFiniteMeasure (volume.restrict (vec3Ball x (r / 2))) :=
    isFiniteMeasure_restrict.mpr
      CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top.ne
  intro i
  let g : Vec3 → ℝ := fun y => D (-x + y) i
  have hgm : MemLp g (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball x (r / 2))) :=
    (hDmem.eval i).comp_measurePreserving hm
  have hgloc : LocallyIntegrableOn g (vec3Ball x (r / 2)) volume :=
    IntegrableOn.locallyIntegrableOn (hgm.integrable (by norm_num))
  have himage : vec3Ball 0 (r / 2) =
      scalingSpace 1 (-x) '' vec3Ball x (r / 2) := by
    ext y
    constructor
    · intro hy
      refine ⟨x + y, ?_, ?_⟩
      · simpa only [mem_vec3Ball, add_sub_cancel_left, sub_zero] using hy
      · simp only [scalingSpace, one_smul, neg_add_cancel_left]
    · rintro ⟨y, hy, rfl⟩
      simpa only [scalingSpace, one_smul, mem_vec3Ball, sub_zero,
        neg_add_eq_sub] using hy
  have hw := hasWeakPartialDerivOn_scaling 1
    (by norm_num : (0 : ℝ) < 1) (-x)
    (isOpen_vec3Ball (0 : Vec3) (r / 2)).measurableSet i himage
    (hDweak i) hp0 (hDmem.eval i).aestronglyMeasurable
  have hweakBack : HasWeakPartialDerivOn (vec3Ball x (r / 2)) i
      (fun y => p (y, s)) g := by
    simpa [rescalePressure, scalingSpace, parabolicTranslate, parabolicScale, g] using hw
  have hcomp := eLpNorm_comp_measurePreserving
    (p := ENNReal.ofReal (6 / 5 : ℝ)) (hDmem.eval i).aestronglyMeasurable hm
  have hMaj : originSliceGradientMajorant
      (rescaleVelocity 1 (x, 0) u) (rescaleGradient 1 (x, 0) Du)
      (rescalePressure 1 (x, 0) p) (rescaleForce 1 (x, 0) f)
      ((0 : Vec3), t₀) hr s =
        CKN.Core.Endgame.theoremATranslatedSliceMajorant u Du p f x hr s := rfl
  have htranslated : eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball x (r / 2))) ≤
        CKN.Core.Endgame.theoremATranslatedSliceMajorant u Du p f x hr s := by
    have hdb : eLpNorm (fun y => D y i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball 0 (r / 2))) ≤
          CKN.Core.Endgame.theoremATranslatedSliceMajorant u Du p f x hr s := by
      simpa only [hMaj] using hDbound i
    change eLpNorm ((fun y => D y i) ∘ (fun y => -x + y))
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x (r / 2))) ≤ _
    exact hcomp.trans_le hdb
  exact eLpNorm_le_of_hasWeakPartialDerivOn (isOpen_vec3Ball x (r / 2)) hball
    (hfield i).1 hgloc (hfield i).2 hweakBack htranslated

theorem pressure_gradient_translated_slice_bound_on_window
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {V : Set Vec3} {Dp : ParabolicPoint → Vec3}
    {x : Vec3} {t₀ r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder x t₀ r) ⊆ CKN.spaceTimeSet Ω I)
    (hball : vec3Ball x (r / 2) ⊆ V)
    (hfield : ∀ᵐ s ∂(volume.restrict I), ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) V volume ∧
      HasWeakPartialDerivOn V i (fun y => p (y, s)) (fun y => Dp (y, s) i)) :
    ∀ᵐ s ∂(volume.restrict (Ioo (t₀ - r ^ 2) t₀)), ∀ i : Fin 3,
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x (r / 2))) ≤
        CKN.Core.Endgame.theoremATranslatedSliceMajorant u Du p f x hr s := by
  obtain ⟨hshift, hsub0⟩ := translated_solution_cell
    (Ω := Ω) (I := I) (q := q) (u := u) (Du := Du) (p := p) (f := f)
    (x := x) (t₀ := t₀) (r := r) hsol hr hsub
  have hslice := origin_local_slice_gradient_bound_ae_of_sws
    (Ω := rescaledSpace 1 x Ω) (I := I) (q := q)
    (u := rescaleVelocity 1 (x, 0) u) (Du := rescaleGradient 1 (x, 0) Du)
    (p := rescalePressure 1 (x, 0) p) (f := rescaleForce 1 (x, 0) f)
    (z := (0, t₀)) hshift hr hsub0
  have hp := CKN.sws_pressure_memLp_slice_ae
    (Ω := rescaledSpace 1 x Ω) (I := I) (q := q)
    (u := rescaleVelocity 1 (x, 0) u) (Du := rescaleGradient 1 (x, 0) Du)
    (p := rescalePressure 1 (x, 0) p) (f := rescaleForce 1 (x, 0) f)
    (z := (0, t₀)) hshift hr hsub0
  have htime : Ioc (t₀ - r ^ 2) t₀ ⊆ I := by
    intro s hs
    have hz : (x, s) ∈ parabolicCylinder x t₀ r := ⟨by
      rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
      exact hr, hs⟩
    exact (hsub (subset_closure hz)).2
  filter_upwards [
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hslice,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hp,
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioc_self.trans htime) hfield]
      with s hs hsP hfV
  exact translated_fixed_gradient_bound_of_origin_slice hr hball hsP hfV hs

private theorem lintegral_lt_top_of_toReal_integrable
    {T : Set ℝ} {K : ℝ → ℝ≥0∞}
    (hfinite : ∀ᵐ s ∂(volume.restrict T), K s ≠ ∞)
    (hInt : Integrable (fun s => (K s).toReal) (volume.restrict T)) :
    (∫⁻ s, K s ∂(volume.restrict T)) < ∞ := by
  have hEq : (fun s => K s) =ᵐ[volume.restrict T]
      (fun s => ENNReal.ofReal ((K s).toReal)) := by
    filter_upwards [hfinite] with s hs
    exact (ENNReal.ofReal_toReal hs).symm
  rw [lintegral_congr_ae hEq, ← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
  exact ENNReal.ofReal_lt_top

private theorem pressure_gradient_integrable_on_backward_patch
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {V : Set Vec3} {Dp : ParabolicPoint → Vec3}
    (hDpMeas : Measurable Dp)
    (hfield : ∀ᵐ s ∂(volume.restrict I), ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) V volume ∧
      HasWeakPartialDerivOn V i (fun y => p (y, s)) (fun y => Dp (y, s) i))
    {c : Vec3} {t₀ r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder c t₀ r) ⊆ CKN.spaceTimeSet Ω I)
    (hball : vec3Ball c (r / 2) ⊆ V) :
    ∀ i : Fin 3,
      IntegrableOn (fun z => Dp z i)
        (vec3Ball c (r / 2) ×ˢ Ioo (t₀ - r ^ 2) t₀) volume := by
  let T : Set ℝ := Ioo (t₀ - r ^ 2) t₀
  have hsub' := hsub
  rw [closure_parabolicCylinder hr] at hsub'
  have ht₀ : t₀ ∈ Icc (t₀ - r ^ 2) t₀ := by
    refine ⟨?_, le_rfl⟩
    have hsq : 0 ≤ r ^ 2 := sq_nonneg r
    linarith only [hsq]
  have hspace : closure (vec3Ball c r) ⊆ Ω := by
    rw [closure_vec3Ball hr]
    intro y hy
    have hz : (y, t₀) ∈
        {w : Vec3 | vec3EuclideanNorm (w - c) ≤ r} ×ˢ Icc (t₀ - r ^ 2) t₀ :=
      ⟨hy, ht₀⟩
    exact (hsub' hz).1
  have hcball : c ∈ {y : Vec3 | vec3EuclideanNorm (y - c) ≤ r} := by
    change vec3EuclideanNorm (c - c) ≤ r
    rw [sub_self, vec3EuclideanNorm_zero]
    exact hr.le
  have htime : Icc (t₀ - r ^ 2) t₀ ⊆ I := by
    intro s hs
    have hz : (c, s) ∈
        {y : Vec3 | vec3EuclideanNorm (y - c) ≤ r} ×ˢ Icc (t₀ - r ^ 2) t₀ :=
      ⟨hcball, hs⟩
    exact (hsub' hz).2
  have hM := CKN.Core.Endgame.theoremA_translated_majorant_time hsol hr hspace
  let M : ℝ → ℝ≥0∞ :=
    CKN.Core.Endgame.theoremATranslatedSliceMajorant u Du p f c hr
  have hMfinite : ∀ᵐ s ∂(volume.restrict (Icc (t₀ - r ^ 2) t₀)), M s ≠ ∞ :=
    ae_restrict_of_ae_restrict_of_subset htime hM.1
  have hIccCompact : IsCompact (closure (Icc (t₀ - r ^ 2) t₀)) := by
    simpa only [isClosed_Icc.closure_eq] using isCompact_Icc
  have hMint := hM.2 (Icc (t₀ - r ^ 2) t₀) hIccCompact
    (by simpa only [isClosed_Icc.closure_eq] using htime)
  have hKclosed :
      (∫⁻ s, M s ∂(volume.restrict (Icc (t₀ - r ^ 2) t₀))) < ∞ :=
    lintegral_lt_top_of_toReal_integrable hMfinite hMint
  have hK : (∫⁻ s, M s ∂(volume.restrict T)) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono_set ?_) hKclosed
    exact Ioo_subset_Icc_self
  have hslice := pressure_gradient_translated_slice_bound_on_window
    hsol (V := V) (Dp := Dp) (x := c) (t₀ := t₀) (r := r) hr hsub hball hfield
  have hBfinite : volume (vec3Ball c (r / 2)) < ∞ :=
    CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
  intro i
  apply integrableOn_prod_of_slice_eLpNorm_bounds (D := fun z => Dp z i) hBfinite
    ((measurable_pi_apply i).comp hDpMeas).aestronglyMeasurable
  · simpa only [T, M, Function.comp_apply] using hslice.mono (fun s hs => hs i)
  · exact hK

private theorem integrableOn_biUnion_finite
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [TopologicalSpace E] [ContinuousENorm E]
    [TopologicalSpace.PseudoMetrizableSpace E]
    {μ : Measure X} {f : X → E}
    {ι : Type*} {S : Set ι} (hS : S.Finite) {U : ι → Set X}
    (hInt : ∀ i ∈ S, IntegrableOn f (U i) μ) :
    IntegrableOn f (⋃ i ∈ S, U i) μ := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | @insert i S hi hS ih =>
      simp only [mem_insert_iff, forall_eq_or_imp] at hInt
      have hUnion : (⋃ j ∈ insert i S, U j) = U i ∪ ⋃ j ∈ S, U j := by
        ext x
        simp
      rw [hUnion]
      exact hInt.1.union (ih hInt.2)

private theorem pressure_gradient_integrable_on_localBox_from_slice_selection
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B V : Set Vec3} (hbox : localBox Ω I B J)
    (hVopen : IsOpen V) (hBV : closure B ⊆ V) (hVΩ : V ⊆ Ω)
    {Dp : ParabolicPoint → Vec3} (hDpMeas : Measurable Dp)
    (hfield : ∀ᵐ s ∂(volume.restrict I), ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) V volume ∧
      HasWeakPartialDerivOn V i (fun y => p (y, s)) (fun y => Dp (y, s) i)) :
    ∀ i : Fin 3, IntegrableOn (fun z => Dp z i) (spaceTimeSet B J) volume := by
  let K : Set ParabolicPoint := closure B ×ˢ closure J
  have hKprod : IsCompact (closure B ×ˢ closure J : Set (Vec3 × ℝ)) :=
    hbox.2.1.prod hbox.2.2.2.2.1
  have hKeq : K = parabolicHomeomorph ⁻¹'
      (closure B ×ˢ closure J : Set (Vec3 × ℝ)) := by
    ext z
    rfl
  have hKcompact : IsCompact K := by
    rw [hKeq]
    exact parabolicHomeomorph.isCompact_preimage.mpr hKprod
  have hpatch : ∀ z : K, ∃ c : Vec3, ∃ t₀ r : ℝ,
      0 < r ∧ vec3Ball c (r / 2) ⊆ V ∧
      closure (parabolicCylinder c t₀ r) ⊆ spaceTimeSet Ω I ∧
      z.1 ∈ vec3Ball c (r / 2) ×ˢ Ioo (t₀ - r ^ 2) t₀ := by
    intro z
    rcases z.2 with ⟨hzB, hzJ⟩
    exact exists_strict_backward_patch hsol.2.1 hVopen hVΩ
      (hBV hzB) (hbox.2.2.2.2.2 hzJ)
  choose c t₀ r hdata using hpatch
  let U : K → Set ParabolicPoint := fun z =>
    vec3Ball (c z) (r z / 2) ×ˢ Ioo (t₀ z - (r z) ^ 2) (t₀ z)
  have hUeq (z : K) : U z = parabolicHomeomorph ⁻¹'
      (vec3Ball (c z) (r z / 2) ×ˢ Ioo (t₀ z - (r z) ^ 2) (t₀ z) :
        Set (Vec3 × ℝ)) := by
    ext w
    rfl
  have hUopen (z : K) : IsOpen (U z) := by
    rw [hUeq z]
    exact parabolicHomeomorph.isOpen_preimage.mpr
      ((isOpen_vec3Ball _ _).prod isOpen_Ioo)
  have hcover : K ⊆ ⋃ z : K, U z := by
    intro z hz
    have hmem := (hdata ⟨z, hz⟩).2.2.2
    apply mem_iUnion.mpr
    refine ⟨⟨z, hz⟩, ?_⟩
    exact hmem
  obtain ⟨S, hS⟩ := hKcompact.elim_finite_subcover U hUopen hcover
  have hpatchInt (z : K) (i : Fin 3) : IntegrableOn (fun w => Dp w i) (U z) volume := by
    simpa only [U] using pressure_gradient_integrable_on_backward_patch hsol hDpMeas hfield
      (hdata z).1 (hdata z).2.2.1 (hdata z).2.1 i
  have hincl : spaceTimeSet B J ⊆ ⋃ z ∈ S, U z := by
    intro z hz
    have hzK : z ∈ K := ⟨subset_closure hz.1, subset_closure hz.2⟩
    apply hS
    exact hzK
  intro i
  have hUnion : IntegrableOn (fun z => Dp z i) (⋃ z ∈ S, U z) volume :=
    integrableOn_biUnion_finite (X := ParabolicPoint) (E := ℝ)
      (μ := volume) (f := fun z => Dp z i) (S := (S : Set K)) S.finite_toSet
      (fun z _ => hpatchInt z i)
  exact hUnion.mono_set hincl

/-- The localized velocity has the gradient-slot Duhamel representation, with
the pressure-gradient field selected and its box integrability proved from
suitability. -/
theorem localized_duhamel_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ} (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) :
    ∃ Dp : ParabolicPoint → Vec3,
      (∀ i, Integrable (fun z => Dp z i)
        (volume.restrict (spaceTimeSet Ω' J))) ∧
      (∀ i (χ : Vec3 × ℝ → ℝ),
        χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
        tsupport χ ⊆ Ω' ×ˢ J →
        (∫ z : ParabolicPoint, p z * spatialPartial χ i z) =
          -(∫ z : ParabolicPoint, Dp z i * χ z)) ∧
      localizedVelocity φ u =ᵐ[volume]
        (fun z i => heatPotential
          (fun w => localizedGradientSourceG φ u Du f Dp w i)
          (fun j w => localizedGradientSourceH φ u j w i) z) := by
  obtain ⟨V, hVopen, hBV, hVΩ, Dp, hDpMeas, _hpV, hfield⟩ :=
    exists_measurable_pressure_slice_gradient_on_neighborhood hsol hbox
  have hDpBox := pressure_gradient_integrable_on_localBox_from_slice_selection
    hsol hbox hVopen hBV hVΩ hDpMeas hfield
  have hDpInt : ∀ i : Fin 3,
      Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet Ω' J)) := by
    intro i
    simpa only [IntegrableOn] using hDpBox i
  have hJsub : J ⊆ I := subset_trans subset_closure hbox.2.2.2.2.2
  have hp : IntegrableOn p (Ω' ×ˢ J) volume :=
    pressure_integrable_on_of_suitable_local_box hsol hbox subset_rfl
  have hDpWeak : ∀ i : Fin 3, ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport χ ⊆ Ω' ×ˢ J →
      (∫ z : ParabolicPoint, p z * spatialPartial χ i z) =
        -(∫ z : ParabolicPoint, Dp z i * χ z) := by
    intro i χ hχ hχbox
    have hweak : ∀ᵐ s ∂volume.restrict J,
        HasWeakPartialDerivOn Ω' i (fun x => p (x, s)) (fun x => Dp (x, s) i) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hJsub hfield] with s hs
      exact (hs i).2.restrict hbox.1 (subset_closure.trans hBV)
    exact pressure_pairing_of_integrable_slice_derivative i hp (hDpBox i) hweak
      hχ.1 hχ.2.1 hχbox
  have hrep := localized_gradient_slot_duhamel_of_sws
    hsol hφ hbox hφbox hDpInt hDpWeak
  exact ⟨Dp, hDpInt, hDpWeak, hrep⟩

end CKN.Core.Step3
