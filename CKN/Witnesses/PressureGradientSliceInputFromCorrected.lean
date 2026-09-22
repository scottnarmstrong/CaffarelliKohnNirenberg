-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientGluedSmallCell
import CKN.Core.Step4.PressureGradientGluedOriginClause
import CKN.Core.Step4.PressureGradientOriginClauseGauge
import CKN.Core.Step4.SliceSelectedGradientCorrectedSWS
import CKN.Core.Step4.SliceSelectedGradientCellIdentification

/-!
# Margin-cell pressure-gradient slice input

The corrected slice estimate on the doubled cell is identified with the
fixed measurable weak gradient on the cell's shorter time window. The margin
geometry keeps the doubled cylinder inside the unit cylinder.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

private theorem origin_fixed_gauge_slice_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (γ : ℝ → ℝ) {B : Set Vec3} {Dp : ParabolicPoint → Vec3}
    (hball : euclideanBall z.1 (ρ / 2) ⊆ B)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun y => p (y, s)) (fun y => Dp (y, s) k)) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ k : Fin 3,
      eLpNorm (fun y => Dp (y, s) k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
        originSliceGradientMajorant u Du (fun w => p w - γ w.2) f z hρ s :=
  origin_fixed_gradient_slice_bound_gauge_of_sws
    hsol hρ hsub γ hball hfield

/-- The explicit doubled-scale majorant in the corrected force-free
centred-source slice estimate. -/
@[irreducible] private def correctedPressureGradientSliceMajorant
    (C₁₇ C_P1 C₈ : ℝ)
    {q : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (z : ParabolicPoint) (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal czGradientOperatorConstant *
      (∑ _i : Fin 3, centredSWSCentredMajorant z.1 ρ q u Du f s) +
    ENNReal.ofReal (C₁₇ *
      (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 ρ)) +
          (9 * C_P1) * (∫ y in vec3Ball z.1 ρ,
            (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) +
        harmonicRemainderForceBound z hρ f s) * ρ ^ (-1 / 2 : ℝ)) +
    ENNReal.ofReal (sliceForceGradientBound czGradientOperatorConstant C₈
      z.1 hρ f s)

private theorem correctedPressureGradientSliceMajorant_eq
    (C₁₇ C_P1 C₈ : ℝ)
    {q : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (z : ParabolicPoint) (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) :
    correctedPressureGradientSliceMajorant C₁₇ C_P1 C₈
      (q := q) (u := u) (Du := Du) (p := p) (f := f) z ρ hρ s =
      ENNReal.ofReal czGradientOperatorConstant *
          (∑ _i : Fin 3, centredSWSCentredMajorant z.1 ρ q u Du f s) +
        ENNReal.ofReal (C₁₇ *
          (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall z.1 ρ)) +
            (9 * C_P1) * (∫ y in vec3Ball z.1 ρ,
              (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) +
            harmonicRemainderForceBound z hρ f s) * ρ ^ (-1 / 2 : ℝ)) +
        ENNReal.ofReal (sliceForceGradientBound czGradientOperatorConstant C₈
          z.1 hρ f s) := by
  unfold correctedPressureGradientSliceMajorant
  rfl

private theorem corrected_sws_doubled_slice_input
    (C₁₇ C_P1 C₈ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    (hCZ_p1 : czP1OperatorConstant ≤ C_P1)
    (hC₈ : sliceForceGradientConstant ≤ C₈)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k)
          (euclideanBall z.1 (ρ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (fun x => p (x, s)) (fun x => D x k)) ∧
        (∀ k : Fin 3, eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
          correctedPressureGradientSliceMajorant C₁₇ C_P1 C₈
            (q := q) (u := u) (Du := Du) (p := p) (f := f) z ρ hρ s) := by
  have hraw := slice_selected_gradient_corrected_ae_of_sws_data
    C₁₇ C_P1 C₈ hC₁₇ hCZ_p1 hC₈ hsol hρ hsub
  filter_upwards [hraw] with s hs
  obtain ⟨D, hloc, hmem, hweak, hbound⟩ := hs
  refine ⟨D, hloc, hmem, hweak, fun k => ?_⟩
  calc
    eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤ _ := hbound k
    _ = correctedPressureGradientSliceMajorant C₁₇ C_P1 C₈
        (q := q) (u := u) (Du := Du) (p := p) (f := f) z ρ hρ s :=
      (correctedPressureGradientSliceMajorant_eq C₁₇ C_P1 C₈
        (q := q) (u := u) (Du := Du) (p := p) (f := f) z ρ hρ s).symm

private theorem glued_cell_gauge_data_of_selected_slice
    {B : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ}
    {Dp : ParabolicPoint → Vec3} {x : Vec3} {t r : ℝ} (hr : 0 < r)
    {M G : ℝ → ℝ≥0∞} (hball : vec3Ball x r ⊆ B)
    (htime : Ioc (t - r ^ 2) t ⊆ I)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun y => p (y, s)) (fun y => Dp (y, s) k))
    (hslice : ∀ᵐ s ∂volume.restrict (Ioc (t - (2 * r) ^ 2) t),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun y => D y k)
          (euclideanBall x ((2 * r) / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) k
          (fun y => p (y, s)) (fun y => D y k)) ∧
        (∀ k : Fin 3, eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ M s))
    (hDpBound : ∀ᵐ s ∂volume.restrict (Ioc (t - r ^ 2) t), ∀ k,
      eLpNorm (fun y => Dp (y, s) k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ G s) :
    ∀ k : Fin 3, ∀ᵐ s ∂volume.restrict (Ioc (t - r ^ 2) t),
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball x r) volume ∧
        HasWeakPartialDerivOn (vec3Ball x r) k (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball x r)) ≤ G s := by
  have hidentified := ae_glued_gradient_cell_selected_slice_identification
    hr hball htime hfield hslice
  have hballEq : euclideanBall x ((2 * r) / 2) = vec3Ball x r := by
    rw [mul_div_cancel_left₀ r (by norm_num : (2 : ℝ) ≠ 0)]
    exact CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr
  intro k
  filter_upwards [hidentified, hDpBound] with s hs hDp
  obtain ⟨D, hDloc, _hDmem, hDweak, _hDbound, _hDpRaw, hEq⟩ := hs
  refine ⟨fun y => D y k, ?_, ?_, ?_⟩
  · simpa only [← hballEq] using hDloc k
  · simpa only [← hballEq] using hDweak k
  · calc
      eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball x r)) =
        eLpNorm (fun y => Dp (y, s) k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) := by
            rw [← hballEq]
            exact (eLpNorm_congr_ae (hEq k)).symm
      _ ≤ G s := hDp k

private theorem cell_window_subset_of_doubled_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆ spaceTimeSet Ω I) :
    Ioc (z.2 - r ^ 2) z.2 ⊆ I := by
  intro s hs
  have hpoint : (z.1, s) ∈ parabolicCylinder z.1 z.2 (2 * r) := by
    rw [mem_parabolicCylinder]
    refine ⟨?_, ?_, hs.2⟩
    · rw [sub_self, vec3EuclideanNorm_zero]
      positivity
    · nlinarith only [hs.1, sq_nonneg r]
  exact (hsub (subset_closure hpoint)).2

private theorem doubled_window_subset_of_doubled_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆ spaceTimeSet Ω I) :
    Ioc (z.2 - (2 * r) ^ 2) z.2 ⊆ I := by
  intro s hs
  have hpoint : (z.1, s) ∈ parabolicCylinder z.1 z.2 (2 * r) := by
    rw [mem_parabolicCylinder]
    refine ⟨?_, hs.1, hs.2⟩
    rw [sub_self, vec3EuclideanNorm_zero]
    positivity
  exact (hsub (subset_closure hpoint)).2

private theorem fixed_field_doubled_slice_data_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} {Dp : ParabolicPoint → Vec3}
    (hball : euclideanBall z.1 r ⊆ B)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun y => p (y, s)) (fun y => Dp (y, s) k)) :
    ∀ k : Fin 3, ∀ᵐ s ∂volume.restrict (Ioc (z.2 - (2 * r) ^ 2) z.2),
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball z.1 r) volume ∧
        HasWeakPartialDerivOn (vec3Ball z.1 r) k (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball z.1 r)) ≤
          originSliceGradientMajorant u Du
            (fun w => p w - average (volume.restrict (vec3Ball z.1 (2 * r)))
              (fun y => p (y, w.2))) f z (ρ := 2 * r)
            (show 0 < 2 * r by nlinarith only [hr]) s := by
  have hballEq : euclideanBall z.1 r = vec3Ball z.1 r :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr
  have hballVec : vec3Ball z.1 r ⊆ B := by
    rw [← hballEq]
    exact hball
  have htime := doubled_window_subset_of_doubled_cylinder hr hsub
  have hρ : 0 < 2 * r := by positivity
  have hhalf : (2 * r) / 2 = r := by ring
  have hballρ : euclideanBall z.1 ((2 * r) / 2) ⊆ B := by
    rw [hhalf]
    exact hball
  let γ : ℝ → ℝ := fun s => average (volume.restrict (vec3Ball z.1 (2 * r)))
    (fun y => p (y, s))
  have hDpGauge := origin_fixed_gauge_slice_bound
    hsol hρ hsub γ hballρ hfield
  have hfieldTime := ae_restrict_of_ae_restrict_of_subset htime hfield
  intro k
  filter_upwards [hfieldTime, hDpGauge] with s hf hDp
  refine ⟨fun y => Dp (y, s) k, ?_, ?_, ?_⟩
  · exact (hf k).1.mono_set hballVec
  · exact (hf k).2.restrict (isOpen_vec3Ball z.1 r) hballVec
  · simpa only [hhalf, hballEq, γ] using hDp k

private theorem corrected_gauge_glued_cell_data_of_sws
    (C₁₇ C_P1 C₈ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    (hCZ_p1 : czP1OperatorConstant ≤ C_P1)
    (hC₈ : sliceForceGradientConstant ≤ C₈)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} {Dp : ParabolicPoint → Vec3}
    (hball : euclideanBall z.1 r ⊆ B)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun y => p (y, s)) (fun y => Dp (y, s) k)) :
    ∀ k : Fin 3, ∀ᵐ s ∂volume.restrict (Ioc (z.2 - r ^ 2) z.2),
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball z.1 r) volume ∧
        HasWeakPartialDerivOn (vec3Ball z.1 r) k (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball z.1 r)) ≤
          originSliceGradientMajorant u Du
            (fun w => p w - average (volume.restrict (vec3Ball z.1 (2 * r)))
              (fun y => p (y, w.2))) f z (ρ := 2 * r)
            (show 0 < 2 * r by positivity) s := by
  have hballEq : euclideanBall z.1 r = vec3Ball z.1 r :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr
  have hballVec : vec3Ball z.1 r ⊆ B := by
    rw [← hballEq]
    exact hball
  have htime := cell_window_subset_of_doubled_cylinder hr hsub
  have hρ : 0 < 2 * r := by positivity
  have hhalf : (2 * r) / 2 = r := by ring
  have hballρ : euclideanBall z.1 ((2 * r) / 2) ⊆ B := by
    rw [hhalf]
    exact hball
  let γ : ℝ → ℝ := fun s => average (volume.restrict (vec3Ball z.1 (2 * r)))
    (fun y => p (y, s))
  have hDpGauge := origin_fixed_gauge_slice_bound
    hsol hρ hsub γ hballρ hfield
  have hwindow : Ioc (z.2 - r ^ 2) z.2 ⊆ Ioc (z.2 - (2 * r) ^ 2) z.2 := by
    intro s hs
    exact ⟨by nlinarith only [hs.1, sq_nonneg r], hs.2⟩
  have hDpGaugeCell := ae_restrict_of_ae_restrict_of_subset hwindow hDpGauge
  have hslice := corrected_sws_doubled_slice_input
    C₁₇ C_P1 C₈ hC₁₇ hCZ_p1 hC₈ hsol
      (z := z) (ρ := 2 * r) hρ hsub
  have hresult := glued_cell_gauge_data_of_selected_slice
    hr hballVec htime hfield hslice hDpGaugeCell
  intro k
  filter_upwards [hresult k] with s hs
  obtain ⟨g, hloc, hweak, hbound⟩ := hs
  refine ⟨g, hloc, hweak, ?_⟩
  simpa only [γ] using hbound

/-- The corrected doubled-cell slice estimate is identified with the fixed
weak gradient on the shorter cell window. Its pressure term is normalized by
the spatial mean on the same doubled ball, so the bound is gauge invariant. -/
private theorem origin_margin_cell_exists_slice_data_of_corrected_sws
    (C₁₇ C_P1 C₈ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    (hCZ_p1 : czP1OperatorConstant ≤ C_P1)
    (hC₈ : sliceForceGradientConstant ≤ C₈)
    {Ω : Set Vec3} {I : Set ℝ} {q τ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {R₁ : ℝ} (hR₁ : 0 < R₁) (hR₁unit : R₁ < 1)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hmargin : r ≤ (1 - R₁) / 4)
    (hmeet : (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁).Nonempty)
    (ht : z.2 ∈ Ioc (-(9 / 16 : ℝ)) (0 : ℝ))
    (Aₚ : ℝ)
    (hGauge : 0 ≤ Aₚ ∧
      (∫ s in Ioc (z.2 - r ^ 2) z.2,
        (((2 * r) ^ (-1 / 2 : ℝ)) *
          lpNorm (fun y => p (y, s) -
            average (volume.restrict (vec3Ball z.1 (2 * r)))
              (fun y => p (y, s)))
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall z.1 (2 * r)))) ^ (6 / 5 : ℝ)) ≤
        Aₚ * r ^ (5 - 6 / min ((1 / τ + 8 / 25)⁻¹) q))
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    {Dp : ParabolicPoint → Vec3}
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) (vec3Ball 0 1) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 1) k (fun y => p (y, s))
        (fun y => Dp (y, s) k)) :
    (0 ≤ Aₚ ∧
      (∫ s in Ioc (z.2 - r ^ 2) z.2,
        (((2 * r) ^ (-1 / 2 : ℝ)) *
          lpNorm (fun y => p (y, s) -
            average (volume.restrict (vec3Ball z.1 (2 * r)))
              (fun y => p (y, s)))
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall z.1 (2 * r)))) ^ (6 / 5 : ℝ)) ≤
        Aₚ * r ^ (5 - 6 / min ((1 / τ + 8 / 25)⁻¹) q)) ∧
    ∀ k : Fin 3, ∀ᵐ s ∂volume.restrict (Ioc (z.2 - r ^ 2) z.2),
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (vec3Ball z.1 r) volume ∧
        HasWeakPartialDerivOn (vec3Ball z.1 r) k (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball z.1 r)) ≤
          originSliceGradientMajorant u Du
            (fun w => p w - average (volume.restrict (vec3Ball z.1 (2 * r)))
              (fun y => p (y, w.2))) f z
            (show 0 < 2 * r by nlinarith only [hr]) s := by
  refine ⟨hGauge, ?_⟩
  have hx : vec3EuclideanNorm (z.1 - 0) < R₁ + r :=
    vec3EuclideanNorm_lt_of_vec3Ball_inter_nonempty hmeet
  have h3r : 3 * r ≤ 1 - R₁ := originMarginScale_triple_le hR₁unit hmargin
  have hdoubleBottom : -1 ≤ z.2 - (2 * r) ^ 2 := by
    have hdepth := originMarginScale_double_sq_le hR₁ hr hmargin
    nlinarith only [ht.1, hdepth]
  have hsub : closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆ spaceTimeSet Ω I :=
    closure_parabolicCylinder_double_subset_spaceTimeSet_of_origin_margin
      hdom le_rfl h3r hx ht.2 hdoubleBottom
  have hball : vec3Ball z.1 r ⊆ vec3Ball (0 : Vec3) 1 :=
    vec3Ball_subset_outer_of_margin (le_of_lt hr) h3r hx
  have hballE : euclideanBall z.1 r ⊆ vec3Ball (0 : Vec3) 1 := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr]
    exact hball
  exact corrected_gauge_glued_cell_data_of_sws
    C₁₇ C_P1 C₈ hC₁₇ hCZ_p1 hC₈ hsol hr hsub hballE hfield

/-- On every origin-carrier cell in the margin regime, the fixed glued field
has a slice weak derivative bounded by the doubled-cell majorant with the
cell's own pressure mean removed. The separate pressure-growth input is kept
explicit for the subsequent time integration. -/
theorem origin_margin_every_cell_slice_input_of_corrected_sws
    (C₁₇ C_P1 C₈ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    (hCZ_p1 : czP1OperatorConstant ≤ C_P1)
    (hC₈ : sliceForceGradientConstant ≤ C₈)
    {Ω : Set Vec3} {I : Set ℝ} {q τ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {R₁ : ℝ} (hR₁ : 0 < R₁) (hR₁unit : R₁ < 1)
    (Aₚ : ℝ) (hAₚ : 0 ≤ Aₚ)
    (hGauge : ∀ (z : ParabolicPoint) (r : ℝ), 0 < r →
      r ≤ (1 - R₁) / 4 →
      (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁).Nonempty →
      z.2 ∈ Ioc (-(9 / 16 : ℝ)) (0 : ℝ) →
      (∫ s in Ioc (z.2 - r ^ 2) z.2,
        (((2 * r) ^ (-1 / 2 : ℝ)) *
          lpNorm (fun y => p (y, s) -
            average (volume.restrict (vec3Ball z.1 (2 * r)))
              (fun y => p (y, s)))
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall z.1 (2 * r)))) ^ (6 / 5 : ℝ)) ≤
        Aₚ * r ^ (5 - 6 / min ((1 / τ + 8 / 25)⁻¹) q))
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    {Dp : ParabolicPoint → Vec3}
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) (vec3Ball 0 1) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 1) k (fun y => p (y, s))
        (fun y => Dp (y, s) k)) :
    ∀ (z : ParabolicPoint) (r : ℝ) (hr : 0 < r), r ≤ (1 - R₁) / 4 →
      (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁).Nonempty →
      z.2 ∈ Ioc (-(9 / 16 : ℝ)) (0 : ℝ) →
      (∀ k : Fin 3, ∀ᵐ s ∂volume.restrict (Ioc (z.2 - (2 * r) ^ 2) z.2),
        ∃ g : Vec3 → ℝ,
          LocallyIntegrableOn g (vec3Ball z.1 r) volume ∧
          HasWeakPartialDerivOn (vec3Ball z.1 r) k (fun y => p (y, s)) g ∧
          eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r)) ≤
            originSliceGradientMajorant u Du
              (fun w => p w - average (volume.restrict (vec3Ball z.1 (2 * r)))
                (fun y => p (y, w.2))) f z (ρ := 2 * r)
              (show 0 < 2 * r by nlinarith only [hr]) s) ∧
      (∀ k : Fin 3, ∀ᵐ s ∂volume.restrict (Ioc (z.2 - r ^ 2) z.2),
        ∃ g : Vec3 → ℝ,
          LocallyIntegrableOn g (vec3Ball z.1 r) volume ∧
          HasWeakPartialDerivOn (vec3Ball z.1 r) k (fun y => p (y, s)) g ∧
          eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r)) ≤
            originSliceGradientMajorant u Du
              (fun w => p w - average (volume.restrict (vec3Ball z.1 (2 * r)))
                (fun y => p (y, w.2))) f z (ρ := 2 * r)
              (show 0 < 2 * r by nlinarith only [hr]) s) := by
  intro z r hr hmargin hmeet ht
  have hGaugeCell := hGauge z r hr hmargin hmeet ht
  have hx : vec3EuclideanNorm (z.1 - 0) < R₁ + r :=
    vec3EuclideanNorm_lt_of_vec3Ball_inter_nonempty hmeet
  have h3r : 3 * r ≤ 1 - R₁ := originMarginScale_triple_le hR₁unit hmargin
  have hdoubleBottom : -1 ≤ z.2 - (2 * r) ^ 2 := by
    have hdepth := originMarginScale_double_sq_le hR₁ hr hmargin
    nlinarith only [ht.1, hdepth]
  have hsub : closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆ spaceTimeSet Ω I :=
    closure_parabolicCylinder_double_subset_spaceTimeSet_of_origin_margin
      hdom le_rfl h3r hx ht.2 hdoubleBottom
  have hball : vec3Ball z.1 r ⊆ vec3Ball (0 : Vec3) 1 :=
    vec3Ball_subset_outer_of_margin (le_of_lt hr) h3r hx
  have hballE : euclideanBall z.1 r ⊆ vec3Ball (0 : Vec3) 1 := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr]
    exact hball
  have hdouble := fixed_field_doubled_slice_data_of_sws
    hsol hr hsub hballE hfield
  have hcell := origin_margin_cell_exists_slice_data_of_corrected_sws
    C₁₇ C_P1 C₈ hC₁₇ hCZ_p1 hC₈ hR₁ hR₁unit hr hmargin hmeet ht
    Aₚ ⟨hAₚ, hGaugeCell⟩ hsol hdom hfield
  exact ⟨hdouble, hcell.2⟩

end CKN.Core.Step4
