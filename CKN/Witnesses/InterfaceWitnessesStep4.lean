-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step3.GradientSlotDuhamel
import CKN.Core.Step4.PressureGradientBase
import CKN.Core.Step4.PressureGradientOneSided
import CKN.Core.Step4.PressureGradientOneSidedCell
import CKN.Core.Step4.RouteAAssembly
import CKN.Core.Step4.RouteAOneRound
import CKN.Foundation.Parabolic.Morrey.Zero

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-- The pressure Laplacian pairing has an instance with zero velocity,
pressure, and force. -/
theorem HasPressureDeltaOn_satisfiable :
    ∃ (U : Set Vec3) (p : Vec3 → ℝ) (u f : Vec3 → Vec3),
      HasPressureDeltaOn (U := U) p u f := by
  refine ⟨Set.univ, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro ψ hψ hψc hψU
  simp

/-- The one-scale pressure-gradient bound holds for zero source and zero
pressure, with the zero weak gradient. -/
theorem pressureGradientOneScaleAt_satisfiable :
    ∃ (C_CZ R₀ : ℝ) (V : ParabolicPoint → Vec3)
      (p : ParabolicPoint → ℝ) (t : ℝ),
      pressureGradientOneScaleAt C_CZ R₀ V p t := by
  refine ⟨0, 1, fun _ => 0, fun _ => 0, 0, ?_⟩
  intro k
  refine ⟨fun _ => 0, MeasureTheory.locallyIntegrableOn_zero, ?_, ?_⟩
  · have h := HasWeakPartialDerivOn.of_contDiff
      (U := vec3Ball (0 : Vec3) 1) (i := k)
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec3 => (0 : ℝ)))
    simpa only [fderiv_const_apply, zero_apply] using h
  · intro x ρ hρ hsub
    simp

/-- The a.e.-time one-scale bound has a zero-data instance on the whole time
line. -/
theorem pressureGradientOneScaleBound_satisfiable :
    ∃ (J : Set ℝ) (C_CZ R₀ : ℝ) (V : ParabolicPoint → Vec3)
      (p : ParabolicPoint → ℝ),
      pressureGradientOneScaleBound (J := J) C_CZ R₀ V p := by
  refine ⟨Set.univ, 0, 1, fun _ => 0, fun _ => 0, ?_⟩
  unfold pressureGradientOneScaleBound
  filter_upwards [] with t
  intro k
  refine ⟨fun _ => 0, MeasureTheory.locallyIntegrableOn_zero, ?_, ?_⟩
  · have h := HasWeakPartialDerivOn.of_contDiff
      (U := vec3Ball (0 : Vec3) 1) (i := k)
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec3 => (0 : ℝ)))
    simpa only [fderiv_const_apply, zero_apply] using h
  · intro x ρ hρ hsub
    simp

/-- The cell-output predicate is inhabited by the identically zero field. -/
theorem oneSidedPressureGradientCellOutput_satisfiable :
    ∃ (z₀ : ParabolicPoint) (R κ : ℝ) (KP : ℝ≥0∞)
      (Dp : ParabolicPoint → Vec3),
      oneSidedPressureGradientCellOutput z₀ R κ KP Dp := by
  refine ⟨oneSidedPressureGradientOrigin, 1, 1, 0, fun _ => 0, ?_⟩
  intro i z r
  have hzero : (Metric.ball oneSidedPressureGradientOrigin (1 / 2 : ℝ)).indicator
      (fun _ : ParabolicPoint => (0 : ℝ)) = fun _ => 0 := by
    funext w
    by_cases hw : w ∈ Metric.ball oneSidedPressureGradientOrigin (1 / 2 : ℝ)
    · rw [Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw]
  change morreyCell (6 / 5 : ℝ) 1
    ((Metric.ball oneSidedPressureGradientOrigin (1 / 2 : ℝ)).indicator
      (fun _ : ParabolicPoint => (0 : ℝ))) z r.1 ≤ 0
  rw [hzero, morreyCell_zero
    (p := (6 / 5 : ℝ)) (q := 1) (by norm_num) z r.1]

/-- The gradient-slot representation used by Route A follows directly from
the Duhamel theorem for suitable weak solutions. -/
theorem routeA_gradient_slot_representation_satisfiable :
    routeA_gradient_slot_representation := by
  intro Ω I q u Du p f hsol φ hφ Ω' J hbox hφbox Dp hDpInt hDpweak
  exact CKN.Core.Step3.localized_gradient_slot_duhamel_of_sws
    hsol hφ hbox hφbox hDpInt hDpweak

/-- The producer-facing heat representation has the same Duhamel producer on
local boxes. -/
theorem routeA_representation_producer_satisfiable :
    routeA_representation_producer := by
  intro Ω I q u Du p f hsol φ hφ U J hbox hφbox Dp hDpInt hDpweak
  exact CKN.Core.Step3.localized_gradient_slot_duhamel_of_sws
    hsol hφ hbox hφbox hDpInt hDpweak

end CKN.Core.Step4
