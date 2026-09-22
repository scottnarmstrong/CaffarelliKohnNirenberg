-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumericalScaling
import CKN.Setting.ScalingInvarianceTests

/-!
# Transport of a selected weak pressure gradient

A parabolic change of variables preserves the spatial weak-gradient identity.
The gradient acquires one additional spatial scaling factor beyond the
pressure amplitude. The identity retains the exact transformed test support.
-/

open MeasureTheory Set
open scoped Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

private def pressureScalingHomeomorph (a : ℝ) (ha : 0 < a) (z₀ : ParabolicPoint) :
    (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
  Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero a ha.ne').trans (Homeomorph.addLeft z₀.1))
    ((Homeomorph.smulOfNeZero (a ^ 2) (sq_pos_of_pos ha).ne').trans
      (Homeomorph.addLeft z₀.2))

private theorem pressureScalingHomeomorph_symm (a : ℝ) (ha : 0 < a) (z₀ : ParabolicPoint) :
    ⇑(pressureScalingHomeomorph a ha z₀).symm =
      (fun w : Vec3 × ℝ => (a⁻¹ • (w.1 - z₀.1), (a ^ 2)⁻¹ * (w.2 - z₀.2))) := by
  ext w <;>
    simp [pressureScalingHomeomorph, Homeomorph.trans, Homeomorph.prodCongr,
      Homeomorph.smulOfNeZero, Homeomorph.addLeft, Equiv.addLeft, Units.smul_def] <;>
    ring

/-- Local integrability of a selected gradient transports to the exact
rescaled product box. -/
theorem force_slot_pressure_integrable_scaling
    (a c : ℝ) (ha : 0 < a) (z₀ : ParabolicPoint)
    {U : Set Vec3} {J : Set ℝ} (hU : MeasurableSet U) (hJ : MeasurableSet J)
    (Dp : ParabolicPoint → Vec3)
    (hInt : ∀ i, Integrable (fun w => Dp w i) (volume.restrict (spaceTimeSet U J))) :
    ∀ i, Integrable (fun w => c * a * Dp (scalingParabolic a z₀ w) i)
      (volume.restrict (spaceTimeSet (rescaledSpace a z₀.1 U) (rescaledTime a z₀.2 J))) := by
  intro i
  exact (integrable_comp_scaling_test a ha z₀ hU hJ (hInt i)).const_mul (c * a)

/-- A weak spatial gradient transforms with the pressure amplitude times
the spatial dilation, on precisely the inverse image of its original domain. -/
theorem force_slot_weak_pressure_gradient_scaling
    (a c : ℝ) (ha : 0 < a) (z₀ : ParabolicPoint)
    (B : Set (Vec3 × ℝ)) (p : ParabolicPoint → ℝ) (Dp : ParabolicPoint → Vec3)
    (hweak : ∀ i (ψ : Vec3 × ℝ → ℝ),
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ → tsupport ψ ⊆ B →
      (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
        -(∫ w : ParabolicPoint, Dp w i * ψ w)) :
    ∀ i (ψ : Vec3 × ℝ → ℝ),
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport ψ ⊆ (fun w : Vec3 × ℝ =>
        (z₀.1 + a • w.1, z₀.2 + a ^ 2 * w.2)) ⁻¹' B →
      (∫ w : ParabolicPoint, (c * p (scalingParabolic a z₀ w)) * spatialPartial ψ i w) =
        -(∫ w : ParabolicPoint, (c * a * Dp (scalingParabolic a z₀ w) i) * ψ w) := by
  intro i ψ hψ hsupp
  let e := pressureScalingHomeomorph a ha z₀
  let φ : Vec3 × ℝ → ℝ := ψ ∘ e.symm
  have hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ := by
    refine ⟨hψ.1.comp ?_, hψ.2.1.comp_homeomorph e.symm, ?_⟩
    · dsimp [e]
      rw [pressureScalingHomeomorph_symm]
      fun_prop
    · intro w _
      exact ⟨mem_univ _, mem_univ _⟩
  have hφB : tsupport φ ⊆ B := by
    rw [show φ = ψ ∘ e.symm from rfl, tsupport_comp_eq_preimage,
      ← e.image_eq_preimage_symm]
    rintro _ ⟨w, hw, rfl⟩
    exact hsupp hw
  have hφcomp (w : ParabolicPoint) : φ (scalingParabolic a z₀ w) = ψ w := by
    change ψ (e.symm (e (w.1, w.2))) = ψ (w.1, w.2)
    rw [e.symm_apply_apply]
  have hder (w : ParabolicPoint) :
      spatialPartial φ i (scalingParabolic a z₀ w) = a⁻¹ * spatialPartial ψ i w := by
    dsimp only [φ, e]
    rw [pressureScalingHomeomorph_symm]
    exact spatialPartial_pullback a ha z₀ hψ.1 i w
  have hleft := force_slot_integral_scaling ha z₀ (fun w => p w * spatialPartial φ i w)
  have hright := force_slot_integral_scaling ha z₀ (fun w => Dp w i * φ w)
  simp only [hder] at hleft
  simp only [hφcomp] at hright
  have hleft' : a⁻¹ * (∫ w : ParabolicPoint,
      p (scalingParabolic a z₀ w) * spatialPartial ψ i w) =
      a⁻¹ ^ 5 * (∫ w : ParabolicPoint, p w * spatialPartial φ i w) := by
    rw [← integral_const_mul]
    convert hleft using 1
    congr 1
    funext w
    ring
  rw [hweak i φ hφ hφB, mul_neg, ← hright] at hleft'
  have hbase : (∫ w : ParabolicPoint,
      p (scalingParabolic a z₀ w) * spatialPartial ψ i w) =
      -a * (∫ w : ParabolicPoint, Dp (scalingParabolic a z₀ w) i * ψ w) := by
    have h := congrArg (fun t : ℝ => a * t) hleft'
    simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul, mul_neg, neg_mul] using h
  calc
    _ = c * (∫ w : ParabolicPoint,
        p (scalingParabolic a z₀ w) * spatialPartial ψ i w) := by
      simp only [mul_assoc, integral_const_mul]
    _ = -(c * a * (∫ w : ParabolicPoint, Dp (scalingParabolic a z₀ w) i * ψ w)) := by
      rw [hbase]
      ring
    _ = _ := by simp only [mul_assoc, integral_const_mul]

end CKN.Core.Endgame
