-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.Potentials
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

/-!
# Rotational invariance of Newtonian potentials

The Newtonian potential of radial data is radial.  This follows by transporting the
integral along a volume-preserving Euclidean isometry taking one point to another
point of the same radius.
-/

namespace CKN.Foundation.Harmonic

private abbrev EuclideanVec3 := WithLp 2 Vec3

private def toEuclideanVec3 : Vec3 ≃ᵐ EuclideanVec3 :=
  MeasurableEquiv.toLp 2 Vec3

private def linearIsometryMeasurableEquiv
    (e : EuclideanVec3 ≃ₗᵢ[ℝ] EuclideanVec3) :
    EuclideanVec3 ≃ᵐ EuclideanVec3 :=
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    measurable_toFun := e.continuous.measurable
    measurable_invFun := e.symm.continuous.measurable }

private def transportedIsometry
    (e : EuclideanVec3 ≃ₗᵢ[ℝ] EuclideanVec3) : Vec3 ≃ᵐ Vec3 :=
  (toEuclideanVec3.trans (linearIsometryMeasurableEquiv e)).trans
    toEuclideanVec3.symm

private lemma transportedIsometry_measurePreserving
    (e : EuclideanVec3 ≃ₗᵢ[ℝ] EuclideanVec3) :
    MeasurePreserving (transportedIsometry e) volume volume := by
  have h₁ : MeasurePreserving (WithLp.toLp 2 : Vec3 → EuclideanVec3)
      volume volume := PiLp.volume_preserving_toLp (Fin 3)
  have h₂ : MeasurePreserving (e : EuclideanVec3 → EuclideanVec3)
      volume volume := LinearIsometryEquiv.measurePreserving e
  have h₃ : MeasurePreserving (WithLp.ofLp : EuclideanVec3 → Vec3)
      volume volume := PiLp.volume_preserving_ofLp (Fin 3)
  change MeasurePreserving
    ((WithLp.ofLp ∘ e ∘ WithLp.toLp 2 : Vec3 → Vec3)) volume volume
  exact h₃.comp (h₂.comp h₁)

private lemma transportedIsometry_euclideanNorm
    (e : EuclideanVec3 ≃ₗᵢ[ℝ] EuclideanVec3) (z : Vec3) :
    vec3EuclideanNorm (transportedIsometry e z) = vec3EuclideanNorm z := by
  change vec3EuclideanNorm (WithLp.ofLp (e (WithLp.toLp 2 z))) = _
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2]
  simp

private lemma exists_transportedIsometry_map
    {x y : Vec3} (hxy : vec3EuclideanNorm x = vec3EuclideanNorm y) :
    ∃ e : EuclideanVec3 ≃ₗᵢ[ℝ] EuclideanVec3,
      transportedIsometry e x = y := by
  let e : EuclideanVec3 ≃ₗᵢ[ℝ] EuclideanVec3 :=
    (ℝ ∙ (WithLp.toLp 2 x - WithLp.toLp 2 y))ᗮ.reflection
  have hn : ‖WithLp.toLp 2 x‖ = ‖WithLp.toLp 2 y‖ := by
    rw [← vec3EuclideanNorm_eq_l2, ← vec3EuclideanNorm_eq_l2]
    exact hxy
  have he : e (WithLp.toLp 2 x) = WithLp.toLp 2 y :=
    Submodule.reflection_sub hn
  refine ⟨e, ?_⟩
  change WithLp.ofLp (e (WithLp.toLp 2 x)) = y
  rw [he]

/-- A radial density has a radial Newtonian potential. -/
theorem pressureNewtonianPotential_eq_of_radial
    {g : Vec3 → ℝ}
    (hrad : ∀ x y, vec3EuclideanNorm x = vec3EuclideanNorm y → g x = g y)
    {x y : Vec3} (hxy : vec3EuclideanNorm x = vec3EuclideanNorm y) :
    CKN.pressureNewtonianPotential g x = CKN.pressureNewtonianPotential g y := by
  obtain ⟨e, he⟩ := exists_transportedIsometry_map hxy
  let T := transportedIsometry e
  have hT := transportedIsometry_measurePreserving e
  have hnorm := transportedIsometry_euclideanNorm e
  have hlin : ∀ a b : Vec3, T (a - b) = T a - T b := by
    intro a b
    change WithLp.ofLp (e (WithLp.toLp 2 (a - b))) = _
    rw [WithLp.toLp_sub, map_sub]
    rfl
  have hsrc : ∀ z, g (T z) = g z := by
    intro z
    exact hrad (T z) z (hnorm z)
  have hker : ∀ z, Foundation.Heat.newtonianKernel (T z) =
      Foundation.Heat.newtonianKernel z := by
    intro z
    unfold Foundation.Heat.newtonianKernel
    rw [hnorm]
  have hchange := hT.integral_comp T.measurableEmbedding
    (fun z : Vec3 => (-Foundation.Heat.newtonianKernel (y - z)) * g z)
  have hresult : CKN.pressureNewtonianPotential g y =
      ∫ z : Vec3,
        (-Foundation.Heat.newtonianKernel (y - T z)) * g (T z) := by
    unfold CKN.pressureNewtonianPotential
    rw [← hchange]
  have hresult' : (∫ z : Vec3,
      (-Foundation.Heat.newtonianKernel (y - T z)) * g (T z)) =
      ∫ z : Vec3,
        (-Foundation.Heat.newtonianKernel (x - z)) * g z := by
    apply integral_congr_ae
    filter_upwards [] with z
    rw [← he, ← hlin x z, hker (x - z), hsrc z]
  have hresult'' : (∫ z : Vec3,
      (-Foundation.Heat.newtonianKernel (x - z)) * g z) =
      CKN.pressureNewtonianPotential g x := by
    rfl
  exact (hresult.trans (hresult'.trans hresult'')).symm

end CKN.Foundation.Harmonic
