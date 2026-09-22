-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Vec3Norm
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Spatial slice norms

The velocity and force use the Euclidean magnitude and the velocity derivative
uses the Frobenius magnitude. Extended values retain infinite norms; no
conversion to real numbers is made outside the finite-norm domain.
-/

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN

/-- The Euclidean velocity L² norm on a spatial slice. -/
def velocitySpatialSliceNorm (u : ParabolicPoint → Vec3) (x : Vec3) (ρ s : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun y => vec3EuclideanNorm (u (y,s))) 2 (volume.restrict (vec3Ball x ρ))

/-- The Frobenius velocity-gradient L² norm on a spatial slice. -/
def gradientSpatialSliceNorm (Du : ParabolicPoint → Fin 3 → Vec3)
    (x : Vec3) (ρ s : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun y => Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y,s) i) ^ 2))
    2 (volume.restrict (vec3Ball x ρ))

/-- The pressure L^(3/2) norm on a spatial slice. -/
def pressureSpatialSliceNorm (p : ParabolicPoint → ℝ) (x : Vec3) (ρ s : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun y => p (y,s)) (ENNReal.ofReal (3/2 : ℝ)) (volume.restrict (vec3Ball x ρ))

/-- The Euclidean force L^q norm on a spatial slice. -/
def forceSpatialSliceNorm (f : ParabolicPoint → Vec3) (x : Vec3) (ρ q s : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun y => vec3EuclideanNorm (f (y,s))) (ENNReal.ofReal q)
    (volume.restrict (vec3Ball x ρ))

/-- The four spatial norms in the slice-norm display, at every time and radius. -/
theorem spatial_slice_norms_display
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) (x : Vec3) (ρ q s : ℝ) :
    velocitySpatialSliceNorm u x ρ s =
      eLpNorm (fun y => vec3EuclideanNorm (u (y,s))) 2 (volume.restrict (vec3Ball x ρ)) ∧
    gradientSpatialSliceNorm Du x ρ s =
      eLpNorm (fun y => Real.sqrt (∑ i : Fin 3, vec3EuclideanNorm (Du (y,s) i) ^ 2))
        2 (volume.restrict (vec3Ball x ρ)) ∧
    pressureSpatialSliceNorm p x ρ s =
      eLpNorm (fun y => p (y,s)) (ENNReal.ofReal (3/2 : ℝ))
        (volume.restrict (vec3Ball x ρ)) ∧
    forceSpatialSliceNorm f x ρ q s =
      eLpNorm (fun y => vec3EuclideanNorm (f (y,s))) (ENNReal.ofReal q)
        (volume.restrict (vec3Ball x ρ)) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end CKN
