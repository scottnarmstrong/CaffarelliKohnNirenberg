-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.AmbientLp
import CKN.Setting.Examples.ShearCounterexample.ScaleL3
import CKN.Setting.Examples.ShearCounterexample.ForceL2
import CKN.Setting.Examples.ShearCounterexample.ShearWeightedProfile
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # The full space-time velocity, gradient, and force fields. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

def shearReducedView (z : ParabolicPoint) : Vec2 × ℝ :=
  ((fun i : Fin 2 => z.1 i.castSucc), z.2)

theorem shearSeries_eq_reduced (z : ParabolicPoint) :
    shearSeries z = shearReducedBumpSeries (shearReducedView z) := by
  unfold shearSeries shearReducedBumpSeries
  apply tsum_congr
  intro n
  have hbumpeq : shearParabolicBump (shearScale n) z =
      shearScaleBump (shearScale n) (shearReducedView z) := by
    rfl
  rw [shearSeriesTerm, shearReducedBumpTerm, shearBumpField, shearWeight,
    smul_eq_mul, hbumpeq]

def shearFullScalar (z : ParabolicPoint) : ℝ :=
  shearReducedBumpSeries (shearReducedView z)

def shearFullGradient (j : Fin 2) (z : ParabolicPoint) : ℝ :=
  shearReducedGradientSeries j (shearReducedView z)

def shearFullForceScalar (z : ParabolicPoint) : ℝ :=
  shearReducedForceSeries (shearReducedView z)

def shearCounterexampleVelocity (z : ParabolicPoint) : Vec3 :=
  fun i => if i = 2 then shearFullScalar z else 0

def shearCounterexamplePressure (_z : ParabolicPoint) : ℝ := 0

def shearCounterexampleForce (z : ParabolicPoint) : Vec3 :=
  fun i => if i = 2 then shearFullForceScalar z else 0

def shearCounterexampleDu (z : ParabolicPoint) : Fin 3 → Vec3 :=
  fun i => fun j => if i = 2 then
    if j = 0 then shearFullGradient 0 z else
      if j = 1 then shearFullGradient 1 z else 0 else 0

theorem shearCounterexampleVelocity_eq_shearVelocity (z : ParabolicPoint) :
    shearCounterexampleVelocity z = shearVelocity z := by
  funext i
  simp [shearCounterexampleVelocity, shearVelocity, shearFullScalar,
    shearSeries_eq_reduced, basisVec_apply]

private theorem shearReducedBumpTerm_continuous_full (n : ℕ) :
    Continuous (shearReducedBumpTerm n) := by
  unfold shearReducedBumpTerm
  exact continuous_const.mul (shearBumpField_continuous (shearScale_pos n))

private theorem shearReducedGradientTerm_continuous_full (i : Fin 2) (n : ℕ) :
    Continuous (shearReducedGradientTerm i n) := by
  unfold shearReducedGradientTerm
  exact continuous_const.mul
    (shearSpatialFirstField_continuous (shearScale_pos n) i)

private theorem shearReducedForceTerm_continuous_full (n : ℕ) :
    Continuous (shearReducedForceTerm n) := by
  unfold shearReducedForceTerm shearReducedForceCore
  exact continuous_const.mul
    (((shearTimeFirstField_continuous (shearScale_pos n)).sub
      (shearSpatialSecondField_continuous (shearScale_pos n) 0)).sub
      (shearSpatialSecondField_continuous (shearScale_pos n) 1))

theorem shearReducedBumpSeries_measurable : Measurable shearReducedBumpSeries := by
  unfold shearReducedBumpSeries
  exact Measurable.tsum (fun n => (shearReducedBumpTerm_continuous_full n).measurable)

theorem shearReducedGradientSeries_measurable (i : Fin 2) :
    Measurable (shearReducedGradientSeries i) := by
  unfold shearReducedGradientSeries
  exact Measurable.tsum (fun n => (shearReducedGradientTerm_continuous_full i n).measurable)

theorem shearReducedForceSeries_measurable : Measurable shearReducedForceSeries := by
  unfold shearReducedForceSeries
  exact Measurable.tsum (fun n => (shearReducedForceTerm_continuous_full n).measurable)

private theorem shearReducedView_measurable : Measurable shearReducedView := by
  apply Measurable.prodMk
  · exact Measurable.of_eval fun i =>
    (measurable_pi_apply (i.castSucc)).comp measurable_fst
  · exact measurable_snd

theorem shearFullScalar_measurable : Measurable shearFullScalar :=
  shearReducedBumpSeries_measurable.comp shearReducedView_measurable

theorem shearFullGradient_measurable (i : Fin 2) : Measurable (shearFullGradient i) :=
  (shearReducedGradientSeries_measurable i).comp shearReducedView_measurable

theorem shearFullForceScalar_measurable : Measurable shearFullForceScalar :=
  shearReducedForceSeries_measurable.comp shearReducedView_measurable

theorem shearCounterexampleVelocity_measurable :
    Measurable shearCounterexampleVelocity := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i = 2
  · simp [shearCounterexampleVelocity, hi, shearFullScalar_measurable]
  · simp [shearCounterexampleVelocity, hi]

theorem shearCounterexampleForce_measurable :
    Measurable shearCounterexampleForce := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i = 2
  · simp [shearCounterexampleForce, hi, shearFullForceScalar_measurable]
  · simp [shearCounterexampleForce, hi]

theorem shearCounterexampleDu_measurable :
    Measurable shearCounterexampleDu := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  by_cases hi : i = 2
  · subst i
    by_cases hj0 : j = 0
    · simp [shearCounterexampleDu, hj0, shearFullGradient_measurable]
    · by_cases hj1 : j = 1
      · simp [shearCounterexampleDu, hj1, shearFullGradient_measurable]
      · simp [shearCounterexampleDu, hj0, hj1]
  · simp [shearCounterexampleDu, hi]

theorem shearFullScalar_memLp_on_localBox {p : ENNReal}
    (hp : MemLp shearReducedBumpSeries p volume)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    MemLp shearFullScalar p (volume.restrict (spaceTimeSet Ω' J)) := by
  have hcomp := shearFullProfile_memLp_of_reduced_on_localBox hp hbox
  have hEq : shearFullScalar =ᵐ[volume.restrict (spaceTimeSet Ω' J)]
      (fun z => shearReducedBumpSeries (shearCoordinateEquiv z).2) := by
    filter_upwards [] with z
    simp [shearFullScalar, shearReducedView, shearCoordinateEquiv_apply]
  exact (memLp_congr_ae hEq).2 hcomp

theorem shearFullGradient_memLp_on_localBox {i : Fin 2}
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    MemLp (shearFullGradient i) 2 (volume.restrict (spaceTimeSet Ω' J)) := by
  have hp : MemLp (shearReducedGradientSeries i) 2 volume :=
    shearReducedGradientSeries_memLp i
  have hcomp := shearFullProfile_memLp_of_reduced_on_localBox hp hbox
  have hEq : shearFullGradient i =ᵐ[volume.restrict (spaceTimeSet Ω' J)]
      (fun z => shearReducedGradientSeries i (shearCoordinateEquiv z).2) := by
    filter_upwards [] with z
    simp [shearFullGradient, shearReducedView, shearCoordinateEquiv_apply]
  exact (memLp_congr_ae hEq).2 hcomp

theorem shearFullForceScalar_memLp_on_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    MemLp shearFullForceScalar 2 (volume.restrict (spaceTimeSet Ω' J)) := by
  have hp := shearReducedForceSeries_memLp
  have hcomp := shearFullProfile_memLp_of_reduced_on_localBox hp hbox
  have hEq : shearFullForceScalar =ᵐ[volume.restrict (spaceTimeSet Ω' J)]
      (fun z => shearReducedForceSeries (shearCoordinateEquiv z).2) := by
    filter_upwards [] with z
    simp [shearFullForceScalar, shearReducedView, shearCoordinateEquiv_apply]
  exact (memLp_congr_ae hEq).2 hcomp

end CKN
