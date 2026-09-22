-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.


import CKN.Setting.Examples.ShearCounterexample.SWSLocalData
import CKN.Setting.Examples.ShearCounterexample.LocalTestBox
import CKN.Setting.Examples.ShearCounterexampleDivergenceLimit
import CKN.Setting.Examples.ShearCounterexampleMomentumLimit
import CKN.Setting.Examples.ShearCounterexampleLEILimit
import CKN.Statements.SpatialPartial
import CKN.Statements.SpatialSecondPartial
import CKN.Statements.TimePartial

/-! # A rough shear field satisfying the suitable weak-solution clauses at exponent two. -/


set_option autoImplicit false
noncomputable section

open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CKN

theorem shearCounterexample_suitableAtExponent :
    IsSuitableWeakSolutionAtExponent (vec3Ball 0 1) (Ioo (-1) 1) 2
      shearCounterexampleVelocity shearCounterexampleDu
      shearCounterexamplePressure shearCounterexampleForce := by
  have hΩ : IsOpen (vec3Ball (0 : Vec3) 1) := isOpen_vec3Ball _ _
  have hI : IsOpen (Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hOrd : OrdConnected (Ioo (-1 : ℝ) 1) := ordConnected_Ioo
  refine ⟨hΩ, hI, hOrd, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω' J hbox
    exact (shearCounterexample_localData_atBox hbox).1
  · intro Ω' J hbox
    rcases shearCounterexample_localData_atBox hbox with
      ⟨_, hu, hDu, hp, hf, hsup, henergy, hpLp, hfLp, hweak⟩
    have hfLp' : MemLp shearCounterexampleForce (ENNReal.ofReal (2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) := by
      convert hfLp using 1; norm_num
    exact ⟨hu, hDu, hp, hf, hsup, henergy, hpLp, hfLp', hweak⟩
  · intro ψ hψ
    rcases hψ with ⟨hψd, hψc, hψsub⟩
    have hKsub : tsupport ψ ⊆
        vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 1 := by
      simpa [spaceTimeSet] using hψsub
    obtain ⟨Ω', J, hbox, hK, hS⟩ :=
      shear_localBox_of_compact_tsupport hψc hKsub
    have hψsubLocal : tsupport ψ ⊆ spaceTimeSet Ω' J := by
      simpa [spaceTimeSet] using hK
    have hdiv := shearDivergenceResidual_integral_zero_of_local_support
      hbox hS ψ hψd hψc hψsubLocal
    have hdivInt := hdiv.1.mono_measure
      (Measure.restrict_mono hψsubLocal le_rfl)
    have htsψ := tsupport_parabolic_eq_product_test ψ
    have hdivIntPar : IntegrableOn
        (show ParabolicPoint → ℝ from shearDivergenceResidual ψ)
        (@tsupport ParabolicPoint ℝ Real.instZero
          PseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (show ParabolicPoint → ℝ from ψ)) (volume : Measure ParabolicPoint) := by
      rw [htsψ, CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
      exact hdivInt
    have hEqPar : (fun z : ParabolicPoint =>
        ∑ i : Fin 3, shearCounterexampleVelocity z i *
          spatialPartial (show ParabolicPoint → ℝ from ψ) i z) =
        (show ParabolicPoint → ℝ from shearDivergenceResidual ψ) := by
      funext z
      simp [shearDivergenceResidual, shearCounterexampleVelocity]
    have hMeas : MeasurableSet
        (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 1) :=
      (vec3Ball_measurable (0 : Vec3) 1).prod measurableSet_Ioo
    have hset := setIntegral_eq_integral_of_tsupport_subset
      (μ := (volume : Measure (Vec3 × ℝ))) hMeas
      ((shearDivergenceResidual_tsupport_subset ψ hψd).trans hψsub)
    refine ⟨?_, ?_⟩
    · rw [hEqPar]
      exact hdivIntPar
    · calc
        ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1),
            ∑ i : Fin 3, shearCounterexampleVelocity z i *
              spatialPartial (show ParabolicPoint → ℝ from ψ) i z =
          ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1),
            (show ParabolicPoint → ℝ from shearDivergenceResidual ψ) z := by
              rw [hEqPar]
        _ = ∫ z in (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 1),
              shearDivergenceResidual ψ z :=
          setIntegral_parabolic_eq_product_test (shearDivergenceResidual ψ)
        _ = ∫ z : Vec3 × ℝ, shearDivergenceResidual ψ z := hset
        _ = 0 := hdiv.2
  · intro φ hφ
    rcases hφ with ⟨hφd, hφc, hφsub⟩
    have hKsub : tsupport φ ⊆
        vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 1 := by
      simpa [spaceTimeSet] using hφsub
    obtain ⟨Ω', J, hbox, hK, hS⟩ :=
      shear_localBox_of_compact_tsupport hφc hKsub
    have hφsubLocal : tsupport φ ⊆ spaceTimeSet Ω' J := by
      simpa [spaceTimeSet] using hK
    have hMomInt := fullMomentumResidual_integrable_on_localBox
      hbox φ hφd hφc
    have hMomZero := fullMomentumResidual_integral_zero_of_local_support
      hbox hS φ hφd hφc hφsubLocal
    have hMomInt' := hMomInt.mono_measure
      (Measure.restrict_mono hφsubLocal le_rfl)
    have htsφ := tsupport_parabolic_eq_product_vec φ
    have hMomIntPar : IntegrableOn
        (show ParabolicPoint → ℝ from fullMomentumResidual φ)
        (@tsupport ParabolicPoint Vec3 (inferInstance : Zero Vec3)
          PseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (show ParabolicPoint → Vec3 from φ))
        (volume : Measure ParabolicPoint) := by
      rw [htsφ, CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
      exact hMomInt'
    have hEqPar : (fun z : ParabolicPoint =>
        (-(∑ i : Fin 3, shearCounterexampleVelocity z i *
            timePartial (fun w : ParabolicPoint =>
              φ (show Vec3 × ℝ from w) i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              shearCounterexampleVelocity z i * shearCounterexampleVelocity z j *
                spatialPartial (fun w : ParabolicPoint =>
                  φ (show Vec3 × ℝ from w) i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              (shearCounterexampleDu z i j) * spatialPartial
                (fun w : ParabolicPoint => φ (show Vec3 × ℝ from w) i) j z
          - shearCounterexamplePressure z *
              ∑ i : Fin 3, spatialPartial
                (fun w : ParabolicPoint => φ (show Vec3 × ℝ from w) i) i z
          - ∑ i : Fin 3, shearCounterexampleForce z i *
              φ (show Vec3 × ℝ from z) i) =
        (show ParabolicPoint → ℝ from fullMomentumResidual φ) := by
      funext z
      simp [fullMomentumResidual, shearCounterexampleVelocity,
        shearCounterexampleDu, shearCounterexamplePressure,
        shearCounterexampleForce, Fin.sum_univ_succ]
      ring
    have hMeas : MeasurableSet
        (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 1) :=
      (vec3Ball_measurable (0 : Vec3) 1).prod measurableSet_Ioo
    have hset := setIntegral_eq_integral_of_tsupport_subset
      (μ := (volume : Measure (Vec3 × ℝ))) hMeas
      ((fullMomentumResidual_tsupport_subset φ hφd).trans hφsub)
    refine ⟨?_, ?_⟩
    · rw [hEqPar]
      exact hMomIntPar
    · calc
        ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1),
            (-(∑ i : Fin 3, shearCounterexampleVelocity z i *
                timePartial (fun w : ParabolicPoint =>
                  φ (show Vec3 × ℝ from w) i) z))
              - ∑ i : Fin 3, ∑ j : Fin 3,
                  shearCounterexampleVelocity z i * shearCounterexampleVelocity z j *
                    spatialPartial (fun w : ParabolicPoint =>
                      φ (show Vec3 × ℝ from w) i) j z
              + ∑ i : Fin 3, ∑ j : Fin 3,
                  shearCounterexampleDu z i j * spatialPartial
                    (fun w : ParabolicPoint => φ (show Vec3 × ℝ from w) i) j z
              - shearCounterexamplePressure z *
                  ∑ i : Fin 3, spatialPartial
                    (fun w : ParabolicPoint => φ (show Vec3 × ℝ from w) i) i z
              - ∑ i : Fin 3, shearCounterexampleForce z i *
                  φ (show Vec3 × ℝ from z) i =
          ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 1),
            (show ParabolicPoint → ℝ from fullMomentumResidual φ) z := by
              rw [hEqPar]
        _ = ∫ z in (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 1),
              fullMomentumResidual φ z :=
          setIntegral_parabolic_eq_product_test (fullMomentumResidual φ)
        _ = ∫ z : Vec3 × ℝ, fullMomentumResidual φ z := hset
        _ = 0 := hMomZero
  · intro ψ hψ hψnonneg
    rcases hψ with ⟨hψd, hψc, hψsub⟩
    exact shearCounterexample_localEnergyClause ψ hψd hψc hψnonneg hψsub

end CKN
