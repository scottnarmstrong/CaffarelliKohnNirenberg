-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.FiniteMomentum
import CKN.Setting.Examples.ShearCounterexample.FactorIBP
import CKN.Setting.Examples.ShearCounterexample.TestSupport
import CKN.Foundation.Parabolic.Topology
import CKN.Statements.TimePartial
import CKN.Statements.SpatialSecondPartial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Finite-scale momentum integration by parts for the shear. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory CKN.Foundation.Parabolic Finset
namespace CKN

private def liftScalar (g : Vec3 × ℝ → ℝ) : ParabolicPoint → ℝ :=
  fun z => g (parabolicHomeomorph z)

private def prodTimePartial (g : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  timePartial (liftScalar g) (parabolicHomeomorph.symm z)

private def prodSpatialPartial (g : Vec3 × ℝ → ℝ) (i : Fin 3)
    (z : Vec3 × ℝ) : ℝ :=
  spatialPartial (liftScalar g) i (parabolicHomeomorph.symm z)

private def prodSpatialSecondPartial (g : Vec3 × ℝ → ℝ) (i j : Fin 3)
    (z : Vec3 × ℝ) : ℝ :=
  prodSpatialPartial (fun w => prodSpatialPartial g i w) j z

private theorem timePartial_bridge (g : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) :
    timePartial (show ParabolicPoint → ℝ from g) z = prodTimePartial g z := by
  rfl

private theorem spatialPartial_bridge (g : Vec3 × ℝ → ℝ) (i : Fin 3)
    (z : Vec3 × ℝ) :
    spatialPartial (show ParabolicPoint → ℝ from g) i z = prodSpatialPartial g i z := by
  rfl

private theorem spatialSecondPartial_bridge (g : Vec3 × ℝ → ℝ) (i j : Fin 3)
    (z : Vec3 × ℝ) :
    spatialSecondPartial (show ParabolicPoint → ℝ from g) i j z =
      prodSpatialSecondPartial g i j z := by
  rfl

private theorem prodSpatialSecond_bridge (g : Vec3 × ℝ → ℝ) (i j : Fin 3)
    (z : Vec3 × ℝ) :
    prodSpatialSecondPartial g i j z =
      spatialSecondPartial (liftScalar g) i j (parabolicHomeomorph.symm z) := by
  unfold prodSpatialSecondPartial prodSpatialPartial
  have hinner :
      liftScalar (fun w : Vec3 × ℝ =>
        spatialPartial (liftScalar g) i (parabolicHomeomorph.symm w)) =
      (fun w : ParabolicPoint => spatialPartial (liftScalar g) i w) := by
    funext w
    simp [liftScalar, parabolicHomeomorph]
  rw [hinner]
  rfl

private theorem integrable_mul_compact
    {F G : Vec3 × ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hGc : HasCompactSupport G) : Integrable (fun z => F z * G z) volume :=
  (hF.mul hG).integrable_of_hasCompactSupport (hGc.mul_left)

theorem shearCounterexample_momentum_finite (N : ℕ)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    ∫ z : Vec3 × ℝ,
      (-(∑ i : Fin 3, shearCounterexampleVelocityPartial N z i *
          timePartial (fun w => φ w i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
            shearCounterexampleVelocityPartial N z i *
              shearCounterexampleVelocityPartial N z j *
                spatialPartial (fun w => φ w i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            shearCounterexampleDuPartial N z i j *
              spatialPartial (fun w => φ w i) j z
        - ∑ i : Fin 3, shearCounterexampleForcePartial N z i * φ z i) ∂volume = 0 := by
  let W : Vec3 × ℝ → ℝ := fun z => shearFullScalarPartial N z
  let F : Vec3 × ℝ → ℝ := fun z => shearFullForcePartial N z
  let P : Vec3 × ℝ → ℝ := fun z => φ z 2
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := shearFullScalarPartial_contDiff N
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := component_contDiff hφ 2
  have hPc : HasCompactSupport P := component_hasCompactSupport hφc 2
  have hF : Continuous F := by
    have hh : Continuous (fun z : Vec3 × ℝ =>
        shearFullForcePartial N (parabolicHomeomorph.symm z)) :=
      (shearFullForcePartial_continuous N).comp parabolicHomeomorph.continuous_invFun
    have heq : F = fun z : Vec3 × ℝ =>
        shearFullForcePartial N (parabolicHomeomorph.symm z) := by
      funext z
      rfl
    rw [heq]
    exact hh
  have hTimeP : ContDiff ℝ (⊤ : ℕ∞) (prodTimePartial P) := by
    have hh := timePartial_contDiff hP
    have heq : prodTimePartial P = fun z : Vec3 × ℝ =>
        timePartial (show ParabolicPoint → ℝ from P) z := by
      funext z
      exact (timePartial_bridge P z).symm
    rw [heq]
    exact hh
  have hSpaceP (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (prodSpatialPartial P i) := by
    have hh := spatialPartial_contDiff hP i
    have heq : prodSpatialPartial P i = fun z : Vec3 × ℝ =>
        spatialPartial (show ParabolicPoint → ℝ from P) i z := by
      funext z
      exact (spatialPartial_bridge P i z).symm
    rw [heq]
    exact hh
  have hTimePc : HasCompactSupport (prodTimePartial P) := by
    have hh := timePartial_hasCompactSupport hP hPc
    have heq : prodTimePartial P = fun z : Vec3 × ℝ =>
        timePartial (show ParabolicPoint → ℝ from P) z := by
      funext z
      exact (timePartial_bridge P z).symm
    rw [heq]
    exact hh
  have hSpacePc (i : Fin 3) : HasCompactSupport (prodSpatialPartial P i) := by
    have hh := spatialPartial_hasCompactSupport hP hPc i
    have heq : prodSpatialPartial P i = fun z : Vec3 × ℝ =>
        spatialPartial (show ParabolicPoint → ℝ from P) i z := by
      funext z
      exact (spatialPartial_bridge P i z).symm
    rw [heq]
    exact hh
  have hW2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => W z ^ 2) := hW.pow 2
  have hW0 : ContDiff ℝ (⊤ : ℕ∞) (prodSpatialPartial W 0) := by
    have hh := spatialPartial_contDiff hW 0
    have heq : prodSpatialPartial W 0 = fun z : Vec3 × ℝ =>
        spatialPartial (show ParabolicPoint → ℝ from W) 0 z := by
      funext z
      exact (spatialPartial_bridge W 0 z).symm
    rw [heq]
    exact hh
  have hW1 : ContDiff ℝ (⊤ : ℕ∞) (prodSpatialPartial W 1) := by
    have hh := spatialPartial_contDiff hW 1
    have heq : prodSpatialPartial W 1 = fun z : Vec3 × ℝ =>
        spatialPartial (show ParabolicPoint → ℝ from W) 1 z := by
      funext z
      exact (spatialPartial_bridge W 1 z).symm
    rw [heq]
    exact hh
  have hW00 : ContDiff ℝ (⊤ : ℕ∞) (prodSpatialSecondPartial W 0 0) := by
    have hh := spatialPartial_contDiff (spatialPartial_contDiff hW 0) 0
    have heq : prodSpatialSecondPartial W 0 0 = fun z : Vec3 × ℝ =>
        spatialSecondPartial (show ParabolicPoint → ℝ from W) 0 0 z := by
      funext z
      exact (spatialSecondPartial_bridge W 0 0 z).symm
    rw [heq]
    exact hh
  have hW11 : ContDiff ℝ (⊤ : ℕ∞) (prodSpatialSecondPartial W 1 1) := by
    have hh := spatialPartial_contDiff (spatialPartial_contDiff hW 1) 1
    have heq : prodSpatialSecondPartial W 1 1 = fun z : Vec3 × ℝ =>
        spatialSecondPartial (show ParabolicPoint → ℝ from W) 1 1 z := by
      funext z
      exact (spatialSecondPartial_bridge W 1 1 z).symm
    rw [heq]
    exact hh
  have hWt : ContDiff ℝ (⊤ : ℕ∞) (prodTimePartial W) := by
    have hh := timePartial_contDiff hW
    have heq : prodTimePartial W = fun z : Vec3 × ℝ =>
        timePartial (show ParabolicPoint → ℝ from W) z := by
      funext z
      exact (timePartial_bridge W z).symm
    rw [heq]
    exact hh
  have hW2P : Integrable
      (fun z => prodSpatialPartial (fun w => W w ^ 2) 2 z * P z) volume :=
    integrable_mul_compact (spatialPartial_contDiff hW2 2).continuous
      hP.continuous hPc
  have hiTime : Integrable (fun z => W z * prodTimePartial P z) volume :=
    integrable_mul_compact hW.continuous hTimeP.continuous hTimePc
  have hiTime' : Integrable (fun z => prodTimePartial W z * P z) volume :=
    integrable_mul_compact hWt.continuous hP.continuous hPc
  have hiNonlin : Integrable (fun z => W z ^ 2 * prodSpatialPartial P 2 z) volume :=
    integrable_mul_compact hW2.continuous (hSpaceP 2).continuous (hSpacePc 2)
  have hiDiff0 : Integrable
      (fun z => prodSpatialPartial W 0 z * prodSpatialPartial P 0 z) volume :=
    integrable_mul_compact (hW0.continuous) (hSpaceP 0).continuous (hSpacePc 0)
  have hiDiff1 : Integrable
      (fun z => prodSpatialPartial W 1 z * prodSpatialPartial P 1 z) volume :=
    integrable_mul_compact (hW1.continuous) (hSpaceP 1).continuous (hSpacePc 1)
  have hiW00P : Integrable (fun z => prodSpatialSecondPartial W 0 0 z * P z) volume :=
    integrable_mul_compact hW00.continuous hP.continuous hPc
  have hiW11P : Integrable (fun z => prodSpatialSecondPartial W 1 1 z * P z) volume :=
    integrable_mul_compact hW11.continuous hP.continuous hPc
  have hiForce : Integrable (fun z => F z * P z) volume :=
    integrable_mul_compact hF hP.continuous hPc
  have hIBPt := integral_mul_timePartial_eq_neg_timePartial_mul hW hP hPc
  have hIBPnl := integral_mul_spatialPartial_eq_neg_spatialPartial_mul hW2 hP hPc 2
  have hIBP0 := integral_mul_spatialPartial_eq_neg_spatialPartial_mul
    (spatialPartial_contDiff hW 0) hP hPc 0
  have hIBP1 := integral_mul_spatialPartial_eq_neg_spatialPartial_mul
    (spatialPartial_contDiff hW 1) hP hPc 1
  have hIBPt' : ∫ z : Vec3 × ℝ, W z * prodTimePartial P z ∂volume =
      -∫ z : Vec3 × ℝ, prodTimePartial W z * P z ∂volume := by
    simpa only [timePartial_bridge] using hIBPt
  have hIBPnl' : ∫ z : Vec3 × ℝ, W z ^ 2 * prodSpatialPartial P 2 z ∂volume =
      -∫ z : Vec3 × ℝ, prodSpatialPartial (fun w => W w ^ 2) 2 z * P z ∂volume := by
    simpa only [spatialPartial_bridge] using hIBPnl
  have hIBP0' : ∫ z : Vec3 × ℝ, prodSpatialPartial W 0 z *
      prodSpatialPartial P 0 z ∂volume =
      -∫ z : Vec3 × ℝ, prodSpatialSecondPartial W 0 0 z * P z ∂volume := by
    simpa only [spatialPartial_bridge, prodSpatialSecondPartial] using hIBP0
  have hIBP1' : ∫ z : Vec3 × ℝ, prodSpatialPartial W 1 z *
      prodSpatialPartial P 1 z ∂volume =
      -∫ z : Vec3 × ℝ, prodSpatialSecondPartial W 1 1 z * P z ∂volume := by
    simpa only [spatialPartial_bridge, prodSpatialSecondPartial] using hIBP1
  have hzero : ∀ z : Vec3 × ℝ,
      prodSpatialPartial (fun w => W w ^ 2) 2 z = 0 := by
    intro z
    change spatialPartial
      (show ParabolicPoint → ℝ from fun w : ParabolicPoint =>
        shearFullScalarPartial N w ^ 2) 2 (parabolicHomeomorph.symm z) = 0
    exact shearScalarSquared_spatialPartial_zero N (parabolicHomeomorph.symm z)
  have hzeroInt : ∫ z : Vec3 × ℝ,
      prodSpatialPartial (fun w => W w ^ 2) 2 z * P z ∂volume = 0 := by
    have heq : (fun z : Vec3 × ℝ =>
        prodSpatialPartial (fun w => W w ^ 2) 2 z * P z) = fun _ => 0 := by
      funext z
      rw [hzero z]
      simp
    rw [heq, integral_zero]
  have hnonlinzero : ∫ z : Vec3 × ℝ,
      W z ^ 2 * prodSpatialPartial P 2 z ∂volume = 0 := by
    calc
      _ = -∫ z : Vec3 × ℝ,
          prodSpatialPartial (fun w => W w ^ 2) 2 z * P z ∂volume := hIBPnl'
      _ = 0 := by rw [hzeroInt]; simp
  have hheat : ∀ z : Vec3 × ℝ,
      prodTimePartial W z - prodSpatialSecondPartial W 0 0 z -
        prodSpatialSecondPartial W 1 1 z - F z = 0 := by
    intro z
    have hh := shearFullScalarPartial_heat_identity N (parabolicHomeomorph.symm z)
    have hthird : spatialSecondPartial
        (show ParabolicPoint → ℝ from shearFullScalarPartial N) 2 2
          (parabolicHomeomorph.symm z) = 0 := by
      unfold spatialSecondPartial
      have hfirst : (fun w : ParabolicPoint =>
          spatialPartial (show ParabolicPoint → ℝ from shearFullScalarPartial N) 2 w) =
          fun _ => 0 := by
        funext w
        simpa using shearFullScalarPartial_spatialPartial N w 2
      rw [hfirst]
      simp [spatialPartial]
    have hthird' : spatialSecondPartial
        (show ParabolicPoint → ℝ from shearFullScalarPartial N)
        (Fin.succ (Fin.succ 0)) (Fin.succ (Fin.succ 0)) (parabolicHomeomorph.symm z) = 0 := by
      simpa using hthird
    have hsum : ∑ i : Fin 3, spatialSecondPartial
        (show ParabolicPoint → ℝ from shearFullScalarPartial N) i i
          (parabolicHomeomorph.symm z) =
        spatialSecondPartial (show ParabolicPoint → ℝ from shearFullScalarPartial N)
          0 0 (parabolicHomeomorph.symm z) + spatialSecondPartial
            (show ParabolicPoint → ℝ from shearFullScalarPartial N) 1 1
              (parabolicHomeomorph.symm z) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      rw [hthird']
      simp
    rw [hsum] at hh
    have hWlift : liftScalar W = shearFullScalarPartial N := by
      funext w
      cases w with
      | mk x t => rfl
    have hWtEq : prodTimePartial W z = timePartial
        (show ParabolicPoint → ℝ from shearFullScalarPartial N)
          (parabolicHomeomorph.symm z) := by
      unfold prodTimePartial
      rw [hWlift]
    have hW00Eq : prodSpatialSecondPartial W 0 0 z =
        spatialSecondPartial (show ParabolicPoint → ℝ from shearFullScalarPartial N)
          0 0 (parabolicHomeomorph.symm z) := by
      rw [prodSpatialSecond_bridge, hWlift]
    have hW11Eq : prodSpatialSecondPartial W 1 1 z =
        spatialSecondPartial (show ParabolicPoint → ℝ from shearFullScalarPartial N)
          1 1 (parabolicHomeomorph.symm z) := by
      rw [prodSpatialSecond_bridge, hWlift]
    have hForceEq : F z = shearFullForcePartial N (parabolicHomeomorph.symm z) := by
      change shearFullForcePartial N z = shearFullForcePartial N (parabolicHomeomorph.symm z)
      cases z with
      | mk x t => rfl
    have hh' : prodTimePartial W z -
        (prodSpatialSecondPartial W 0 0 z + prodSpatialSecondPartial W 1 1 z) = F z := by
      rw [hWtEq, hW00Eq, hW11Eq, hForceEq]
      exact hh
    linarith only [hh']
  have hResidualIntegral : ∫ z : Vec3 × ℝ,
      (prodTimePartial W z - prodSpatialSecondPartial W 0 0 z -
        prodSpatialSecondPartial W 1 1 z - F z) * P z ∂volume = 0 := by
    have heq : (fun z : Vec3 × ℝ =>
        (prodTimePartial W z - prodSpatialSecondPartial W 0 0 z -
          prodSpatialSecondPartial W 1 1 z - F z) * P z) = fun _ => 0 := by
      funext z
      rw [hheat z]
      simp
    rw [heq, integral_zero]
  have hAlgebra :
      (∫ z : Vec3 × ℝ, prodTimePartial W z * P z ∂volume) -
       (∫ z : Vec3 × ℝ, prodSpatialSecondPartial W 0 0 z * P z ∂volume) -
       (∫ z : Vec3 × ℝ, prodSpatialSecondPartial W 1 1 z * P z ∂volume) -
       (∫ z : Vec3 × ℝ, F z * P z ∂volume) = 0 := by
    have hsum : ∫ z : Vec3 × ℝ,
        (prodTimePartial W z - prodSpatialSecondPartial W 0 0 z -
          prodSpatialSecondPartial W 1 1 z - F z) * P z ∂volume =
        (∫ z : Vec3 × ℝ, prodTimePartial W z * P z ∂volume) -
         (∫ z : Vec3 × ℝ, prodSpatialSecondPartial W 0 0 z * P z ∂volume) -
         (∫ z : Vec3 × ℝ, prodSpatialSecondPartial W 1 1 z * P z ∂volume) -
         (∫ z : Vec3 × ℝ, F z * P z ∂volume) := by
      have hiA : Integrable (fun z : Vec3 × ℝ => prodTimePartial W z * P z -
          prodSpatialSecondPartial W 0 0 z * P z) := hiTime'.sub hiW00P
      have hiB : Integrable (fun z : Vec3 × ℝ =>
          (prodTimePartial W z * P z - prodSpatialSecondPartial W 0 0 z * P z) -
            prodSpatialSecondPartial W 1 1 z * P z) := hiA.sub hiW11P
      have hiC : Integrable (fun z : Vec3 × ℝ =>
          ((prodTimePartial W z * P z - prodSpatialSecondPartial W 0 0 z * P z) -
            prodSpatialSecondPartial W 1 1 z * P z) - F z * P z) := hiB.sub hiForce
      calc
        _ = ∫ z : Vec3 × ℝ,
            ((prodTimePartial W z * P z - prodSpatialSecondPartial W 0 0 z * P z) -
              prodSpatialSecondPartial W 1 1 z * P z) - F z * P z ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with z
          ring
        _ = _ := by
          rw [integral_sub hiB hiForce, integral_sub hiA hiW11P,
            integral_sub hiTime' hiW00P]
    calc
      _ = ∫ z : Vec3 × ℝ,
          (prodTimePartial W z - prodSpatialSecondPartial W 0 0 z -
            prodSpatialSecondPartial W 1 1 z - F z) * P z ∂volume := hsum.symm
      _ = 0 := hResidualIntegral
  have hStart : ∫ z : Vec3 × ℝ,
      -(W z * prodTimePartial P z) - W z ^ 2 * prodSpatialPartial P 2 z +
        prodSpatialPartial W 0 z * prodSpatialPartial P 0 z +
        prodSpatialPartial W 1 z * prodSpatialPartial P 1 z - F z * P z
        ∂volume = 0 := by
    have hiStartA : Integrable (fun z : Vec3 × ℝ =>
        -(W z * prodTimePartial P z) - W z ^ 2 * prodSpatialPartial P 2 z) :=
      (hiTime.neg).sub hiNonlin
    have hiStartB : Integrable (fun z : Vec3 × ℝ =>
        (-(W z * prodTimePartial P z) - W z ^ 2 * prodSpatialPartial P 2 z) +
          prodSpatialPartial W 0 z * prodSpatialPartial P 0 z) := hiStartA.add hiDiff0
    have hiStartC : Integrable (fun z : Vec3 × ℝ =>
        ((-(W z * prodTimePartial P z) - W z ^ 2 * prodSpatialPartial P 2 z) +
          prodSpatialPartial W 0 z * prodSpatialPartial P 0 z) +
          prodSpatialPartial W 1 z * prodSpatialPartial P 1 z) := hiStartB.add hiDiff1
    have hC : ∫ z : Vec3 × ℝ,
        ((-(W z * prodTimePartial P z) - W z ^ 2 * prodSpatialPartial P 2 z) +
          prodSpatialPartial W 0 z * prodSpatialPartial P 0 z) +
          prodSpatialPartial W 1 z * prodSpatialPartial P 1 z ∂volume =
        (∫ z : Vec3 × ℝ, -(W z * prodTimePartial P z) -
          W z ^ 2 * prodSpatialPartial P 2 z ∂volume) +
          (∫ z : Vec3 × ℝ, prodSpatialPartial W 0 z *
            prodSpatialPartial P 0 z ∂volume) +
      ∫ z : Vec3 × ℝ, prodSpatialPartial W 1 z *
            prodSpatialPartial P 1 z ∂volume := by
      rw [integral_add hiStartB hiDiff1, integral_add hiStartA hiDiff0]
    calc
      _ = ∫ z : Vec3 × ℝ,
          (((-(W z * prodTimePartial P z) - W z ^ 2 * prodSpatialPartial P 2 z) +
            prodSpatialPartial W 0 z * prodSpatialPartial P 0 z) +
            prodSpatialPartial W 1 z * prodSpatialPartial P 1 z) - F z * P z
          ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = ((∫ z : Vec3 × ℝ, -(W z * prodTimePartial P z) -
            W z ^ 2 * prodSpatialPartial P 2 z ∂volume) +
          ∫ z : Vec3 × ℝ, prodSpatialPartial W 0 z * prodSpatialPartial P 0 z ∂volume) +
          ∫ z : Vec3 × ℝ, prodSpatialPartial W 1 z * prodSpatialPartial P 1 z ∂volume -
          ∫ z : Vec3 × ℝ, F z * P z ∂volume := by
        have heq : (fun z : Vec3 × ℝ =>
            (((-(W z * prodTimePartial P z) - W z ^ 2 * prodSpatialPartial P 2 z) +
              prodSpatialPartial W 0 z * prodSpatialPartial P 0 z) +
              prodSpatialPartial W 1 z * prodSpatialPartial P 1 z) - F z * P z) =
            fun z => (((-(W z * prodTimePartial P z) - W z ^ 2 *
              prodSpatialPartial P 2 z) + prodSpatialPartial W 0 z *
              prodSpatialPartial P 0 z) + prodSpatialPartial W 1 z *
              prodSpatialPartial P 1 z) - F z * P z := by
          funext z
          rfl
        rw [heq, integral_sub hiStartC hiForce]
        rw [hC]
      _ = 0 := by
        have hA : ∫ z : Vec3 × ℝ,
            -(W z * prodTimePartial P z) -
              W z ^ 2 * prodSpatialPartial P 2 z ∂volume =
            -(∫ z : Vec3 × ℝ, W z * prodTimePartial P z ∂volume) -
              ∫ z : Vec3 × ℝ, W z ^ 2 * prodSpatialPartial P 2 z ∂volume := by
          calc
            _ = (∫ z : Vec3 × ℝ, -(W z * prodTimePartial P z) ∂volume) -
                ∫ z : Vec3 × ℝ, W z ^ 2 * prodSpatialPartial P 2 z ∂volume :=
              integral_sub hiTime.neg hiNonlin
            _ = _ := by rw [integral_neg]
        rw [hA]
        rw [hIBPt', hnonlinzero, hIBP0', hIBP1']
        linarith only [hAlgebra]
  calc
    _ = ∫ z : Vec3 × ℝ,
        -(W z * prodTimePartial P z) - W z ^ 2 * prodSpatialPartial P 2 z +
          prodSpatialPartial W 0 z * prodSpatialPartial P 0 z +
          prodSpatialPartial W 1 z * prodSpatialPartial P 1 z - F z * P z
        ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      have hsimp := shearFiniteMomentumResidual_simplify N φ z
      have hPt : prodTimePartial P z = timePartial (fun w => φ w 2) z := by
        unfold prodTimePartial liftScalar
        cases z with
        | mk x t => rfl
      have hP0 : prodSpatialPartial P 0 z = spatialPartial (fun w => φ w 2) 0 z := by
        unfold prodSpatialPartial liftScalar
        cases z with
        | mk x t => rfl
      have hP1 : prodSpatialPartial P 1 z = spatialPartial (fun w => φ w 2) 1 z := by
        unfold prodSpatialPartial liftScalar
        cases z with
        | mk x t => rfl
      have hP2 : prodSpatialPartial P 2 z = spatialPartial (fun w => φ w 2) 2 z := by
        unfold prodSpatialPartial liftScalar
        cases z with
        | mk x t => rfl
      have hW0 : prodSpatialPartial W 0 z = shearFullGradientPartial 0 N z := by
        rw [← spatialPartial_bridge W 0 z]
        simpa [W] using shearFullScalarPartial_spatialPartial N z 0
      have hW1 : prodSpatialPartial W 1 z = shearFullGradientPartial 1 N z := by
        rw [← spatialPartial_bridge W 1 z]
        simpa [W] using shearFullScalarPartial_spatialPartial N z 1
      have hred :
          -(shearFullScalarPartial N z * timePartial (fun w => φ w 2) z) -
            shearFullScalarPartial N z ^ 2 * spatialPartial (fun w => φ w 2) 2 z +
            (shearFullGradientPartial 0 N z * spatialPartial (fun w => φ w 2) 0 z +
              shearFullGradientPartial 1 N z * spatialPartial (fun w => φ w 2) 1 z) -
            shearFullForcePartial N z * φ z 2 =
          -(W z * prodTimePartial P z) - W z ^ 2 * prodSpatialPartial P 2 z +
            prodSpatialPartial W 0 z * prodSpatialPartial P 0 z +
            prodSpatialPartial W 1 z * prodSpatialPartial P 1 z - F z * P z := by
        rw [← hPt, ← hP0, ← hP1, ← hP2, ← hW0, ← hW1]
        simp only [P, W, F]
        ring
      have hdu :
          ∑ j : Fin 3, shearCounterexampleDuPartial N z 2 j *
            spatialPartial (fun w => φ w 2) j z =
            shearFullGradientPartial 0 N z * spatialPartial (fun w => φ w 2) 0 z +
              shearFullGradientPartial 1 N z * spatialPartial (fun w => φ w 2) 1 z := by
        simp [shearCounterexampleDuPartial, Fin.sum_univ_succ]
      calc
        _ = -(shearFullScalarPartial N z * timePartial (fun w => φ w 2) z) -
              shearFullScalarPartial N z ^ 2 * spatialPartial (fun w => φ w 2) 2 z +
              (∑ j : Fin 3, shearCounterexampleDuPartial N z 2 j *
                spatialPartial (fun w => φ w 2) j z) -
              shearFullForcePartial N z * φ z 2 := by
          exact hsimp
        _ = -(shearFullScalarPartial N z * timePartial (fun w => φ w 2) z) -
              shearFullScalarPartial N z ^ 2 * spatialPartial (fun w => φ w 2) 2 z +
              (shearFullGradientPartial 0 N z * spatialPartial (fun w => φ w 2) 0 z +
                shearFullGradientPartial 1 N z * spatialPartial (fun w => φ w 2) 1 z) -
              shearFullForcePartial N z * φ z 2 := by
          rw [hdu]
        _ = _ := hred
    _ = 0 := hStart

end CKN
