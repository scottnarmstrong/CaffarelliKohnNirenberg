-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.FiniteLEI
import CKN.Setting.Examples.ShearCounterexample.MomentumMajorant
import CKN.Setting.Examples.ShearCounterexample.LocalTestBox
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Algebraic and majorant identities for the local energy inequality. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory Filter
open scoped ENNReal Topology
namespace CKN

def shearLEILeft (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z * ψ z

def shearLEIRight (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 *
      (timePartial (show ParabolicPoint → ℝ from ψ) z +
        ∑ i : Fin 3, spatialSecondPartial
          (show ParabolicPoint → ℝ from ψ) i i z) +
    (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 *
      (∑ i : Fin 3, shearCounterexampleVelocity z i *
        spatialPartial (show ParabolicPoint → ℝ from ψ) i z) +
    2 * (∑ i : Fin 3,
      shearCounterexampleForce z i * shearCounterexampleVelocity z i) * ψ z

def shearLEILeftPartial (N : ℕ) (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  spatialGradientSq (shearCounterexampleVelocityPartial N)
    (shearCounterexampleDuPartial N) z * ψ z

def shearLEIRightPartial (N : ℕ) (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
      (timePartial (show ParabolicPoint → ℝ from ψ) z +
        ∑ i : Fin 3, spatialSecondPartial
          (show ParabolicPoint → ℝ from ψ) i i z) +
    (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
      (∑ i : Fin 3,
        shearCounterexampleVelocityPartial N z i *
          spatialPartial (show ParabolicPoint → ℝ from ψ) i z) +
    2 * (∑ i : Fin 3,
      shearCounterexampleForcePartial N z i *
        shearCounterexampleVelocityPartial N z i) * ψ z

theorem lei_zero_of_not_tsupport {g : Vec3 × ℝ → ℝ}
    {z : Vec3 × ℝ} (hz : z ∉ tsupport g) : g z = 0 := by
  by_contra hne
  exact hz (subset_tsupport g (Function.mem_support.mpr hne))

theorem lei_spatialPartial_tsupport_subset {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) :
    tsupport (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from g) i z) ⊆ tsupport g := by
  have heq : (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from g) i z) =
      fun z => fderiv ℝ g z (basisVec i, (0 : ℝ)) := by
    funext z
    exact spatialPartial_eq_joint_fderiv hg z i
  rw [heq]
  exact tsupport_fderiv_apply_subset ℝ (basisVec i, (0 : ℝ))

theorem lei_timePartial_tsupport_subset {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    tsupport (fun z : Vec3 × ℝ => timePartial
      (show ParabolicPoint → ℝ from g) z) ⊆ tsupport g := by
  have heq : (fun z : Vec3 × ℝ => timePartial
      (show ParabolicPoint → ℝ from g) z) =
      fun z => fderiv ℝ g z ((0 : Vec3), (1 : ℝ)) := by
    funext z
    exact timePartial_eq_joint_fderiv hg z
  rw [heq]
  exact tsupport_fderiv_apply_subset ℝ ((0 : Vec3), (1 : ℝ))

theorem lei_spatialPartial_zero_of_not_tsupport {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport g) :
    spatialPartial (show ParabolicPoint → ℝ from g) i z = 0 := by
  apply lei_zero_of_not_tsupport
  intro h
  exact hz ((lei_spatialPartial_tsupport_subset hg i) h)

theorem lei_timePartial_zero_of_not_tsupport {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport g) :
    timePartial (show ParabolicPoint → ℝ from g) z = 0 := by
  apply lei_zero_of_not_tsupport
  intro h
  exact hz ((lei_timePartial_tsupport_subset hg) h)

theorem lei_spatialSecond_zero_of_not_tsupport {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport g) :
    spatialSecondPartial (show ParabolicPoint → ℝ from g) i i z = 0 := by
  apply lei_spatialPartial_zero_of_not_tsupport
    (spatialPartial_contDiff hg i) i
  intro h
  exact hz ((lei_spatialPartial_tsupport_subset hg i) h)


private theorem shearCounterexampleVelocity_norm_sq (z : Vec3 × ℝ) :
    (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 =
      (shearFullScalar z) ^ 2 := by
  rw [vec3EuclideanNorm]
  have hsum : (∑ i : Fin 3, shearCounterexampleVelocity z i ^ 2) =
      shearFullScalar z ^ 2 := by
    simp [shearCounterexampleVelocity]
  rw [hsum, Real.sq_sqrt (sq_nonneg (shearFullScalar z))]

theorem shearCounterexampleDu_energy_eq (z : Vec3 × ℝ) :
    spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z =
      (shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2 := by
  simp [spatialGradientSq, shearCounterexampleDu, Fin.sum_univ_succ]

theorem lei_rhs_scalar_simplify (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) :
    shearLEIRight ψ z =
      (shearFullScalar z) ^ 2 *
        (timePartial (show ParabolicPoint → ℝ from ψ) z +
          ∑ i : Fin 3, spatialSecondPartial
            (show ParabolicPoint → ℝ from ψ) i i z) +
      (shearFullScalar z) ^ 3 * spatialPartial
        (show ParabolicPoint → ℝ from ψ) 2 z +
      2 * shearFullForceScalar z * shearFullScalar z * ψ z := by
  change (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 *
        (timePartial (show ParabolicPoint → ℝ from ψ) z +
          ∑ i : Fin 3, spatialSecondPartial
            (show ParabolicPoint → ℝ from ψ) i i z) +
      (vec3EuclideanNorm (shearCounterexampleVelocity z)) ^ 2 *
        (∑ i : Fin 3, shearCounterexampleVelocity z i *
          spatialPartial (show ParabolicPoint → ℝ from ψ) i z) +
      2 * (∑ i : Fin 3, shearCounterexampleForce z i *
        shearCounterexampleVelocity z i) * ψ z = _
  rw [shearCounterexampleVelocity_norm_sq]
  simp [shearCounterexampleVelocity, shearCounterexampleForce,
    Fin.sum_univ_succ]
  ring

theorem lei_rhs_partial_scalar_simplify (N : ℕ) (ψ : Vec3 × ℝ → ℝ)
    (z : Vec3 × ℝ) :
    shearLEIRightPartial N ψ z =
      (shearFullScalarPartial N z) ^ 2 *
        (timePartial (show ParabolicPoint → ℝ from ψ) z +
          ∑ i : Fin 3, spatialSecondPartial
            (show ParabolicPoint → ℝ from ψ) i i z) +
      (shearFullScalarPartial N z) ^ 3 * spatialPartial
        (show ParabolicPoint → ℝ from ψ) 2 z +
      2 * shearFullForcePartial N z * shearFullScalarPartial N z * ψ z := by
  change (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
        (timePartial (show ParabolicPoint → ℝ from ψ) z +
          ∑ i : Fin 3, spatialSecondPartial
            (show ParabolicPoint → ℝ from ψ) i i z) +
      (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
        (∑ i : Fin 3, shearCounterexampleVelocityPartial N z i *
          spatialPartial (show ParabolicPoint → ℝ from ψ) i z) +
      2 * (∑ i : Fin 3, shearCounterexampleForcePartial N z i *
        shearCounterexampleVelocityPartial N z i) * ψ z = _
  rw [shearCounterexampleVelocityPartial_norm_sq N (show ParabolicPoint from z)]
  simp [shearCounterexampleVelocityPartial, shearCounterexampleForcePartial,
    Fin.sum_univ_succ]
  ring

theorem lei_left_scalar_simplify (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) :
    shearLEILeft ψ z =
      ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) * ψ z := by
  change spatialGradientSq shearCounterexampleVelocity shearCounterexampleDu z * ψ z = _
  rw [shearCounterexampleDu_energy_eq (show ParabolicPoint from z)]

theorem lei_left_partial_scalar_simplify (N : ℕ) (ψ : Vec3 × ℝ → ℝ)
    (z : Vec3 × ℝ) :
    shearLEILeftPartial N ψ z =
      ((shearFullGradientPartial 0 N z) ^ 2 +
        (shearFullGradientPartial 1 N z) ^ 2) * ψ z := by
  change spatialGradientSq (shearCounterexampleVelocityPartial N)
    (shearCounterexampleDuPartial N) z * ψ z = _
  rw [shearCounterexampleDuPartial_energy_eq N (show ParabolicPoint from z)]

private theorem lei_testHeat_contDiff {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      timePartial (show ParabolicPoint → ℝ from ψ) z + ∑ i : Fin 3,
        spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      timePartial (show ParabolicPoint → ℝ from ψ) z) := timePartial_contDiff hψ
  have hs (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial
        (show ParabolicPoint → ℝ from ψ) i i z) :=
    spatialPartial_contDiff (spatialPartial_contDiff hψ i) i
  have hsum : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => ∑ i : Fin 3,
        spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z) := by
    exact ContDiff.sum (s := Finset.univ) (fun i hi => hs i)
  exact ht.add hsum

private theorem lei_testHeat_compact {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    HasCompactSupport (fun z : Vec3 × ℝ =>
      timePartial (show ParabolicPoint → ℝ from ψ) z + ∑ i : Fin 3,
        spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z) := by
  have ht : HasCompactSupport (fun z : Vec3 × ℝ =>
      timePartial (show ParabolicPoint → ℝ from ψ) z) := timePartial_hasCompactSupport hψ hψc
  have hs (i : Fin 3) : HasCompactSupport (fun z : Vec3 × ℝ =>
      spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z) :=
    spatialPartial_hasCompactSupport (spatialPartial_contDiff hψ i)
      (spatialPartial_hasCompactSupport hψ hψc i) i
  have hsum_eq : (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, spatialSecondPartial
        (show ParabolicPoint → ℝ from ψ) i i z) =
      (fun z => spatialSecondPartial (show ParabolicPoint → ℝ from ψ) 0 0 z) +
        ((fun z => spatialSecondPartial
          (show ParabolicPoint → ℝ from ψ) 1 1 z) +
         fun z => spatialSecondPartial (show ParabolicPoint → ℝ from ψ) 2 2 z) := by
    funext z
    simp [Fin.sum_univ_succ]
    rfl
  have hsum : HasCompactSupport (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, spatialSecondPartial
        (show ParabolicPoint → ℝ from ψ) i i z) := by
    rw [hsum_eq]
    exact (hs 0).add ((hs 1).add (hs 2))
  exact ht.add hsum

private theorem lei_testTop {g : Vec3 × ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    [hOpen : OpensMeasurableSpace (Vec3 × ℝ)]
    (μ : Measure (Vec3 × ℝ)) : MemLp g ⊤ μ :=
  @Continuous.memLp_top_of_hasCompactSupport ℝ _ (Vec3 × ℝ) _ _ hOpen g hg hgc μ

def shearLEIMajorant (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) * |ψ z| +
    |shearFullScalar z| ^ 2 *
      |timePartial (show ParabolicPoint → ℝ from ψ) z +
        ∑ i : Fin 3, spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z| +
    |shearFullScalar z| ^ 3 *
      |spatialPartial (show ParabolicPoint → ℝ from ψ) 2 z| +
    2 * |shearFullForceScalar z| * |shearFullScalar z| * |ψ z|

private theorem shearLEIMajorant_integrable_on_localBox_aux {Ω' : Set Vec3} {J : Set ℝ}
    [IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J))]
    [hOpen : OpensMeasurableSpace (Vec3 × ℝ)]
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
      Integrable (shearLEIMajorant ψ)
      (volume.restrict (spaceTimeSet Ω' J)) := by
  let μ := volume.restrict (spaceTimeSet Ω' J)
  have hψtop : MemLp ψ ⊤ μ :=
    lei_testTop hψ.continuous hψc μ
  let heat : Vec3 × ℝ → ℝ := fun z =>
    timePartial (show ParabolicPoint → ℝ from ψ) z +
      ∑ i : Fin 3, spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z
  have hheat : ContDiff ℝ (⊤ : ℕ∞) heat := lei_testHeat_contDiff hψ
  have hheatc : HasCompactSupport heat := lei_testHeat_compact hψ hψc
  have hheattop : MemLp heat ⊤ μ := lei_testTop hheat.continuous hheatc μ
  have hψ2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from ψ) 2 z) := spatialPartial_contDiff hψ 2
  have hψ2c : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from ψ) 2 z) := spatialPartial_hasCompactSupport hψ hψc 2
  have hψ2top : MemLp (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from ψ) 2 z) ⊤ μ :=
    lei_testTop hψ2.continuous hψ2c μ
  have hW3 : MemLp shearFullScalar 3 μ :=
    shearFullScalar_memLp_on_localBox shearReducedBumpSeries_memLp_three hbox
  have hW2 : MemLp shearFullScalar 2 μ := hW3.mono_exponent (by norm_num)
  have hWabs2 : MemLp (fun z => |shearFullScalar z|) 2 μ := hW2.abs
  have hWsq1 : MemLp (fun z => |shearFullScalar z| ^ 2) 1 μ := by
    have hmul : MemLp
        (fun z => |shearFullScalar z| * |shearFullScalar z|) 1 μ :=
      hWabs2.mul hWabs2
    convert hmul using 1
    ext z
    ring
  have hWcube1 : MemLp (fun z => |shearFullScalar z| ^ 3) 1 μ := by
    have hcube : Integrable (fun z => ‖shearFullScalar z‖ ^ 3) μ :=
      hW3.integrable_norm_pow (by norm_num : 3 ≠ 0)
    rw [memLp_one_iff_integrable]
    simpa only [Real.norm_eq_abs] using hcube
  have hG0 : MemLp (shearFullGradient 0) 2 μ :=
    shearFullGradient_memLp_on_localBox (i := 0) hbox
  have hG1 : MemLp (shearFullGradient 1) 2 μ :=
    shearFullGradient_memLp_on_localBox (i := 1) hbox
  have hG0sq : MemLp (fun z => (shearFullGradient 0 z) ^ 2) 1 μ := by
    have hmul : MemLp (fun z => |shearFullGradient 0 z| *
      |shearFullGradient 0 z|) 1 μ := hG0.abs.mul hG0.abs
    convert hmul using 1
    ext z
    calc
      shearFullGradient 0 z ^ 2 = |shearFullGradient 0 z| ^ 2 :=
        (sq_abs _).symm
      _ = |shearFullGradient 0 z| * |shearFullGradient 0 z| := by ring
  have hG1sq : MemLp (fun z => (shearFullGradient 1 z) ^ 2) 1 μ := by
    have hmul : MemLp (fun z => |shearFullGradient 1 z| *
      |shearFullGradient 1 z|) 1 μ := hG1.abs.mul hG1.abs
    convert hmul using 1
    ext z
    calc
      shearFullGradient 1 z ^ 2 = |shearFullGradient 1 z| ^ 2 :=
        (sq_abs _).symm
      _ = |shearFullGradient 1 z| * |shearFullGradient 1 z| := by ring
  have hGrad : MemLp (fun z =>
      (shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) 1 μ :=
    hG0sq.add hG1sq
  have hF : MemLp shearFullForceScalar 2 μ :=
    shearFullForceScalar_memLp_on_localBox hbox
  have hGradψ : Integrable (fun z =>
      ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) *
        |ψ z|) μ := by
    apply MemLp.integrable (q := 1) (by norm_num)
    exact hGrad.mul hψtop.abs
  have hWheat : Integrable (fun z =>
      |shearFullScalar z| ^ 2 * |heat z|) μ := by
    apply MemLp.integrable (q := 1) (by norm_num)
    exact hWsq1.mul hheattop.abs
  have hWcube : Integrable (fun z =>
      |shearFullScalar z| ^ 3 * |spatialPartial
        (show ParabolicPoint → ℝ from ψ) 2 z|) μ := by
    apply MemLp.integrable (q := 1) (by norm_num)
    exact hWcube1.mul hψ2top.abs
  have hFW : MemLp (fun z => |shearFullForceScalar z| *
      |shearFullScalar z|) 1 μ := hF.abs.mul hWabs2
  have hFWψ : Integrable (fun z => 2 *
      |shearFullForceScalar z| * |shearFullScalar z| * |ψ z|) μ := by
    have hprod : Integrable (fun z =>
        |shearFullForceScalar z| * |shearFullScalar z| * |ψ z|) μ := by
      apply MemLp.integrable (q := 1) (by norm_num)
      exact hFW.mul hψtop.abs
    simpa only [mul_assoc] using hprod.const_mul 2
  change Integrable (fun z =>
      ((shearFullGradient 0 z) ^ 2 + (shearFullGradient 1 z) ^ 2) * |ψ z| +
        |shearFullScalar z| ^ 2 * |heat z| +
        |shearFullScalar z| ^ 3 * |spatialPartial
          (show ParabolicPoint → ℝ from ψ) 2 z| +
        2 * |shearFullForceScalar z| * |shearFullScalar z| * |ψ z|) μ
  exact ((hGradψ.add hWheat).add hWcube).add hFWψ

theorem shearLEIMajorant_integrable_on_localBox {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (shearLEIMajorant ψ)
      (volume.restrict (spaceTimeSet Ω' J)) := by
  let hμ : IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) :=
    shear_localBox_volume_restrict_finite hbox
  exact @shearLEIMajorant_integrable_on_localBox_aux Ω' J hμ inferInstance
    hbox ψ hψ hψc

end CKN
