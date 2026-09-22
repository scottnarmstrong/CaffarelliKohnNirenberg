-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.FiniteMomentumIntegral
import CKN.Setting.Examples.ShearCounterexample.FactorIBP
import CKN.Setting.Examples.ShearCounterexample.TestSupport
import CKN.Foundation.Parabolic.Topology
import CKN.Statements.TimePartial
import CKN.Statements.SpatialSecondPartial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Finite-scale local energy identities for the shear. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory CKN.Foundation.Parabolic Finset
namespace CKN

private def leiTimePartial (g : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  timePartial (show ParabolicPoint → ℝ from g) z

private def leiSpatialPartial (g : Vec3 × ℝ → ℝ) (i : Fin 3)
    (z : Vec3 × ℝ) : ℝ :=
  spatialPartial (show ParabolicPoint → ℝ from g) i z

private theorem leiTimePartial_bridge (g : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) :
    timePartial (show ParabolicPoint → ℝ from g) z = leiTimePartial g z := by
  rfl

private theorem leiSpatialPartial_bridge (g : Vec3 × ℝ → ℝ) (i : Fin 3)
    (z : Vec3 × ℝ) :
    spatialPartial (show ParabolicPoint → ℝ from g) i z = leiSpatialPartial g i z := by
  rfl

private theorem leiIntegrableMulCompact {F G : Vec3 × ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) (hGc : HasCompactSupport G) :
    Integrable (fun z => F z * G z) volume :=
  (hF.mul hG).integrable_of_hasCompactSupport (hGc.mul_left)

private theorem shearScalarPartial_spaceDerivative_prod (N : ℕ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (show ParabolicPoint → ℝ from shearFullScalarPartial N) i z =
      (if i = 0 then shearFullGradientPartial 0 N z else
        if i = 1 then shearFullGradientPartial 1 N z else 0) := by
  simpa only [parabolicHomeomorph_symm_apply] using
    shearFullScalarPartial_spatialPartial N (parabolicHomeomorph.symm z) i

private theorem leiTimePartial_mul {f g : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (z : Vec3 × ℝ) :
    timePartial (show ParabolicPoint → ℝ from fun w => f w * g w) z =
      f z * timePartial (show ParabolicPoint → ℝ from g) z +
        g z * timePartial (show ParabolicPoint → ℝ from f) z := by
  let F : ℝ → ℝ := fun t => f (z.1, t)
  let G : ℝ → ℝ := fun t => g (z.1, t)
  have hcurve : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (z.1, t)) := by fun_prop
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    dsimp [F]
    exact hf.comp hcurve
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    dsimp [G]
    exact hg.comp hcurve
  have hFd : DifferentiableAt ℝ F z.2 :=
    (hF.differentiable (by simp)).differentiableAt
  have hGd : DifferentiableAt ℝ G z.2 :=
    (hG.differentiable (by simp)).differentiableAt
  change fderiv ℝ (fun t : ℝ => f (z.1, t) * g (z.1, t)) z.2 1 = _
  change fderiv ℝ (F * G) z.2 1 = _
  rw [fderiv_mul hFd hGd]
  simp [F, G, timePartial]

private theorem leiSpatialSecondContDiff {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ =>
        spatialSecondPartial (show ParabolicPoint → ℝ from g) i j z) := by
  exact spatialPartial_contDiff (spatialPartial_contDiff hg i) j

private theorem leiSpatialSecondHasCompactSupport {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (i j : Fin 3) :
    HasCompactSupport (fun z : Vec3 × ℝ =>
      spatialSecondPartial (show ParabolicPoint → ℝ from g) i j z) := by
  exact spatialPartial_hasCompactSupport
    (spatialPartial_contDiff hg i)
    (spatialPartial_hasCompactSupport hg hgc i) j

/-- A finite smooth shear satisfies the local energy identity. -/
theorem shearCounterexample_finite_energy_identity (N : ℕ)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    2 * ∫ z : Vec3 × ℝ,
      spatialGradientSq (shearCounterexampleVelocityPartial N)
        (shearCounterexampleDuPartial N) z * ψ z ∂volume =
      ∫ z : Vec3 × ℝ,
        (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z)
          + (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
              shearCounterexampleVelocityPartial N z 2 * spatialPartial ψ 2 z
          + 2 * (∑ i : Fin 3,
              shearCounterexampleForcePartial N z i *
                shearCounterexampleVelocityPartial N z i) * ψ z ∂volume := by
  let W : Vec3 × ℝ → ℝ := fun z => shearFullScalarPartial N z
  let F : Vec3 × ℝ → ℝ := fun z => shearFullForcePartial N z
  let P : Vec3 × ℝ → ℝ := fun z => W z * ψ z
  let φ : Vec3 × ℝ → Vec3 := fun z => fun i => if i = 2 then P z else 0
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := shearFullScalarPartial_contDiff N
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
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := hW.mul hψ
  have hPc : HasCompactSupport P := hψc.mul_left
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    apply contDiff_pi.mpr
    intro i
    by_cases hi : i = 2
    · simp [φ, hi, hP]
    · simpa [φ, hi] using
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 × ℝ => (0 : ℝ)))
  have hφsupport : Function.support φ ⊆ tsupport ψ := by
    intro z hz
    have hφz : φ z ≠ 0 := Function.mem_support.mp hz
    have hPz : P z ≠ 0 := by
      intro hzero
      apply hφz
      ext i
      simp [φ, hzero]
    have hψz : ψ z ≠ 0 := by
      intro hzero
      apply hPz
      simp [P, hzero]
    exact subset_tsupport (f := ψ) (Function.mem_support.mpr hψz)
  have hφts : tsupport φ ⊆ tsupport ψ :=
    closure_minimal hφsupport (isClosed_tsupport ψ)
  have hφc : HasCompactSupport φ := hψc.mono' hφsupport
  have hmomentum := shearCounterexample_momentum_finite N φ hφ hφc
  have hweak : ∫ z : Vec3 × ℝ,
      -(shearFullScalarPartial N z *
          timePartial (fun w => shearFullScalarPartial N w * ψ w) z)
        - (shearFullScalarPartial N z) ^ 2 *
          spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 2 z
        + shearFullGradientPartial 0 N z *
          spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 0 z
        + shearFullGradientPartial 1 N z *
          spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 1 z
        - shearFullForcePartial N z * (shearFullScalarPartial N z * ψ z)
        ∂volume = 0 := by
    have heq : (fun z : Vec3 × ℝ =>
        (-(∑ i : Fin 3, shearCounterexampleVelocityPartial N z i *
            timePartial (fun w => φ w i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              shearCounterexampleVelocityPartial N z i *
                shearCounterexampleVelocityPartial N z j *
                  spatialPartial (fun w => φ w i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              shearCounterexampleDuPartial N z i j *
                spatialPartial (fun w => φ w i) j z
          - ∑ i : Fin 3, shearCounterexampleForcePartial N z i * φ z i)) =
      fun z =>
        -(shearFullScalarPartial N z *
            timePartial (fun w => shearFullScalarPartial N w * ψ w) z)
          - (shearFullScalarPartial N z) ^ 2 *
            spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 2 z
          + shearFullGradientPartial 0 N z *
            spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 0 z
          + shearFullGradientPartial 1 N z *
            spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 1 z
          - shearFullForcePartial N z * (shearFullScalarPartial N z * ψ z) := by
      funext z
      rw [shearFiniteMomentumResidual_simplify N φ z]
      simp [φ, P, W, shearCounterexampleDuPartial, Fin.sum_univ_succ]
      ring
    have heqint : ∫ z : Vec3 × ℝ,
        (-(∑ i : Fin 3, shearCounterexampleVelocityPartial N z i *
            timePartial (fun w => φ w i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              shearCounterexampleVelocityPartial N z i *
                shearCounterexampleVelocityPartial N z j *
                  spatialPartial (fun w => φ w i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              shearCounterexampleDuPartial N z i j *
                spatialPartial (fun w => φ w i) j z
          - ∑ i : Fin 3, shearCounterexampleForcePartial N z i * φ z i) ∂volume =
        ∫ z : Vec3 × ℝ,
          -(shearFullScalarPartial N z *
              timePartial (fun w => shearFullScalarPartial N w * ψ w) z)
            - (shearFullScalarPartial N z) ^ 2 *
              spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 2 z
            + shearFullGradientPartial 0 N z *
              spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 0 z
            + shearFullGradientPartial 1 N z *
              spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 1 z
            - shearFullForcePartial N z * (shearFullScalarPartial N z * ψ z)
          ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact congrFun heq z
    exact heqint.symm.trans hmomentum
  let Wt : Vec3 × ℝ → ℝ := leiTimePartial W
  let ψt : Vec3 × ℝ → ℝ := leiTimePartial ψ
  let ψ0 : Vec3 × ℝ → ℝ := leiSpatialPartial ψ 0
  let ψ1 : Vec3 × ℝ → ℝ := leiSpatialPartial ψ 1
  let ψ2 : Vec3 × ℝ → ℝ := leiSpatialPartial ψ 2
  let G0 : Vec3 × ℝ → ℝ := fun z => shearFullGradientPartial 0 N z
  let G1 : Vec3 × ℝ → ℝ := fun z => shearFullGradientPartial 1 N z
  have hweakExpanded : ∫ z : Vec3 × ℝ,
      -(shearFullScalarPartial N z * Wt z * ψ z)
        - shearFullScalarPartial N z ^ 2 * ψt z
        - shearFullScalarPartial N z ^ 3 * ψ2 z
        + G0 z ^ 2 * ψ z + shearFullScalarPartial N z * G0 z * ψ0 z
        + G1 z ^ 2 * ψ z + shearFullScalarPartial N z * G1 z * ψ1 z
        - shearFullForcePartial N z * shearFullScalarPartial N z * ψ z
        ∂volume = 0 := by
    have hEq : (fun z : Vec3 × ℝ =>
        -(shearFullScalarPartial N z *
            timePartial (fun w => shearFullScalarPartial N w * ψ w) z)
          - shearFullScalarPartial N z ^ 2 *
            spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 2 z
          + shearFullGradientPartial 0 N z *
            spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 0 z
          + shearFullGradientPartial 1 N z *
            spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 1 z
          - shearFullForcePartial N z * (shearFullScalarPartial N z * ψ z)) =
      fun z =>
        -(shearFullScalarPartial N z * Wt z * ψ z)
          - shearFullScalarPartial N z ^ 2 * ψt z
          - shearFullScalarPartial N z ^ 3 * ψ2 z
          + G0 z ^ 2 * ψ z + shearFullScalarPartial N z * G0 z * ψ0 z
          + G1 z ^ 2 * ψ z + shearFullScalarPartial N z * G1 z * ψ1 z
          - shearFullForcePartial N z * shearFullScalarPartial N z * ψ z := by
      funext z
      have htime := leiTimePartial_mul hW hψ z
      have hspace0 := spatialPartial_mul hW hψ 0 z
      have hspace1 := spatialPartial_mul hW hψ 1 z
      have hspace2 := spatialPartial_mul hW hψ 2 z
      have hw0 := shearScalarPartial_spaceDerivative_prod N 0 z
      have hw1 := shearScalarPartial_spaceDerivative_prod N 1 z
      have hw2 := shearScalarPartial_spaceDerivative_prod N 2 z
      simp only [Wt, ψt, ψ0, ψ1, ψ2, G0, G1,
        leiTimePartial, leiSpatialPartial] at *
      rw [htime, hspace0, hspace1, hspace2, hw0, hw1, hw2]
      simp only [ite_true]
      dsimp [W] at *
      ring_nf
    have hEqInt : ∫ z : Vec3 × ℝ,
        -(shearFullScalarPartial N z *
            timePartial (fun w => shearFullScalarPartial N w * ψ w) z)
          - shearFullScalarPartial N z ^ 2 *
            spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 2 z
          + shearFullGradientPartial 0 N z *
            spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 0 z
          + shearFullGradientPartial 1 N z *
            spatialPartial (fun w => shearFullScalarPartial N w * ψ w) 1 z
          - shearFullForcePartial N z * (shearFullScalarPartial N z * ψ z)
          ∂volume =
        ∫ z : Vec3 × ℝ,
          -(shearFullScalarPartial N z * Wt z * ψ z)
            - shearFullScalarPartial N z ^ 2 * ψt z
            - shearFullScalarPartial N z ^ 3 * ψ2 z
            + G0 z ^ 2 * ψ z + shearFullScalarPartial N z * G0 z * ψ0 z
            + G1 z ^ 2 * ψ z + shearFullScalarPartial N z * G1 z * ψ1 z
            - shearFullForcePartial N z * shearFullScalarPartial N z * ψ z
          ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact congrFun hEq z
    exact hEqInt.symm.trans hweak
  have hWtC : Continuous Wt := by
    have ht := timePartial_contDiff hW
    change Continuous (fun z : Vec3 × ℝ =>
      timePartial (show ParabolicPoint → ℝ from shearFullScalarPartial N) z)
    exact ht.continuous
  have hψtC : Continuous ψt := (timePartial_contDiff hψ).continuous
  have hψtc : HasCompactSupport ψt := timePartial_hasCompactSupport hψ hψc
  have hψ0C : Continuous ψ0 := (spatialPartial_contDiff hψ 0).continuous
  have hψ0c : HasCompactSupport ψ0 := spatialPartial_hasCompactSupport hψ hψc 0
  have hψ1C : Continuous ψ1 := (spatialPartial_contDiff hψ 1).continuous
  have hψ1c : HasCompactSupport ψ1 := spatialPartial_hasCompactSupport hψ hψc 1
  have hψ2C : Continuous ψ2 := (spatialPartial_contDiff hψ 2).continuous
  have hψ2c : HasCompactSupport ψ2 := spatialPartial_hasCompactSupport hψ hψc 2
  have hG0C : Continuous G0 := (shearFullGradientPartial_contDiff N 0).continuous
  have hG1C : Continuous G1 := (shearFullGradientPartial_contDiff N 1).continuous
  let term : Fin 8 → Vec3 × ℝ → ℝ := fun i z =>
    if i = 0 then (-(shearFullScalarPartial N z * Wt z)) * ψ z else
    if i = 1 then (-(shearFullScalarPartial N z ^ 2)) * ψt z else
    if i = 2 then (-(shearFullScalarPartial N z ^ 3)) * ψ2 z else
    if i = 3 then (G0 z ^ 2) * ψ z else
    if i = 4 then (shearFullScalarPartial N z * G0 z) * ψ0 z else
    if i = 5 then (G1 z ^ 2) * ψ z else
    if i = 6 then (shearFullScalarPartial N z * G1 z) * ψ1 z else
      (-(shearFullForcePartial N z * shearFullScalarPartial N z)) * ψ z
  have hterm : ∀ i : Fin 8, Integrable (term i) volume := by
    intro i
    fin_cases i
    · simpa [term] using leiIntegrableMulCompact
        ((hW.continuous.mul hWtC).neg) hψ.continuous hψc
    · simpa [term] using leiIntegrableMulCompact
        (hW.pow 2).continuous.neg hψtC hψtc
    · simpa [term] using leiIntegrableMulCompact
        (hW.pow 3).continuous.neg hψ2C hψ2c
    · simpa [term] using leiIntegrableMulCompact
        (hG0C.pow 2) hψ.continuous hψc
    · simpa [term] using leiIntegrableMulCompact
        (hW.continuous.mul hG0C) hψ0C hψ0c
    · simpa [term] using leiIntegrableMulCompact
        (hG1C.pow 2) hψ.continuous hψc
    · simpa [term] using leiIntegrableMulCompact
        (hW.continuous.mul hG1C) hψ1C hψ1c
    · simpa [term] using leiIntegrableMulCompact
        (hF.mul hW.continuous).neg hψ.continuous hψc
  have hsumPoint : (fun z : Vec3 × ℝ =>
      -(shearFullScalarPartial N z * Wt z * ψ z)
        - shearFullScalarPartial N z ^ 2 * ψt z
        - shearFullScalarPartial N z ^ 3 * ψ2 z
        + G0 z ^ 2 * ψ z + shearFullScalarPartial N z * G0 z * ψ0 z
        + G1 z ^ 2 * ψ z + shearFullScalarPartial N z * G1 z * ψ1 z
        - shearFullForcePartial N z * shearFullScalarPartial N z * ψ z) =
      fun z => ∑ i : Fin 8, term i z := by
    funext z
    simp [term, Fin.sum_univ_succ]
    ring
  have hsumInt : ∫ z : Vec3 × ℝ, ∑ i : Fin 8, term i z ∂volume =
      ∑ i : Fin 8, ∫ z : Vec3 × ℝ, term i z ∂volume := by
    exact integral_finsetSum Finset.univ (by
      intro i hi
      exact hterm i)
  have hweakValues :
      -(∫ z : Vec3 × ℝ, shearFullScalarPartial N z * Wt z * ψ z ∂volume)
        -(∫ z : Vec3 × ℝ, shearFullScalarPartial N z ^ 2 * ψt z ∂volume)
        -(∫ z : Vec3 × ℝ, shearFullScalarPartial N z ^ 3 * ψ2 z ∂volume)
        + (∫ z : Vec3 × ℝ, G0 z ^ 2 * ψ z ∂volume)
        + (∫ z : Vec3 × ℝ, shearFullScalarPartial N z * G0 z * ψ0 z ∂volume)
        + (∫ z : Vec3 × ℝ, G1 z ^ 2 * ψ z ∂volume)
        + (∫ z : Vec3 × ℝ, shearFullScalarPartial N z * G1 z * ψ1 z ∂volume)
        -(∫ z : Vec3 × ℝ, shearFullForcePartial N z * shearFullScalarPartial N z * ψ z ∂volume) = 0 := by
    have hEq : ∫ z : Vec3 × ℝ,
        -(shearFullScalarPartial N z * Wt z * ψ z)
          - shearFullScalarPartial N z ^ 2 * ψt z
          - shearFullScalarPartial N z ^ 3 * ψ2 z
          + G0 z ^ 2 * ψ z + shearFullScalarPartial N z * G0 z * ψ0 z
          + G1 z ^ 2 * ψ z + shearFullScalarPartial N z * G1 z * ψ1 z
          - shearFullForcePartial N z * shearFullScalarPartial N z * ψ z ∂volume =
        ∫ z : Vec3 × ℝ, ∑ i : Fin 8, term i z ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact congrFun hsumPoint z
    have htotal := hEq.trans hsumInt
    have htmp := htotal.symm.trans hweakExpanded
    have htmp' := by simpa [term, Fin.sum_univ_succ, integral_neg] using htmp
    ring_nf at htmp' ⊢
    exact htmp' 
  have hTimeIBP := integral_mul_timePartial_eq_neg_timePartial_mul
    (hW.pow 2) hψ hψc
  have hWsqTime (z : Vec3 × ℝ) :
      timePartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) z =
        2 * W z * Wt z := by
    have hfun : (fun w : ParabolicPoint => W w ^ 2) =
        fun w => W w * W w := by
      funext w
      exact pow_two _
    calc
      _ = timePartial (show ParabolicPoint → ℝ from fun w => W w * W w) z := by
        rw [hfun]
        rfl
      _ = W z * timePartial (show ParabolicPoint → ℝ from W) z +
          W z * timePartial (show ParabolicPoint → ℝ from W) z :=
        leiTimePartial_mul hW hW z
      _ = _ := by
        change W z * leiTimePartial W z + W z * leiTimePartial W z = _
        ring
  have hTimeDerivInt :
      ∫ z : Vec3 × ℝ,
        timePartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) z * ψ z ∂volume =
      2 * ∫ z : Vec3 × ℝ, W z * Wt z * ψ z ∂volume := by
    calc
      _ = ∫ z : Vec3 × ℝ, 2 * (W z * Wt z * ψ z) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hWsqTime z]
        ring
      _ = _ := integral_const_mul 2 _
  have hTimeRel :
      ∫ z : Vec3 × ℝ, W z * Wt z * ψ z ∂volume =
        -(1 / 2 : ℝ) * ∫ z : Vec3 × ℝ, W z ^ 2 * timePartial ψ z ∂volume := by
    have hEq : ∫ z : Vec3 × ℝ, W z ^ 2 * timePartial ψ z ∂volume =
        -2 * ∫ z : Vec3 × ℝ, W z * Wt z * ψ z ∂volume := by
      calc
        _ = -∫ z : Vec3 × ℝ,
            timePartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) z * ψ z ∂volume := hTimeIBP
        _ = _ := by rw [hTimeDerivInt]; ring
    calc
      _ = -(1 / 2 : ℝ) * (-2 *
          ∫ z : Vec3 × ℝ, W z * Wt z * ψ z ∂volume) := by ring
      _ = _ := by rw [← hEq]
  have hTimeRelWrapper :
      ∫ z : Vec3 × ℝ, W z * Wt z * ψ z ∂volume =
        -(1 / 2 : ℝ) * ∫ z : Vec3 × ℝ, W z ^ 2 * ψt z ∂volume := by
    have hbridge (z : Vec3 × ℝ) :
        timePartial (show ParabolicPoint → ℝ from ψ) z = ψt z :=
      leiTimePartial_bridge ψ z
    have hint :
        ∫ z : Vec3 × ℝ, W z ^ 2 * timePartial
          (show ParabolicPoint → ℝ from ψ) z ∂volume =
        ∫ z : Vec3 × ℝ, W z ^ 2 * ψt z ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hbridge z]
    calc
      _ = -(1 / 2 : ℝ) * ∫ z : Vec3 × ℝ,
          W z ^ 2 * timePartial (show ParabolicPoint → ℝ from ψ) z ∂volume := hTimeRel
      _ = _ := congrArg (fun x : ℝ => -(1 / 2 : ℝ) * x) hint
  have hSquareSpace (i : Fin 3) (z : Vec3 × ℝ) :
      spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) i z =
        2 * W z * spatialPartial (show ParabolicPoint → ℝ from W) i z := by
    have hfun : (fun w : ParabolicPoint => W w ^ 2) =
        fun w => W w * W w := by
      funext w
      exact pow_two _
    calc
      _ = spatialPartial (show ParabolicPoint → ℝ from fun w => W w * W w) i z := by
        rw [hfun]
        rfl
      _ = W z * spatialPartial (show ParabolicPoint → ℝ from W) i z +
          W z * spatialPartial (show ParabolicPoint → ℝ from W) i z :=
        spatialPartial_mul hW hW i z
      _ = _ := by ring
  have hWsp0 (z : Vec3 × ℝ) :
      spatialPartial (show ParabolicPoint → ℝ from W) 0 z = G0 z := by
    simpa [W, G0] using shearScalarPartial_spaceDerivative_prod N 0 z
  have hWsp1 (z : Vec3 × ℝ) :
      spatialPartial (show ParabolicPoint → ℝ from W) 1 z = G1 z := by
    simpa [W, G1] using shearScalarPartial_spaceDerivative_prod N 1 z
  have hWsp2 (z : Vec3 × ℝ) :
      spatialPartial (show ParabolicPoint → ℝ from W) 2 z = 0 := by
    simpa [W] using shearScalarPartial_spaceDerivative_prod N 2 z
  have hSquareDerivInt0 :
      ∫ z : Vec3 × ℝ,
        spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) 0 z * ψ0 z ∂volume =
      2 * ∫ z : Vec3 × ℝ, W z * G0 z * ψ0 z ∂volume := by
    calc
      _ = ∫ z : Vec3 × ℝ, 2 * (W z * G0 z * ψ0 z) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hSquareSpace 0 z, hWsp0 z]
        ring
      _ = _ := integral_const_mul 2 _
  have hSquareDerivInt1 :
      ∫ z : Vec3 × ℝ,
        spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) 1 z * ψ1 z ∂volume =
      2 * ∫ z : Vec3 × ℝ, W z * G1 z * ψ1 z ∂volume := by
    calc
      _ = ∫ z : Vec3 × ℝ, 2 * (W z * G1 z * ψ1 z) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hSquareSpace 1 z, hWsp1 z]
        ring
      _ = _ := integral_const_mul 2 _
  have hSpaceIBP0 := integral_mul_spatialPartial_eq_neg_spatialPartial_mul
    (hW.pow 2) (spatialPartial_contDiff hψ 0)
    (spatialPartial_hasCompactSupport hψ hψc 0) 0
  have hSpaceIBP1 := integral_mul_spatialPartial_eq_neg_spatialPartial_mul
    (hW.pow 2) (spatialPartial_contDiff hψ 1)
    (spatialPartial_hasCompactSupport hψ hψc 1) 1
  have hCrossRel0 :
      ∫ z : Vec3 × ℝ, W z * G0 z * ψ0 z ∂volume =
        -(1 / 2 : ℝ) * ∫ z : Vec3 × ℝ,
          W z ^ 2 * spatialSecondPartial ψ 0 0 z ∂volume := by
    have hEq : ∫ z : Vec3 × ℝ,
        W z ^ 2 * spatialSecondPartial ψ 0 0 z ∂volume =
        -2 * ∫ z : Vec3 × ℝ, W z * G0 z * ψ0 z ∂volume := by
      calc
        _ = -∫ z : Vec3 × ℝ,
            spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) 0 z * ψ0 z ∂volume := by
          convert hSpaceIBP0 using 1 <;> rfl
        _ = _ := by rw [hSquareDerivInt0]; ring
    calc
      _ = -(1 / 2 : ℝ) * (-2 *
          ∫ z : Vec3 × ℝ, W z * G0 z * ψ0 z ∂volume) := by ring
      _ = _ := by rw [← hEq]
  have hCrossRel1 :
      ∫ z : Vec3 × ℝ, W z * G1 z * ψ1 z ∂volume =
        -(1 / 2 : ℝ) * ∫ z : Vec3 × ℝ,
          W z ^ 2 * spatialSecondPartial ψ 1 1 z ∂volume := by
    have hEq : ∫ z : Vec3 × ℝ,
        W z ^ 2 * spatialSecondPartial ψ 1 1 z ∂volume =
        -2 * ∫ z : Vec3 × ℝ, W z * G1 z * ψ1 z ∂volume := by
      calc
        _ = -∫ z : Vec3 × ℝ,
            spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) 1 z * ψ1 z ∂volume := by
          convert hSpaceIBP1 using 1 <;> rfl
        _ = _ := by rw [hSquareDerivInt1]; ring
    calc
      _ = -(1 / 2 : ℝ) * (-2 *
          ∫ z : Vec3 × ℝ, W z * G1 z * ψ1 z ∂volume) := by ring
      _ = _ := by rw [← hEq]
  have hSpaceIBP2 := integral_mul_spatialPartial_eq_neg_spatialPartial_mul
    (hW.pow 2) (spatialPartial_contDiff hψ 2)
    (spatialPartial_hasCompactSupport hψ hψc 2) 2
  have hSquareDerivZero2 (z : Vec3 × ℝ) :
      spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) 2 z = 0 := by
    rw [hSquareSpace 2 z, hWsp2 z]
    ring
  have hSecondZero2 :
      ∫ z : Vec3 × ℝ, W z ^ 2 * spatialSecondPartial ψ 2 2 z ∂volume = 0 := by
    have hEq : ∫ z : Vec3 × ℝ,
        W z ^ 2 * spatialSecondPartial ψ 2 2 z ∂volume =
        -∫ z : Vec3 × ℝ,
          spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) 2 z * ψ2 z ∂volume := by
      convert hSpaceIBP2 using 1 <;> rfl
    rw [hEq]
    have hZero : (fun z : Vec3 × ℝ =>
        spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) 2 z * ψ2 z) =
        fun _ => 0 := by
      funext z
      rw [hSquareDerivZero2 z]
      simp
    rw [hZero, integral_zero]
    simp
  have hCubeDerivZero2 (z : Vec3 × ℝ) :
      spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 3) 2 z = 0 := by
    have hfun : (fun w : ParabolicPoint => W w ^ 3) =
        fun w => W w ^ 2 * W w := by
      funext w
      rw [pow_succ]
    have hmul : spatialPartial
        (show ParabolicPoint → ℝ from fun w => W w ^ 2 * W w) 2 z =
        W z ^ 2 * spatialPartial (show ParabolicPoint → ℝ from W) 2 z +
          W z * spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 2) 2 z :=
      spatialPartial_mul (hW.pow 2) hW 2 z
    calc
      _ = spatialPartial
          (show ParabolicPoint → ℝ from fun w => W w ^ 2 * W w) 2 z := by
        rw [hfun]
        rfl
      _ = _ := by rw [hmul, hWsp2 z, hSquareDerivZero2 z]; ring
  have hCubeIBP := integral_mul_spatialPartial_eq_neg_spatialPartial_mul
    (hW.pow 3) hψ hψc 2
  have hCubeZero :
      ∫ z : Vec3 × ℝ, W z ^ 3 * ψ2 z ∂volume = 0 := by
    have hEq : ∫ z : Vec3 × ℝ, W z ^ 3 * ψ2 z ∂volume =
        -∫ z : Vec3 × ℝ,
          spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 3) 2 z * ψ z ∂volume := by
      convert hCubeIBP using 1 <;> rfl
    rw [hEq]
    have hZero : (fun z : Vec3 × ℝ =>
        spatialPartial (show ParabolicPoint → ℝ from fun w => W w ^ 3) 2 z * ψ z) =
        fun _ => 0 := by
      funext z
      rw [hCubeDerivZero2 z]
      simp
    rw [hZero, integral_zero]
    simp
  have hscalar :
      2 * (∫ z : Vec3 × ℝ, G0 z ^ 2 * ψ z ∂volume +
        ∫ z : Vec3 × ℝ, G1 z ^ 2 * ψ z ∂volume) =
      ∫ z : Vec3 × ℝ, W z ^ 2 * ψt z ∂volume +
        ∫ z : Vec3 × ℝ, W z ^ 2 * spatialSecondPartial ψ 0 0 z ∂volume +
        ∫ z : Vec3 × ℝ, W z ^ 2 * spatialSecondPartial ψ 1 1 z ∂volume +
        ∫ z : Vec3 × ℝ, W z ^ 2 * spatialSecondPartial ψ 2 2 z ∂volume +
        2 * ∫ z : Vec3 × ℝ, shearFullForcePartial N z * W z * ψ z ∂volume := by
    dsimp [W] at hweakValues hTimeRelWrapper hCrossRel0 hCrossRel1 hSecondZero2 hCubeZero ⊢
    linarith only [hweakValues, hTimeRelWrapper, hCrossRel0, hCrossRel1, hSecondZero2,
      hCubeZero]
  have htargetIntegral :
      ∫ z : Vec3 × ℝ,
        (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z)
          + (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
              shearCounterexampleVelocityPartial N z 2 * spatialPartial ψ 2 z
          + 2 * (∑ i : Fin 3,
              shearCounterexampleForcePartial N z i *
                shearCounterexampleVelocityPartial N z i) * ψ z ∂volume =
      ∫ z : Vec3 × ℝ, W z ^ 2 * ψt z ∂volume +
        ∫ z : Vec3 × ℝ, W z ^ 2 * spatialSecondPartial ψ 0 0 z ∂volume +
        ∫ z : Vec3 × ℝ, W z ^ 2 * spatialSecondPartial ψ 1 1 z ∂volume +
        ∫ z : Vec3 × ℝ, W z ^ 2 * spatialSecondPartial ψ 2 2 z ∂volume +
        2 * ∫ z : Vec3 × ℝ, shearFullForcePartial N z * W z * ψ z ∂volume := by
    have hpoint : (fun z : Vec3 × ℝ =>
        (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z)
          + (vec3EuclideanNorm (shearCounterexampleVelocityPartial N z)) ^ 2 *
              shearCounterexampleVelocityPartial N z 2 * spatialPartial ψ 2 z
          + 2 * (∑ i : Fin 3,
              shearCounterexampleForcePartial N z i *
                shearCounterexampleVelocityPartial N z i) * ψ z) =
        fun z => W z ^ 2 * ψt z +
          W z ^ 2 * spatialSecondPartial ψ 0 0 z +
          W z ^ 2 * spatialSecondPartial ψ 1 1 z +
          W z ^ 2 * spatialSecondPartial ψ 2 2 z +
          W z ^ 3 * ψ2 z +
          2 * (shearFullForcePartial N z * W z * ψ z) := by
      funext z
      rw [shearCounterexampleVelocityPartial_norm_sq N z]
      rw [leiTimePartial_bridge ψ z, leiSpatialPartial_bridge ψ 2 z]
      simp [W, shearCounterexampleVelocityPartial, shearCounterexampleForcePartial,
        Fin.sum_univ_succ]
      ring
    have h0 := leiIntegrableMulCompact (hW.pow 2).continuous hψtC hψtc
    have h00 := leiIntegrableMulCompact (hW.pow 2).continuous
      (leiSpatialSecondContDiff hψ 0 0).continuous
      (leiSpatialSecondHasCompactSupport hψ hψc 0 0)
    have h11 := leiIntegrableMulCompact (hW.pow 2).continuous
      (leiSpatialSecondContDiff hψ 1 1).continuous
      (leiSpatialSecondHasCompactSupport hψ hψc 1 1)
    have h22 := leiIntegrableMulCompact (hW.pow 2).continuous
      (leiSpatialSecondContDiff hψ 2 2).continuous
      (leiSpatialSecondHasCompactSupport hψ hψc 2 2)
    have hforceBase := leiIntegrableMulCompact (hF.mul hW.continuous)
      hψ.continuous hψc
    have hforce2 : Integrable (fun z : Vec3 × ℝ =>
        2 * (shearFullForcePartial N z * W z * ψ z)) volume :=
      hforceBase.const_mul 2
    have hcubeInt : Integrable (fun z : Vec3 × ℝ => W z ^ 3 * ψ2 z) volume :=
      leiIntegrableMulCompact (hW.pow 3).continuous hψ2C hψ2c
    let rhsTerm : Fin 6 → Vec3 × ℝ → ℝ := fun i z =>
      if i = 0 then W z ^ 2 * ψt z else
      if i = 1 then W z ^ 2 * spatialSecondPartial ψ 0 0 z else
      if i = 2 then W z ^ 2 * spatialSecondPartial ψ 1 1 z else
      if i = 3 then W z ^ 2 * spatialSecondPartial ψ 2 2 z else
      if i = 4 then W z ^ 3 * ψ2 z else
        2 * (shearFullForcePartial N z * W z * ψ z)
    have hrhsTerm : ∀ i : Fin 6, Integrable (rhsTerm i) volume := by
      intro i
      fin_cases i
      · simpa [rhsTerm] using h0
      · simpa [rhsTerm] using h00
      · simpa [rhsTerm] using h11
      · simpa [rhsTerm] using h22
      · simpa [rhsTerm] using hcubeInt
      · simpa [rhsTerm] using hforce2
    have hsumPoint : (fun z : Vec3 × ℝ =>
        W z ^ 2 * ψt z + W z ^ 2 * spatialSecondPartial ψ 0 0 z +
          W z ^ 2 * spatialSecondPartial ψ 1 1 z +
          W z ^ 2 * spatialSecondPartial ψ 2 2 z + W z ^ 3 * ψ2 z +
          2 * (shearFullForcePartial N z * W z * ψ z)) =
        fun z => ∑ i : Fin 6, rhsTerm i z := by
      funext z
      simp [rhsTerm, Fin.sum_univ_succ]
      ring
    calc
      _ = ∫ z : Vec3 × ℝ,
          ∑ i : Fin 6, rhsTerm i z ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [congrFun hpoint z, congrFun hsumPoint z]
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun i hi => hrhsTerm i)]
        simp [rhsTerm, Fin.sum_univ_succ, integral_const_mul, hCubeZero]
        ring
  rw [htargetIntegral]
  have hgrad :
      ∫ z : Vec3 × ℝ,
        spatialGradientSq (shearCounterexampleVelocityPartial N)
          (shearCounterexampleDuPartial N) z * ψ z ∂volume =
      ∫ z : Vec3 × ℝ, G0 z ^ 2 * ψ z ∂volume +
        ∫ z : Vec3 × ℝ, G1 z ^ 2 * ψ z ∂volume := by
    calc
      _ = ∫ z : Vec3 × ℝ, (G0 z ^ 2 + G1 z ^ 2) * ψ z ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [shearCounterexampleDuPartial_energy_eq N z]
      _ = ∫ z : Vec3 × ℝ, G0 z ^ 2 * ψ z + G1 z ^ 2 * ψ z ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = _ := by
        have hi0 := leiIntegrableMulCompact (hG0C.pow 2) hψ.continuous hψc
        have hi1 := leiIntegrableMulCompact (hG1C.pow 2) hψ.continuous hψc
        exact integral_add hi0 hi1
  rw [hgrad]
  exact hscalar

end CKN
