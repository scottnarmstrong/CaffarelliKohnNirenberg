-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.HessianL2
import CKN.Foundation.Harmonic.NewtonianRadialPotential
import CKN.Foundation.Harmonic.NewtonianRadialODE
import CKN.Foundation.Harmonic.Commutator.SphereTransport
import CKN.Pressure.PotentialDecayFarField
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set Filter MeasureTheory
open scoped Topology BigOperators Interval
open CKN.Foundation.Parabolic CKN.Foundation.Heat

/-!
# Compact support of radial Newtonian potentials

A smooth radial source with zero integral has a Newtonian potential that vanishes outside
the source ball. The proof reduces the potential to a radial profile, uses the radial
Laplacian equation to show that the profile is constant outside the source, and uses
Newtonian decay to identify that constant as zero.
-/
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Harmonic

private def axis : Vec3 := CKN.basisVec 0

private lemma axis_norm : vec3EuclideanNorm axis = 1 := by
  unfold axis vec3EuclideanNorm
  simp [CKN.basisVec_apply]

private lemma q_axis_scale (r : ℝ) : q (r • axis) = r ^ 2 := by
  unfold axis q
  simp [CKN.basisVec_apply, pow_two]

private lemma axis_scale_norm (r : ℝ) : vec3EuclideanNorm (r • axis) = |r| := by
  rw [vec3EuclideanNorm_smul, axis_norm, mul_one]

private lemma axis_sup_norm : ‖axis‖ = 1 := by
  change ‖CKN.basisVec (0 : Fin 3)‖ = 1
  apply le_antisymm
  · rw [Pi.norm_def]
    change (↑(Finset.univ.sup
      (fun b => ‖CKN.basisVec (0 : Fin 3) b‖₊) : NNReal) : ℝ) ≤ ↑(1 : NNReal)
    exact_mod_cast (Finset.sup_le fun j hj => by
      by_cases h : j = 0
      · subst j
        simp [CKN.basisVec_apply]
      · simp [CKN.basisVec_apply, h])
  · have hi : ‖CKN.basisVec (0 : Fin 3) (0 : Fin 3)‖ ≤
        ‖CKN.basisVec (0 : Fin 3)‖ := norm_le_pi_norm _ _
    simpa [CKN.basisVec] using hi

private theorem radial_potential_eq_profile {g : Vec3 → ℝ}
    (hrad : ∀ x y, vec3EuclideanNorm x = vec3EuclideanNorm y → g x = g y)
    :
    ∀ x, CKN.pressureNewtonianPotential g x =
      (fun t => CKN.pressureNewtonianPotential g (Real.sqrt t • axis)) (q x) := by
  intro x
  have hrootnorm : Real.sqrt (q x) = vec3EuclideanNorm x := by
    rw [q_eq_vec3Norm_sq, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg x)]
  have hnorm : vec3EuclideanNorm x =
      vec3EuclideanNorm (Real.sqrt (q x) • axis) := by
    rw [axis_scale_norm, abs_of_nonneg (Real.sqrt_nonneg _), hrootnorm]
  exact pressureNewtonianPotential_eq_of_radial hrad hnorm

theorem radial_zeroMean_potential_vanishes {g : Vec3 → ℝ}
    (hrad : ∀ x y, vec3EuclideanNorm x = vec3EuclideanNorm y → g x = g y)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hmean : ∫ y, g y = 0) {R : ℝ} (hR : 0 < R)
    (hsupp : tsupport g ⊆ Metric.closedBall (0 : Vec3) R)
    {x : Vec3} (hx : R < vec3EuclideanNorm x) :
    CKN.pressureNewtonianPotential g x = 0 := by
  let w : Vec3 → ℝ := CKN.pressureNewtonianPotential g
  let φ : ℝ → ℝ := fun t => w (Real.sqrt t • axis)
  let v : ℝ → ℝ := fun r => w (r • axis)
  let sqfun : ℝ → ℝ := fun r => r * r
  have hws : ContDiff ℝ (⊤ : ℕ∞) w := by
    exact CKN.pressureNewtonianPotential_smooth hg hgc
  have hroot : ContDiffOn ℝ 2 (fun t : ℝ => Real.sqrt t) (Ioi 0) := by
    have hbase : ContDiffOn ℝ 2 (id : ℝ → ℝ) (Ioi 0) := contDiffOn_id
    have h := hbase.sqrt (fun t ht => ne_of_gt ht)
    simpa only [id_eq] using h
  have hmap : ContDiffOn ℝ 2 (fun t : ℝ => Real.sqrt t • axis) (Ioi 0) := by
    simpa only [id_eq] using hroot.smul_const axis
  have hφ : ContDiffOn ℝ 2 φ (Ioi 0) := by
    exact (hws.of_le (by norm_num)).comp_contDiffOn hmap
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := by
    exact hws.comp (contDiff_id.smul_const axis)
  have hWprofile : ∀ y, w y = φ (q y) := by
    intro y
    change CKN.pressureNewtonianPotential g y = _
    rw [radial_potential_eq_profile hrad y]
  have hWprofileFun : w = φ ∘ q := by
    funext y
    exact hWprofile y
  have hvprofile : v = φ ∘ sqfun := by
    funext r
    dsimp [v, sqfun]
    rw [hWprofile, q_axis_scale]
    simp [pow_two]
  have hradSourcePoint : ∀ y, g y = g (vec3EuclideanNorm y • axis) := by
    intro y
    apply hrad
    rw [axis_scale_norm, abs_of_nonneg (vec3EuclideanNorm_nonneg y)]
  have hnormEq (y : Vec3) : vec3EuclideanNorm y =
      CKN.vecEuclideanNorm y := by
    rw [vec3EuclideanNorm_eq_l2,
      CKN.Foundation.Harmonic.Commutator.vecEuclideanNorm_eq_l2]
  have hradialIntegral :
      ∫ r in Ioi (0 : ℝ), r ^ 2 * g (r • axis) = 0 := by
    have hpolar : ∫ y : Vec3, g y =
        4 * Real.pi * ∫ r in Ioi (0 : ℝ), r ^ 2 * g (r • axis) := by
      calc
        ∫ y : Vec3, g y = ∫ y : Vec3,
            (fun r : ℝ => g (r • axis)) (vec3EuclideanNorm y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          exact hradSourcePoint y
        _ = ∫ y : Vec3,
            (fun r : ℝ => g (r • axis))
              (CKN.vecEuclideanNorm y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [hnormEq]
        _ = 4 * Real.pi * ∫ r in Ioi (0 : ℝ), r ^ 2 * g (r • axis) := by
          convert CKN.Foundation.Harmonic.Commutator.integral_vecEuclideanNorm_radial
            (fun r : ℝ => g (r • axis)) using 1
          congr 1
          apply integral_congr_ae
          filter_upwards [] with r
          norm_num [Real.rpow_natCast]
    rw [hpolar] at hmean
    have hpi : (4 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
    exact (mul_eq_zero.mp hmean).resolve_left hpi
  let radialDensity : ℝ → ℝ := fun r =>
    if 0 < r then r ^ 2 * g (r • axis) else 0
  have hradialDensity :
      ∫ r, radialDensity r = 0 := by
    have hindicator : radialDensity =
      Set.indicator (Ioi (0 : ℝ)) (fun r => r ^ 2 * g (r • axis)) := by
      funext r
      by_cases hr : 0 < r
      · simp [radialDensity, Set.indicator, hr]
      · simp [radialDensity, Set.indicator, hr]
    calc
      ∫ r, radialDensity r = ∫ r in Ioi (0 : ℝ), r ^ 2 * g (r • axis) := by
        rw [hindicator, integral_indicator measurableSet_Ioi]
      _ = 0 := hradialIntegral
  have hsourceZero (r : ℝ) (hrR : R < r) : g (r • axis) = 0 := by
    have hr : 0 < r := lt_trans hR hrR
    have hball : r • axis ∉ Metric.closedBall (0 : Vec3) R := by
      intro hmem
      have hmem' := hmem
      rw [Metric.mem_closedBall, dist_pi_le_iff hR.le] at hmem'
      have hcoord := hmem' (0 : Fin 3)
      have hle : |r| ≤ R := by
        simpa [axis, CKN.basisVec_apply] using hcoord
      rw [abs_of_pos hr] at hle
      linarith only [hrR, hle]
    have hnot : r • axis ∉ tsupport g := by
      intro hmem
      exact hball (hsupp hmem)
    exact image_eq_zero_of_notMem_tsupport hnot
  have hradialSupport (s : ℝ) (hsR : R < s) :
      Function.support radialDensity ⊆ Set.Ioc 0 s := by
    intro r hrmem
    have hrnz : radialDensity r ≠ 0 := by
      simpa only [Function.mem_support] using hrmem
    have hrpos : 0 < r := by
      by_contra hrnot
      have hrle : r ≤ 0 := le_of_not_gt hrnot
      simp [radialDensity, not_lt.mpr hrle] at hrnz
    refine ⟨hrpos, ?_⟩
    by_contra hnot
    have hslt : s < r := lt_of_not_ge hnot
    have hrR : R < r := lt_trans hsR hslt
    have hzero := hsourceZero r hrR
    simp [radialDensity, hrpos, hzero] at hrnz
  have hradialInterval (s : ℝ) (hsR : R < s) :
      ∫ r in (0 : ℝ)..s, radialDensity r = 0 := by
    calc
      ∫ r in (0 : ℝ)..s, radialDensity r = ∫ r, radialDensity r :=
        intervalIntegral.integral_eq_integral_of_support_subset (hradialSupport s hsR)
      _ = 0 := hradialDensity
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hvDerivDiff : Differentiable ℝ (deriv v) := hv2.differentiable_deriv_two
  let flux : ℝ → ℝ := fun r => sqfun r * deriv v r
  have hfluxCont : Continuous flux := by
    have hderivCont : Continuous (deriv v) := hv.continuous_deriv (by norm_num)
    dsimp [flux, sqfun]
    exact (continuous_id.mul continuous_id).mul hderivCont
  have hsourceCont : Continuous (fun r : ℝ => r ^ 2 * g (r • axis)) := by
    have haxisCont : Continuous (fun r : ℝ => r • axis) := by fun_prop
    exact (continuous_id.pow 2).mul (hg.continuous.comp haxisCont)
  have hsourceInterval (s : ℝ) (hsR : R < s) :
      ∫ r in (0 : ℝ)..s, r ^ 2 * g (r • axis) = 0 := by
    calc
      ∫ r in (0 : ℝ)..s, r ^ 2 * g (r • axis) =
          ∫ r in (0 : ℝ)..s, radialDensity r := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le (a := (0 : ℝ)) (b := s)
          (le_of_lt (lt_trans hR hsR))] at hr
        by_cases hr0 : r = 0
        · subst r
          simp [radialDensity]
        · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
          simp [radialDensity, hrpos]
      _ = 0 := hradialInterval s hsR
  have hfluxDeriv (r : ℝ) (hr : 0 < r) :
      HasDerivAt flux (r ^ 2 * g (r • axis)) r := by
    have hsq : HasDerivAt sqfun (2 * r) r := by
      dsimp [sqfun]
      convert (hasDerivAt_id r).mul (hasDerivAt_id r) using 1
      · rfl
      · simp only [id_eq]
        ring
    have hprod := hsq.mul (hvDerivDiff r).hasDerivAt
    have hderiv1 : deriv v r = 2 * r * deriv φ (r ^ 2) := by
      rw [hvprofile]
      exact radialProfile_deriv hφ hr
    have hderiv2 : deriv (deriv v) r =
        2 * deriv φ (r ^ 2) + 4 * r ^ 2 * deriv (deriv φ) (r ^ 2) := by
      rw [hvprofile]
      exact radialProfile_secondDeriv hφ hr
    have hpotentialLap := CKN.pressureNewtonianPotential_laplacian_eq hg hgc (r • axis)
    change CKN.spatialLaplacian w (r • axis) = g (r • axis) at hpotentialLap
    rw [hWprofileFun] at hpotentialLap
    have hqpos : 0 < q (r • axis) := by
      rw [q_axis_scale]
      positivity
    rw [spatialLaplacian_comp_q_formula hφ hqpos, q_axis_scale] at hpotentialLap
    have hsourceProfile : g (r • axis) =
        4 * r ^ 2 * deriv (deriv φ) (r ^ 2) + 6 * deriv φ (r ^ 2) :=
      hpotentialLap.symm
    convert hprod using 1
    · rw [hderiv1, hderiv2]
      rw [hsourceProfile]
      ring
  have hfluxZero (s : ℝ) (hsR : R < s) : flux s = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := (0 : ℝ)) (b := s) (le_of_lt (lt_trans hR hsR))
      hfluxCont.continuousOn
      (fun r hr => hfluxDeriv r hr.1)
      (hsourceCont.intervalIntegrable 0 s)
    rw [hsourceInterval s hsR] at hFTC
    have hzero : flux 0 = 0 := by simp [flux, sqfun]
    rw [hzero, sub_zero] at hFTC
    exact hFTC.symm
  have hvderivZero (s : ℝ) (hsR : R < s) : deriv v s = 0 := by
    have hspos : 0 < s := lt_trans hR hsR
    have hsqpos : 0 < sqfun s := by
      dsimp [sqfun]
      exact mul_pos hspos hspos
    have hmul : sqfun s * deriv v s = 0 := by
      simpa [flux] using hfluxZero s hsR
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hsqpos)
  have hvDiff : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hvConst : ∀ a b, R < a → R < b → v a = v b := by
    intro a b ha hb
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      hvDiff.differentiableOn
      (fun r hr => hvderivZero r hr)
      ha hb
  have hvOutside : ∀ r, R < r → v r = 0 := by
    have h2R : R < 2 * R := by linarith only [hR]
    have hv2R : v (2 * R) = 0 := by
      by_contra hne
      let A : ℝ := |v (2 * R)|
      let C : ℝ := 2 * (4 * Real.pi)⁻¹ * ∫ y, |g y|
      have hA : 0 < A := by
        dsimp [A]
        exact abs_pos.mpr hne
      have hCnonneg : 0 ≤ C := by
        dsimp [C]
        positivity
      obtain ⟨n, hn⟩ := exists_nat_gt (C / A)
      have hn' : C / A < (n : ℝ) := by exact_mod_cast hn
      let s : ℝ := 2 * R + n
      have hsR : R < s := by
        dsimp [s]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        linarith only [hR, hn0]
      have hspos : 0 < s := lt_trans hR hsR
      have h2Rle : 2 * R ≤ s := by
        dsimp [s]
        exact le_add_of_nonneg_right (Nat.cast_nonneg n)
      have hnorms : ‖s • axis - (0 : Vec3)‖ = s := by
        rw [sub_zero, norm_smul, Real.norm_eq_abs, axis_sup_norm, mul_one,
          abs_of_pos hspos]
      have htail := CKN.pressureNewtonianPotential_tail_bound_centre
        (hg.continuous.integrable_of_hasCompactSupport hgc)
        (x₀ := (0 : Vec3)) hR hsupp (x := s • axis) (by
          rw [sub_zero, norm_smul, Real.norm_eq_abs, axis_sup_norm, mul_one,
            abs_of_pos hspos]
          exact h2Rle)
      have htailV : |v s| ≤ C / s := by
        calc
          |v s| = |CKN.pressureNewtonianPotential g (s • axis)| := rfl
          _ ≤ (2 * (4 * Real.pi)⁻¹ / ‖s • axis - (0 : Vec3)‖) *
              ∫ y, |g y| := htail
          _ = C / s := by
            rw [hnorms]
            dsimp [C]
            ring
      have hconst : v (2 * R) = v s := hvConst (2 * R) s h2R hsR
      have hAbsEq : |v s| = A := by
        dsimp [A]
        rw [← hconst]
      have hnle : (n : ℝ) ≤ s := by
        dsimp [s]
        linarith only [hR]
      have hCn' : C < (n : ℝ) * A := by
        rw [div_lt_iff₀ hA] at hn'
        exact hn'
      have hCs : C < A * s := by
        calc
          C < (n : ℝ) * A := hCn'
          _ ≤ s * A := mul_le_mul_of_nonneg_right hnle hA.le
          _ = A * s := by ring
      have hsmall : C / s < A := (div_lt_iff₀ hspos).2 hCs
      have hbound : A ≤ C / s := by
        rw [← hAbsEq]
        exact htailV
      linarith only [hsmall, hbound]
    intro r hrR
    have hconst : v (2 * R) = v r := hvConst (2 * R) r h2R hrR
    rw [hv2R] at hconst
    exact hconst.symm
  have hnormRad : vec3EuclideanNorm x =
      vec3EuclideanNorm (vec3EuclideanNorm x • axis) := by
    rw [axis_scale_norm, abs_of_nonneg (vec3EuclideanNorm_nonneg x)]
  have hradPot := pressureNewtonianPotential_eq_of_radial hrad hnormRad
  calc
    CKN.pressureNewtonianPotential g x =
        CKN.pressureNewtonianPotential g (vec3EuclideanNorm x • axis) := hradPot
    _ = v (vec3EuclideanNorm x) := rfl
    _ = 0 := hvOutside _ hx

end CKN.Foundation.Harmonic
