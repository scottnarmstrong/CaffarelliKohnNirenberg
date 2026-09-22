-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.InteriorEstimates
import CKN.Foundation.Parabolic.BallBasics
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import CKN.Foundation.Harmonic.InteriorSupThreeQuarters
import CKN.Foundation.Harmonic.InteriorSupSmoothBoundSupport

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Heat

/-- A smooth harmonic function on a ball obeys the annular Newtonian interior
supremum estimate through the three-quarter ball, with the prescribed-ball
`L^(3/2)` norm. -/
theorem smooth_harmonic_interior_sup_bound_three_quarters
    {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (euclideanBall x₀ ρ))
    (hHarm : ∀ y ∈ euclideanBall x₀ ρ,
      CKN.spatialLaplacian H y = 0)
    (hHmem : MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))) :
    ∀ x ∈ euclideanBall x₀ (3 * ρ / 4),
      |H x| ≤ harmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
  classical
  let U : Set Vec3 := euclideanBall x₀ ρ
  let η : Vec3 → ℝ := eta x₀ (ρ := 4 * ρ / 3) (by positivity)
  let K : Set Vec3 := tsupport η
  have hUopen : IsOpen U := by
    change IsOpen {y : Vec3 | euclideanSqDist y x₀ < ρ ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hηcompact : HasCompactSupport η := by
    simpa only [η, eta] using
      (mollifiedBallCutoff_hasCompactSupport x₀ (show 0 < 4 * ρ / 3 by positivity))
  have hKcompact : IsCompact K := by
    change IsCompact (tsupport η)
    exact hηcompact
  have hKsubU : K ⊆ U := by
    have hs := mollifiedBallCutoff_tsupport_subset_outer x₀
      (show 0 < 4 * ρ / 3 by positivity)
    have hs' : tsupport η ⊆ euclideanBall x₀ ρ := by
      simpa only [η, eta, show 3 * (4 * ρ / 3) / 4 = ρ by ring] using hs
    simpa only [K, U] using hs'
  obtain ⟨ξ, hξ, hξcompact, hξrange, hξts, W, hWopen, hKW, hWU, hξone⟩ :=
    exists_smooth_cutoff_one_near_compact hKcompact hUopen hKsubU
  let F : Vec3 → ℝ := fun y => if hy : y ∈ U then ξ y * H y else 0
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · have hprod : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Vec3 => ξ z * H z) y :=
        hξ.contDiffAt.mul (hH.contDiffAt (hUopen.mem_nhds hy))
      apply hprod.congr_of_eventuallyEq
      filter_upwards [hUopen.mem_nhds hy] with z hz
      change (if hz' : z ∈ U then ξ z * H z else 0) = ξ z * H z
      rw [dite_eq_left hz]
    · have hyts : y ∉ tsupport ξ := fun h => hy (hξts h)
      have hnear := (isClosed_tsupport ξ).isOpen_compl.mem_nhds hyts
      have hFzero : F =ᶠ[𝓝 y] fun _ : Vec3 => (0 : ℝ) := by
        filter_upwards [hnear] with z hz
        have hξz : ξ z = 0 := image_eq_zero_of_notMem_tsupport hz
        by_cases hzU : z ∈ U
        · change (if hz' : z ∈ U then ξ z * H z else 0) = 0
          rw [dite_eq_left hzU, hξz, zero_mul]
        · change (if hz' : z ∈ U then ξ z * H z else 0) = 0
          rw [dite_eq_right hzU]
      exact contDiffAt_const.congr_of_eventuallyEq hFzero
  have hFW : ∀ y ∈ W, F y = H y := by
    intro y hy
    change (if hyU : y ∈ U then ξ y * H y else 0) = H y
    rw [dite_eq_left (hWU hy), hξone y hy, one_mul]
  have hFharm : ∀ y ∈ K, CKN.spatialLaplacian F y = 0 := by
    intro y hy
    calc
      CKN.spatialLaplacian F y = CKN.spatialLaplacian H y :=
        spatialLaplacian_eq_of_eqOn_open hUopen hWopen hWU hF hH hFW y (hKW hy)
      _ = 0 := hHarm y (hKsubU hy)
  intro x hx
  have hxcutoff : x ∈ euclideanBall x₀ (13 * (4 * ρ / 3) / 20) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
    exact hx'.trans (by nlinarith only [hρ])
  have hηx : η x = 1 := by
    simpa only [η, eta] using
      (mollifiedBallCutoff_eq_one_on_inner x₀
        (show 0 < 4 * ρ / 3 by positivity) hxcutoff)
  have hxK : x ∈ K := by
    change x ∈ tsupport η
    apply subset_tsupport (f := η)
    exact Function.mem_support.mpr (by rw [hηx]; norm_num)
  have hFx : F x = H x := hFW x (hKW hxK)
  let A : Set Vec3 := cutoffAnnulus x₀ (4 * ρ / 3)
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact cutoffAnnulus_measurable (by positivity)
  have hAsub : A ⊆ euclideanBall x₀ ρ := by
    dsimp [A]
    exact cutoffAnnulus_subset_outer_ball hρ
  have hAvol : volume A ≠ ∞ := by
    apply ne_of_lt
    have hAclosed : A ⊆ euclideanClosedBall x₀ ρ := by
      intro y hy
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hρ.le).2
      exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).1 (hAsub hy)).le
    exact lt_of_le_of_lt (measure_mono hAclosed)
      ((isCompact_euclideanClosedBall x₀ hρ.le).measure_lt_top)
  let _ : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAvol
  have hxinner : x ∈ euclideanBall x₀ (13 * (4 * ρ / 3) / 20) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
    exact hx'.trans (by nlinarith only [hρ])
  have hrep := smooth_harmonic_annular_representation_on_tsupport
    hF (show 0 < 4 * ρ / 3 by positivity) hFharm hxinner
  have hH_A : MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict A) :=
    hHmem.mono_measure (Measure.restrict_mono_set volume hAsub)
  have hHlp_mono : lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict A) ≤ lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) := by
    rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
    apply ENNReal.toReal_mono hHmem.eLpNorm_lt_top.ne
    exact eLpNorm_mono_measure H (Measure.restrict_mono_set volume hAsub)
  have hFbound : ∀ y : Vec3, ‖F y‖ ≤ ‖H y‖ := by
    intro y
    by_cases hy : y ∈ U
    · have hFy : F y = ξ y * H y := by
        change (if hy' : y ∈ U then ξ y * H y else 0) = ξ y * H y
        rw [dite_eq_left hy]
      have hξabs : |ξ y| ≤ 1 := abs_le.mpr ⟨by linarith only [(hξrange y).1],
        (hξrange y).2⟩
      rw [Real.norm_eq_abs, hFy, abs_mul, Real.norm_eq_abs]
      calc
        |ξ y| * |H y| ≤ 1 * |H y| :=
          mul_le_mul_of_nonneg_right hξabs (abs_nonneg _)
        _ = |H y| := by ring
    · change ‖(if hy' : y ∈ U then ξ y * H y else 0)‖ ≤ ‖H y‖
      rw [dite_eq_right hy]
      rw [norm_zero]
      exact norm_nonneg (H y)
  have hF_A : MemLp F (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict A) :=
    hH_A.of_le hF.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hFbound y)
  have hFlp_mono : lpNorm F (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict A) ≤ lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) := by
    calc
      lpNorm F (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) ≤
          lpNorm H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) := by
        rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
        apply ENNReal.toReal_mono hH_A.eLpNorm_lt_top.ne
        exact eLpNorm_mono_ae hF_A.aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => hFbound y)
      _ ≤ lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := hHlp_mono
  let source : Vec3 → ℝ := fun y =>
    newtonianKernel (x - y) *
      (F y * CKN.spatialLaplacian
        (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y)
  have hsource_cont : ContinuousOn
      (fun y => newtonianKernel (x - y) *
        CKN.spatialLaplacian
          (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y) A := by
    intro y hy
    have hxy : x - y ≠ 0 := by
      intro hzero
      have hd := cutoff_annulus_norm_distance_for_three_quarters hρ hx hy
      rw [hzero] at hd
      exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hd)
    have hN : ContinuousAt (fun z : Vec3 => newtonianKernel (x - z)) y :=
      (newtonianKernel_continuousAt hxy).comp
        (continuousAt_const.sub continuousAt_id)
    have hD : Continuous (CKN.spatialLaplacian
        (eta (ρ := 4 * ρ / 3) x₀ (by positivity))) := by
      simpa only [eta] using
        (CKN.contDiff_spatialLaplacian_smooth
          (mollifiedBallCutoff_smooth x₀ (by positivity))).continuous
    exact hN.continuousWithinAt.mul hD.continuousAt.continuousWithinAt
  let k₀ : Vec3 → ℝ := fun y =>
    newtonianKernel (x - y) *
      CKN.spatialLaplacian (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y
  have hk₀cont : ContinuousOn k₀ A := by
    simpa only [k₀] using hsource_cont
  have hk₀bound : ∀ y ∈ A, |k₀ y| ≤
      harmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
    intro y hy
    exact source_kernel_bound_scaled_three_quarters hρ hx hy
  have hk₀ : MemLp k₀ (ENNReal.ofReal (3 : ℝ))
      (volume.restrict A) := memLp_of_continuousOn_bound hAmeas hk₀cont
        _ hk₀bound _
  have hk₀lp := lpNorm_bound_on hAmeas
    (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ 0)
    (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ ∞)
    (harmonicInteriorSourceConstant * (ρ ^ 3)⁻¹)
    (mul_nonneg harmonicInteriorSourceConstant_nonneg (by positivity)) (fun y hy => by
      simpa only [Real.norm_eq_abs] using hk₀bound y hy)
  have hk₀lp' : lpNorm k₀ (ENNReal.ofReal (3 : ℝ))
      (volume.restrict A) ≤ harmonicInteriorSourceConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ := by
    have hv := volume_root_bound hρ hAsub
    have hk₀lp'' : lpNorm k₀ (ENNReal.ofReal (3 : ℝ))
        (volume.restrict A) ≤ harmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ *
          (volume A).toReal ^ (1 / (3 : ℝ)) := by
      convert hk₀lp using 1; norm_num
    exact (calc
        lpNorm k₀ (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) ≤
            harmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ *
              (volume A).toReal ^ (1 / (3 : ℝ)) := hk₀lp''
        _ ≤ harmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ *
              (ρ * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ))) := by
                exact mul_le_mul_of_nonneg_left hv
                  (mul_nonneg harmonicInteriorSourceConstant_nonneg (by positivity))
        _ = harmonicInteriorSourceConstant *
              (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ := by
                field_simp [hρ.ne']
                )
  have hsource : |∫ y, source y| ≤
      harmonicInteriorSourceConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    have hbound := integral_mul_memLp_bound_on hAmeas hF_A hk₀
      (fun y hy => by
        dsimp [k₀]
        have hz := eta_laplacian_zero_off_annulus (R := 4 * ρ / 3)
          (by positivity) (by simpa [A] using hy)
        simp [hz])
    calc
      |∫ y, source y| ≤
          lpNorm F (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) *
            lpNorm k₀ (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
        have heq : (fun y : Vec3 => newtonianKernel (x - y) *
            (F y * CKN.spatialLaplacian
              (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y)) =
            (fun y => F y * k₀ y) := by
          funext y
          simp only [k₀]
          ring
        rw [show source = fun y => newtonianKernel (x - y) *
            (F y * CKN.spatialLaplacian
              (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) y) by rfl, heq]
        exact hbound
      _ ≤ _ := by
        calc
          _ ≤ (lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x₀ ρ))) *
              lpNorm k₀ (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) :=
            mul_le_mul_of_nonneg_right hFlp_mono lpNorm_nonneg
          _ ≤ (lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x₀ ρ))) *
              (harmonicInteriorSourceConstant *
                (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hk₀lp' lpNorm_nonneg
          _ = _ := by ring
  have hderiv_bound : ∀ i : Fin 3, |∫ y, F y *
      CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
        x x₀ (by positivity) i) i y| ≤
      harmonicInteriorGradientConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    intro i
    let k : Vec3 → ℝ := fun y =>
      CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
        x x₀ (by positivity) i) i y
    have hxinner' : x ∈ euclideanBall x₀ (13 * (4 * ρ / 3) / 20) := hxinner
    have hkcont : Continuous k := by
      dsimp [k]
      exact ((kernelCutoffDerivative_contDiff_one x x₀ (by positivity)
        hxinner' i).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hkbound : ∀ y ∈ A, |k y| ≤
        harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ := by
      intro y hy
      exact kernel_cutoff_derivative_bound_scaled_three_quarters hρ hx hy i i
    have hk : MemLp k (ENNReal.ofReal (3 : ℝ))
        (volume.restrict A) := memLp_of_continuousOn_bound hAmeas
      hkcont.continuousOn _ hkbound _
    have hklp := lpNorm_bound_on hAmeas
      (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ 0)
      (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ ∞)
      (harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹)
      (mul_nonneg harmonicInteriorGradientConstant_nonneg (by positivity)) (fun y hy => by
        simpa only [Real.norm_eq_abs] using hkbound y hy)
    have hklp' : lpNorm k (ENNReal.ofReal (3 : ℝ))
        (volume.restrict A) ≤ harmonicInteriorGradientConstant *
          (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ := by
      have hv := volume_root_bound hρ hAsub
      have hklp'' : lpNorm k (ENNReal.ofReal (3 : ℝ))
          (volume.restrict A) ≤ harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ *
            (volume A).toReal ^ (1 / (3 : ℝ)) := by
        convert hklp using 1; norm_num
      exact (calc
          lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) ≤
              harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ *
                (volume A).toReal ^ (1 / (3 : ℝ)) := hklp''
          _ ≤ harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ *
                (ρ * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ))) := by
                  exact mul_le_mul_of_nonneg_left hv
                    (mul_nonneg harmonicInteriorGradientConstant_nonneg (by positivity))
          _ = harmonicInteriorGradientConstant *
                (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ := by
                  field_simp [hρ.ne']
                  )
    have hbound := integral_mul_memLp_bound_on hAmeas hF_A hk
      (fun y hy => by
        dsimp [k]
        exact kernel_cutoff_derivative_zero_off_annulus_three_quarters
          hρ hx (by simpa [A] using hy) i i)
    calc
      |∫ y, F y * k y| ≤
          lpNorm F (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) *
            lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
        simpa [k] using hbound
      _ ≤ _ := by
        calc
          _ ≤ (lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x₀ ρ))) *
              lpNorm k (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) :=
            mul_le_mul_of_nonneg_right hFlp_mono lpNorm_nonneg
          _ ≤ (lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x₀ ρ))) *
              (harmonicInteriorGradientConstant *
                (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hklp' lpNorm_nonneg
          _ = _ := by ring
  have hsum : |2 * ∑ i : Fin 3, ∫ y, F y *
      CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
        x x₀ (by positivity) i) i y| ≤
      6 * harmonicInteriorGradientConstant *
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    let I : Fin 3 → ℝ := fun i => ∫ y : Vec3, F y *
      CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
        x x₀ (by positivity) i) i y
    change 2 * |∑ i : Fin 3, I i| ≤ _
    have habs : |∑ i : Fin 3, I i| ≤ ∑ i : Fin 3, |I i| := by
      simpa only [Fin.sum_univ_three] using
        (Finset.abs_sum_le_sum_abs I (Finset.univ : Finset (Fin 3)))
    calc
      2 * |∑ i : Fin 3, I i| ≤ 2 * ∑ i : Fin 3, |I i| :=
        mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ 2 * ∑ i : Fin 3,
          (harmonicInteriorGradientConstant *
            (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ *
            lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : 0 ≤ (2 : ℝ))
        apply Finset.sum_le_sum
        intro i hi
        exact hderiv_bound i
      _ = _ := by simp; ring
  rw [← hFx, hrep]
  calc
    |(-∫ y, source y) + 2 * ∑ i : Fin 3, ∫ y, F y *
        CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
          x x₀ (by positivity) i) i y| ≤
        |∫ y, source y| + |2 * ∑ i : Fin 3, ∫ y, F y *
          CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
            x x₀ (by positivity) i) i y| := by
      calc
        |(-∫ y, source y) + 2 * ∑ i : Fin 3, ∫ y, F y *
            CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
              x x₀ (by positivity) i) i y| ≤
            |-(∫ y, source y)| + |2 * ∑ i : Fin 3, ∫ y, F y *
              CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
                x x₀ (by positivity) i) i y| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    _ ≤ harmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
      rw [show harmonicInteriorSupConstant =
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
          (harmonicInteriorSourceConstant +
            6 * harmonicInteriorGradientConstant) by rfl]
      exact (add_le_add hsource hsum).trans_eq (by ring)



end CKN.Foundation.Heat
