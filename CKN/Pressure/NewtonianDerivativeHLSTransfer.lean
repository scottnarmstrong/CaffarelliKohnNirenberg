-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.NewtonianDerivativeHLS
import CKN.Foundation.Euclidean.InterpolationLpChar
import CKN.Foundation.Harmonic.InteriorBasic

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
open CKN.Foundation.Euclidean

set_option autoImplicit false

noncomputable section

namespace CKN

private lemma newtonian_first_derivative_kernel_integrand_ae
    (j : Fin 3) (g : Vec3 → ℝ) (x : Vec3) :
    (fun y : Vec3 => ((x - y) j /
        (4 * Real.pi * vec3EuclideanNorm (x - y) ^ 3)) * g y) =ᵐ[volume]
      (fun y => -(CKN.spatialDeriv newtonianKernel j (x - y) * g y)) := by
  filter_upwards [Measure.ae_ne volume x] with y hy
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr hy.symm
  have hnorm : 0 < vec3EuclideanNorm (x - y) := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hzero
    apply hxy
    exact (WithLp.toLp_eq_zero 2).mp hzero
  rw [newtonianKernel_spatialDeriv_formula hxy j, q_eq_vec3Norm_sq]
  have hpow : (vec3EuclideanNorm (x - y) ^ 2) ^ (-(3 : ℝ) / 2) =
      (vec3EuclideanNorm (x - y)) ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnorm.le]
    norm_num
  have hpow3 : (vec3EuclideanNorm (x - y)) ^ (-3 : ℝ) =
      (vec3EuclideanNorm (x - y) ^ 3)⁻¹ := by
    calc
      (vec3EuclideanNorm (x - y)) ^ (-3 : ℝ) =
          (vec3EuclideanNorm (x - y) ^ (3 : ℝ))⁻¹ :=
        Real.rpow_neg hnorm.le (3 : ℝ)
      _ = (vec3EuclideanNorm (x - y) ^ 3)⁻¹ := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
        rw [Real.rpow_natCast]
  rw [hpow, hpow3]
  field_simp

/-- The signed first-derivative Newtonian potential has the exact L^{5/2}-to-L^{15}
bound of the source statement, for arbitrary `MemLp` data. -/
theorem newtonian_first_derivative_hls :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Vec3 → ℝ),
      MemLp g (ENNReal.ofReal (5 / 2 : ℝ)) volume → ∀ j : Fin 3,
        (∀ᵐ x ∂volume, Integrable (fun y : Vec3 =>
          ((x - y) j / (4 * Real.pi * vec3EuclideanNorm (x - y) ^ 3) * g y)
            ) volume) ∧
        MemLp (fun x => ∫ y, ((x - y) j /
          (4 * Real.pi * vec3EuclideanNorm (x - y) ^ 3)) * g y)
          15 volume ∧
        eLpNorm (fun x => ∫ y, ((x - y) j /
          (4 * Real.pi * vec3EuclideanNorm (x - y) ^ 3)) * g y)
          15 volume ≤ ENNReal.ofReal C *
            eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
  obtain ⟨C, hC, hHLS⟩ := newtonianDerivativePotential_hls_display
  refine ⟨C, hC, ?_⟩
  intro g hg j
  let hga : AEMeasurable g volume := hg.aestronglyMeasurable.aemeasurable
  let gm : Vec3 → ℝ := hga.mk g
  have hgm : Measurable gm := hga.measurable_mk
  have hggm : g =ᵐ[volume] gm := hga.ae_eq_mk
  have hgmMem : MemLp gm (ENNReal.ofReal (5 / 2 : ℝ)) volume :=
    (memLp_congr_ae hggm).1 hg
  have hfinite' := lintegral_absE_rpow_lt_top
    (f := gm) (p := (5 / 2 : ℝ)) (by norm_num) hgmMem
  have hfinite : (∫⁻ y, ENNReal.ofReal |gm y| ^ (5 / 2 : ℝ)) < ∞ := by
    simpa [absE] using hfinite'
  obtain ⟨hIntRep, hMemRep, hBoundRep⟩ := hHLS gm hgm hfinite j
  have hIntOrig : ∀ᵐ x ∂volume, Integrable
      (fun y => CKN.spatialDeriv newtonianKernel j (x - y) * g y) volume := by
    filter_upwards [hIntRep] with x hx
    apply hx.congr
    filter_upwards [hggm] with y hy
    rw [hy]
  have hInt : ∀ᵐ x ∂volume, Integrable
      (fun y : Vec3 => ((x - y) j /
        (4 * Real.pi * vec3EuclideanNorm (x - y) ^ 3) * g y)) volume := by
    filter_upwards [hIntOrig] with x hx
    have hneg : Integrable
        (fun y => -(CKN.spatialDeriv newtonianKernel j (x - y) * g y)) volume :=
      hx.neg
    exact hneg.congr (newtonian_first_derivative_kernel_integrand_ae j g x).symm
  have hPotentialEq : pressureNewtonianDerivativePotential j g =
      pressureNewtonianDerivativePotential j gm :=
    pressureNewtonianDerivativePotential_congr_of_ae_eq j hggm
  have hRawEq :
      (fun x => ∫ y, ((x - y) j /
        (4 * Real.pi * vec3EuclideanNorm (x - y) ^ 3) * g y)) =ᵐ[volume]
      (fun x => -pressureNewtonianDerivativePotential j gm x) := by
    filter_upwards [] with x
    calc
      (∫ y, ((x - y) j /
          (4 * Real.pi * vec3EuclideanNorm (x - y) ^ 3) * g y)) =
          (∫ y, -(CKN.spatialDeriv newtonianKernel j (x - y) * g y)) :=
        integral_congr_ae (newtonian_first_derivative_kernel_integrand_ae j g x)
      _ = -(∫ y, CKN.spatialDeriv newtonianKernel j (x - y) * g y) := by
        rw [integral_neg]
      _ = -pressureNewtonianDerivativePotential j g x := rfl
      _ = -pressureNewtonianDerivativePotential j gm x := by rw [hPotentialEq]
  have hNegMem : MemLp (fun x => -pressureNewtonianDerivativePotential j gm x)
      15 volume := by
    have hfun : (fun x => -pressureNewtonianDerivativePotential j gm x) =
        -pressureNewtonianDerivativePotential j gm := rfl
    rw [hfun]
    simpa using hMemRep.neg
  refine ⟨hInt, (memLp_congr_ae hRawEq).2 hNegMem, ?_⟩
  have hOutputNorm : eLpNorm (pressureNewtonianDerivativePotential j gm)
        (15 : ℝ≥0∞) volume =
      eLpNorm' (pressureNewtonianDerivativePotential j gm) (15 : ℝ) volume := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)
      hMemRep.aestronglyMeasurable]
    norm_num
  have hInputPower :
      (∫⁻ y, ENNReal.ofReal |gm y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) =
        eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
    have hPowerRep :
        (∫⁻ y, ENNReal.ofReal |gm y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) =
          eLpNorm' gm (5 / 2 : ℝ) volume := by
      symm
      rw [eLpNorm'_eq_lintegral_enorm]
      congr 1
      · apply lintegral_congr_ae
        filter_upwards [] with y
        simp [Real.enorm_eq_ofReal_abs]
      · norm_num
    calc
      _ = eLpNorm' gm (5 / 2 : ℝ) volume := hPowerRep
      _ = eLpNorm gm (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
        symm
        rw [eLpNorm_eq_eLpNorm' (by norm_num) ENNReal.ofReal_ne_top
          hgmMem.aestronglyMeasurable]
        norm_num
      _ = eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume :=
        (eLpNorm_congr_ae hggm).symm
  calc
    eLpNorm (fun x => ∫ y, ((x - y) j /
        (4 * Real.pi * vec3EuclideanNorm (x - y) ^ 3) * g y))
        (15 : ℝ≥0∞) volume =
        eLpNorm' (pressureNewtonianDerivativePotential j gm) (15 : ℝ) volume := by
          rw [eLpNorm_congr_ae hRawEq]
          have hNegNorm : eLpNorm
              (fun x => -pressureNewtonianDerivativePotential j gm x)
              (15 : ℝ≥0∞) volume =
                eLpNorm (pressureNewtonianDerivativePotential j gm)
                  (15 : ℝ≥0∞) volume := by
            calc
              _ = eLpNorm (-pressureNewtonianDerivativePotential j gm)
                  (15 : ℝ≥0∞) volume := by
                    apply eLpNorm_congr_ae
                    filter_upwards [] with x
                    rfl
              _ = eLpNorm (pressureNewtonianDerivativePotential j gm)
                  (15 : ℝ≥0∞) volume := by rw [eLpNorm_neg]
          rw [hNegNorm, hOutputNorm]
    _ ≤ ENNReal.ofReal C *
        (∫⁻ y, ENNReal.ofReal |gm y| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := hBoundRep
    _ = ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
      rw [hInputPower]

end CKN
