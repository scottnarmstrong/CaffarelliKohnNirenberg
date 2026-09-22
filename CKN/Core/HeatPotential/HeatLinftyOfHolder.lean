-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatLinftyCore

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

/-- The Hölder representative supplied by the heat-potential holder theorem
satisfies the pointwise ball estimate for the same representative. -/
theorem heatLinfty_of_holder_representative
    {K : ℕ} {γ P : ℝ} (hγ : 0 < γ) (hP : 1 ≤ P)
    (σ : Fin K → Vec3 → ℂ)
    {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    (C : ℝ) (hC : 0 ≤ C) (hbar : ParabolicPoint → ℂ)
    (hbarLoc : LocallyIntegrable hbar volume)
    (hbarEq : hbar =ᵐ[volume] multiplierHeatPotential σ F G)
    (hbarHolder : ∀ z w, ‖hbar z - hbar w‖ ≤
      C * multiplierHeatSourceSize P (5 / (2 - γ)) (5 / (1 - γ)) F G *
        parabolicDist z w ^ γ) :
    LocallyIntegrable hbar volume ∧
      hbar =ᵐ[volume] multiplierHeatPotential σ F G ∧
      (∀ z : ParabolicPoint, ∀ R : ℝ, 0 < R →
        ∀ w ∈ Metric.ball z R,
          ‖hbar w‖ ≤
            (2 : ℝ) ^ γ * max 1 (parabolicCampanatoHolderConstant γ P) *
                C * multiplierHeatSourceSize P (5 / (2 - γ))
                  (5 / (1 - γ)) F G * R ^ γ +
              (⨍ v in Metric.ball z R, ‖hbar v‖ ^ P) ^ (1 / P)) := by
  refine ⟨hbarLoc, hbarEq, ?_⟩
  intro z R hR w hw
  let s : Set ParabolicPoint :=
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z R
  let _ : IsFiniteMeasure (volume.restrict s) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      dsimp [s]
      exact parabolicBall_closedBall_top hR⟩
  have hsMeas : MeasurableSet s := by
    dsimp [s]
    exact Metric.isClosed_closedBall.measurableSet
  have hAEM : AEStronglyMeasurable hbar (volume.restrict s) :=
    hbarLoc.aestronglyMeasurable.restrict
  have hsize : 0 ≤ multiplierHeatSourceSize P (5 / (2 - γ))
      (5 / (1 - γ)) F G := by
    unfold multiplierHeatSourceSize
    positivity
  let L : ℝ := C * multiplierHeatSourceSize P (5 / (2 - γ))
    (5 / (1 - γ)) F G
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hC hsize
  have hbound : ∀ x ∈ s, ‖hbar x‖ ≤ ‖hbar z‖ + L * R ^ γ := by
    intro x hx
    have hdist : parabolicDist x z ≤ R := by
      rw [← dist_eq_parabolicDist]
      exact Metric.mem_closedBall.mp hx
    have hpow : parabolicDist x z ^ γ ≤ R ^ γ :=
      Real.rpow_le_rpow (parabolicDist_nonneg x z) hdist hγ.le
    have hdiff : ‖hbar x - hbar z‖ ≤ L * R ^ γ := by
      dsimp [L]
      exact (hbarHolder x z).trans
        (mul_le_mul_of_nonneg_left hpow hL)
    calc
      ‖hbar x‖ = ‖(hbar x - hbar z) + hbar z‖ := by
        congr 1
        ring
      _ ≤ ‖hbar x - hbar z‖ + ‖hbar z‖ := norm_add_le _ _
      _ ≤ L * R ^ γ + ‖hbar z‖ := by
        simpa [add_comm] using
          (add_le_add (le_refl (‖hbar z‖)) hdiff)
      _ = ‖hbar z‖ + L * R ^ γ := by ring
  have hboundAE : ∀ᵐ x ∂(volume.restrict s),
      ‖hbar x‖ ≤ ‖hbar z‖ + L * R ^ γ :=
    ae_restrict_of_forall_mem hsMeas hbound
  have hmem : MemLp hbar (ENNReal.ofReal P) (volume.restrict s) :=
    MemLp.of_bound hAEM (‖hbar z‖ + L * R ^ γ) hboundAE
  have hlocal := complex_holder_linf_on_memLp_ball
    (h := hbar) (z := z) (R := R) (γ := γ) (P := P) (L := L)
    hγ hP hR hL hmem hbarHolder w hw
  have hmax : 1 ≤ max 1 (parabolicCampanatoHolderConstant γ P) :=
    le_max_left _ _
  have hcoef : (2 : ℝ) ^ γ * L * R ^ γ ≤
      (2 : ℝ) ^ γ * max 1 (parabolicCampanatoHolderConstant γ P) * C *
        multiplierHeatSourceSize P (5 / (2 - γ)) (5 / (1 - γ)) F G * R ^ γ := by
    have hleft : (2 : ℝ) ^ γ * 1 ≤
        (2 : ℝ) ^ γ * max 1 (parabolicCampanatoHolderConstant γ P) :=
      mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by norm_num) _)
    have htail : 0 ≤ C * multiplierHeatSourceSize P (5 / (2 - γ))
        (5 / (1 - γ)) F G * R ^ γ := by
      exact mul_nonneg (mul_nonneg hC hsize)
        (Real.rpow_nonneg hR.le _)
    have hmul := mul_le_mul_of_nonneg_right hleft htail
    dsimp [L] at hlocal ⊢
    simpa [mul_assoc] using hmul
  exact hlocal.trans (by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add (le_refl ((⨍ v in Metric.ball z R, ‖hbar v‖ ^ P) ^ (1 / P))) hcoef))

end CKN.Core.HeatPotential
