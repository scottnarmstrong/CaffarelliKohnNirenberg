-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.UniformBallGluing
import CKN.Core.Endgame.BallRepresentativeBound
import CKN.Core.Endgame.SourceCoefficient
import CKN.Core.Endgame.CompactBall
import CKN.Core.Parameters

/-! # Quantitative endgame from uniform local source bounds

The local radius and final coefficient depend only on numerical data. The
velocity L^(10/3) bound controls the absolute value of the representative;
source Morrey bounds control its seminorm. Fixed-radius gluing preserves
this dependence on every prescribed inner ball.
-/

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- A fixed local radius inside the Step 2 Morrey carrier. -/
def endgameLocalRadius (r₂ r₃ : ℝ) : ℝ := (r₂ / 4 - r₃) / 512

/-- The full local norm bound from numerical source bounds and a velocity
L^(10/3) cap. -/
def endgameLocalHolderBound (q a U : ℝ) (KF KG : ℝ≥0∞) : ℝ :=
  let H := uniformVectorHeatHolderCoefficient (stepGamma₀ q)
    (stepTheta₀ (stepGamma₀ q)) (stepTheta₁ (stepGamma₀ q)) (6 / 5) KF KG
  H * (2 * a) ^ (stepGamma₀ q) +
    (8 * Real.pi / 3 * a ^ 5) ^ (-3 / 10 : ℝ) * U + H

/-- The explicit norm coefficient after gluing on an inner ball. -/
def endgameHolderBound (q r₂ r₃ U : ℝ) (KF KG : ℝ≥0∞) : ℝ :=
  let a := endgameLocalRadius r₂ r₃
  let L := endgameLocalHolderBound q a U KF KG
  L + max L (2 * L / (a / 2) ^ (stepGamma₀ q))

/-- The local coefficient is nonnegative for nonnegative numerical data. -/
theorem endgameLocalHolderBound_nonneg (q : ℝ) {a U : ℝ}
    (ha : 0 ≤ a) (hU : 0 ≤ U) (KF KG : ℝ≥0∞) :
    0 ≤ endgameLocalHolderBound q a U KF KG := by
  have hH := uniformVectorHeatHolderCoefficient_nonneg (stepGamma₀ q)
    (stepTheta₀ (stepGamma₀ q)) (stepTheta₁ (stepGamma₀ q)) (6 / 5) KF KG
  unfold endgameLocalHolderBound
  positivity

/-- Uniform numerical bounds on actual local heat sources give a full
Hölder norm with explicit numerical dependence and interior regularity.
The source witnesses contain no assumed Hölder conclusion. -/
theorem endgame_holder_norm_of_local_source_bounds
    (q r₂ r₃ U : ℝ) (KF KG : ℝ≥0∞)
    (hq : 5 / 2 < q) (hr₃ : 0 < r₃) (hrr : r₃ < r₂ / 4)
    (hU : 0 ≤ U) (hKF : KF < ∞) (hKG : KG < ∞)
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {z₀ : ParabolicPoint}
    (hdom : Metric.ball z₀ r₂ ⊆ spaceTimeSet Ω I)
    (hu : AEStronglyMeasurable (fun z => vec3EuclideanNorm (u z))
      (volume.restrict (Metric.ball z₀ r₂)))
    (hUnorm : eLpNorm (fun z => vec3EuclideanNorm (u z))
      (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict (Metric.ball z₀ r₂)) ≤
        ENNReal.ofReal U)
    (hsource : ∀ z ∈ Metric.closedBall z₀ r₃,
      ∃ (F : ParabolicPoint → Vec3) (G : Fin 3 → ParabolicPoint → Vec3),
        (∀ i, AEMeasurable (fun w => F w i) volume) ∧
        (∀ j i, AEMeasurable (fun w => G j w i) volume) ∧
        (∀ i, HasCompactSupport (fun w => F w i)) ∧
        (∀ j i, HasCompactSupport (fun w => G j w i)) ∧
        (∀ i, morreyNorm (6 / 5 : ℝ) (stepTheta₀ (stepGamma₀ q))
          (fun w => F w i) ≤ KF) ∧
        (∀ j i, morreyNorm (6 / 5 : ℝ) (stepTheta₁ (stepGamma₀ q))
          (fun w => G j w i) ≤ KG) ∧
        u =ᵐ[volume.restrict (Metric.ball z (endgameLocalRadius r₂ r₃))]
          (fun w i => heatPotential (fun y => F y i) (fun j y => G j y i) w)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (Metric.closedBall z₀ r₃)] u ∧
      ParabolicHolderVecNormLE (Metric.closedBall z₀ r₃) w (stepGamma₀ q)
        (endgameHolderBound q r₂ r₃ U KF KG) ∧
      ∀ z ∈ Metric.ball z₀ r₃, IsRegularPoint Ω I u z := by
  let a := endgameLocalRadius r₂ r₃
  let H := uniformVectorHeatHolderCoefficient (stepGamma₀ q)
    (stepTheta₀ (stepGamma₀ q)) (stepTheta₁ (stepGamma₀ q)) (6 / 5) KF KG
  have ha : 0 < a := by dsimp [a, endgameLocalRadius]; linarith only [hrr]
  have hH : 0 ≤ H := uniformVectorHeatHolderCoefficient_nonneg _ _ _ _ _ _
  have hγ := stepGamma₀_pos hq
  have hγ₁ := stepGamma₀_lt_one q
  have hθ₀ := stepTheta₀_gt_half hγ hγ₁
  have hθ₁ := stepTheta₁_gt_five hγ hγ₁
  have hlocal : ∀ z ∈ Metric.closedBall z₀ r₃, ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (Metric.ball z a)] u ∧
      ParabolicHolderVecNormLE (Metric.ball z a) w (stepGamma₀ q)
        (endgameLocalHolderBound q a U KF KG) := by
    intro z hz
    obtain ⟨F, G, hF, hG, hFc, hGc, hNF, hNG, hrep⟩ := hsource z hz
    obtain ⟨w, hw, hsemi, _⟩ := vector_heat_representative_and_seminorm_of_morrey
      hγ hγ₁ (stepTheta₀_inv _) (stepTheta₁_inv _) (by norm_num : (1 : ℝ) ≤ 6 / 5)
      (by linarith only [hθ₀]) (by linarith only [hθ₁]) hF hG
      (fun i => (hNF i).trans_lt hKF) (fun j i => (hNG j i).trans_lt hKG) hFc hGc
    have hcoef := vectorHeatHolderCoefficient_le_of_source_bounds
      (stepGamma₀ q) (stepTheta₀ (stepGamma₀ q))
      (stepTheta₁ (stepGamma₀ q)) (6 / 5) KF KG hKF hKG hNF hNG
    have hwsemi : ∀ x y, vec3EuclideanNorm (w x - w y) ≤
        H * parabolicDist x y ^ (stepGamma₀ q) := by
      intro x y
      exact (hsemi x y).trans (mul_le_mul_of_nonneg_right hcoef
        (Real.rpow_nonneg (parabolicDist_nonneg _ _) _))
    have hwlocal : w =ᵐ[volume.restrict (Metric.ball z a)]
        (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x) :=
      ae_restrict_of_ae hw
    have hwu : w =ᵐ[volume.restrict (Metric.ball z a)] u := hwlocal.trans hrep.symm
    have hsub : Metric.ball z a ⊆ Metric.ball z₀ r₂ :=
      parabolic_ball_subset_ball_of_center_mem_closedBall hz
        (by dsimp [a, endgameLocalRadius]; linarith only [hr₃, hrr])
    have hμ := Measure.restrict_mono_set volume hsub
    refine ⟨w, hwu, ?_⟩
    exact ball_holder_norm_of_seminorm_of_eLpNorm_ten_thirds z ha hγ.le hH hU
      hwsemi hwu (hu.mono_measure hμ)
      ((eLpNorm_mono_measure _ hμ).trans hUnorm)
  obtain ⟨w, hw, hnorm⟩ := exists_holder_norm_on_compact_of_uniform_balls
    (isCompact_parabolic_closedBall z₀ r₃) ha
    (endgameLocalHolderBound_nonneg q ha.le hU KF KG) hγ hlocal
  refine ⟨w, hw, hnorm, ?_⟩
  intro z hz
  exact regular_point_of_holder_norm Metric.isOpen_ball hz Metric.ball_subset_closedBall
    ((Metric.ball_subset_ball (by linarith only [hr₃, hrr])).trans hdom)
    hγ hγ₁.le hw hnorm

end CKN.Core.Endgame
