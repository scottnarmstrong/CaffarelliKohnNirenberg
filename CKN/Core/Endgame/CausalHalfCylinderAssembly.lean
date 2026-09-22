-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.CausalHalfCylinder
import CKN.Core.HeatPotential.HeatHolderOfConclusion
import CKN.Core.HeatPotential.GeneralSymbolHeatConclusionAssembly
import CKN.Core.HeatPotential.HeatFarAssembly

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Endgame

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

private theorem vec3EuclideanNorm_le_sum_abs (v : Vec3) :
    vec3EuclideanNorm v ≤ ∑ i, |v i| := by
  rw [vec3EuclideanNorm]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) ≤
      (|v 0| + (|v 1| + |v 2|)) ^ 2
    have h0 := sq_abs (v 0)
    have h1 := sq_abs (v 1)
    have h2 := sq_abs (v 2)
    have h01 := mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1))
    have h02 := mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2))
    have h12 := mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))
    nlinarith only [h0, h1, h2, h01, h02, h12]

private def causalHalfCylinderBound (ε₀ : ℝ) (Kσ : ℝ) : ℝ :=
  2 * Kσ +
    ((volume (parabolicCylinder 0 0 (1 / 2))).toReal⁻¹ * ε₀) ^ (1 / 3 : ℝ)

private theorem causalHalfCylinderBound_nonneg
    {ε₀ Kσ : ℝ} (hε₀ : 0 ≤ ε₀) (hKσ : 0 ≤ Kσ) :
    0 ≤ causalHalfCylinderBound ε₀ Kσ := by
  unfold causalHalfCylinderBound
  positivity

/-! The source package is consumed before the solution variables, so the
    coefficient produced below is fixed uniformly for all solutions. -/
theorem causal_halfCylinder_of_past_source_producer
    (q : ℝ) (hq : 5 / 2 < q) (ε₀ K : ℝ) (hε₀ : 0 ≤ ε₀) (hK : 0 ≤ K)
    (hsource :
      ∃ N : ℕ, ∃ σ : Fin N → Vec3 → ℂ, ∃ KF KG : ℝ≥0∞,
        (∀ k, SmoothOffOrigin (σ k)) ∧
        (∀ k, IsDegreeOneHomogeneous (σ k)) ∧
        KF < ⊤ ∧ KG < ⊤ ∧
        ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
          (Du : ParabolicPoint → Fin 3 → Vec3)
          (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
          IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
          closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
          (∫⁻ z in parabolicCylinder 0 0 1,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
          let Q₂s : Set ParabolicPoint :=
            vec3Ball 0 (5 / 8) ×ˢ Ioc (-(25 / 64 : ℝ)) 0
          (∀ i : Fin 3,
            morreyBallNorm 3 stepTau₂ (Q₂s.indicator (fun z => u z i)) ≤
              ENNReal.ofReal K) →
          (∀ i j : Fin 3,
            morreyBallNorm 2 stepTau₃ (Q₂s.indicator (fun z => Du z i j)) ≤
              ENNReal.ofReal K) →
          morreyBallNorm (3 / 2) stepTauP (Q₂s.indicator p) ≤ ENNReal.ofReal K →
          ∃ Fminus : ParabolicPoint → Vec3,
          ∃ Gminus : Fin N → ParabolicPoint → Vec3,
            (∀ i : Fin 3, AEMeasurable (fun z => Fminus z i) volume) ∧
            (∀ (j : Fin N) (i : Fin 3),
              AEMeasurable (fun z => Gminus j z i) volume) ∧
            (∀ i : Fin 3,
              morreyNorm (6 / 5) (stepTheta₀ (stepGamma₀ q))
                (fun z => Fminus z i) ≤ KF) ∧
            (∀ (j : Fin N) (i : Fin 3),
              morreyNorm (6 / 5) (stepTheta₁ (stepGamma₀ q))
                (fun z => Gminus j z i) ≤ KG) ∧
            (∀ i : Fin 3, HasCompactSupport (fun z => Fminus z i)) ∧
            (∀ (j : Fin N) (i : Fin 3),
              HasCompactSupport (fun z => Gminus j z i)) ∧
            (∀ z : ParabolicPoint,
              z ∉ Q₂s → Fminus z = 0) ∧
            (∀ j : Fin N, ∀ z : ParabolicPoint,
              z ∉ Q₂s → Gminus j z = 0) ∧
            (∀ i : Fin 3,
              (fun z => (u z i : ℂ)) =ᵐ[volume.restrict
                (parabolicCylinder 0 0 (1 / 2))]
                multiplierHeatPotential σ (fun y => Fminus y i)
                  (fun k y => Gminus k y i)) ∧
            (∀ i : Fin 3, ∀ᵐ w ∂volume,
              Integrable (fun v =>
                (heatKernelPlus (pointSub w v) : ℂ) * (Fminus v i : ℂ)) volume ∧
              ∀ k, Integrable (fun v =>
                spatialMultiplierHeatKernel (σ k) (pointSub w v).1
                  (pointSub w v).2 * (Gminus k v i : ℂ)) volume) ∧
            (∀ i : Fin 3, ∀ᵐ w ∂volume,
              multiplierHeatPotential σ (fun y => Fminus y i)
                  (fun k y => Gminus k y i) w =
                (∫ s : ℝ, spatialHeatConv (w.2 - s)
                  (fun y : Vec3 => (Fminus (y, s) i : ℂ)) w.1) +
                ∑ k, ∫ s : ℝ, spatialMultiplierApply (σ k)
                  (spatialHeatConv (w.2 - s)
                    (fun y => (Gminus k (y, s) i : ℂ))) w.1)) :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        (∀ i : Fin 3,
          morreyBallNorm 3 stepTau₂
            ((vec3Ball 0 (5 / 8) ×ˢ Ioc (-(25 / 64 : ℝ)) 0).indicator
              (fun z => u z i)) ≤ ENNReal.ofReal K) →
        (∀ i j : Fin 3,
          morreyBallNorm 2 stepTau₃
            ((vec3Ball 0 (5 / 8) ×ˢ Ioc (-(25 / 64 : ℝ)) 0).indicator
              (fun z => Du z i j)) ≤ ENNReal.ofReal K) →
        morreyBallNorm (3 / 2) stepTauP
          ((vec3Ball 0 (5 / 8) ×ˢ Ioc (-(25 / 64 : ℝ)) 0).indicator p) ≤
            ENNReal.ofReal K →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w (stepGamma₀ q) C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  obtain ⟨N, σ, KF, KG, hσ, hhom, hKF, hKG, hproducer⟩ := hsource
  have hγ : 0 < stepGamma₀ q := stepGamma₀_pos hq
  have hγ1 : stepGamma₀ q < 1 := stepGamma₀_lt_one q
  have hθ₀ : 1 / stepTheta₀ (stepGamma₀ q) =
      (2 - stepGamma₀ q) / 5 := stepTheta₀_inv _
  have hθ₁ : 1 / stepTheta₁ (stepGamma₀ q) =
      (1 - stepGamma₀ q) / 5 := stepTheta₁_inv _
  have hP : (1 : ℝ) ≤ 6 / 5 := by norm_num
  have hPθ₀ : (6 / 5 : ℝ) ≤ stepTheta₀ (stepGamma₀ q) := by
    linarith only [stepTheta₀_gt_half hγ hγ1]
  have hPθ₁ : (6 / 5 : ℝ) ≤ stepTheta₁ (stepGamma₀ q) := by
    linarith only [stepTheta₁_gt_five hγ hγ1]
  obtain ⟨Cfar, hCfar, hfar⟩ := heatFar hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ σ hσ hhom
  obtain ⟨Ccon, hCcon, hcon⟩ := heatConclusion_of_heatFar
    hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ σ hσ hhom ⟨Cfar, hCfar, hfar⟩
  have hcamp : 0 ≤ parabolicCampanatoHolderConstant (stepGamma₀ q) (6 / 5) := by
    have h := heat_holder_campanato_coefficient_nonneg
      hγ (p := (6 / 5 : ℝ)) (K := (1 : ℝ))
    simpa using h
  let A : ℝ := 2 * parabolicCampanatoHolderConstant (stepGamma₀ q) (6 / 5) * Ccon
  let S : ℝ := KF.toReal + N * KG.toReal
  let Kσ : ℝ := 3 * A * S
  let V : ℝ :=
    ((volume (parabolicCylinder 0 0 (1 / 2))).toReal⁻¹ * ε₀) ^ (1 / 3 : ℝ)
  let C₄ : ℝ := causalHalfCylinderBound ε₀ Kσ
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hKσ : 0 ≤ Kσ := by
    dsimp [Kσ]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hC₄ : 0 ≤ C₄ := by
    dsimp [C₄]
    have hbound := causalHalfCylinderBound_nonneg hε₀ hKσ
    have hzero : 0 ≤ (0 : ℝ) * K := mul_nonneg (by norm_num) hK
    simpa using add_nonneg hbound hzero
  refine ⟨C₄, hC₄, ?_⟩
  intro Ω I u Du p f hsol hdom hsmall hU hD hp
  obtain ⟨Fminus, Gminus, hFmeas, hGmeas, hFmorrey, hGmorrey,
      hFsupp, hGsupp, hFzero, hGzero, hrep, hkernel, hslice⟩ :=
    hproducer Ω I u Du p f hsol hdom hsmall hU hD hp
  have hFfinite : ∀ i, morreyNorm (6 / 5) (stepTheta₀ (stepGamma₀ q))
      (fun z => Fminus z i) < ∞ := by
    intro i
    exact (hFmorrey i).trans_lt hKF
  have hGfinite : ∀ j i, morreyNorm (6 / 5) (stepTheta₁ (stepGamma₀ q))
      (fun z => Gminus j z i) < ∞ := by
    intro j i
    exact (hGmorrey j i).trans_lt hKG
  have hcomponents : ∀ i : Fin 3, ∃ g : ParabolicPoint → ℂ,
      g =ᵐ[volume] multiplierHeatPotential σ (fun y => Fminus y i)
        (fun k y => Gminus k y i) ∧
      ∀ x y, ‖g x - g y‖ ≤
        A * multiplierHeatSourceSize (6 / 5)
          (stepTheta₀ (stepGamma₀ q)) (stepTheta₁ (stepGamma₀ q))
          (fun y => Fminus y i) (fun k y => Gminus k y i) *
          parabolicDist x y ^ stepGamma₀ q := by
    intro i
    obtain ⟨hbar, hbarLoc, hbarEq, hbarMem, hbarOsc⟩ := hcon
      (F := fun y => Fminus y i) (G := fun k y => Gminus k y i)
      (hFmeas i) (fun k => hGmeas k i) (hFfinite i)
      (fun k => hGfinite k i) (hFsupp i) (fun k => hGsupp k i)
    obtain ⟨g, hgLoc, hgEq, hgsemi⟩ := heatHolder_of_conclusion_data
      hγ hγ1 hP σ hCcon hbarLoc hbarEq hbarMem hbarOsc
    refine ⟨g, hgEq, ?_⟩
    intro x y
    simpa [A] using hgsemi x y
  choose g hgEq hgsemi using hcomponents
  let w : ParabolicPoint → Vec3 := fun z i => (g i z).re
  have hwu : w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u := by
    have hcomponent : ∀ i : Fin 3, ∀ᵐ z ∂volume.restrict
        (parabolicCylinder 0 0 (1 / 2)), w z i = u z i := by
      intro i
      have hgi : ∀ᵐ z ∂volume.restrict (parabolicCylinder 0 0 (1 / 2)),
          g i z = multiplierHeatPotential σ (fun y => Fminus y i)
            (fun k y => Gminus k y i) z :=
        ae_restrict_of_ae (hgEq i)
      filter_upwards [hgi, hrep i] with z hgz hzu
      have hz : g i z = (u z i : ℂ) := hgz.trans hzu.symm
      simpa [w] using congrArg Complex.re hz
    filter_upwards [ae_all_iff.mpr hcomponent] with z hz
    exact funext hz
  have hsourceSize : ∀ i : Fin 3,
      multiplierHeatSourceSize (6 / 5)
        (stepTheta₀ (stepGamma₀ q)) (stepTheta₁ (stepGamma₀ q))
        (fun y => Fminus y i) (fun k y => Gminus k y i) ≤ S := by
    intro i
    unfold multiplierHeatSourceSize
    calc
      _ ≤ KF.toReal + ∑ k : Fin N, KG.toReal := by
        exact add_le_add (ENNReal.toReal_mono hKF.ne (hFmorrey i))
          (Finset.sum_le_sum fun k _ =>
            ENNReal.toReal_mono hKG.ne (hGmorrey k i))
      _ = S := by simp [S]
  have hsemi : ∀ x y,
      vec3EuclideanNorm (w x - w y) ≤ Kσ * parabolicDist x y ^ stepGamma₀ q := by
    intro x y
    refine (vec3EuclideanNorm_le_sum_abs (w x - w y)).trans ?_
    calc
      _ ≤ ∑ i : Fin 3, A * S * parabolicDist x y ^ stepGamma₀ q := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := hgsemi i x y
        have hsi := hsourceSize i
        have hpow : 0 ≤ parabolicDist x y ^ stepGamma₀ q :=
          Real.rpow_nonneg (parabolicDist_nonneg x y) _
        have hbound : A *
            multiplierHeatSourceSize (6 / 5)
              (stepTheta₀ (stepGamma₀ q)) (stepTheta₁ (stepGamma₀ q))
              (fun y => Fminus y i) (fun k y => Gminus k y i) *
            parabolicDist x y ^ stepGamma₀ q ≤
            A * S * parabolicDist x y ^ stepGamma₀ q := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsi hA) hpow
        calc
          |w x i - w y i| ≤ ‖g i x - g i y‖ := by
            simpa [w, map_sub] using RCLike.norm_re_le_norm (g i x - g i y)
          _ ≤ A *
              multiplierHeatSourceSize (6 / 5)
                (stepTheta₀ (stepGamma₀ q)) (stepTheta₁ (stepGamma₀ q))
                (fun y => Fminus y i) (fun k y => Gminus k y i) *
              parabolicDist x y ^ stepGamma₀ q := hi'
          _ ≤ _ := hbound
      _ = Kσ * parabolicDist x y ^ stepGamma₀ q := by
        simp [Kσ]
        ring
  obtain ⟨hu, hu3, havg⟩ := halfCylinder_velocity_average_of_small_data
    hε₀ hsol hdom hsmall
  have hnorm := halfCylinder_holder_norm_of_seminorm
    hγ.le hKσ hsemi hwu hu hu3
  have hnorm' : ParabolicHolderVecNormLE
      (closure (parabolicCylinder 0 0 (1 / 2))) w (stepGamma₀ q) C₄ := by
    obtain ⟨B, L, hB, hL, hBL, hb, hLipschitz⟩ := hnorm
    refine ⟨B, L, hB, hL, ?_, hb, hLipschitz⟩
    exact hBL.trans (by
      dsimp [C₄, causalHalfCylinderBound, Kσ, V] at *
      simpa [add_comm] using add_le_add_left havg (2 * (3 * A * S)))
  refine ⟨w, hwu, hnorm', ?_⟩
  have hinterior : interior (parabolicCylinder 0 0 (1 / 2)) =
      vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0 := by
    rw [interior_parabolicCylinder]
    norm_num
    rfl
  have hsub : parabolicCylinder 0 0 (1 / 2) ⊆ spaceTimeSet Ω I :=
    subset_closure.trans ((closure_parabolicCylinder_mono
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hdom)
  intro z hz
  have hz' : z ∈ interior (parabolicCylinder 0 0 (1 / 2)) := hinterior.symm ▸ hz
  exact regular_point_of_holder_norm isOpen_interior hz' interior_subset
    (interior_subset.trans hsub) hγ hγ1.le hwu
    (holder_norm_mono hnorm' subset_closure)

end CKN.Core.Endgame
