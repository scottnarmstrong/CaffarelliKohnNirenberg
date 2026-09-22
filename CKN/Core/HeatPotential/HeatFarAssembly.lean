-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.HeatFarAssemblySlots
import CKN.Core.HeatPotential.GeneralSymbolHeatNear

/-!
# The far-shell oscillation of the general-symbol heat potential

`step:heat-far` of `paper/ckn.tex`.  The potential of the source restricted
to the far shell of inner radius `2 ^ j r`, `j ≥ 6`, oscillates over the ball
of radius `r` by at most the parabolic distance of the two observation points
times the shell factor `(2 ^ j r) ^ (γ - 1)` times the Morrey size of the
source.  Summed over `j` the shell factors form a geometric series of ratio
`2 ^ (γ - 1)`.

The proof pairs each kernel of the potential with its own source slot.  Both
slot estimates are proved on the shell itself; the exponents
`1/θ₀ = (2-γ)/5` and `1/θ₁ = (1-γ)/5` convert the Morrey mass of a shell into
exactly the shell factor after dividing by the kernel order.  The two
observation points are ordered in time without loss of generality, because
both sides of the estimate are symmetric in them.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat

/-- The parabolic distance is symmetric. -/
private lemma farShellAssembly_dist_comm (a b : ParabolicPoint) :
    parabolicDist a b = parabolicDist b a := by
  rw [← dist_eq_parabolicDist, ← dist_eq_parabolicDist, dist_comm]

/-- The shell potential is the sum of its slot pairings over the shell. -/
private lemma farShellAssembly_shell_potential_eq {K : ℕ} (σ : Fin K → Vec3 → ℂ)
    (F : ParabolicPoint → ℝ) (G : Fin K → ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) (j : ℕ) (q : ParabolicPoint) :
    multiplierHeatPotentialShell σ F G z r j q =
      (∫ v in multiplierHeatShellSet z r j,
          ((heatPotentialKernel q v : ℝ) : ℂ) * (F v : ℂ)) +
        ∑ k, ∫ v in multiplierHeatShellSet z r j,
          spatialMultiplierHeatKernel (σ k) (q.1 - v.1) (q.2 - v.2) *
            (G k v : ℂ) := by
  have hS : MeasurableSet (multiplierHeatShellSet z r j) :=
    farShellAssembly_measurableSet_shell z r j
  have hA : (∫ v, ((heatKernelPlus (pointSub q v) : ℝ) : ℂ) *
      (((multiplierHeatShellSet z r j).indicator F v : ℝ) : ℂ)) =
      ∫ v in multiplierHeatShellSet z r j,
        ((heatPotentialKernel q v : ℝ) : ℂ) * (F v : ℂ) :=
    farShellAssembly_indicator_pairing hS
      (fun v => ((heatPotentialKernel q v : ℝ) : ℂ)) F
  have hB : ∀ k : Fin K,
      (∫ v, spatialMultiplierHeatKernel (σ k) (pointSub q v).1 (pointSub q v).2 *
        (((multiplierHeatShellSet z r j).indicator (G k) v : ℝ) : ℂ)) =
      ∫ v in multiplierHeatShellSet z r j,
        spatialMultiplierHeatKernel (σ k) (q.1 - v.1) (q.2 - v.2) *
          (G k v : ℂ) := fun k =>
    farShellAssembly_indicator_pairing hS
      (fun v => spatialMultiplierHeatKernel (σ k) (q.1 - v.1) (q.2 - v.2)) (G k)
  simp only [multiplierHeatPotentialShell, multiplierHeatPotential]
  rw [hA]
  congr 1
  exact Finset.sum_congr rfl fun k _ => hB k

/-- **`step:heat-far`.**  One constant, fixed after the symbols and the
exponents and before the source, bounds the oscillation over the ball of
radius `r` of the potential of the source restricted to the far shell of
inner radius `2 ^ j r`, by the parabolic distance of the two observation
points times `(2 ^ j r) ^ (γ - 1)` times the Morrey size of the source. -/
theorem heatFar
    {K : ℕ} {γ θ₀ θ₁ P : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (σ : Fin K → Vec3 → ℂ) (hσ : ∀ k, SmoothOffOrigin (σ k))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ},
        AEMeasurable F volume → (∀ k, AEMeasurable (G k) volume) →
        morreyNorm P θ₀ F < ∞ → (∀ k, morreyNorm P θ₁ (G k) < ∞) →
        ∀ (z : ParabolicPoint) (r : ℝ) (j : ℕ), 0 < r → 6 ≤ j →
          ∀ w w' : ParabolicPoint,
            w ∈ Metric.ball z r → w' ∈ Metric.ball z r →
            ‖multiplierHeatPotentialShell σ F G z r j w -
                multiplierHeatPotentialShell σ F G z r j w'‖ ≤
              C * parabolicDist w w' *
                ((2 : ℝ) ^ (j : ℝ) * r) ^ (γ - 1) *
                multiplierHeatSourceSize P θ₀ θ₁ F G := by
  -- Exponent bookkeeping.
  have hexp₀ : 1 - 5 / θ₀ = γ - 1 := by
    have h5 : 5 / θ₀ = 2 - γ := by
      rw [show (5 : ℝ) / θ₀ = 5 * (1 / θ₀) by ring, hθ₀]
      ring
    linarith only [h5]
  have hθ₁pos : 0 < θ₁ := by
    apply one_div_pos.mp
    rw [hθ₁]
    have : (0 : ℝ) < 1 - γ := by linarith only [hγ1]
    positivity
  have hθ₁five : 5 < θ₁ := by
    refine lt_of_one_div_lt_one_div hθ₁pos ?_
    rw [hθ₁]
    apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 5)).2
    linarith only [hγ]
  have hexp₁ : (-5 : ℝ) / θ₁ = γ - 1 := by
    have h5 : 5 / θ₁ = 1 - γ := by
      rw [show (5 : ℝ) / θ₁ = 5 * (1 / θ₁) by ring, hθ₁]
      ring
    rw [neg_div]
    linarith only [h5]
  -- Slot constants.
  obtain ⟨C₀, hC₀, hslot₀⟩ := farShellAssembly_exists_scalar_slot_bound hP hPθ₀
  have hslots : ∀ k : Fin K, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {G : ParabolicPoint → ℝ}, AEMeasurable G volume →
        morreyNorm P θ₁ G < ∞ →
        ∀ (z : ParabolicPoint) (r : ℝ) (j : ℕ), 0 < r → 6 ≤ j →
          ∀ w w' : ParabolicPoint, w ∈ Metric.ball z r → w' ∈ Metric.ball z r →
            w.2 ≤ w'.2 →
            ‖(∫ v in multiplierHeatShellSet z r j,
                spatialMultiplierHeatKernel (σ k) (w.1 - v.1) (w.2 - v.2) *
                  (G v : ℂ)) -
              ∫ v in multiplierHeatShellSet z r j,
                spatialMultiplierHeatKernel (σ k) (w'.1 - v.1) (w'.2 - v.2) *
                  (G v : ℂ)‖ ≤
              C * parabolicDist w w' * ((2 : ℝ) ^ j * r) ^ (-5 / θ₁ : ℝ) *
                (morreyNorm P θ₁ G).toReal := fun k =>
    farShellAssembly_exists_multiplier_slot_bound (σ k) (hσ k) (hhom k) hP hPθ₁
      hθ₁five
  choose Ck hCk hslotk using hslots
  refine ⟨C₀ + ∑ k, Ck k,
    add_nonneg hC₀ (Finset.sum_nonneg fun k _ => hCk k), ?_⟩
  intro F G hF hG hFM hGM z r j hr hj
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ j * r := by positivity
  have hRr : ((2 : ℝ) ^ (j : ℝ) * r) = (2 : ℝ) ^ j * r := by
    rw [Real.rpow_natCast]
  have hCsum : ∀ k : Fin K, Ck k ≤ C₀ + ∑ k, Ck k := by
    intro k
    have h := Finset.single_le_sum (f := fun k : Fin K => Ck k)
      (fun i _ => hCk i) (Finset.mem_univ k)
    linarith only [h, hC₀]
  have hC₀le : C₀ ≤ C₀ + ∑ k, Ck k := by
    have : (0 : ℝ) ≤ ∑ k, Ck k := Finset.sum_nonneg fun k _ => hCk k
    linarith only [this]
  -- The ordered estimate.
  have hmain : ∀ w w' : ParabolicPoint, w ∈ Metric.ball z r →
      w' ∈ Metric.ball z r → w.2 ≤ w'.2 →
      ‖multiplierHeatPotentialShell σ F G z r j w -
          multiplierHeatPotentialShell σ F G z r j w'‖ ≤
        (C₀ + ∑ k, Ck k) * parabolicDist w w' *
          ((2 : ℝ) ^ j * r) ^ (γ - 1) *
          multiplierHeatSourceSize P θ₀ θ₁ F G := by
    intro w w' hw hw' hww'
    have hD0 : (0 : ℝ) ≤ parabolicDist w w' := by
      rw [← dist_eq_parabolicDist]; exact dist_nonneg
    have hRexp : (0 : ℝ) ≤ ((2 : ℝ) ^ j * r) ^ (γ - 1) :=
      Real.rpow_nonneg hRpos.le _
    rw [farShellAssembly_shell_potential_eq, farShellAssembly_shell_potential_eq]
    have hsplit :
        ((∫ v in multiplierHeatShellSet z r j,
            ((heatPotentialKernel w v : ℝ) : ℂ) * (F v : ℂ)) +
          ∑ k, ∫ v in multiplierHeatShellSet z r j,
            spatialMultiplierHeatKernel (σ k) (w.1 - v.1) (w.2 - v.2) *
              (G k v : ℂ)) -
        ((∫ v in multiplierHeatShellSet z r j,
            ((heatPotentialKernel w' v : ℝ) : ℂ) * (F v : ℂ)) +
          ∑ k, ∫ v in multiplierHeatShellSet z r j,
            spatialMultiplierHeatKernel (σ k) (w'.1 - v.1) (w'.2 - v.2) *
              (G k v : ℂ)) =
        ((∫ v in multiplierHeatShellSet z r j,
            ((heatPotentialKernel w v : ℝ) : ℂ) * (F v : ℂ)) -
          ∫ v in multiplierHeatShellSet z r j,
            ((heatPotentialKernel w' v : ℝ) : ℂ) * (F v : ℂ)) +
        ∑ k, ((∫ v in multiplierHeatShellSet z r j,
            spatialMultiplierHeatKernel (σ k) (w.1 - v.1) (w.2 - v.2) *
              (G k v : ℂ)) -
          ∫ v in multiplierHeatShellSet z r j,
            spatialMultiplierHeatKernel (σ k) (w'.1 - v.1) (w'.2 - v.2) *
              (G k v : ℂ)) := by
      rw [Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hscalar := hslot₀ hF hFM z r j hr hj w w' hw hw' hww'
    rw [hexp₀] at hscalar
    have hvector : ∀ k : Fin K,
        ‖(∫ v in multiplierHeatShellSet z r j,
            spatialMultiplierHeatKernel (σ k) (w.1 - v.1) (w.2 - v.2) *
              (G k v : ℂ)) -
          ∫ v in multiplierHeatShellSet z r j,
            spatialMultiplierHeatKernel (σ k) (w'.1 - v.1) (w'.2 - v.2) *
              (G k v : ℂ)‖ ≤
          Ck k * parabolicDist w w' * ((2 : ℝ) ^ j * r) ^ (γ - 1) *
            (morreyNorm P θ₁ (G k)).toReal := by
      intro k
      have h := hslotk k (hG k) (hGM k) z r j hr hj w w' hw hw' hww'
      rwa [hexp₁] at h
    have hsum : ∑ k : Fin K,
        ‖(∫ v in multiplierHeatShellSet z r j,
            spatialMultiplierHeatKernel (σ k) (w.1 - v.1) (w.2 - v.2) *
              (G k v : ℂ)) -
          ∫ v in multiplierHeatShellSet z r j,
            spatialMultiplierHeatKernel (σ k) (w'.1 - v.1) (w'.2 - v.2) *
              (G k v : ℂ)‖ ≤
        ∑ k : Fin K, (C₀ + ∑ i, Ck i) * parabolicDist w w' *
          ((2 : ℝ) ^ j * r) ^ (γ - 1) * (morreyNorm P θ₁ (G k)).toReal := by
      refine Finset.sum_le_sum fun k _ => (hvector k).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
      refine mul_le_mul_of_nonneg_right ?_ hRexp
      exact mul_le_mul_of_nonneg_right (hCsum k) hD0
    refine (add_le_add hscalar ((norm_sum_le _ _).trans hsum)).trans ?_
    have hmulsum : ∑ k : Fin K, (C₀ + ∑ i, Ck i) * parabolicDist w w' *
        ((2 : ℝ) ^ j * r) ^ (γ - 1) * (morreyNorm P θ₁ (G k)).toReal =
        (C₀ + ∑ i, Ck i) * parabolicDist w w' * ((2 : ℝ) ^ j * r) ^ (γ - 1) *
          ∑ k : Fin K, (morreyNorm P θ₁ (G k)).toReal := by
      rw [Finset.mul_sum]
    rw [hmulsum]
    have hfirst : C₀ * parabolicDist w w' * ((2 : ℝ) ^ j * r) ^ (γ - 1) *
        (morreyNorm P θ₀ F).toReal ≤
        (C₀ + ∑ i, Ck i) * parabolicDist w w' * ((2 : ℝ) ^ j * r) ^ (γ - 1) *
          (morreyNorm P θ₀ F).toReal := by
      refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
      refine mul_le_mul_of_nonneg_right ?_ hRexp
      exact mul_le_mul_of_nonneg_right hC₀le hD0
    refine (add_le_add hfirst le_rfl).trans (le_of_eq ?_)
    simp only [multiplierHeatSourceSize]
    ring
  intro w w' hw hw'
  rw [hRr]
  rcases le_total w.2 w'.2 with hle | hle
  · exact hmain w w' hw hw' hle
  · have h := hmain w' w hw' hw hle
    rw [farShellAssembly_dist_comm w' w] at h
    rw [← norm_neg, neg_sub]
    exact h

end CKN.Core.HeatPotential
