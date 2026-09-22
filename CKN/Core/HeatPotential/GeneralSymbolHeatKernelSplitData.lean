-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbolPairings
import CKN.Core.HeatPotential.GeneralSymbol
import CKN.Foundation.Heat.CausalDistribution

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

/- The smooth symbol class used by the split node. -/
def SmoothOffOrigin (σ : Vec3 → ℂ) : Prop :=
  ∀ n : ℕ, ContDiffOn ℝ (n : ℕ∞) σ ({0}ᶜ : Set Vec3)

/-- A constant symbol supplies a concrete inhabitant of the smooth-symbol class. -/
theorem SmoothOffOrigin_satisfiable :
    SmoothOffOrigin (fun _ : Vec3 => (0 : ℂ)) := by
  intro n
  exact contDiff_const.contDiffOn

def multiplierHeatNearSet (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  Metric.ball z ((2 : ℝ) ^ (6 : ℕ) * r)

def multiplierHeatShellSet (z : ParabolicPoint) (r : ℝ) (j : ℕ) : Set ParabolicPoint :=
  Metric.ball z ((2 : ℝ) ^ (j + 1) * r) \
    Metric.ball z ((2 : ℝ) ^ j * r)

def multiplierHeatPotentialNear {K : ℕ} (σ : Fin K → Vec3 → ℂ)
    (F : ParabolicPoint → ℝ) (G : Fin K → ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) (w : ParabolicPoint) : ℂ :=
  multiplierHeatPotential σ
    ((multiplierHeatNearSet z r).indicator F)
    (fun k => (multiplierHeatNearSet z r).indicator (G k)) w

def multiplierHeatPotentialShell {K : ℕ} (σ : Fin K → Vec3 → ℂ)
    (F : ParabolicPoint → ℝ) (G : Fin K → ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) (j : ℕ) (w : ParabolicPoint) : ℂ :=
  multiplierHeatPotential σ
    ((multiplierHeatShellSet z r j).indicator F)
    (fun k => (multiplierHeatShellSet z r j).indicator (G k)) w

private lemma dyadic_ball_radius_mono {r : ℝ}
    (hr : 0 < r) (n : ℕ) :
    (2 : ℝ) ^ (n + 6) * r ≤ (2 : ℝ) ^ (n + 7) * r := by
  have hpow : (2 : ℝ) ^ (n + 6) ≤ (2 : ℝ) ^ (n + 7) := by
    calc
      (2 : ℝ) ^ (n + 6) ≤ (2 : ℝ) ^ (n + 6) * 2 := by
        have ha : 0 ≤ (2 : ℝ) ^ (n + 6) := by positivity
        nlinarith only [ha]
      _ = (2 : ℝ) ^ (n + 7) := by
        conv_rhs =>
          rw [show n + 7 = (n + 6) + 1 by omega, pow_succ]
  exact mul_le_mul_of_nonneg_right hpow hr.le

private lemma indicator_add_shell {α : Type} [TopologicalSpace α]
    {A B : Set α} {g : α → ℝ} (hAB : A ⊆ B) :
    A.indicator g + (B \ A).indicator g = B.indicator g := by
  funext x
  by_cases hxA : x ∈ A
  · have hxB : x ∈ B := hAB hxA
    have hxBA : x ∉ B \ A := by
      intro hx
      exact hx.2 hxA
    simp only [Pi.add_apply, indicator_of_mem hxA, indicator_of_notMem hxBA,
      indicator_of_mem hxB, add_zero]
  · by_cases hxB : x ∈ B
    · have hxBA : x ∈ B \ A := ⟨hxB, hxA⟩
      simp only [Pi.add_apply, indicator_of_notMem hxA,
        indicator_of_mem hxBA, zero_add, indicator_of_mem hxB]
    · have hxBA : x ∉ B \ A := by
        intro hx
        exact hxB hx.1
      simp only [Pi.add_apply, indicator_of_notMem hxA,
        indicator_of_notMem hxBA, indicator_of_notMem hxB, add_zero]

private lemma near_shell_indicator_eq_ball_indicator
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) (N : ℕ)
    {g : ParabolicPoint → ℝ} :
    (multiplierHeatNearSet z r).indicator g +
        Finset.sum (Finset.range N) (fun j =>
          (multiplierHeatShellSet z r (j + 6)).indicator g) =
      (Metric.ball z ((2 : ℝ) ^ (N + 6) * r)).indicator g := by
  induction N with
  | zero =>
      simp [multiplierHeatNearSet]
  | succ N ih =>
      rw [Finset.sum_range_succ (fun j =>
        (multiplierHeatShellSet z r (j + 6)).indicator g) N]
      rw [← add_assoc, ih]
      apply indicator_add_shell
      exact Metric.ball_subset_ball (dyadic_ball_radius_mono hr N)

private lemma source_split_of_outer_ball
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) {N : ℕ}
    {g : ParabolicPoint → ℝ}
    (houter : tsupport g ⊆ Metric.ball z ((2 : ℝ) ^ (N + 6) * r)) :
    g = (multiplierHeatNearSet z r).indicator g +
        Finset.sum (Finset.range N) (fun j =>
          (multiplierHeatShellSet z r (j + 6)).indicator g) := by
  rw [near_shell_indicator_eq_ball_indicator hr N]
  symm
  apply indicator_eq_self.2
  intro x hx
  exact houter (subset_tsupport g hx)

theorem indicator_hasCompactSupport_of_hasCompactSupport
    {s : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (s.indicator g) := by
  apply hg.mono
  intro x hx
  by_cases hxs : x ∈ s
  · change s.indicator g x ≠ 0 at hx
    change g x ≠ 0
    simpa only [indicator_of_mem hxs] using hx
  · change s.indicator g x ≠ 0 at hx
    simp only [indicator_of_notMem hxs] at hx
    exact (hx rfl).elim

private lemma dyadic_outer_radius
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    {S : Set ParabolicPoint} (hS : IsCompact S) :
    ∃ N : ℕ, S ⊆ Metric.ball z ((2 : ℝ) ^ (N + 6) * r) := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall z
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R / r)
    (show (1 : ℝ) < 2 by norm_num)
  refine ⟨N, ?_⟩
  intro x hx
  have hdist : dist x z ≤ R := (mem_closedBall.mp (hR hx))
  have hRpow : R < (2 : ℝ) ^ N * r :=
    (div_lt_iff₀ hr).mp hN
  have hpow : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (N + 6) := by
    rw [show N + 6 = N + 1 + 5 by omega]
    gcongr
    · norm_num
    · omega
  have houter : R < (2 : ℝ) ^ (N + 6) * r :=
    lt_of_lt_of_le hRpow (mul_le_mul_of_nonneg_right hpow hr.le)
  exact mem_ball'.2 (lt_of_le_of_lt (by simpa [dist_comm] using hdist) houter)

private lemma compact_support_union_sources
    {K : ℕ} {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    (hFsupp : HasCompactSupport F)
    (hGsupp : ∀ k, HasCompactSupport (G k)) :
    IsCompact (tsupport F ∪ ⋃ k, tsupport (G k)) := by
  exact hFsupp.isCompact.union (isCompact_iUnion (fun k => (hGsupp k).isCompact))

/-- The compact source data admit one common finite near/shell decomposition. -/
theorem source_split_data_of_compact_support
    {K : ℕ} {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hFsupp : HasCompactSupport F) (hGsupp : ∀ k, HasCompactSupport (G k)) :
    ∃ N : ℕ,
      F = (multiplierHeatNearSet z r).indicator F +
          Finset.sum (Finset.range N) (fun j =>
            (multiplierHeatShellSet z r (j + 6)).indicator F) ∧
      ∀ k, G k = (multiplierHeatNearSet z r).indicator (G k) +
          Finset.sum (Finset.range N) (fun j =>
            (multiplierHeatShellSet z r (j + 6)).indicator (G k)) := by
  let S : Set ParabolicPoint := tsupport F ∪ ⋃ k, tsupport (G k)
  obtain ⟨N, hN⟩ := dyadic_outer_radius hr (S := S)
    (compact_support_union_sources hFsupp hGsupp)
  change tsupport F ∪ ⋃ k, tsupport (G k) ⊆
    Metric.ball z ((2 : ℝ) ^ (N + 6) * r) at hN
  refine ⟨N, source_split_of_outer_ball hr (fun x hx => hN (Or.inl hx)), ?_⟩
  intro k
  exact source_split_of_outer_ball hr (fun x hx =>
    hN (Or.inr (mem_iUnion.2 ⟨k, hx⟩)))

/-- A compactly supported kernel potential splits along a finite source sum
without any pointwise assertion about the totalized potential. -/
theorem kernel_potential_split_ae
    {k : ParabolicPoint → ℂ} (hk : LocallyIntegrable k volume)
    (hkm : Measurable k) {g g₀ : ParabolicPoint → ℝ}
    {gs : ℕ → ParabolicPoint → ℝ} {N : ℕ}
    (hdecomp : g = g₀ + Finset.sum (Finset.range N) gs)
    (hg₀ : Integrable g₀) (hgc₀ : HasCompactSupport g₀)
    (hgs : ∀ j ∈ Finset.range N, Integrable (gs j) volume)
    (hgcs : ∀ j ∈ Finset.range N, HasCompactSupport (gs j)) :
    ∀ᵐ w ∂volume,
      (∫ v, k (pointSub w v) * (g v : ℂ)) =
        (∫ v, k (pointSub w v) * (g₀ v : ℂ)) +
          Finset.sum (Finset.range N) (fun j =>
            ∫ v, k (pointSub w v) * ((gs j) v : ℂ)) := by
  have hpair₀ := kernel_pairings_ae_of_compact hk hkm hg₀ hgc₀
  have hpairj : ∀ j, j ∈ Finset.range N → ∀ᵐ w ∂volume, Integrable (fun v =>
      k (pointSub w v) * ((gs j) v : ℂ)) volume := by
    intro j hj
    exact kernel_pairings_ae_of_compact hk hkm (hgs j hj) (hgcs j hj)
  have hpairj_all : ∀ᵐ w ∂volume, ∀ j ∈ Finset.range N, Integrable (fun v =>
      k (pointSub w v) * ((gs j) v : ℂ)) volume := by
    apply ae_all_iff.2
    intro j
    by_cases hj : j ∈ Finset.range N
    · filter_upwards [hpairj j hj] with w hw
      exact fun _ => hw
    · filter_upwards [] with w hw
      exact (hj hw).elim
  filter_upwards [hpair₀, hpairj_all] with w hw₀ hwj
  have hsum : Integrable (fun v =>
      k (pointSub w v) *
        ((Finset.sum (Finset.range N) gs) v : ℂ)) volume := by
    have hsum' : Integrable (fun v =>
        Finset.sum (Finset.range N) (fun j =>
          k (pointSub w v) * ((gs j) v : ℂ))) volume :=
      integrable_finsetSum (Finset.range N) (fun j hj => hwj j hj)
    convert hsum' using 1
    funext v
    simp only [Complex.ofReal_sum, Finset.sum_apply, Finset.mul_sum]
  have hsum' : Integrable (fun v =>
      k (pointSub w v) * ((Finset.sum (Finset.range N) gs) v : ℂ)) volume := hsum
  calc
    (∫ v, k (pointSub w v) * (g v : ℂ)) =
        ∫ v, k (pointSub w v) *
          ((g₀ v + (Finset.sum (Finset.range N) gs) v : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [hdecomp]
      simp only [Pi.add_apply]
    _ = (∫ v, k (pointSub w v) * (g₀ v : ℂ)) +
        ∫ v, k (pointSub w v) * ((Finset.sum (Finset.range N) gs) v : ℂ) :=
      by
        simpa only [Complex.ofReal_add, Pi.add_apply, mul_add] using
          (integral_add hw₀ hsum')
    _ = (∫ v, k (pointSub w v) * (g₀ v : ℂ)) +
        Finset.sum (Finset.range N) (fun j =>
          ∫ v, k (pointSub w v) * ((gs j) v : ℂ)) := by
      have hsumIntegral :
          (∫ v, k (pointSub w v) * ((Finset.sum (Finset.range N) gs) v : ℂ)) =
            Finset.sum (Finset.range N) (fun j =>
              ∫ v, k (pointSub w v) * ((gs j) v : ℂ)) := by
        calc
          (∫ v, k (pointSub w v) * ((Finset.sum (Finset.range N) gs) v : ℂ)) =
              ∫ v, Finset.sum (Finset.range N) (fun j =>
                k (pointSub w v) * ((gs j) v : ℂ)) := by
            apply integral_congr_ae
            filter_upwards [] with v
            simp only [Complex.ofReal_sum, Finset.sum_apply, Finset.mul_sum]
          _ = _ := integral_finsetSum (Finset.range N)
            (fun j hj => hwj j hj)
      rw [hsumIntegral]

end CKN.Core.HeatPotential
