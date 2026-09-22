-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbolHeatConclusion

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Parabolic.Morrey

private lemma pair_avg_congr {E : Type*} [NormedAddCommGroup E]
    {h h' : ParabolicPoint → E} {B : Set ParabolicPoint} {p : ℝ}
    (hB : MeasurableSet B) (heq : h =ᵐ[volume] h') :
    (⨍ x in B, ⨍ y in B, ‖h x - h y‖ ^ p) =
      (⨍ x in B, ⨍ y in B, ‖h' x - h' y‖ ^ p) := by
  have heq' : ∀ᵐ x ∂volume, x ∈ B → h x = h' x := by
    filter_upwards [heq] with x hx _
    exact hx
  have hinner : ∀ᵐ x ∂volume, x ∈ B →
      (⨍ y in B, ‖h x - h y‖ ^ p) =
        (⨍ y in B, ‖h' x - h' y‖ ^ p) := by
    filter_upwards [heq'] with x hx
    intro hxB
    apply setAverage_congr_fun hB
    filter_upwards [heq'] with y hy hyB
    rw [hx hxB, hy hyB]
  exact setAverage_congr_fun hB hinner

private lemma pair_root_add_bound {a b c p A B : ℝ} (hp : 1 ≤ p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hineq : c ≤ (2 : ℝ) ^ (p - 1) * (a + b))
    (hA : a ^ (1 / p) ≤ A) (hB : b ^ (1 / p) ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    c ^ (1 / p) ≤ 2 * (A + B) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have haPow : a ≤ A ^ p := by
    calc
      a = (a ^ (1 / p)) ^ p := by
        rw [← Real.rpow_mul ha, one_div, inv_mul_cancel₀ hpne, Real.rpow_one]
      _ ≤ A ^ p := Real.rpow_le_rpow (Real.rpow_nonneg ha _) hA hp0.le
  have hbPow : b ≤ B ^ p := by
    calc
      b = (b ^ (1 / p)) ^ p := by
        rw [← Real.rpow_mul hb, one_div, inv_mul_cancel₀ hpne, Real.rpow_one]
      _ ≤ B ^ p := Real.rpow_le_rpow (Real.rpow_nonneg hb _) hB hp0.le
  have hsum : a + b ≤ 2 * (A + B) ^ p := by
    calc
      a + b ≤ A ^ p + B ^ p := add_le_add haPow hbPow
      _ ≤ (A + B) ^ p + (A + B) ^ p := by
        gcongr
        · exact le_add_of_nonneg_right hB0
        · exact le_add_of_nonneg_left hA0
      _ = 2 * (A + B) ^ p := by ring_nf
  have hpow : c ≤ (2 : ℝ) ^ p * (A + B) ^ p := by
    calc
      c ≤ (2 : ℝ) ^ (p - 1) * (a + b) := hineq
      _ ≤ (2 : ℝ) ^ (p - 1) * (2 * (A + B) ^ p) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ p * (A + B) ^ p := by
        calc
          _ = ((2 : ℝ) ^ (p - 1) * 2) * (A + B) ^ p := by ring_nf
          _ = (2 : ℝ) ^ p * (A + B) ^ p := by
            have h2pow : (2 : ℝ) ^ (p - 1) * 2 = 2 ^ p := by
              calc
                _ = (2 : ℝ) ^ (p - 1) * 2 ^ (1 : ℝ) := by rw [Real.rpow_one]
                _ = (2 : ℝ) ^ ((p - 1) + 1) :=
                  (Real.rpow_add (by norm_num) _ _).symm
                _ = 2 ^ p := by congr 1; ring_nf
            rw [h2pow]
  have hroot : c ^ (1 / p) ≤
      ((2 : ℝ) ^ p * (A + B) ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow hc hpow (by positivity)
  calc
    c ^ (1 / p) ≤ ((2 : ℝ) ^ p * (A + B) ^ p) ^ (1 / p) := hroot
    _ = 2 * (A + B) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      have h2root : ((2 : ℝ) ^ p) ^ (1 / p) = 2 := by
        rw [← Real.rpow_mul (by norm_num), one_div]
        have hp_mul : p * p⁻¹ = 1 := by field_simp
        rw [hp_mul, Real.rpow_one]
      have hAB : 0 ≤ A + B := add_nonneg hA0 hB0
      have hABroot : ((A + B) ^ p) ^ (1 / p) = A + B := by
        rw [← Real.rpow_mul hAB, one_div]
        have hp_mul : p * p⁻¹ = 1 := by field_simp
        rw [hp_mul, Real.rpow_one]
      rw [h2root, hABroot]

/-- Assemble the near estimate, the finite split, and the approved far-shell
estimate.  The final public theorem uses this adapter with the same far-shell
interface, while the shell theorem itself remains an independent input. -/
theorem heatConclusion_of_heatFar
    {K : ℕ} {γ θ₀ θ₁ P : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (σ : Fin K → Vec3 → ℂ) (hσ : ∀ k, SmoothOffOrigin (σ k))
    (hhom : ∀ k, IsDegreeOneHomogeneous (σ k))
    (hfar : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ},
        AEMeasurable F volume → (∀ k : Fin K, AEMeasurable (G k) volume) →
        morreyNorm P θ₀ F < ∞ → (∀ k : Fin K, morreyNorm P θ₁ (G k) < ∞) →
        ∀ (z : ParabolicPoint) (r : ℝ) (j : ℕ), 0 < r → 6 ≤ j →
          ∀ w w' : ParabolicPoint,
            w ∈ Metric.ball z r → w' ∈ Metric.ball z r →
            ‖multiplierHeatPotentialShell σ F G z r j w -
                multiplierHeatPotentialShell σ F G z r j w'‖ ≤
              C * parabolicDist w w' *
                ((2 : ℝ) ^ (j : ℝ) * r) ^ (γ - 1) *
                multiplierHeatSourceSize P θ₀ θ₁ F G) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : ParabolicPoint → ℝ} {G : Fin K → ParabolicPoint → ℝ},
        AEMeasurable F volume → (∀ k, AEMeasurable (G k) volume) →
        morreyNorm P θ₀ F < ∞ → (∀ k, morreyNorm P θ₁ (G k) < ∞) →
        HasCompactSupport F → (∀ k, HasCompactSupport (G k)) →
        ∃ hbar : ParabolicPoint → ℂ,
          LocallyIntegrable hbar volume ∧
          hbar =ᵐ[volume] multiplierHeatPotential σ F G ∧
          (∀ z : ParabolicPoint, ∀ R : ℝ, 0 < R →
            MemLp hbar (ENNReal.ofReal P)
              (volume.restrict (Metric.closedBall z R))) ∧
          ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r →
            multiplierHeatPairOscillation hbar z r P ≤
              C * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G := by
  obtain ⟨Cfar, hCfar, hfar⟩ := hfar
  obtain ⟨Cnear, hCnear, hnear⟩ := heatNear hγ hγ1 hθ₀ hθ₁ hP hPθ₀ σ hσ hhom
  refine ⟨2 * (Cnear + 2 *
      (2 * Cfar) * (2 : ℝ) ^ ((6 : ℝ) * (γ - 1)) *
        (1 - (2 : ℝ) ^ (γ - 1))⁻¹), ?_, ?_⟩
  · have hratio : 0 ≤ (1 - (2 : ℝ) ^ (γ - 1))⁻¹ := by
      exact inv_nonneg.mpr (sub_nonneg.mpr
        (heat_morrey_geometric_ratio_lt_one hγ1).le)
    positivity
  intro F G hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp
  have hlocal := locallyIntegrable_multiplierHeatPotential_of_morrey
    hP hPθ₀ hPθ₁ (fun k n => hσ k n) hhom hFmeas hGmeas
      hFmorrey hGmorrey hFsupp hGsupp
  let hbar : ParabolicPoint → ℂ := multiplierHeatPotential σ F G
  have hsource : 0 ≤ multiplierHeatSourceSize P θ₀ θ₁ F G := by
    dsimp [multiplierHeatSourceSize]
    positivity
  let Dcoef : ℝ := (2 * Cfar) * (2 : ℝ) ^ ((6 : ℝ) * (γ - 1)) *
    (1 - (2 : ℝ) ^ (γ - 1))⁻¹
  have hDcoef : 0 ≤ Dcoef := by
    dsimp [Dcoef]
    have hratio : 0 ≤ (1 - (2 : ℝ) ^ (γ - 1))⁻¹ := by
      exact inv_nonneg.mpr (sub_nonneg.mpr
        (heat_morrey_geometric_ratio_lt_one hγ1).le)
    positivity
  have hassemble : ∀ (z : ParabolicPoint) {r : ℝ}, 0 < r →
      ∃ hn k : ParabolicPoint → ℂ,
        LocallyIntegrable k volume ∧
        multiplierHeatPotential σ F G =ᵐ[volume] hn + k ∧
        MemLp (multiplierHeatPotential σ F G) (ENNReal.ofReal P)
          (volume.restrict (Metric.closedBall z r)) ∧
        multiplierHeatPairOscillation (multiplierHeatPotential σ F G) z r P ≤
          2 * (Cnear + 2 * Dcoef) * r ^ γ *
            multiplierHeatSourceSize P θ₀ θ₁ F G := by
    intro z r hr
    obtain ⟨hsplit, N, hsplitLocal, hsplitRaw, hsplitSum⟩ := heatKernelSplit
      hP hPθ₀ hPθ₁ σ hσ hhom hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp hr
    obtain ⟨hn, hnLocal, hnNear, hnMem, hnOsc⟩ := hnear
      hFmeas hGmeas hFmorrey hGmorrey hFsupp hGsupp hr
    let k : ParabolicPoint → ℂ :=
      Finset.sum (Finset.range N) (fun j =>
        multiplierHeatPotentialShell σ F G z r (j + 6))
    have hrawSum : multiplierHeatPotential σ F G =ᵐ[volume] fun w =>
        multiplierHeatPotentialNear σ F G z r w + k w := by
      filter_upwards [hsplitRaw.symm, hsplitSum] with w hw₁ hw₂
      simpa [k] using hw₁.trans hw₂
    have hrawDecomp : multiplierHeatPotential σ F G =ᵐ[volume] hn + k := by
      filter_upwards [hrawSum, hnNear] with w hw₁ hw₂
      simpa only [Pi.add_apply] using (hw₁.trans (congrArg (fun q => q + k w) hw₂.symm))
    have hkEq : k =ᵐ[volume]
        (fun w => multiplierHeatPotential σ F G w - hn w) := by
      filter_upwards [hrawDecomp] with w hw
      rw [hw]
      simp only [Pi.add_apply]
      ring_nf
    have hkLocal : LocallyIntegrable k volume := by
      exact (hlocal.sub hnLocal).congr hkEq.symm
    let B : Set ParabolicPoint := Metric.closedBall z r
    have hBmeas : MeasurableSet B := measurableSet_closedBall
    have hBpos : 0 < volume B := parabolicBall_closedBall_pos hr
    have hBtop : volume B < ∞ := parabolicBall_closedBall_top hr
    let _ : IsFiniteMeasure (volume.restrict B) :=
      ⟨by simpa [B] using hBtop⟩
    let A : ℕ → ℝ := fun n => Cfar * (2 * r) *
      ((2 : ℝ) ^ (n : ℝ) * r) ^ (γ - 1) *
        multiplierHeatSourceSize P θ₀ θ₁ F G
    have hA : ∀ n, 0 ≤ A n := by
      intro n
      dsimp [A]
      positivity
    have hAj : ∀ j : ℕ,
        A (j + 6) ≤ (2 * Cfar * multiplierHeatSourceSize P θ₀ θ₁ F G) *
          (2 : ℝ) ^ (((j + 6 : ℕ) : ℝ) * (γ - 1)) * r ^ γ := by
      intro j
      dsimp [A]
      rw [multiplier_rpow_shell_bound hr (j + 6)]
    have hq0 : 0 ≤ (2 : ℝ) ^ (γ - 1) :=
      heat_morrey_geometric_ratio_nonneg
    have hq1 : (2 : ℝ) ^ (γ - 1) < 1 :=
      heat_morrey_geometric_ratio_lt_one hγ1
    have hgeo : Summable (fun j : ℕ =>
        (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) := by
      rw [show (fun j : ℕ => (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) =
          (fun j : ℕ => ((2 : ℝ) ^ (γ - 1)) ^ j) by
            funext j
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            ring_nf]
      exact summable_geometric_of_lt_one hq0 hq1
    have hAshift : Summable (fun j : ℕ => A (j + 6)) := by
      apply Summable.of_norm_bounded
        (hgeo.mul_left ((2 * Cfar * multiplierHeatSourceSize P θ₀ θ₁ F G) *
          (2 : ℝ) ^ ((6 : ℝ) * (γ - 1)) * r ^ γ))
      intro j
      rw [Real.norm_eq_abs, abs_of_nonneg (hA (j + 6))]
      calc
        A (j + 6) ≤
            (2 * Cfar * multiplierHeatSourceSize P θ₀ θ₁ F G) *
              (2 : ℝ) ^ (((j + 6 : ℕ) : ℝ) * (γ - 1)) * r ^ γ := hAj j
        _ = ((2 * Cfar * multiplierHeatSourceSize P θ₀ θ₁ F G) *
            (2 : ℝ) ^ ((6 : ℝ) * (γ - 1)) * r ^ γ) *
              (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) := by
          rw [Nat.cast_add, add_mul, Real.rpow_add (by norm_num)]
          ring_nf
    have hsumTsum := heatPotential_far_shell_sum_from_six hγ1
      (mul_nonneg (mul_nonneg (by positivity) hCfar) hsource) hr.le hA hAj
    let D : ℝ := Dcoef * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G
    have hD : 0 ≤ D := by
      dsimp [D]
      positivity
    have hsum : (∑ j ∈ Finset.range N, A (j + 6)) ≤ D := by
      calc
        ∑ j ∈ Finset.range N, A (j + 6) ≤ ∑' j : ℕ, A (j + 6) := by
          exact Summable.sum_le_tsum (Finset.range N)
            (fun j _ => hA (j + 6)) hAshift
        _ ≤ (2 * Cfar * multiplierHeatSourceSize P θ₀ θ₁ F G) *
            (2 : ℝ) ^ ((6 : ℝ) * (γ - 1)) *
              (1 - (2 : ℝ) ^ (γ - 1))⁻¹ * r ^ γ := hsumTsum
        _ = D := by
          dsimp [D, Dcoef]
          ring_nf
    have hballAE : ∀ᵐ w ∂(volume.restrict B), w ∈ Metric.ball z r := by
      apply (ae_restrict_iff' hBmeas).2
      rw [ae_iff]
      have hnull := multiplier_closedBall_diff_ball_null z hr
      have hset : {a : ParabolicPoint | ¬ (a ∈ B → a ∈ Metric.ball z r)} =
          Metric.closedBall z r \ Metric.ball z r := by
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_imp, B]
      rw [hset]
      exact hnull
    have hshell : ∀ j : ℕ, ∀ w : ParabolicPoint, w ∈ Metric.ball z r →
        ‖multiplierHeatPotentialShell σ F G z r (j + 6) w -
            multiplierHeatPotentialShell σ F G z r (j + 6) z‖ ≤ A (j + 6) := by
      intro j w hw
      have hzball : z ∈ Metric.ball z r := by
        rw [Metric.mem_ball]
        simpa using hr
      have hdist : parabolicDist w z ≤ 2 * r := by
        have hw' : parabolicDist w z < r := by
          simpa [dist_eq_parabolicDist] using hw
        linarith only [hw', hr]
      have hinc := hfar (F := F) (G := G) hFmeas hGmeas hFmorrey hGmorrey z r (j + 6) hr
        (by omega) w z hw hzball
      calc
        _ ≤ Cfar * (2 * r) * ((2 : ℝ) ^ ((j + 6 : ℕ) : ℝ) * r) ^ (γ - 1) *
            multiplierHeatSourceSize P θ₀ θ₁ F G := by
          exact hinc.trans (by gcongr)
        _ = A (j + 6) := by rfl
    have hkcenter : ∀ᵐ w ∂(volume.restrict B), ‖k w - k z‖ ≤ D := by
      filter_upwards [hballAE] with w hw
      calc
        ‖k w - k z‖ = ‖∑ j ∈ Finset.range N,
            (multiplierHeatPotentialShell σ F G z r (j + 6) w -
              multiplierHeatPotentialShell σ F G z r (j + 6) z)‖ := by
          rw [show k w - k z = ∑ j ∈ Finset.range N,
            (multiplierHeatPotentialShell σ F G z r (j + 6) w -
              multiplierHeatPotentialShell σ F G z r (j + 6) z) by
                simp [k, Finset.sum_sub_distrib]]
        _ ≤ ∑ j ∈ Finset.range N, A (j + 6) := by
          calc
            _ ≤ ∑ j ∈ Finset.range N,
                ‖multiplierHeatPotentialShell σ F G z r (j + 6) w -
                  multiplierHeatPotentialShell σ F G z r (j + 6) z‖ :=
              norm_sum_le _ _
            _ ≤ _ := Finset.sum_le_sum fun j hj => hshell j w hw
        _ ≤ D := hsum
    have hkAEM : AEStronglyMeasurable k (volume.restrict B) :=
      hkLocal.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    have hkcenterAEM : AEStronglyMeasurable (fun w => k w - k z)
        (volume.restrict B) := hkAEM.sub (aestronglyMeasurable_const)
    have hkOsc : multiplierHeatPairOscillation k z r P ≤ 2 * D := by
      rw [← multiplier_pairOscillation_sub_const (k := k) (c := k z)]
      exact heat_near_pair_average_rpow_bound hP hBmeas hBpos hBtop
        hkcenterAEM hkcenter (by positivity)
    have hkdiff : ∀ᵐ xy ∂((volume.restrict B).prod (volume.restrict B)),
        ‖k xy.1 - k xy.2‖ ≤ 2 * D := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hkcenter,
        Measure.quasiMeasurePreserving_snd.ae hkcenter] with xy hxy₁ hxy₂
      calc
        ‖k xy.1 - k xy.2‖ ≤ ‖k xy.1 - k z‖ + ‖k xy.2 - k z‖ := by
          rw [show k xy.1 - k xy.2 = (k xy.1 - k z) - (k xy.2 - k z) by ring_nf]
          exact norm_sub_le _ _
        _ ≤ D + D := add_le_add hxy₁ hxy₂
        _ = 2 * D := by ring_nf
    have hkpow : Integrable (fun xy : ParabolicPoint × ParabolicPoint =>
        ‖k xy.1 - k xy.2‖ ^ P)
        ((volume.restrict B).prod (volume.restrict B)) := by
      have hkdiffAEM : AEStronglyMeasurable
          (fun xy : ParabolicPoint × ParabolicPoint => k xy.1 - k xy.2)
          ((volume.restrict B).prod (volume.restrict B)) := by
        exact (hkAEM.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_fst).sub
          (hkAEM.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
      have hqAEM : AEStronglyMeasurable (fun xy : ParabolicPoint × ParabolicPoint =>
          ‖k xy.1 - k xy.2‖ ^ P)
          ((volume.restrict B).prod (volume.restrict B)) := by
        exact (Real.continuous_rpow_const (zero_le_one.trans hP)).comp_aestronglyMeasurable
          hkdiffAEM.norm
      have hqbound : ∀ᵐ xy ∂((volume.restrict B).prod (volume.restrict B)),
          ‖‖k xy.1 - k xy.2‖ ^ P‖ ≤ (2 * D) ^ P := by
        filter_upwards [hkdiff] with xy hxy
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        have hP0 : 0 ≤ P := le_trans zero_le_one hP
        exact Real.rpow_le_rpow (norm_nonneg _) hxy hP0
      exact (MemLp.of_bound (p := (1 : ℝ≥0∞)) hqAEM ((2 * D) ^ P) hqbound).integrable
        (by norm_num)
    have hadd := multiplier_pairAverage_add_le hP hBpos hBtop hnMem hkAEM hkpow
    have hpairNearRoot :
        (⨍ x in B, ⨍ y in B, ‖hn x - hn y‖ ^ P) ^ (1 / P) ≤
          Cnear * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G := hnOsc
    have hpairFarRoot :
        (⨍ x in B, ⨍ y in B, ‖k x - k y‖ ^ P) ^ (1 / P) ≤ 2 * D := hkOsc
    have hnearPow0 : 0 ≤ (⨍ x in B, ⨍ y in B, ‖hn x - hn y‖ ^ P) := by
      apply Integration.setAverage_nonneg_of_ae
      filter_upwards [] with x
      exact Integration.setAverage_nonneg_of_ae
        (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)
    have hfarPow0 : 0 ≤ (⨍ x in B, ⨍ y in B, ‖k x - k y‖ ^ P) := by
      apply Integration.setAverage_nonneg_of_ae
      filter_upwards [] with x
      exact Integration.setAverage_nonneg_of_ae
        (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)
    have hsumPow0 : 0 ≤
        (⨍ x in B, ⨍ y in B, ‖(hn + k) x - (hn + k) y‖ ^ P) := by
      apply Integration.setAverage_nonneg_of_ae
      filter_upwards [] with x
      exact Integration.setAverage_nonneg_of_ae
        (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)
    have hnearRoot0 : 0 ≤ Cnear * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G := by
      positivity
    have hfarRoot0 : 0 ≤ 2 * D := by positivity
    have hpair : multiplierHeatPairOscillation (hn + k) z r P ≤
        2 * (Cnear * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G + 2 * D) := by
      unfold multiplierHeatPairOscillation
      exact pair_root_add_bound hP hnearPow0 hfarPow0 hsumPow0
        hadd hpairNearRoot hpairFarRoot hnearRoot0 hfarRoot0
    have hrawOsc : multiplierHeatPairOscillation
        (multiplierHeatPotential σ F G) z r P ≤
        2 * (Cnear * r ^ γ * multiplierHeatSourceSize P θ₀ θ₁ F G + 2 * D) := by
      unfold multiplierHeatPairOscillation
      rw [pair_avg_congr measurableSet_closedBall hrawDecomp]
      exact hpair
    have hrawMem : MemLp (multiplierHeatPotential σ F G) (ENNReal.ofReal P)
        (volume.restrict B) := by
      have hkMem : MemLp k (ENNReal.ofReal P) (volume.restrict B) := by
        apply MemLp.of_bound (p := ENNReal.ofReal P) hkAEM (‖k z‖ + D)
        filter_upwards [hkcenter] with w hw
        calc
          ‖k w‖ = ‖(k w - k z) + k z‖ := by congr 1; ring_nf
          _ ≤ ‖k w - k z‖ + ‖k z‖ := norm_add_le _ _
          _ ≤ D + ‖k z‖ := add_le_add_left hw _
          _ = ‖k z‖ + D := by ring_nf
      exact (memLp_congr_ae (hrawDecomp.filter_mono ae_restrict_le)).2
        (hnMem.add hkMem)
    refine ⟨hn, k, hkLocal, hrawDecomp, hrawMem, ?_⟩
    convert hrawOsc using 1
    dsimp [D, Dcoef]
    ring_nf
  refine ⟨hbar, hlocal, Filter.Eventually.of_forall (fun w => rfl), ?_, ?_⟩
  · intro z R hR
    obtain ⟨hn, k, hk, heq, hmem, hosc⟩ := hassemble z hR
    simpa [hbar] using hmem
  · intro z r hr
    obtain ⟨hn, k, hk, heq, hmem, hosc⟩ := hassemble z hr
    change multiplierHeatPairOscillation (multiplierHeatPotential σ F G) z r P ≤ _
    convert hosc using 1
    dsimp [Dcoef]
    ring_nf

end CKN.Core.HeatPotential
