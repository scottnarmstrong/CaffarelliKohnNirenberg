-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Covering.CylinderRadiusContent

/-! # Comparison of the parabolic spherical and diameter gauges

The countable-cover radius gauge on parabolic balls and the diameter gauge
defined by Mathlib's Hausdorff measure differ by at most the factor `2^α`.
-/

open MeasureTheory Set Metric
open scoped ENNReal

set_option autoImplicit false
noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

private lemma spherical_ediam_le (c : ParabolicPoint) (r : ℝ) :
    Metric.ediam (Metric.ball c r) ≤ ENNReal.ofReal (2 * r) := by
  refine Metric.ediam_le_of_forall_dist_le ?_
  intro x hx y hy
  calc
    dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
    _ ≤ r + r := add_le_add hx.le (by rw [dist_comm]; exact hy.le)
    _ = 2 * r := by ring

private lemma iSup_ediam_rpow_of_nonempty (α : ℝ) (s : Set ParabolicPoint)
    (hs : s.Nonempty) :
    (⨆ _ : s.Nonempty, Metric.ediam s ^ α) = Metric.ediam s ^ α := by
  exact le_antisymm (iSup_le fun _ => le_rfl) (le_iSup (fun _ : s.Nonempty =>
    Metric.ediam s ^ α) hs)

private lemma iSup_ediam_rpow_of_empty (α : ℝ) (s : Set ParabolicPoint)
    (hs : ¬ s.Nonempty) :
    (⨆ _ : s.Nonempty, Metric.ediam s ^ α) = 0 := by
  rw [Set.not_nonempty_iff_eq_empty.mp hs, Metric.ediam_empty]
  simp

private lemma hausdorff_scale_le_spherical_scale
    (α : ℝ) (hα : 0 ≤ α) (ε : ℝ≥0∞) (E : Set ParabolicPoint)
    (δ : ℝ) (hε : ENNReal.ofReal (2 * δ) ≤ ε) :
    (⨅ (t : ℕ → Set ParabolicPoint) (_ : E ⊆ ⋃ n, t n)
      (_ : ∀ n, Metric.ediam (t n) ≤ ε),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) ≤
    (2 : ℝ≥0∞) ^ α * parabolicBallRadiusContent α δ E := by
  classical
  unfold parabolicBallRadiusContent radiusCoverContent
  simp_rw [ENNReal.mul_iInf_of_ne
    (by positivity : (2 : ℝ≥0∞) ^ α ≠ 0)
    (by finiteness : (2 : ℝ≥0∞) ^ α ≠ ⊤)]
  refine le_iInf fun T => le_iInf fun z => le_iInf fun r =>
    le_iInf fun hr => le_iInf fun hc => ?_
  let cover : ℕ → Set ParabolicPoint := fun n =>
    if hn : n ∈ T then Metric.ball (z ⟨n, hn⟩) (r ⟨n, hn⟩) else ∅
  have hcover : E ⊆ ⋃ n, cover n := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hc hx)
    exact mem_iUnion.mpr ⟨i.1, by simpa only [cover, dite_eq_left i.2] using hi⟩
  have hdiam : ∀ n, Metric.ediam (cover n) ≤ ε := by
    intro n
    by_cases hn : n ∈ T
    · simp only [cover, dite_eq_left hn]
      calc
        Metric.ediam (Metric.ball (z ⟨n, hn⟩) (r ⟨n, hn⟩)) ≤
            ENNReal.ofReal (2 * r ⟨n, hn⟩) := spherical_ediam_le _ _
        _ ≤ ENNReal.ofReal (2 * δ) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith only [(hr ⟨n, hn⟩).2]
        _ ≤ ε := hε
    · simp only [cover, dite_eq_right hn, ediam_empty]
      exact bot_le
  have hterm : ∀ n,
      (⨆ _ : (cover n).Nonempty, Metric.ediam (cover n) ^ α) ≤
        (if hn : n ∈ T then (2 : ℝ≥0∞) ^ α *
          ENNReal.ofReal (r ⟨n, hn⟩) ^ α else 0) := by
    intro n
    by_cases hn : n ∈ T
    · simp only [cover, dite_eq_left hn]
      rw [iSup_ediam_rpow_of_nonempty]
      · calc
          Metric.ediam (Metric.ball (z ⟨n, hn⟩) (r ⟨n, hn⟩)) ^ α ≤
              ENNReal.ofReal (2 * r ⟨n, hn⟩) ^ α :=
                ENNReal.rpow_le_rpow (spherical_ediam_le _ _) hα
          _ = (2 : ℝ≥0∞) ^ α * ENNReal.ofReal (r ⟨n, hn⟩) ^ α := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
              ENNReal.mul_rpow_of_nonneg _ _ hα]
            norm_num
      · exact ⟨z ⟨n, hn⟩, Metric.mem_ball_self (hr ⟨n, hn⟩).1⟩
    · simp only [cover, dite_eq_right hn, ediam_empty]
      simp
  have hsum :
      (∑' n, ⨆ _ : (cover n).Nonempty, Metric.ediam (cover n) ^ α) ≤
        (2 : ℝ≥0∞) ^ α * (∑' i : T, ENNReal.ofReal (r i) ^ α) := by
    calc
      _ ≤ ∑' n, (if hn : n ∈ T then (2 : ℝ≥0∞) ^ α *
            ENNReal.ofReal (r ⟨n, hn⟩) ^ α else 0) := ENNReal.tsum_le_tsum hterm
      _ = (2 : ℝ≥0∞) ^ α * ∑' i : T, ENNReal.ofReal (r i) ^ α := by
        let f : ℕ → ℝ≥0∞ := fun n =>
          if hn : n ∈ T then ENNReal.ofReal (r ⟨n, hn⟩) ^ α else 0
        calc
          ∑' n, (if hn : n ∈ T then (2 : ℝ≥0∞) ^ α *
              ENNReal.ofReal (r ⟨n, hn⟩) ^ α else 0) =
              ∑' n, (2 : ℝ≥0∞) ^ α * f n := by
            apply tsum_congr
            intro n
            by_cases hn : n ∈ T <;> simp [f, hn]
          _ = (2 : ℝ≥0∞) ^ α * ∑' n, f n := ENNReal.tsum_mul_left
          _ = (2 : ℝ≥0∞) ^ α * ∑' i : T, f i := by
            congr 1
            calc
              ∑' n, f n = ∑' n, T.indicator f n := by
                apply tsum_congr
                intro n
                by_cases hn : n ∈ T <;> simp [f, hn]
              _ = ∑' i : T, f i := (tsum_subtype T f).symm
          _ = (2 : ℝ≥0∞) ^ α * ∑' i : T, ENNReal.ofReal (r i) ^ α := by
            congr 1
            apply tsum_congr
            intro i
            simp [f]
  exact (iInf_le_of_le cover (iInf_le_of_le hcover
    (iInf_le_of_le hdiam hsum)))

private lemma hausdorff_le_spherical_gauge
    (α : ℝ) (hα : 0 ≤ α) (E : Set ParabolicPoint) :
    Measure.hausdorffMeasure α E ≤
      (2 : ℝ≥0∞) ^ α * parabolicBallRadiusHausdorffContent α E := by
  rw [Measure.hausdorffMeasure_apply]
  refine iSup_le fun ε => iSup_le fun hε => ?_
  by_cases htop : ε = ⊤
  · subst ε
    have hscale := hausdorff_scale_le_spherical_scale α hα ⊤ E 1 (by simp)
    exact hscale.trans (mul_le_mul_of_nonneg_left
      (le_iSup_of_le 1 (le_iSup_of_le (by norm_num) le_rfl)) (by positivity))
  · have hreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    let δ := ε.toReal / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hdiam : ENNReal.ofReal (2 * δ) ≤ ε := by
      dsimp [δ]
      rw [show (2 : ℝ) * (ε.toReal / 2) = ε.toReal by ring,
        ENNReal.ofReal_toReal htop]
    have hscale := hausdorff_scale_le_spherical_scale α hα ε E δ hdiam
    exact hscale.trans (mul_le_mul_of_nonneg_left
      (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)) (by positivity))

private lemma spherical_scale_le_hausdorff_scale_zero
    (δ : ℝ) (hδ : 0 < δ) (E : Set ParabolicPoint) :
    parabolicBallRadiusContent 0 δ E ≤
      (⨅ (t : ℕ → Set ParabolicPoint) (_ : E ⊆ ⋃ n, t n)
        (_ : ∀ n, Metric.ediam (t n) ≤ ENNReal.ofReal (δ / 2)),
        ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (0 : ℝ)) := by
  classical
  unfold parabolicBallRadiusContent radiusCoverContent
  refine le_iInf fun t => le_iInf fun hc => le_iInf fun hd => ?_
  let T : Set ℕ := {n | (t n).Nonempty}
  let z : T → ParabolicPoint := fun n => n.2.some
  let r : T → ℝ := fun _ => δ
  have hr : ∀ i : T, 0 < r i ∧ r i ≤ δ := fun _ => ⟨hδ, le_rfl⟩
  have hcover : E ⊆ ⋃ i : T, Metric.ball (z i) (r i) := by
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp (hc hx)
    have hn : n ∈ T := ⟨x, hxn⟩
    have hw : z ⟨n, hn⟩ ∈ t n := hn.some_mem
    have hed : edist x (z ⟨n, hn⟩) ≤ Metric.ediam (t n) :=
      Metric.edist_le_ediam_of_mem hxn hw
    have hdist' : ENNReal.ofReal (dist x (z ⟨n, hn⟩)) ≤ ENNReal.ofReal (δ / 2) := by
      calc
        ENNReal.ofReal (dist x (z ⟨n, hn⟩)) = edist x (z ⟨n, hn⟩) := by
          rw [edist_dist]
        _ ≤ Metric.ediam (t n) := hed
        _ ≤ ENNReal.ofReal (δ / 2) := hd n
    have hdist : dist x (z ⟨n, hn⟩) ≤ δ / 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hdist'
    have hball : dist x (z ⟨n, hn⟩) < δ := by linarith only [hdist, hδ]
    exact mem_iUnion.mpr ⟨⟨n, hn⟩, Metric.mem_ball.mpr hball⟩
  have hcost :
      (∑' i : T, ENNReal.ofReal (r i) ^ (0 : ℝ)) =
        ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (0 : ℝ) := by
    calc
      ∑' i : T, ENNReal.ofReal (r i) ^ (0 : ℝ) = ∑' i : T, 1 := by
        apply tsum_congr
        intro i
        simp [r]
      _ = ∑' n, T.indicator (fun _ : ℕ => (1 : ℝ≥0∞)) n := by
        simpa using (tsum_subtype T (fun _ : ℕ => (1 : ℝ≥0∞)))
      _ = ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (0 : ℝ) := by
        apply tsum_congr
        intro n
        by_cases hn : n ∈ T
        · have hnon : (t n).Nonempty := hn
          rw [Set.indicator_of_mem hn, iSup_ediam_rpow_of_nonempty 0 (t n) hnon]
          simp
        · have hempty : ¬ (t n).Nonempty := hn
          rw [iSup_ediam_rpow_of_empty 0 (t n) hempty]
          simp [Set.indicator, hn]
  exact iInf_le_of_le T (iInf_le_of_le z (iInf_le_of_le r
    (iInf_le_of_le hr (iInf_le_of_le hcover (le_of_eq hcost)))))

private lemma spherical_scale_le_hausdorff_scale_add
    (α δ e : ℝ) (hα : 0 < α) (hδ : 0 < δ)
    (he : 0 < e) (heδ : e ≤ (δ / 2) ^ α) (E : Set ParabolicPoint) :
    parabolicBallRadiusContent α δ E ≤
      (2 : ℝ≥0∞) ^ α *
        (⨅ (t : ℕ → Set ParabolicPoint) (_ : E ⊆ ⋃ n, t n)
          (_ : ∀ n, Metric.ediam (t n) ≤ ENNReal.ofReal (δ / 4)),
          ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) +
        ENNReal.ofReal e := by
  classical
  unfold parabolicBallRadiusContent radiusCoverContent
  simp_rw [ENNReal.mul_iInf_of_ne
    (by positivity : (2 : ℝ≥0∞) ^ α ≠ 0)
    (by finiteness : (2 : ℝ≥0∞) ^ α ≠ ⊤), ENNReal.iInf_add]
  refine le_iInf fun t => le_iInf fun hc => le_iInf fun hd => ?_
  let d : ℕ → ℝ := fun n => (Metric.ediam (t n)).toReal
  let q : ℕ → ℝ := fun n => e / 2 / 2 ^ n
  let η : ℕ → ℝ := fun n => (q n) ^ α⁻¹
  let w : ℕ → ParabolicPoint := fun n =>
    if hn : (t n).Nonempty then hn.some else (0, 0)
  let R : ℕ → ℝ := fun n => max (2 * d n) (η n)
  have hdtop : ∀ n, Metric.ediam (t n) ≠ ⊤ := by
    intro n
    exact (lt_of_le_of_lt (hd n) ENNReal.ofReal_lt_top).ne
  have hd_eq : ∀ n, ENNReal.ofReal (d n) = Metric.ediam (t n) := by
    intro n
    exact ENNReal.ofReal_toReal (hdtop n)
  have hd_nonneg : ∀ n, 0 ≤ d n := fun n => ENNReal.toReal_nonneg
  have hd_bound : ∀ n, d n ≤ δ / 4 := by
    intro n
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [hd_eq n]
    exact hd n
  have hq_pos : ∀ n, 0 < q n := by
    intro n
    dsimp [q]
    positivity
  have hq_le : ∀ n, q n ≤ e := by
    intro n
    have hn : (1 : ℝ) ≤ 2 * 2 ^ n := by
      have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith only [hp]
    dsimp [q]
    rw [div_div]
    exact div_le_self he.le hn
  have hη_pos : ∀ n, 0 < η n := by
    intro n
    dsimp [η]
    exact Real.rpow_pos_of_pos (hq_pos n) _
  have hη_pow : ∀ n, η n ^ α = q n := by
    intro n
    dsimp [η]
    exact Real.rpow_inv_rpow (le_of_lt (hq_pos n)) (ne_of_gt hα)
  have hη_bound : ∀ n, η n ≤ δ / 2 := by
    intro n
    have hbase : q n ≤ (δ / 2) ^ α := (hq_le n).trans heδ
    calc
      η n = q n ^ α⁻¹ := rfl
      _ ≤ ((δ / 2) ^ α) ^ α⁻¹ :=
        Real.rpow_le_rpow (hq_pos n).le hbase (inv_nonneg.mpr hα.le)
      _ = δ / 2 := by
        rw [Real.rpow_rpow_inv (by positivity) (ne_of_gt hα)]
  have hR_pos : ∀ n, 0 < R n := by
    intro n
    exact lt_of_lt_of_le (hη_pos n) (le_max_right _ _)
  have hR_le : ∀ n, R n ≤ δ := by
    intro n
    apply (max_le_iff.mpr ⟨?_, ?_⟩)
    · nlinarith only [hd_bound n, hδ]
    · linarith only [hη_bound n, hδ]
  have hd_lt_R : ∀ n, d n < R n := by
    intro n
    by_cases hz : d n = 0
    · rw [hz]
      exact lt_of_lt_of_le (hη_pos n) (le_max_right _ _)
    · have hp : 0 < d n := lt_of_le_of_ne (hd_nonneg n) (Ne.symm hz)
      exact (by
        calc
          d n < 2 * d n := by nlinarith only [hp]
          _ ≤ R n := le_max_left _ _)
  have hw : ∀ n, (t n).Nonempty → w n ∈ t n := by
    intro n hn
    have hchoose : w n = hn.some := by simp [w, hn]
    rw [hchoose]
    exact hn.some_mem
  have hcover : E ⊆ ⋃ n, Metric.ball (w n) (R n) := by
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp (hc hx)
    have hwn : w n ∈ t n := hw n ⟨x, hxn⟩
    have hed : edist x (w n) ≤ Metric.ediam (t n) :=
      Metric.edist_le_ediam_of_mem hxn hwn
    have hdist' : ENNReal.ofReal (dist x (w n)) ≤ ENNReal.ofReal (d n) := by
      calc
        ENNReal.ofReal (dist x (w n)) = edist x (w n) := by rw [edist_dist]
        _ ≤ Metric.ediam (t n) := hed
        _ = ENNReal.ofReal (d n) := (hd_eq n).symm
    have hdist : dist x (w n) ≤ d n :=
      (ENNReal.ofReal_le_ofReal_iff (hd_nonneg n)).mp hdist'
    exact mem_iUnion.mpr ⟨n, Metric.mem_ball.mpr (hdist.trans_lt (hd_lt_R n))⟩
  have hcost_term : ∀ n,
      ENNReal.ofReal (R n) ^ α ≤
        (2 : ℝ≥0∞) ^ α *
          (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) +
          ENNReal.ofReal (η n ^ α) := by
    intro n
    have hdR : 0 ≤ R n := (hR_pos n).le
    have hmaxpow : R n ^ α = max ((2 * d n) ^ α) (η n ^ α) := by
      dsimp [R]
      exact Real.rpow_max (by positivity) (hη_pos n).le hα.le
    have hmain : ENNReal.ofReal ((2 * d n) ^ α) =
        (2 : ℝ≥0∞) ^ α * (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hα.le,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.mul_rpow_of_nonneg _ _ hα.le]
      norm_num
      rw [hd_eq n]
      by_cases hn : (t n).Nonempty
      · rw [iSup_ediam_rpow_of_nonempty α (t n) hn]
      · rw [iSup_ediam_rpow_of_empty α (t n) hn]
        have ht : t n = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
        simp [ht, ENNReal.zero_rpow_of_pos hα]
    rw [ENNReal.ofReal_rpow_of_nonneg hdR hα.le, hmaxpow, ENNReal.ofReal_max]
    refine (max_le_iff.mpr ⟨?_, ?_⟩)
    · calc
        ENNReal.ofReal ((2 * d n) ^ α) =
            (2 : ℝ≥0∞) ^ α * (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) := hmain
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · exact le_add_of_nonneg_left (by positivity)
  have hηsum : (∑' n, ENNReal.ofReal (η n ^ α)) = ENNReal.ofReal e := by
    calc
      ∑' n, ENNReal.ofReal (η n ^ α) = ∑' n, ENNReal.ofReal (q n) := by
        apply tsum_congr
        intro n
        rw [hη_pow n]
      _ = ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hq_pos n).le)
          (hasSum_geometric_two' e).summable]
        rw [(hasSum_geometric_two' e).tsum_eq]
  have hsum :
      (∑' n, ENNReal.ofReal (R n) ^ α) ≤
        (2 : ℝ≥0∞) ^ α *
            (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) +
          ENNReal.ofReal e := by
    calc
      _ ≤ ∑' n, ((2 : ℝ≥0∞) ^ α *
          (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) +
          ENNReal.ofReal (η n ^ α)) := ENNReal.tsum_le_tsum hcost_term
      _ = (2 : ℝ≥0∞) ^ α *
          (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) +
          ∑' n, ENNReal.ofReal (η n ^ α) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
      _ = _ := by rw [hηsum]
  let T : Set ℕ := Set.univ
  let z : T → ParabolicPoint := fun i => w i
  let r : T → ℝ := fun i => R i
  have hr : ∀ i : T, 0 < r i ∧ r i ≤ δ := fun i => ⟨hR_pos i, hR_le i⟩
  have hballcover : E ⊆ ⋃ i : T, Metric.ball (z i) (r i) := by
    simpa [T, z, r] using hcover
  have hsum_subtype : (∑' i : T, ENNReal.ofReal (r i) ^ α) =
      ∑' n, ENNReal.ofReal (R n) ^ α := by
    simpa [T, r] using
      (tsum_subtype (Set.univ : Set ℕ) (fun n : ℕ => ENNReal.ofReal (R n) ^ α))
  refine iInf_le_of_le (Set.univ : Set ℕ) ?_
  refine iInf_le_of_le z ?_
  refine iInf_le_of_le r ?_
  refine iInf_le_of_le hr ?_
  refine iInf_le_of_le hballcover ?_
  calc
    ∑' i : T, ENNReal.ofReal (r i) ^ α =
        ∑' n, ENNReal.ofReal (R n) ^ α := hsum_subtype
    _ ≤ _ := hsum

private lemma hausdorff_scale_le_measure
    (α : ℝ) (ε : ℝ≥0∞) (hε : 0 < ε) (E : Set ParabolicPoint) :
    (⨅ (t : ℕ → Set ParabolicPoint) (_ : E ⊆ ⋃ n, t n)
      (_ : ∀ n, Metric.ediam (t n) ≤ ε),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) ≤
      Measure.hausdorffMeasure α E := by
  rw [Measure.hausdorffMeasure_apply]
  exact le_iSup_of_le ε (le_iSup_of_le hε le_rfl)

private lemma spherical_gauge_le_hausdorff
    (α : ℝ) (hα : 0 < α) (E : Set ParabolicPoint) :
    parabolicBallRadiusHausdorffContent α E ≤
      (2 : ℝ≥0∞) ^ α * Measure.hausdorffMeasure α E := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  unfold parabolicBallRadiusHausdorffContent
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
  let e := min (ε : ℝ) ((δ / 2) ^ α)
  have he : 0 < e := by
    dsimp [e]
    exact lt_min hεreal (by positivity)
  have heδ : e ≤ (δ / 2) ^ α := min_le_right _ _
  have heε : e ≤ (ε : ℝ) := min_le_left _ _
  have hscale := spherical_scale_le_hausdorff_scale_add α δ e hα hδ he heδ E
  have hscale_pos : 0 < ENNReal.ofReal (δ / 4) := ENNReal.ofReal_pos.mpr (by positivity)
  have hmeasure := hausdorff_scale_le_measure α (ENNReal.ofReal (δ / 4))
    hscale_pos E
  have he' : ENNReal.ofReal e ≤ (ε : ℝ≥0∞) := by
    rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
    exact heε
  calc
    parabolicBallRadiusContent α δ E ≤
        (2 : ℝ≥0∞) ^ α *
          (⨅ (t : ℕ → Set ParabolicPoint) (_ : E ⊆ ⋃ n, t n)
            (_ : ∀ n, Metric.ediam (t n) ≤ ENNReal.ofReal (δ / 4)),
            ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ α) +
          ENNReal.ofReal e := hscale
    _ ≤ (2 : ℝ≥0∞) ^ α * Measure.hausdorffMeasure α E + ε := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmeasure (by positivity)) he'

private lemma spherical_gauge_zero_le_hausdorff
    (E : Set ParabolicPoint) :
    parabolicBallRadiusHausdorffContent 0 E ≤ Measure.hausdorffMeasure 0 E := by
  unfold parabolicBallRadiusHausdorffContent
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  have hscale := spherical_scale_le_hausdorff_scale_zero δ hδ E
  have hscale_pos : 0 < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.mpr (by positivity)
  have hmeasure := hausdorff_scale_le_measure 0 (ENNReal.ofReal (δ / 2)) hscale_pos E
  simpa using hscale.trans hmeasure

/-- The diameter-based Hausdorff measure and the countable-cover spherical
radius gauge are comparable in every nonnegative dimension, with the source's
factor `2^α` in both directions. The radius gauge allows arbitrary subsets of
`ℕ` as cover indices, including finite and empty covers. -/
theorem parabolic_spherical_hausdorff_comparison
    (α : ℝ) (hα : 0 ≤ α) (E : Set ParabolicPoint) :
    Measure.hausdorffMeasure α E ≤
      (2 : ℝ≥0∞) ^ α * parabolicBallRadiusHausdorffContent α E ∧
    parabolicBallRadiusHausdorffContent α E ≤
      (2 : ℝ≥0∞) ^ α * Measure.hausdorffMeasure α E := by
  refine ⟨hausdorff_le_spherical_gauge α hα E, ?_⟩
  by_cases hzero : α = 0
  · subst α
    simpa using spherical_gauge_zero_le_hausdorff E
  · have hpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hzero)
    exact spherical_gauge_le_hausdorff α hpos E

end CKN
