-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.PkBoundsP7SolutionBound

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Euclidean

set_option autoImplicit false
noncomputable section

namespace CKN

/-- The solution-level cylinder estimate for the seventh pressure term retains
the scale gain from the source estimate. -/
theorem pressureP7_cylinder_bound_sharp_of_sws (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ r : ℝ}, (hρ : 0 < ρ) → 0 < r → r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint =>
          pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        ENNReal.ofReal (C * (r / ρ) ^ (9 / 5 - 2 / q : ℝ) * lambda q f z ρ) := by
  let C₇q : ℝ := (pressureP7SolutionConstant q).toReal
  have hC₇q : 0 ≤ C₇q := by
    dsimp [C₇q]
    exact ENNReal.toReal_nonneg
  refine ⟨C₇q, hC₇q, ?_⟩
  intro Ω I u Du p f hsol z ρ r hρ hr hhalf hsub
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hconstant : pressureP7SolutionConstant q = ENNReal.ofReal C₇q := by
    dsimp [C₇q]
    rw [ENNReal.ofReal_toReal (pressureP7SolutionConstant_ne_top hq)]
  have hbound :
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint =>
          pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        pressureP7SolutionConstant q *
          ENNReal.ofReal ((r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
            lambda q f z ρ) := by
    let Bρ : Set Vec3 := vec3Ball z.1 ρ
    let Br : Set Vec3 := vec3Ball z.1 r
    let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
    let Tr : Set ℝ := Ioc (z.2 - r ^ 2) z.2
    let H : ℝ → ℝ≥0∞ := fun s =>
      ∫⁻ x in Bρ, ‖f (x, s)‖ₑ ^ q
    let G : ℝ → ℝ := fun s => (H s).toReal ^ (1 / q : ℝ)
    let C : ℝ≥0∞ := 3 * (ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant)
    let V : ℝ≥0∞ := volume Bρ ^ (2 / 5 - 1 / q : ℝ)
    let W : ℝ≥0∞ := volume Br ^ (3 / 5 : ℝ)
    obtain ⟨Ω', J, hbox, hball, htime⟩ :=
      pressure_box_geometry hsol hρ hsub
    have hBΩ : Bρ ⊆ Ω := by
      intro x hx
      exact hbox.2.2.1 (subset_closure (hball hx))
    have hηc : HasCompactSupport (mollifiedBallCutoff z.1 hρ) :=
      mollifiedBallCutoff_hasCompactSupport z.1 hρ
    have hηΩ : tsupport (mollifiedBallCutoff z.1 hρ) ⊆ Ω :=
      (pressure_cutoff_support_subset_ball z.1 hρ).trans hBΩ
    have hηbound : ∀ x, |mollifiedBallCutoff z.1 hρ x| ≤ 1 := by
      intro x
      apply abs_le.mpr
      constructor
      · linarith only [mollifiedBallCutoff_nonneg z.1 hρ x]
      · exact mollifiedBallCutoff_le_one z.1 hρ x
    have hηmeas : AEStronglyMeasurable (mollifiedBallCutoff z.1 hρ) volume :=
      (mollifiedBallCutoff_smooth z.1 hρ).continuous.aestronglyMeasurable
    have hηsupport : tsupport (mollifiedBallCutoff z.1 hρ) ⊆ Bρ := by
      exact pressure_cutoff_support_subset_ball z.1 hρ
    have hqpos : 0 < q := lt_trans (by norm_num) hq
    obtain ⟨hHmeas, hHglobal⟩ := sws_force_time_data hsol hρ hsub
    have hHmeas' : AEMeasurable H (volume.restrict Tρ) := by
      simpa [H, Bρ, Tρ] using hHmeas
    have hHglobal' : (∫⁻ s in Tρ, H s) ≤
        ENNReal.ofReal ((ρ ^ (5 / q - 3) * lambda q f z ρ) ^ q) := by
      have hz : (z.1, z.2) = z := by cases z; rfl
      simpa [H, Bρ, Tρ, hz] using hHglobal
    have hHtop : (∫⁻ s in Tρ, H s) < ⊤ :=
      lt_of_le_of_lt hHglobal' ENNReal.ofReal_lt_top
    have hHs : ∀ᵐ s ∂volume.restrict Tρ, H s < ⊤ :=
      ae_lt_top' hHmeas' (ne_of_lt hHtop)
    have hGmeas : AEStronglyMeasurable G (volume.restrict Tρ) := by
      have hreal := hHmeas'.ennreal_toReal
      have hc : Continuous (fun x : ℝ => x ^ (1 / q : ℝ)) :=
        Real.continuous_rpow_const (by positivity)
      simpa [Function.comp_def, G] using
        (hc.measurable.comp_aemeasurable hreal).aestronglyMeasurable
    have hGnonneg : 0 ≤ᵐ[volume.restrict Tρ] G :=
      Eventually.of_forall (fun s => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    have hforce : 0 ≤ ρ ^ (5 / q - 3) * lambda q f z ρ := by
      exact mul_nonneg (Real.rpow_nonneg hρ.le _) (by unfold lambda; positivity)
    have hGbound : eLpNorm' G q (volume.restrict Tρ) ≤
        ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ) := by
      exact force_time_norm_bound hqpos hforce hHs hHglobal'
    have htime_holder := time_holder_q (t₀ := z.2) (r := r) (ρ := ρ) (q := q)
      hr hhalf (by linarith only [hq]) (g := G) hGmeas hGnonneg
    have hsource := sws_p7_slice_data hsol hρ hsub hηc hηΩ hηbound hηsupport hηmeas
    have hD : ∀ᵐ s ∂volume.restrict Tρ,
        eLpNorm' (fun x : Vec3 =>
          pressureP7 (mollifiedBallCutoff z.1 hρ) f s x) (15 : ℝ) volume ≤
        C * eLpNorm' (fun x : Vec3 => f (x, s)) q
            (volume.restrict Bρ) * V := by
      filter_upwards [hsource, hHs] with s hs htop
      have hsP := pressureP7_eLpNorm15_le_slice_holder hq hηbound hηsupport
        hs.1 hs.2.1 (fun j => (hs.2.2 j).1)
        (fun j => (hs.2.2 j).2.1) (fun j => (hs.2.2 j).2.2)
      simpa [C, V, Bρ] using hsP
    have hnorm : ∀ᵐ s ∂volume.restrict Tρ,
        eLpNorm' (fun x : Vec3 => f (x, s)) q (volume.restrict Bρ) ≤
          ENNReal.ofReal (G s) := by
      filter_upwards [hHs] with s hs
      rw [eLpNorm'_eq_lintegral_enorm]
      have hpow : (∫⁻ x in Bρ, ‖f (x, s)‖ₑ ^ q) ^ (1 / q : ℝ) =
          ENNReal.ofReal (G s) := by
        rw [show (∫⁻ x in Bρ, ‖f (x, s)‖ₑ ^ q) = H s by rfl]
        rw [ennreal_rpow_eq_ofReal_toReal_rpow hs.ne hqpos]
      exact hpow.le
    have hQr : parabolicCylinder z.1 z.2 r ⊆
        parabolicCylinder z.1 z.2 ρ := by
      intro w hw
      change w.1 ∈ vec3Ball z.1 r ∧
        w.2 ∈ Ioc (z.2 - r ^ 2) z.2 at hw
      change w.1 ∈ vec3Ball z.1 ρ ∧
        w.2 ∈ Ioc (z.2 - ρ ^ 2) z.2
      rcases hw with ⟨hwx, hwt⟩
      refine ⟨?_, ?_⟩
      · rw [mem_vec3Ball] at hwx ⊢
        have hrho : r ≤ ρ := hhalf.trans (by linarith only [hρ])
        exact lt_of_lt_of_le hwx hrho
      · have hρ0 : 0 ≤ ρ := by linarith only [hhalf, hr]
        have hsq : r ^ 2 ≤ ρ ^ 2 := by
          exact (sq_le_sq₀ hr.le hρ0).2 (by linarith only [hhalf, hρ0])
        exact ⟨by linarith only [hwt.1, hsq], hwt.2⟩
    have hTr : Tr ⊆ Tρ := by
      intro s hs
      have hρ0 : 0 ≤ ρ := by linarith only [hhalf, hr]
      have hsq : r ^ 2 ≤ ρ ^ 2 := by
        exact (sq_le_sq₀ hr.le hρ0).2 (by linarith only [hhalf, hρ0])
      exact ⟨by linarith only [hs.1, hsq], hs.2⟩
    have hPprod : AEStronglyMeasurable
        (fun w : Vec3 × ℝ =>
          pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
        ((volume.restrict Br).prod (volume.restrict Tr)) := by
      have hP := pressureP7_aestronglyMeasurable_on_cylinder hsol hρ hsub
      have hP' := hP.mono_measure (Measure.restrict_mono_set volume hQr)
      have hset : parabolicCylinder z.1 z.2 r = Br ×ˢ Tr := by
        ext w
        rfl
      rw [hset] at hP'
      have hmeasure : volume.restrict (Br ×ˢ Tr) =
          (volume.restrict Br).prod (volume.restrict Tr) := by
        rw [Measure.prod_restrict Br Tr,
          MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
      rw [← hmeasure]
      exact hP'
    let D : ℝ → ℝ≥0∞ := fun s =>
      C * eLpNorm' (fun x : Vec3 => f (x, s)) q (volume.restrict Bρ) * V
    have hprod : eLpNorm'
        (fun w : Vec3 × ℝ =>
          pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
        (3 / 2 : ℝ) ((volume.restrict Br).prod (volume.restrict Tr)) ≤
        (∫⁻ s in Tr,
          ((C * eLpNorm' (fun x : Vec3 => f (x, s)) q
            (volume.restrict Bρ) * V) * W) ^ (3 / 2 : ℝ)) ^
              (2 / 3 : ℝ) := by
      have hDTr := ae_restrict_of_ae_restrict_of_subset hTr hD
      have hmeasure : volume.restrict (Br ×ˢ Tr) =
          (volume.restrict Br).prod (volume.restrict Tr) := by
        rw [Measure.prod_restrict Br Tr,
          MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
      have hPprod' := hPprod
      rw [← hmeasure] at hPprod'
      have hbound := eLpNorm'_prod_three_halves (P := fun w : Vec3 × ℝ =>
        pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
        (B := Br) (T := Tr) hPprod' hDTr
      rw [hmeasure] at hbound
      simpa [W] using hbound
    have hnormTr := ae_restrict_of_ae_restrict_of_subset hTr hnorm
    have hDpoint : ∀ᵐ s ∂volume.restrict Tr,
        D s * W ≤ (C * V * W) * ENNReal.ofReal (G s) := by
      filter_upwards [hnormTr] with s hs
      dsimp [D]
      calc
        (C * eLpNorm' (fun x : Vec3 => f (x, s)) q
            (volume.restrict Bρ) * V) * W ≤
            (C * ENNReal.ofReal (G s) * V) * W := by
              gcongr
        _ = (C * V * W) * ENNReal.ofReal (G s) := by ring
    have hInt :
        (∫⁻ s in Tr, (D s * W) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
          (C * V * W) *
            ((ENNReal.ofReal r) ^ (2 * (2 / 3 - 1 / q : ℝ)) *
              eLpNorm' G q (volume.restrict Tρ)) := by
      have hmonpow : ∀ᵐ s ∂volume.restrict Tr,
          (D s * W) ^ (3 / 2 : ℝ) ≤
            ((C * V * W) * ENNReal.ofReal (G s)) ^ (3 / 2 : ℝ) := by
        filter_upwards [hDpoint] with s hs
        exact ENNReal.rpow_le_rpow hs (by norm_num)
      have hmonint := lintegral_mono_ae
        (μ := volume.restrict Tr) hmonpow
      calc
        _ ≤ (∫⁻ s in Tr,
            ((C * V * W) * ENNReal.ofReal (G s)) ^ (3 / 2 : ℝ)) ^
              (2 / 3 : ℝ) :=
          ENNReal.rpow_le_rpow hmonint (by norm_num)
        _ = (C * V * W) *
            (∫⁻ s in Tr, ENNReal.ofReal (G s) ^ (3 / 2 : ℝ)) ^
              (2 / 3 : ℝ) := by
          have hfactor : (∫⁻ s in Tr,
              (C * V * W * ENNReal.ofReal (G s)) ^ (3 / 2 : ℝ)) =
              (C * V * W) ^ (3 / 2 : ℝ) *
                (∫⁻ s in Tr, ENNReal.ofReal (G s) ^ (3 / 2 : ℝ)) := by
            simp_rw [ENNReal.mul_rpow_of_nonneg (C * V * W) _
              (by norm_num : (0 : ℝ) ≤ 3 / 2)]
            have hGTr := hGmeas.mono_measure
              (Measure.restrict_mono_set volume hTr)
            have hGpow : AEMeasurable
                (fun s => ENNReal.ofReal (G s) ^ (3 / 2 : ℝ))
                (volume.restrict Tr) :=
              (hGTr.aemeasurable.ennreal_ofReal).pow_const (3 / 2 : ℝ)
            rw [MeasureTheory.lintegral_const_mul'' _ hGpow]
          rw [hfactor]
          rw [ENNReal.mul_rpow_of_nonneg _ _
            (by norm_num : (0 : ℝ) ≤ 2 / 3)]
          rw [← ENNReal.rpow_mul]
          norm_num
        _ ≤ _ := by
          gcongr
    have hmeasureR : (volume : Measure (Vec3 × ℝ)).restrict (Br ×ˢ Tr) =
        (volume.restrict Br).prod (volume.restrict Tr) := by
      rw [Measure.prod_restrict Br Tr,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    have hprodQ := hprod
    rw [← hmeasureR] at hprodQ
    have hraw : ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint =>
          pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          ((C * V * W) *
            ((ENNReal.ofReal r) ^ (2 * (2 / 3 - 1 / q : ℝ)) *
              ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ))) := by
      calc
        _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
            (∫⁻ s in Tr,
              (D s * W) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hprodQ (by positivity)
        _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
            ((C * V * W) *
              ((ENNReal.ofReal r) ^ (2 * (2 / 3 - 1 / q : ℝ)) *
                eLpNorm' G q (volume.restrict Tρ))) := by
          gcongr
        _ ≤ _ := by
          gcongr
    have hscale_eq :
        ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          ((C * V * W) *
            ((ENNReal.ofReal r) ^ (2 * (2 / 3 - 1 / q : ℝ)) *
              ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ))) =
        pressureP7SolutionConstant q *
          ENNReal.ofReal ((r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
            lambda q f z ρ) := by
      have hV := pressure_volume_ball (x₀ := z.1) hρ
      have hW := pressure_volume_ball (x₀ := z.1) hr
      have hqV : 0 ≤ 2 / 5 - 1 / q := by
        have hq' : 1 / q ≤ (2 / 5 : ℝ) := by
          apply (div_le_iff₀ hqpos).2
          nlinarith only [hq]
        linarith only [hq']
      dsimp [V, W, C, pressureP7SolutionConstant]
      rw [hV, hW]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi / 3)]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi / 3)]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hqV]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num :
        (0 : ℝ) ≤ 3 / 5)]
      rw [show (ρ ^ (3 : ℕ) : ℝ) = ρ ^ (3 : ℝ) by norm_num]
      rw [show (r ^ (3 : ℕ) : ℝ) = r ^ (3 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_rpow_of_pos (p := (3 : ℝ)) hρ]
      rw [← ENNReal.ofReal_rpow_of_pos (p := (3 : ℝ)) hr]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      have hsource : ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ) =
          ENNReal.ofReal ρ ^ (5 / q - 3) *
            ENNReal.ofReal (lambda q f z ρ) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
        rw [← ENNReal.ofReal_rpow_of_pos hρ]
      rw [hsource]
      rw [← ENNReal.ofReal_rpow_of_pos (p := (-4 / 3 : ℝ)) hr]
      have htarget : ENNReal.ofReal ((r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
          lambda q f z ρ) =
          ENNReal.ofReal (r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
            ENNReal.ofReal (lambda q f z ρ) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
        rw [← ENNReal.ofReal_rpow_of_pos (div_pos hr hρ)]
      rw [htarget]
      have hc0 : ENNReal.ofReal (4 * Real.pi / 3) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
      have hctop : ENNReal.ofReal (4 * Real.pi / 3) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      have hr0 : ENNReal.ofReal r ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr hr)
      have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
      have hρ0 : ENNReal.ofReal ρ ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr hρ)
      have hρtop : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
      have hc : ENNReal.ofReal (4 * Real.pi / 3) ^ (2 / 5 - 1 / q : ℝ) *
          ENNReal.ofReal (4 * Real.pi / 3) ^ (3 / 5 : ℝ) =
          ENNReal.ofReal (4 * Real.pi / 3) ^ (1 - 1 / q : ℝ) := by
        rw [← ENNReal.rpow_add]
        all_goals first | exact hc0 | exact hctop | (congr 1; ring)
      have hrpow : ENNReal.ofReal r ^ (-4 / 3 : ℝ) *
          ENNReal.ofReal r ^ (3 * (3 / 5 : ℝ)) *
          ENNReal.ofReal r ^ (2 * (2 / 3 - 1 / q : ℝ)) =
          ENNReal.ofReal r ^ (9 / 5 - 2 / q : ℝ) := by
        rw [← ENNReal.rpow_add, ← ENNReal.rpow_add]
        all_goals first | exact hr0 | exact hrtop | (congr 1; ring)
      have hrhopow : ENNReal.ofReal ρ ^ (3 * (2 / 5 - 1 / q : ℝ)) *
          ENNReal.ofReal ρ ^ (5 / q - 3 : ℝ) =
          ENNReal.ofReal ρ ^ (-(9 / 5 - 2 / q : ℝ)) := by
        rw [← ENNReal.rpow_add]
        all_goals first | exact hρ0 | exact hρtop | (congr 1; ring)
      calc
        _ = 3 * (ENNReal.ofReal (4 * Real.pi)⁻¹ * hlsRieszConstant) *
            (ENNReal.ofReal (4 * Real.pi / 3) ^ (2 / 5 - 1 / q : ℝ) *
              ENNReal.ofReal (4 * Real.pi / 3) ^ (3 / 5 : ℝ)) *
            (ENNReal.ofReal r ^ (-4 / 3 : ℝ) *
              ENNReal.ofReal r ^ (3 * (3 / 5 : ℝ)) *
              ENNReal.ofReal r ^ (2 * (2 / 3 - 1 / q : ℝ))) *
            (ENNReal.ofReal ρ ^ (3 * (2 / 5 - 1 / q : ℝ)) *
              ENNReal.ofReal ρ ^ (5 / q - 3 : ℝ)) *
            ENNReal.ofReal (lambda q f z ρ) := by ring
        _ = 3 * (ENNReal.ofReal (4 * Real.pi)⁻¹ * hlsRieszConstant) *
            ENNReal.ofReal (4 * Real.pi / 3) ^ (1 - 1 / q : ℝ) *
            (ENNReal.ofReal r ^ (9 / 5 - 2 / q : ℝ) *
              ENNReal.ofReal ρ ^ (-(9 / 5 - 2 / q : ℝ))) *
            ENNReal.ofReal (lambda q f z ρ) := by
          rw [hc, hrpow, hrhopow]
          ring
        _ = _ := by
          have hratio : ENNReal.ofReal (r / ρ) ^ (9 / 5 - 2 / q : ℝ) =
              ENNReal.ofReal r ^ (9 / 5 - 2 / q : ℝ) *
                ENNReal.ofReal ρ ^ (-(9 / 5 - 2 / q : ℝ)) := by
            rw [ENNReal.ofReal_rpow_of_pos (div_pos hr hρ)]
            rw [pressure_rpow_div hr hρ]
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
            rw [← ENNReal.ofReal_rpow_of_pos
              (p := (9 / 5 - 2 / q : ℝ)) hr]
            rw [← ENNReal.ofReal_rpow_of_pos
              (p := (-(9 / 5 - 2 / q : ℝ))) hρ]
          rw [hratio]
          ring
    exact hraw.trans hscale_eq.le
  have hcoef :
      ENNReal.ofReal (C₇q * ((r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
        lambda q f z ρ)) =
      pressureP7SolutionConstant q *
        ENNReal.ofReal ((r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
          lambda q f z ρ) := by
    rw [ENNReal.ofReal_mul hC₇q, hconstant]
  calc
    _ ≤ pressureP7SolutionConstant q *
        ENNReal.ofReal ((r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
          lambda q f z ρ) := hbound
    _ = ENNReal.ofReal (C₇q * ((r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
        lambda q f z ρ)) := hcoef.symm
    _ = ENNReal.ofReal (C₇q * (r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
        lambda q f z ρ) := by congr 1; ring

end CKN
