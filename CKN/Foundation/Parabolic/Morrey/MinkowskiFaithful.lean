-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Minkowski
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Morrey bounds for bounded diameter support and real kernels

This module records the diameter-support and real-kernel forms of the
Morrey estimates.
-/

open MeasureTheory MeasureTheory.Measure Set Metric
open Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

private theorem morreyNorm_lower_exponent_on_cylinder
    {P κ τ R : ℝ} (hP : 1 ≤ P) (hPκ : P ≤ κ) (hκτ : κ ≤ τ)
    {f : ParabolicPoint → ℝ} {x : Vec3} {t : ℝ} (hR : 0 < R)
    (hsupp : ∀ w ∉ parabolicCylinder x t R, f w = 0) :
    morreyNorm P κ f ≤
      (ENNReal.ofReal R) ^ (5 * (1 / κ - 1 / τ)) * morreyNorm P τ f := by
  exact morreyNorm_bounded_support (p := P) (q := τ) (q' := κ)
    hP (hPκ.trans hκτ) hPκ hκτ (f := f) (z₀ := (x, t)) (R := R) hR hsupp

private lemma parabolic_diameter_subset_cylinder
    {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε)
    {E : Set ParabolicPoint} (hE : E.Nonempty)
    (hdiam : ∀ w ∈ E, ∀ w' ∈ E, parabolicDist w w' ≤ D) :
    ∃ x : Vec3, ∃ t : ℝ, E ⊆ parabolicCylinder x t (D + ε) := by
  classical
  obtain ⟨w₀, hw₀⟩ := hE
  let T : Set ℝ := (fun w : ParabolicPoint => w.2) '' E
  have htime (w w' : ParabolicPoint) (hw : w ∈ E) (hw' : w' ∈ E) :
      |w.2 - w'.2| ≤ D ^ 2 := by
    have hroot : Real.sqrt |w.2 - w'.2| ≤ D := by
      have := (le_max_right (vec3EuclideanNorm (w.1 - w'.1))
        (Real.sqrt |w.2 - w'.2|)).trans (hdiam w hw w' hw')
      simpa [parabolicDist] using this
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hD.le).2 hroot
    simpa only [Real.sq_sqrt (abs_nonneg _)] using hsquare
  have hTupper : BddAbove T := by
    refine ⟨w₀.2 + D ^ 2, ?_⟩
    rintro t ⟨w, hw, rfl⟩
    have ht := htime w w₀ hw hw₀
    have := (abs_le.mp ht).2
    linarith only [this]
  refine ⟨w₀.1, sSup T, ?_⟩
  intro w hw
  have hmem : w.2 ∈ T := ⟨w, hw, rfl⟩
  have hlow : w.2 ≤ sSup T := le_csSup hTupper hmem
  have htop : sSup T ≤ w.2 + D ^ 2 :=
    csSup_le ⟨w.2, hmem⟩ fun s hs => by
      rcases hs with ⟨w', hw', rfl⟩
      have ht := htime w' w hw' hw
      have := (abs_le.mp ht).2
      linarith only [this]
  have hspace : vec3EuclideanNorm (w.1 - w₀.1) ≤ D := by
    have := (le_max_left (vec3EuclideanNorm (w.1 - w₀.1))
      (Real.sqrt |w.2 - w₀.2|)).trans (hdiam w hw w₀ hw₀)
    simpa [parabolicDist] using this
  have hrad : D < D + ε := by linarith only [hε]
  have hradSq : D ^ 2 < (D + ε) ^ 2 := by nlinarith only [hD, hε]
  change (w.1, w.2) ∈ parabolicCylinder w₀.1 (sSup T) (D + ε)
  rw [mem_parabolicCylinder]
  refine ⟨hspace.trans_lt hrad, ?_, hlow⟩
  have hgap : sSup T - w.2 ≤ D ^ 2 := by linarith only [htop]
  nlinarith only [hgap, hradSq]

/-- Lowering the Morrey exponent for support in an arbitrary set of bounded
parabolic diameter. -/
theorem morreyNorm_lower_morrey_exponent_of_diameter
    {P κ τ D : ℝ} (hP : 1 ≤ P) (hPκ : P ≤ κ) (hκτ : κ ≤ τ) (hD : 0 < D)
    {f : ParabolicPoint → ℝ} {E : Set ParabolicPoint}
    (hdiam : ∀ w ∈ E, ∀ w' ∈ E, parabolicDist w w' ≤ D)
    (hsupp : ∀ w ∉ E, f w = 0) :
    morreyNorm P κ f ≤
      ENNReal.ofReal (max 1 (D ^ (5 * (1 / κ - 1 / τ)))) * morreyNorm P τ f := by
  classical
  let δ : ℝ := 5 * (1 / κ - 1 / τ)
  have hPτ : P ≤ τ := hPκ.trans hκτ
  have hκpos : 0 < κ := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hP) hPκ
  have hτpos : 0 < τ := lt_of_lt_of_le hκpos hκτ
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr
      (one_div_le_one_div_of_le hκpos hκτ))
  have hRlim : Tendsto (fun n : ℕ => D + (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 D) := by
    simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpowlim : Tendsto
      (fun n : ℕ => (D + (1 : ℝ) / ((n : ℝ) + 1)) ^ δ) atTop (𝓝 (D ^ δ)) := by
    have hpair : Tendsto (fun n : ℕ => (D + (1 : ℝ) / ((n : ℝ) + 1), δ)) atTop
        (𝓝 (D, δ)) := by
      simpa only [nhds_prod_eq] using hRlim.prodMk
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ))
    exact (Real.continuousAt_rpow (D, δ) (Or.inl hD.ne')).tendsto.comp hpair
  have hbound (n : ℕ) : morreyNorm P κ f ≤
      ENNReal.ofReal ((D + (1 : ℝ) / ((n : ℝ) + 1)) ^ δ) * morreyNorm P τ f := by
    let R : ℝ := D + (1 : ℝ) / ((n : ℝ) + 1)
    have hε : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hR : 0 < R := by dsimp [R]; positivity
    by_cases hE : E.Nonempty
    · obtain ⟨x, t, hEcyl⟩ := parabolic_diameter_subset_cylinder hD hε hE hdiam
      have hsuppCyl : ∀ w ∉ parabolicCylinder x t R, f w = 0 := by
        intro w hw
        apply hsupp
        intro hwe
        exact hw (hEcyl hwe)
      have hraw := morreyNorm_lower_exponent_on_cylinder hP hPκ hκτ hR hsuppCyl
      calc
        morreyNorm P κ f ≤
            (ENNReal.ofReal R) ^ (5 * (1 / κ - 1 / τ)) * morreyNorm P τ f := hraw
        _ = ENNReal.ofReal (R ^ δ) * morreyNorm P τ f := by
          rw [show 5 * (1 / κ - 1 / τ) = δ by rfl,
            ENNReal.ofReal_rpow_of_nonneg (le_of_lt hR) hδ]
    · have hzero : f = fun _ => 0 := by
        funext w
        by_cases hwe : w ∈ E
        · exact (hE ⟨w, hwe⟩).elim
        · exact hsupp w hwe
      have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
      have hinvpos : 0 < P⁻¹ := inv_pos.mpr hPpos
      rw [hzero]
      simp [morreyNorm, morreyCell, cylinderPowerIntegral,
        ENNReal.zero_rpow_of_pos hPpos, ENNReal.zero_rpow_of_pos hinvpos]
  by_cases hMtop : morreyNorm P τ f = ∞
  · simp [hMtop]
  · have hM : morreyNorm P τ f ≠ ∞ := hMtop
    have hright : Tendsto
        (fun n : ℕ => ENNReal.ofReal ((D + (1 : ℝ) / ((n : ℝ) + 1)) ^ δ) *
          morreyNorm P τ f) atTop
        (𝓝 (ENNReal.ofReal (D ^ δ) * morreyNorm P τ f)) := by
      exact (ENNReal.continuous_mul_const hM).tendsto _ |>.comp
        ((ENNReal.continuous_ofReal.tendsto (D ^ δ)).comp hpowlim)
    have hlim := le_of_tendsto_of_tendsto tendsto_const_nhds hright
      (Eventually.of_forall hbound)
    calc
      morreyNorm P κ f ≤ ENNReal.ofReal (D ^ δ) * morreyNorm P τ f := hlim
      _ ≤ ENNReal.ofReal (max 1 (D ^ (5 * (1 / κ - 1 / τ)))) *
          morreyNorm P τ f := by
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        change D ^ δ ≤ max 1 (D ^ δ)
        exact le_max_right _ _

private lemma morreyENorm_mono {p q : ℝ} (hp : 0 ≤ p)
    {f g : ParabolicPoint → ℝ≥0∞} (hfg : ∀ z, f z ≤ g z) :
    morreyENorm p q f ≤ morreyENorm p q g := by
  unfold morreyENorm
  refine iSup_le fun z => iSup_le fun r => ?_
  calc
    morreyENormCell p q f z r.1 ≤ morreyENormCell p q g z r.1 := by
      unfold morreyENormCell
      apply mul_le_mul_right
      apply ENNReal.rpow_le_rpow
      · apply lintegral_mono
        intro w
        exact ENNReal.rpow_le_rpow (hfg w) hp
      · exact one_div_nonneg.mpr hp
    _ ≤ ⨆ z' : ParabolicPoint, ⨆ r' : {s : ℝ // 0 < s},
        morreyENormCell p q g z' r'.1 :=
      le_iSup_of_le z (le_iSup_of_le r le_rfl)

private lemma measurePreserving_spatial_convolution_shear :
    MeasurePreserving
      (fun yz : Vec3 × ParabolicPoint =>
        (yz.1, parabolicTranslate (-yz.1) 0 yz.2))
      ((volume : Measure Vec3).prod volume) ((volume : Measure Vec3).prod volume) := by
  let _ : SFinite (volume : Measure Vec3) := by infer_instance
  let _ : SFinite (volume : Measure ℝ) := by infer_instance
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  rw [Integration.volume_parabolicPoint_eq_prod]
  change MeasurePreserving
    (fun yz : Vec3 × (Vec3 × ℝ) => (yz.1, (-yz.1 + yz.2.1, 0 + yz.2.2)))
    ((volume : Measure Vec3).prod (volume.prod volume))
    ((volume : Measure Vec3).prod (volume.prod volume))
  let e : (Vec3 × Vec3) × ℝ ≃ᵐ Vec3 × (Vec3 × ℝ) := MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e ((volume.prod volume).prod volume)
      (volume.prod (volume.prod volume)) :=
    measurePreserving_prodAssoc volume volume volume
  have hs : MeasurePreserving (fun yz : Vec3 × Vec3 => (yz.1, -yz.1 + yz.2))
      (volume.prod volume) (volume.prod volume) :=
    measurePreserving_prod_neg_add (μ := (volume : Measure Vec3)) (ν := volume)
  have hsi : MeasurePreserving (fun p : (Vec3 × Vec3) × ℝ =>
      ((p.1.1, -p.1.1 + p.1.2), p.2))
      ((volume.prod volume).prod volume) ((volume.prod volume).prod volume) :=
    hs.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hcomp := he.comp (hsi.comp he.symm)
  convert hcomp using 1
  funext z
  rcases z with ⟨y, xt⟩
  rcases xt with ⟨x, t⟩
  simp [e, MeasurableEquiv.prodAssoc]

private lemma measurePreserving_spacetime_convolution_shear :
    MeasurePreserving
      (fun wz : ParabolicPoint × ParabolicPoint =>
        (wz.1, parabolicTranslate (-wz.1.1) (-wz.1.2) wz.2))
      ((volume : Measure ParabolicPoint).prod volume)
      ((volume : Measure ParabolicPoint).prod volume) := by
  let _ : AddCommGroup ParabolicPoint := inferInstanceAs (AddCommGroup (Vec3 × ℝ))
  let _ : MeasurableAdd₂ ParabolicPoint := inferInstanceAs (MeasurableAdd₂ (Vec3 × ℝ))
  let _ : MeasurableNeg ParabolicPoint := inferInstanceAs (MeasurableNeg (Vec3 × ℝ))
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  let _ : IsAddLeftInvariant (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    change IsAddLeftInvariant ((volume : Measure Vec3).prod (volume : Measure ℝ))
    refine ⟨fun a => ?_⟩
    rcases a with ⟨x, t⟩
    change Measure.map (fun p : Vec3 × ℝ => (x + p.1, t + p.2))
      (volume.prod volume) = volume.prod volume
    exact ((measurePreserving_add_left (volume : Measure Vec3) x).prod
      (measurePreserving_add_left (volume : Measure ℝ) t)).map_eq
  have h := measurePreserving_prod_neg_add
    (μ := (volume : Measure ParabolicPoint)) (ν := volume)
  convert h using 1
  funext z
  rcases z with ⟨w, z⟩
  change (w, (-w.1 + z.1, -w.2 + z.2)) = (w, -w + z)
  rfl

private lemma aemeasurable_spatial_convolution_integrand
    {k : Vec3 → ℝ} {g : ParabolicPoint → ℝ}
    (hk : Integrable k volume) (hg : AEMeasurable g volume) :
    AEMeasurable
      (fun yz : Vec3 × ParabolicPoint =>
        ENNReal.ofReal |k yz.1| *
          ENNReal.ofReal |g (parabolicTranslate (-yz.1) 0 yz.2)|)
      ((volume : Measure Vec3).prod volume) := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  have hk' : AEMeasurable (fun yz : Vec3 × ParabolicPoint => k yz.1)
      ((volume : Measure Vec3).prod volume) :=
    hk.aemeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
  have hg' : AEMeasurable (fun yz : Vec3 × ParabolicPoint => g yz.2)
      ((volume : Measure Vec3).prod volume) :=
    hg.comp_quasiMeasurePreserving quasiMeasurePreserving_snd
  have htrans : QuasiMeasurePreserving
      (fun yz : Vec3 × ParabolicPoint => parabolicTranslate (-yz.1) 0 yz.2)
      ((volume : Measure Vec3).prod volume) volume := by
    have h := quasiMeasurePreserving_snd.comp
      measurePreserving_spatial_convolution_shear.quasiMeasurePreserving
    convert h using 1; funext yz; rfl
  have hgtrans : AEMeasurable
      (fun yz : Vec3 × ParabolicPoint => g (parabolicTranslate (-yz.1) 0 yz.2))
      ((volume : Measure Vec3).prod volume) :=
    hg.comp_quasiMeasurePreserving htrans
  have hK : AEMeasurable (fun y : Vec3 => ENNReal.ofReal |k y|) volume := by
    exact (ENNReal.continuous_ofReal.comp continuous_abs).measurable.comp_aemeasurable
      hk.aemeasurable
  have hG : AEMeasurable
      (fun yz : Vec3 × ParabolicPoint =>
        ENNReal.ofReal |g (parabolicTranslate (-yz.1) 0 yz.2)|)
      ((volume : Measure Vec3).prod volume) := by
    exact (ENNReal.continuous_ofReal.comp continuous_abs).measurable.comp_aemeasurable hgtrans
  have hK' : AEMeasurable
      (fun yz : Vec3 × ParabolicPoint => ENNReal.ofReal |k yz.1|)
      ((volume : Measure Vec3).prod volume) :=
    hK.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
  change AEMeasurable
    ((fun yz : Vec3 × ParabolicPoint => ENNReal.ofReal |k yz.1|) *
      (fun yz : Vec3 × ParabolicPoint =>
        ENNReal.ofReal |g (parabolicTranslate (-yz.1) 0 yz.2)|)) _
  exact hK'.mul hG

private lemma aemeasurable_spacetime_convolution_integrand
    {k g : ParabolicPoint → ℝ}
    (hk : Integrable k volume) (hg : AEMeasurable g volume) :
    AEMeasurable
      (fun wz : ParabolicPoint × ParabolicPoint =>
        ENNReal.ofReal |k wz.1| *
          ENNReal.ofReal |g (parabolicTranslate (-wz.1.1) (-wz.1.2) wz.2)|)
      ((volume : Measure ParabolicPoint).prod volume) := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  have hk' : AEMeasurable (fun wz : ParabolicPoint × ParabolicPoint => k wz.1)
      (volume.prod volume) :=
    hk.aemeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
  have hg' : AEMeasurable (fun wz : ParabolicPoint × ParabolicPoint => g wz.2)
      (volume.prod volume) :=
    hg.comp_quasiMeasurePreserving quasiMeasurePreserving_snd
  have htrans : QuasiMeasurePreserving
      (fun wz : ParabolicPoint × ParabolicPoint =>
        parabolicTranslate (-wz.1.1) (-wz.1.2) wz.2)
      (volume.prod volume) volume := by
    have h := quasiMeasurePreserving_snd.comp
      measurePreserving_spacetime_convolution_shear.quasiMeasurePreserving
    convert h using 1; funext wz; rfl
  have hgtrans : AEMeasurable
      (fun wz : ParabolicPoint × ParabolicPoint =>
        g (parabolicTranslate (-wz.1.1) (-wz.1.2) wz.2)) (volume.prod volume) :=
    hg.comp_quasiMeasurePreserving htrans
  have hK : AEMeasurable
      (fun wz : ParabolicPoint × ParabolicPoint => ENNReal.ofReal |k wz.1|)
      (volume.prod volume) := by
    exact (ENNReal.continuous_ofReal.comp continuous_abs).measurable.comp_aemeasurable hk'
  have hG : AEMeasurable
      (fun wz : ParabolicPoint × ParabolicPoint =>
        ENNReal.ofReal |g (parabolicTranslate (-wz.1.1) (-wz.1.2) wz.2)|)
      (volume.prod volume) := by
    exact (ENNReal.continuous_ofReal.comp continuous_abs).measurable.comp_aemeasurable hgtrans
  change AEMeasurable
    ((fun wz : ParabolicPoint × ParabolicPoint => ENNReal.ofReal |k wz.1|) *
      (fun wz : ParabolicPoint × ParabolicPoint =>
        ENNReal.ofReal |g (parabolicTranslate (-wz.1.1) (-wz.1.2) wz.2)|)) _
  exact hK.mul hG

/-- The real-kernel Minkowski inequality for spatial convolution. -/
theorem morreyNorm_real_spatial_convolution_le
    {P τ : ℝ} (hP : 1 ≤ P) (hPτ : P ≤ τ)
    {k : Vec3 → ℝ} {g : ParabolicPoint → ℝ}
    (hk : Integrable k volume) (hg : AEMeasurable g volume)
    (hM : morreyNorm P τ g ≠ ∞) :
    morreyNorm P τ
      (fun z => ∫ y, k y * g (z.1 - y, z.2)) ≤
      ENNReal.ofReal (∫ y, |k y|) * morreyNorm P τ g := by
  let K : Vec3 → ℝ≥0∞ := fun y => ENNReal.ofReal |k y|
  let G : ParabolicPoint → ℝ≥0∞ := fun z => ENNReal.ofReal |g z|
  have hKG := aemeasurable_spatial_convolution_integrand hk hg
  have hKtop : ∀ y, K y ≠ ∞ := by intro y; simp [K]
  have hGfinite : morreyENorm P τ G ≠ ∞ := by
    simpa [G, morreyENorm_ofReal_abs] using hM
  have hpoint : ∀ z, ENNReal.ofReal
      |∫ y, k y * g (z.1 - y, z.2)| ≤ spatialConvolution K G z := by
    intro z
    have h := enorm_integral_le_lintegral_enorm
      (μ := (volume : Measure Vec3)) (fun y : Vec3 => k y * g (z.1 - y, z.2))
    simpa [K, G, spatialConvolution, parabolicTranslate, Real.enorm_eq_ofReal_abs,
      abs_mul, ENNReal.ofReal_mul, sub_eq_add_neg, add_comm] using h
  have hmono := morreyENorm_mono (p := P) (q := τ)
    (le_trans (by norm_num : 0 ≤ (1 : ℝ)) hP) hpoint
  have hconv := morreyENorm_spatialConvolution_le hP hPτ hKG hKtop hGfinite
  have hmass : (∫⁻ y, K y ∂volume) = ENNReal.ofReal (∫ y, |k y| ∂volume) := by
    have hkabs : Integrable (fun y : Vec3 => |k y|) volume := by
      simpa only [Real.norm_eq_abs] using hk.norm
    simp only [K]
    exact (ofReal_integral_eq_lintegral_ofReal hkabs
      (Eventually.of_forall fun y => abs_nonneg (k y))).symm
  calc
    morreyNorm P τ (fun z => ∫ y, k y * g (z.1 - y, z.2)) =
        morreyENorm P τ
          (fun z => ENNReal.ofReal |∫ y, k y * g (z.1 - y, z.2)|) := by
      symm
      exact morreyENorm_ofReal_abs P τ _
    _ ≤ morreyENorm P τ (spatialConvolution K G) := hmono
    _ ≤ (∫⁻ y, K y ∂volume) * morreyENorm P τ G := hconv
    _ = ENNReal.ofReal (∫ y, |k y| ∂volume) * morreyNorm P τ g := by
      rw [hmass, morreyENorm_ofReal_abs]

/-- The real-kernel Minkowski inequality for convolution in all parabolic variables. -/
theorem morreyNorm_real_parabolic_convolution_le
    {P τ : ℝ} (hP : 1 ≤ P) (hPτ : P ≤ τ)
    {k g : ParabolicPoint → ℝ}
    (hk : Integrable k volume) (hg : AEMeasurable g volume)
    (hM : morreyNorm P τ g ≠ ∞) :
    morreyNorm P τ
      (fun z => ∫ w, k w * g (parabolicTranslate (-w.1) (-w.2) z)) ≤
      ENNReal.ofReal (∫ w, |k w|) * morreyNorm P τ g := by
  let K : ParabolicPoint → ℝ≥0∞ := fun w => ENNReal.ofReal |k w|
  let G : ParabolicPoint → ℝ≥0∞ := fun z => ENNReal.ofReal |g z|
  have hKG := aemeasurable_spacetime_convolution_integrand hk hg
  have hKtop : ∀ w, K w ≠ ∞ := by intro w; simp [K]
  have hGfinite : morreyENorm P τ G ≠ ∞ := by
    simpa [G, morreyENorm_ofReal_abs] using hM
  have hpoint : ∀ z, ENNReal.ofReal
      |∫ w, k w * g (parabolicTranslate (-w.1) (-w.2) z)| ≤
        parabolicConvolution K G z := by
    intro z
    have h := enorm_integral_le_lintegral_enorm
      (μ := (volume : Measure ParabolicPoint))
      (fun w : ParabolicPoint => k w * g (parabolicTranslate (-w.1) (-w.2) z))
    simpa [K, G, parabolicConvolution, parabolicTranslate, Real.enorm_eq_ofReal_abs,
      abs_mul, ENNReal.ofReal_mul] using h
  have hmono := morreyENorm_mono (p := P) (q := τ)
    (le_trans (by norm_num : 0 ≤ (1 : ℝ)) hP) hpoint
  have hconv := morreyENorm_parabolicConvolution_le hP hPτ hKG hKtop hGfinite
  have hmass : (∫⁻ w, K w ∂volume) = ENNReal.ofReal (∫ w, |k w| ∂volume) := by
    have hkabs : Integrable (fun w : ParabolicPoint => |k w|) volume := by
      simpa only [Real.norm_eq_abs] using hk.norm
    simp only [K]
    exact (ofReal_integral_eq_lintegral_ofReal hkabs
      (Eventually.of_forall fun w => abs_nonneg (k w))).symm
  calc
    morreyNorm P τ
        (fun z => ∫ w, k w * g (parabolicTranslate (-w.1) (-w.2) z)) =
        morreyENorm P τ
          (fun z => ENNReal.ofReal
            |∫ w, k w * g (parabolicTranslate (-w.1) (-w.2) z)|) := by
      symm
      exact morreyENorm_ofReal_abs P τ _
    _ ≤ morreyENorm P τ (parabolicConvolution K G) := hmono
    _ ≤ (∫⁻ w, K w ∂volume) * morreyENorm P τ G := hconv
    _ = ENNReal.ofReal (∫ w, |k w| ∂volume) * morreyNorm P τ g := by
      rw [hmass, morreyENorm_ofReal_abs]

/-- The bounded-diameter support estimate and the spatial real-kernel
Minkowski estimate in their common range of exponents. -/
theorem morrey_lower_exponent_and_real_minkowski
    {P κ τ D : ℝ} (hP : 1 ≤ P) (hPκ : P ≤ κ) (hκτ : κ ≤ τ) (hD : 0 < D) :
    (∀ {f : ParabolicPoint → ℝ} {E : Set ParabolicPoint},
      (∀ w ∈ E, ∀ w' ∈ E, parabolicDist w w' ≤ D) →
      (∀ w ∉ E, f w = 0) →
      morreyNorm P κ f ≤
        ENNReal.ofReal (max 1 (D ^ (5 * (1 / κ - 1 / τ)))) * morreyNorm P τ f) ∧
    (∀ {k : Vec3 → ℝ} {g : ParabolicPoint → ℝ},
      Integrable k volume → AEMeasurable g volume → morreyNorm P τ g ≠ ∞ →
      morreyNorm P τ (fun z => ∫ y, k y * g (z.1 - y, z.2)) ≤
        ENNReal.ofReal (∫ y, |k y|) * morreyNorm P τ g) := by
  constructor
  · intro f E hdiam hsupp
    exact morreyNorm_lower_morrey_exponent_of_diameter hP hPκ hκτ hD hdiam hsupp
  · intro k g hk hg hM
    exact morreyNorm_real_spatial_convolution_le hP (hPκ.trans hκτ) hk hg hM

end CKN.Foundation.Parabolic.Morrey
