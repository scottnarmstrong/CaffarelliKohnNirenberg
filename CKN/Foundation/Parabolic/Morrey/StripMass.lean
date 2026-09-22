-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Tail
import CKN.Foundation.Parabolic.Integration.Average
import CKN.Foundation.Parabolic.Vec3Norm

/-!
# Mass of a parabolic Morrey source on a thin time strip

A parabolic Morrey source of exponents `(p, q)` has controlled mass on every
backward cylinder: on a cylinder of radius `d` the mass is `O(d^{5 - 5/q})`.
The cylinder is isotropic in the parabolic sense, its time width being the
square of its spatial radius.  This module records the *anisotropic* estimate
that a shrinking time strip needs: on

```
parabolicStrip x a R d = vec3Ball x R ×ˢ Ioc (a - d ^ 2) a,
```

a spatial ball of radius `R` crossed with a time interval of the much smaller
width `d ^ 2`, the mass is `O(R ^ 3 * d ^ (2 - 5/q))`.

The estimate is obtained by covering the strip with backward cylinders of
radius `d`.  Because such a cylinder already has the strip's exact time face
`Ioc (a - d ^ 2) a`, the covering is purely spatial: the spatial ball of
radius `R` is cut into `⌈2R/d⌉₊ ^ 3` grid cubes of side at most `d`, and each
cube sits inside a ball of radius `d` since its half-diagonal is `√3/2` times
its side.  Summing the cylinder estimate over the `O((R/d) ^ 3)` cubes turns
`d ^ (5 - 5/q)` into `R ^ 3 * d ^ (2 - 5/q)`, which is the shrinking factor
`(d/R) ^ (2 - 5/q)` times the isotropic mass `R ^ (5 - 5/q)` of the full
cylinder of radius `R`.

No hypothesis beyond measurability of the source and the finiteness of its
Morrey seminorm enters the statements.
-/

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The thin space-time strip of spatial radius `R` and time width `d ^ 2`
ending at time `a`.  For `d = R` it is the backward parabolic cylinder. -/
def parabolicStrip (x : Vec3) (a R d : ℝ) : Set ParabolicPoint :=
  vec3Ball x R ×ˢ Ioc (a - d ^ 2) a

/-- A strip whose time width matches its spatial radius is a parabolic cylinder. -/
theorem parabolicStrip_self (x : Vec3) (a r : ℝ) :
    parabolicStrip x a r r = parabolicCylinder x a r := rfl

/-- A spatial ball of radius `R` is covered by at most `27 (R/d) ^ 3` balls of
radius `d`, for every `0 < d ≤ R`.  The centres are the centres of a cubic
grid of side `2R/⌈2R/d⌉₊`. -/
private lemma exists_vec3Ball_cover (x : Vec3) {R d : ℝ} (hd : 0 < d) (hdR : d ≤ R) :
    ∃ (N : ℕ) (c : Fin N → Vec3),
      (N : ℝ) * d ^ 3 ≤ 27 * R ^ 3 ∧ vec3Ball x R ⊆ ⋃ i, vec3Ball (c i) d := by
  have hR : 0 < R := hd.trans_le hdR
  set M : ℕ := ⌈2 * R / d⌉₊ with hMdef
  have hMpos : 0 < M := Nat.ceil_pos.mpr (by positivity)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hMd : (M : ℝ) * d ≤ 3 * R := by
    have hceil : (M : ℝ) < 2 * R / d + 1 := by
      rw [hMdef]
      exact Nat.ceil_lt_add_one (by positivity)
    have hmul : (M : ℝ) * d ≤ (2 * R / d + 1) * d :=
      mul_le_mul_of_nonneg_right hceil.le hd.le
    have hexp : (2 * R / d + 1) * d = 2 * R + d := by field_simp
    rw [hexp] at hmul
    linarith only [hmul, hdR]
  set s : ℝ := 2 * R / (M : ℝ) with hsdef
  have hs : 0 < s := by
    rw [hsdef]
    positivity
  have hMs : (M : ℝ) * s = 2 * R := by
    rw [hsdef]
    field_simp
  have hsd : s ≤ d := by
    have hle : 2 * R / d ≤ (M : ℝ) := by
      rw [hMdef]
      exact Nat.le_ceil _
    have h2R : 2 * R ≤ (M : ℝ) * d := by
      rw [div_le_iff₀ hd] at hle
      linarith only [hle]
    rw [hsdef, div_le_iff₀ hMR]
    linarith only [h2R]
  -- the grid centres, indexed by triples of cell indices
  set c₀ : (Fin 3 → Fin M) → Vec3 :=
    fun k i => x i - R + (((k i : ℕ) : ℝ) + 1 / 2) * s with hc₀
  refine ⟨M ^ 3, fun n => c₀ (finFunctionFinEquiv.symm n), ?_, ?_⟩
  · have hcast : ((M ^ 3 : ℕ) : ℝ) = (M : ℝ) ^ 3 := by push_cast; ring
    have hcube : ((M : ℝ) * d) ^ 3 ≤ (3 * R) ^ 3 := by
      have hnn : (0 : ℝ) ≤ (M : ℝ) * d := by positivity
      exact pow_le_pow_left₀ hnn hMd 3
    rw [hcast]
    calc (M : ℝ) ^ 3 * d ^ 3 = ((M : ℝ) * d) ^ 3 := by ring
      _ ≤ (3 * R) ^ 3 := hcube
      _ = 27 * R ^ 3 := by ring
  · intro y hy
    have hyx : vec3EuclideanNorm (y - x) < R := hy
    have habs : ∀ i : Fin 3, |y i - x i| < R := by
      intro i
      have h := abs_apply_le_vec3EuclideanNorm (y - x) i
      have hcoord : (y - x) i = y i - x i := rfl
      rw [hcoord] at h
      exact h.trans_lt hyx
    have hlt : ∀ i : Fin 3, ⌊(y i - x i + R) / s⌋₊ < M := by
      intro i
      have hnn : (0 : ℝ) ≤ (y i - x i + R) / s := by
        have := (abs_lt.mp (habs i)).1
        have hnum : 0 ≤ y i - x i + R := by linarith only [this]
        positivity
      rw [Nat.floor_lt hnn, div_lt_iff₀ hs, mul_comm ((M : ℕ) : ℝ) s,
        mul_comm s ((M : ℕ) : ℝ)] at *
      have hup := (abs_lt.mp (habs i)).2
      rw [hMs]
      linarith only [hup]
    set k : Fin 3 → Fin M := fun i => ⟨⌊(y i - x i + R) / s⌋₊, hlt i⟩ with hk
    refine mem_iUnion.2 ⟨finFunctionFinEquiv k, ?_⟩
    simp only [Equiv.symm_apply_apply]
    show vec3EuclideanNorm (y - c₀ k) < d
    have hcoord : ∀ i : Fin 3, |(y - c₀ k) i| ≤ s / 2 := by
      intro i
      have hnn : (0 : ℝ) ≤ (y i - x i + R) / s := by
        have hlow := (abs_lt.mp (habs i)).1
        have hnum : 0 ≤ y i - x i + R := by linarith only [hlow]
        positivity
      have hfl : ((⌊(y i - x i + R) / s⌋₊ : ℕ) : ℝ) * s ≤ y i - x i + R := by
        have h := Nat.floor_le hnn
        rwa [le_div_iff₀ hs] at h
      have hfu : y i - x i + R <
          (((⌊(y i - x i + R) / s⌋₊ : ℕ) : ℝ) + 1) * s := by
        have h := Nat.lt_floor_add_one ((y i - x i + R) / s)
        rwa [div_lt_iff₀ hs] at h
      have hval : (y - c₀ k) i =
          (y i - x i + R) -
            (((⌊(y i - x i + R) / s⌋₊ : ℕ) : ℝ) + 1 / 2) * s := by
        show y i - c₀ k i = _
        simp only [hc₀, hk]
        ring
      rw [hval, abs_le]
      constructor <;> linarith only [hfl, hfu]
    have hsup : ‖y - c₀ k‖ ≤ s / 2 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact hcoord i
    have hsqrt3 : Real.sqrt 3 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    calc vec3EuclideanNorm (y - c₀ k) ≤ Real.sqrt 3 * ‖y - c₀ k‖ :=
          vec3EuclideanNorm_le_sqrt_three_mul_norm _
      _ ≤ Real.sqrt 3 * (s / 2) :=
          mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 3)
      _ < 2 * (s / 2) :=
          mul_lt_mul_of_pos_right hsqrt3 (by positivity)
      _ = s := by ring
      _ ≤ d := hsd

/-- **Strip mass estimate.**  The absolute mass of a parabolic Morrey source on
the thin strip `parabolicStrip x a R d` is at most `27 R ^ 3 d ^ (2 - 5/q)`
times the Morrey seminorm, up to the fixed unit-cylinder volume factor coming
from the passage between the exponents `1` and `p`. -/
theorem stripAbsLintegral_le_morreyNorm {P θ : ℝ} (hP : 1 ≤ P) (hPθ : P ≤ θ)
    {G : ParabolicPoint → ℝ} (hG : AEMeasurable G volume)
    (x : Vec3) (a : ℝ) {R d : ℝ} (hd : 0 < d) (hdR : d ≤ R) :
    (∫⁻ v in parabolicStrip x a R d, ENNReal.ofReal |G v|) ≤
      ENNReal.ofReal (27 * R ^ 3 * d ^ (2 - 5 / θ)) *
        volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P) * morreyNorm P θ G := by
  have hR : 0 < R := hd.trans_le hdR
  have hθ : 1 ≤ θ := hP.trans hPθ
  obtain ⟨N, c, hcard, hcov⟩ := exists_vec3Ball_cover x hd hdR
  set V : ℝ≥0∞ := volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P) with hV
  set B : ℝ≥0∞ :=
    ENNReal.ofReal (d ^ (5 * (1 - 1 / θ))) * V * morreyNorm P θ G with hB
  have hlow : morreyNorm 1 θ G ≤ V * morreyNorm P θ G := by
    have h := morreyNorm_lower_p (p' := 1) (p := P) (q := θ) le_rfl hP hPθ hG
    rw [hV]
    simpa using h
  have hstep : ∀ i : Fin N,
      (∫⁻ v in parabolicCylinder (c i) a d, ENNReal.ofReal |G v|) ≤ B := by
    intro i
    have hcyl := cylinderAbsIntegral_le_morreyNorm (q := θ) hθ hG ((c i, a)) hd
    have hcyl' : (∫⁻ v in parabolicCylinder (c i) a d, ENNReal.ofReal |G v|) ≤
        ENNReal.ofReal d ^ (5 * (1 - 1 / θ)) * morreyNorm 1 θ G := hcyl
    rw [hB, ← ENNReal.ofReal_rpow_of_pos hd, mul_assoc]
    exact hcyl'.trans (mul_le_mul_right hlow _)
  have hsub : parabolicStrip x a R d ⊆ ⋃ i, parabolicCylinder (c i) a d := by
    have h1 : parabolicStrip x a R d ⊆
        (⋃ i, vec3Ball (c i) d) ×ˢ Ioc (a - d ^ 2) a := Set.prod_mono_left hcov
    have h2 : (⋃ i, vec3Ball (c i) d) ×ˢ Ioc (a - d ^ 2) a =
        ⋃ i, parabolicCylinder (c i) a d := Set.iUnion_prod_const
    rw [← h2]
    exact h1
  have hreal : (N : ℝ) * d ^ (5 * (1 - 1 / θ)) ≤ 27 * R ^ 3 * d ^ (2 - 5 / θ) := by
    have hsplit : d ^ (5 * (1 - 1 / θ)) = d ^ (3 : ℕ) * d ^ (2 - 5 / θ) := by
      rw [show (5 : ℝ) * (1 - 1 / θ) = (3 : ℕ) + (2 - 5 / θ) by push_cast; ring,
        Real.rpow_add hd, Real.rpow_natCast]
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hd.le _)
  calc (∫⁻ v in parabolicStrip x a R d, ENNReal.ofReal |G v|)
      ≤ ∫⁻ v in ⋃ i, parabolicCylinder (c i) a d, ENNReal.ofReal |G v| :=
        lintegral_mono_set hsub
    _ ≤ ∑' i : Fin N, ∫⁻ v in parabolicCylinder (c i) a d, ENNReal.ofReal |G v| :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' _i : Fin N, B := ENNReal.tsum_le_tsum hstep
    _ = (N : ℝ≥0∞) * B := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (27 * R ^ 3 * d ^ (2 - 5 / θ)) * V * morreyNorm P θ G := by
        rw [hB, ← mul_assoc, ← mul_assoc]
        refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
        rw [show ((N : ℝ≥0∞)) = ENNReal.ofReal (N : ℝ) by
            simp [ENNReal.ofReal_natCast],
          ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
        exact ENNReal.ofReal_le_ofReal hreal

/-- The strip mass is finite for a source with finite Morrey seminorm. -/
theorem stripAbsLintegral_lt_top {P θ : ℝ} (hP : 1 ≤ P) (hPθ : P ≤ θ)
    {G : ParabolicPoint → ℝ} (hG : AEMeasurable G volume)
    (hGM : morreyNorm P θ G < ∞) (x : Vec3) (a : ℝ) {R d : ℝ}
    (hd : 0 < d) (hdR : d ≤ R) :
    (∫⁻ v in parabolicStrip x a R d, ENNReal.ofReal |G v|) < ∞ := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hexp : (0 : ℝ) ≤ 1 - 1 / P := by
    have : 1 / P ≤ 1 := by
      rw [div_le_one hP0]
      exact hP
    linarith only [this]
  have hV : volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hexp
      (Integration.volume_parabolicCylinder_lt_top (x := (0 : Vec3)) (t := 0)
        (r := 1)).ne
  refine lt_of_le_of_lt
    (stripAbsLintegral_le_morreyNorm hP hPθ hG x a hd hdR) ?_
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV.lt_top) hGM

/-- **Strip mass estimate, real form.**  One constant, fixed before the source
and before the strip, controls the absolute integral of a parabolic Morrey
source on every thin strip. -/
theorem exists_stripAbsIntegral_bound {P θ : ℝ} (hP : 1 ≤ P) (hPθ : P ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {G : ParabolicPoint → ℝ}, AEMeasurable G volume → morreyNorm P θ G < ∞ →
        ∀ (x : Vec3) (a R d : ℝ), 0 < d → d ≤ R →
          IntegrableOn G (parabolicStrip x a R d) volume ∧
          (∫ v in parabolicStrip x a R d, |G v|) ≤
            C * R ^ 3 * d ^ (2 - 5 / θ) * (morreyNorm P θ G).toReal := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hexp : (0 : ℝ) ≤ 1 - 1 / P := by
    have : 1 / P ≤ 1 := by
      rw [div_le_one hP0]
      exact hP
    linarith only [this]
  set V : ℝ≥0∞ := volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P) with hVdef
  have hVtop : V ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hexp
      (Integration.volume_parabolicCylinder_lt_top (x := (0 : Vec3)) (t := 0)
        (r := 1)).ne
  refine ⟨27 * V.toReal, by positivity, ?_⟩
  intro G hG hGM x a R d hd hdR
  have hR : 0 < R := hd.trans_le hdR
  have hbound := stripAbsLintegral_le_morreyNorm hP hPθ hG x a hd hdR
  have hfin := stripAbsLintegral_lt_top hP hPθ hG hGM x a hd hdR
  have hmeas : AEStronglyMeasurable G (volume.restrict (parabolicStrip x a R d)) :=
    hG.aestronglyMeasurable.restrict
  have henorm : ∀ v : ParabolicPoint, ‖G v‖ₑ = ENNReal.ofReal |G v| := by
    intro v
    rw [← ofReal_norm, Real.norm_eq_abs]
  have hlint : (∫⁻ v in parabolicStrip x a R d, ‖G v‖ₑ) =
      ∫⁻ v in parabolicStrip x a R d, ENNReal.ofReal |G v| := by
    exact lintegral_congr fun v => henorm v
  have hint : IntegrableOn G (parabolicStrip x a R d) volume := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hlint]
    exact hfin
  refine ⟨hint, ?_⟩
  have habs : (∫ v in parabolicStrip x a R d, |G v|) =
      (∫⁻ v in parabolicStrip x a R d, ENNReal.ofReal |G v|).toReal := by
    have := integral_norm_eq_lintegral_enorm (μ := volume.restrict
      (parabolicStrip x a R d)) hmeas
    simp only [Real.norm_eq_abs] at this
    rw [this, hlint]
  rw [habs]
  have hnn : (0 : ℝ) ≤ 27 * R ^ 3 * d ^ (2 - 5 / θ) := by positivity
  have htoReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop) hGM.ne)
    hbound
  refine htoReal.trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn]
  ring

end CKN.Foundation.Parabolic.Morrey
