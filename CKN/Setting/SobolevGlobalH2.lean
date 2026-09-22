-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Setting.SobolevGlobalH2Core
import CKN.Setting.SobolevGlobalL6
import CKN.Foundation.Sobolev.Mollify.LpApproximation
import CKN.Foundation.Sobolev.Mollify.Transport
import CKN.Foundation.Euclidean.LpDensity

open MeasureTheory Set Filter
open scoped ENNReal Convolution Topology
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

private lemma h2_memLp_value (v : H1Function (Set.univ : Set Vec3)) :
    MemLp v.toFun 2 volume := by
  simpa [MemL2On, MemLpOn, volumeOn] using v.memL2

private lemma h2_memLp_gradient (v : H1Function (Set.univ : Set Vec3)) :
    MemLp v.grad 2 volume := by
  apply (memLp_pi_iff).2
  intro i
  simpa [MemL2On, MemLpOn, volumeOn] using v.grad_memL2 i

private lemma h2_memLp_euclidean_gradient
    (v : H1Function (Set.univ : Set Vec3)) :
    MemLp (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
  apply MemLp.of_le_mul (c := (3 : ℝ)) (h2_memLp_gradient v)
  · exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      (h2_memLp_gradient v).aestronglyMeasurable
  · filter_upwards [] with x
    have h := euclideanNorm_le_three_mul_space_norm (v.grad x)
    simpa [spaceEuclideanNorm, vec3EuclideanNorm, Real.norm_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)] using h

private lemma h2_mollify_memLp {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {g : Vec3 → ℝ} (hg : MemLp g p volume) {ε : ℝ} (hε : 0 < ε) :
    MemLp (mollify g ε hε) p volume := by
  rw [memLp_iff]
  have hconv := young_convolution_nonneg_integral_one_of_aemeasurable
    (p := p) hp hpTop
    (mollifier_nonneg hε)
    ((mollifier_contDiff hε (n := 0)).continuous.integrable_of_hasCompactSupport
      (mollifier_hasCompactSupport hε))
    (mollifier_integral_one hε)
    (mollifier_contDiff hε (n := 0)).continuous.measurable
    hg.aestronglyMeasurable.aemeasurable
  simpa only [mollify] using hconv.trans_lt hg

private lemma h2_mollify_component_derivative
    {v : H1Function (Set.univ : Set Vec3)}
    {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    (fun x => (fderiv ℝ (mollify v.toFun ε hε) x) (basisVec i)) =
      mollify (fun x => v.grad x i) ε hε := by
  funext x
  have hvi : MemLp (fun x => v.grad x i) 2 volume :=
    (memLp_pi_iff.mp (h2_memLp_gradient v)) i
  exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ
    ((h2_memLp_value v).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (hvi.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (v.hasWeakPartialDerivOn i) hε (by simp)

private lemma h2_mollify_gradient_component_memLp
    {v : H1Function (Set.univ : Set Vec3)}
    {ε : ℝ} (hε : 0 < ε) (i : Fin 3)
    (hgi : MemLp (fun x => v.grad x i) (ENNReal.ofReal (6 : ℝ)) volume) :
    MemLp (fun x => (fderiv ℝ (mollify v.toFun ε hε) x) (basisVec i))
      (ENNReal.ofReal (6 : ℝ)) volume := by
  rw [h2_mollify_component_derivative hε i]
  exact h2_mollify_memLp (by norm_num) (by norm_num) hgi hε

private lemma h2_component_l6_of_sobolev
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hSob : ∀ g : H1Function (Set.univ : Set Vec3),
      lpNormOn 6 Set.univ g.toFun ≤ C * weakGradientLpNormOn 2 Set.univ g.grad)
    (g : H1Function (Set.univ : Set Vec3)) :
    MemLp g.toFun 6 volume := by
  rw [memLp_iff]
  have hgrad := h2_memLp_gradient g
  have hbound : eLpNorm g.toFun 6 volume ≤ C * eLpNorm g.grad 2 volume := by
    simpa [lpNormOn, weakGradientLpNormOn, Measure.restrict_univ] using hSob g
  exact hbound.trans_lt (ENNReal.mul_lt_top hC.lt_top hgrad.eLpNorm_lt_top)

private lemma h2_constant_top_norm {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun _ : Vec3 => c) ⊤ volume = ENNReal.ofReal c := by
  have hvol : (volume : Measure Vec3) ≠ 0 := by
    intro hzero
    have hpos : 0 < volume (Metric.ball (0 : Vec3) 1) :=
      Metric.isOpen_ball.measure_pos volume ⟨0, by simp⟩
    rw [hzero] at hpos
    simp at hpos
  rw [eLpNorm_const c (by simp) hvol]
  simp [hc, Real.enorm_eq_ofReal]

private lemma h2_real_component_bound
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    {v : H1Function (Set.univ : Set Vec3)}
    {G : Fin 3 → H1Function (Set.univ : Set Vec3)}
    (hG : ∀ i, (G i).toFun =ᵐ[volume] fun x => v.grad x i)
    (hSob : ∀ g : H1Function (Set.univ : Set Vec3),
      lpNormOn 6 Set.univ g.toFun ≤ C * weakGradientLpNormOn 2 Set.univ g.grad)
    (i : Fin 3) :
    lpNorm (fun x => v.grad x i) 6 volume ≤ C.toReal *
      lpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume := by
  have hGi6 := h2_component_l6_of_sobolev hC hSob (G i)
  have hvi6 : MemLp (fun x => v.grad x i) 6 volume := by
    exact MemLp.ae_eq (hG i) hGi6
  have hbound : eLpNorm (fun x => v.grad x i) 6 volume ≤
      C * eLpNorm (G i).grad 2 volume := by
    have hs := hSob (G i)
    have hgi := h2_memLp_gradient (G i)
    have hs' : eLpNorm (G i).toFun 6 volume ≤ C * eLpNorm (G i).grad 2 volume := by
      simpa [lpNormOn, weakGradientLpNormOn, Measure.restrict_univ] using hs
    exact (eLpNorm_congr_ae (hG i).symm).trans_le hs'
  have hGnorm : eLpNorm (G i).grad 2 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume := by
    have hmeas := h2_memLp_gradient (G i)
    apply eLpNorm_mono_ae hmeas.aestronglyMeasurable
    filter_upwards [] with x
    have h := space_norm_le_euclideanNorm ((G i).grad x)
    simpa [spaceEuclideanNorm, vec3EuclideanNorm, Real.norm_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)] using h
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hC (h2_memLp_euclidean_gradient (G i)).eLpNorm_ne_top)
    (hbound.trans (mul_le_mul_of_nonneg_left hGnorm (by positivity)))
  simpa [lpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
    using hreal

/-- The global weak `H²` embedding, expressed using the first-derivative
representatives supplied by the weak `H¹` interfaces. -/
theorem global_sobolev_embeddings :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ v : H1Function (Set.univ : Set Vec3),
      eLpNorm v.toFun 6 volume ≤ ENNReal.ofReal C *
        eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ v : H1Function (Set.univ : Set Vec3),
      ∀ G : Fin 3 → H1Function (Set.univ : Set Vec3),
      (∀ i, (G i).toFun =ᵐ[volume] fun x => v.grad x i) →
      eLpNorm v.toFun ⊤ volume ≤ ENNReal.ofReal C *
        (eLpNorm v.toFun 2 volume +
          eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume +
          ∑ i : Fin 3, eLpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume)) := by
  obtain ⟨C₆, hC₆, hSob⟩ := sobolev_L6_global
  have hfirst : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : H1Function (Set.univ : Set Vec3),
      eLpNorm v.toFun 6 volume ≤ ENNReal.ofReal C *
        eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
    refine ⟨C₆.toReal, ENNReal.toReal_nonneg, ?_⟩
    intro v
    have hv := hSob v
    have hnorm := eLpNorm_norm (p := (2 : ℝ≥0∞)) v.grad
      (h2_memLp_gradient v).aestronglyMeasurable
    have hgradNorm : eLpNorm v.grad 2 volume ≤
        eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
      apply eLpNorm_mono_ae (h2_memLp_gradient v).aestronglyMeasurable
      filter_upwards [] with x
      have h := space_norm_le_euclideanNorm (v.grad x)
      simpa [spaceEuclideanNorm, vec3EuclideanNorm, Real.norm_eq_abs,
        abs_of_nonneg (vec3EuclideanNorm_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _)] using h
    have hCeq : ENNReal.ofReal C₆.toReal = C₆ := ENNReal.ofReal_toReal hC₆
    have hv0 : eLpNorm v.toFun 6 volume ≤ C₆ * eLpNorm v.grad 2 volume := by
      simpa [lpNormOn, weakGradientLpNormOn, Measure.restrict_univ] using hv
    have hv' := hv0.trans (mul_le_mul_of_nonneg_left hgradNorm (by positivity))
    simpa [lpNormOn, weakGradientLpNormOn, Measure.restrict_univ, hCeq,
      hnorm] using hv'
  refine ⟨hfirst, ?_⟩
  obtain ⟨Cstar, hCstar, hcore⟩ := smooth_global_linf_uniform
  refine ⟨Cstar * (1 + C₆.toReal), ?_, ?_⟩
  · have hC₆r : 0 ≤ C₆.toReal := ENNReal.toReal_nonneg
    nlinarith only [hCstar, hC₆r]
  intro v G hG
  let S : ℝ≥0∞ := eLpNorm v.toFun 2 volume +
    eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume +
    ∑ i : Fin 3, eLpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume
  let R : ℝ := S.toReal
  have hv2 := h2_memLp_value v
  have hgrad2 := h2_memLp_gradient v
  have hgradNorm2 := h2_memLp_euclidean_gradient v
  have hGiNorm2 (i : Fin 3) :
      MemLp (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume :=
    h2_memLp_euclidean_gradient (G i)
  have hGgrad2 (i : Fin 3) : MemLp (G i).grad 2 volume :=
    h2_memLp_gradient (G i)
  have hVcomp6 (i : Fin 3) : MemLp (fun x => v.grad x i) 6 volume := by
    have hGi6 := h2_component_l6_of_sobolev hC₆ hSob (G i)
    exact MemLp.ae_eq (hG i) hGi6
  have hS_top : S ≠ ∞ := by
    have hsumTop : (∑ i : Fin 3,
        eLpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume) < ∞ :=
      ENNReal.sum_lt_top.2 (fun i _ => (hGiNorm2 i).eLpNorm_lt_top)
    exact ENNReal.add_ne_top.mpr ⟨
      ENNReal.add_ne_top.mpr ⟨hv2.eLpNorm_ne_top, hgradNorm2.eLpNorm_ne_top⟩,
      hsumTop.ne⟩
  have hR_nonneg : 0 ≤ R := ENNReal.toReal_nonneg
  have hR_v : lpNorm v.toFun 2 volume ≤ R := by
    change (eLpNorm v.toFun 2 volume).toReal ≤ R
    exact ENNReal.toReal_mono hS_top (by
      dsimp [S]
      calc
        _ ≤ eLpNorm v.toFun 2 volume +
            eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume :=
          le_add_of_nonneg_right (by positivity)
        _ ≤ _ := le_add_of_nonneg_right (by positivity))
  have hR_grad : lpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume ≤ R := by
    change (eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume).toReal ≤ R
    exact ENNReal.toReal_mono hS_top (by
      dsimp [S]
      calc
        _ ≤ eLpNorm v.toFun 2 volume +
            eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume :=
          le_add_of_nonneg_left (by positivity)
        _ ≤ _ := by
          have hsum : 0 ≤ ∑ i : Fin 3,
              eLpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume := by
            positivity
          exact le_add_of_nonneg_right hsum)
  have hR_G (i : Fin 3) :
      lpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume ≤ R := by
    change (eLpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume).toReal ≤ R
    apply ENNReal.toReal_mono hS_top
    dsimp [S]
    have hsingle : eLpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume ≤
        ∑ j : Fin 3, eLpNorm (fun x => vec3EuclideanNorm ((G j).grad x)) 2 volume := by
      apply Finset.single_le_sum (s := Finset.univ)
        (f := fun j => eLpNorm (fun x => vec3EuclideanNorm ((G j).grad x)) 2 volume)
      · intro j hj
        exact bot_le
      · exact Finset.mem_univ i
    have htail : (∑ j : Fin 3,
        eLpNorm (fun x => vec3EuclideanNorm ((G j).grad x)) 2 volume) ≤
        eLpNorm v.toFun 2 volume +
          eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume +
            ∑ j : Fin 3, eLpNorm (fun x => vec3EuclideanNorm ((G j).grad x)) 2 volume := by
      exact le_add_of_nonneg_left (by positivity)
    exact hsingle.trans htail
  have hR_G_sum : (∑ i : Fin 3,
      lpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume) ≤ R := by
    have hle : (∑ i : Fin 3,
        eLpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume) ≤ S := by
      dsimp [S]
      exact le_add_of_nonneg_left (by positivity)
    have hreal := ENNReal.toReal_mono hS_top hle
    calc
      _ = (∑ i : Fin 3, eLpNorm
          (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume).toReal := by
        rw [ENNReal.toReal_sum (fun i _ => (hGiNorm2 i).eLpNorm_ne_top)]
        simp [lpNorm]
      _ ≤ R := hreal
  have hderivSum :
      (∑ i : Fin 3, lpNorm (fun x => v.grad x i) 6 volume) ≤ C₆.toReal * R := by
    have hsum : (∑ i : Fin 3, lpNorm (fun x => v.grad x i) 6 volume) ≤
        ∑ i : Fin 3, C₆.toReal *
          lpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume := by
      apply Finset.sum_le_sum
      intro i hi
      exact h2_real_component_bound hC₆ hG hSob i
    calc
      _ ≤ ∑ i : Fin 3, C₆.toReal *
          lpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume := hsum
      _ = C₆.toReal * ∑ i : Fin 3,
          lpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume := by
        rw [Finset.mul_sum]
      _ ≤ C₆.toReal * R := by
        exact mul_le_mul_of_nonneg_left hR_G_sum (by positivity)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hvApprox := tendsto_eLpNorm_sub_zero_mollify (p := (2 : ENNReal))
    (by norm_num) ENNReal.coe_ne_top hv2 hε hεpos
  have hMbound (n : ℕ) :
      eLpNorm (mollify v.toFun (ε n) (hεpos n)) ⊤ volume ≤
        ENNReal.ofReal (Cstar * (1 + C₆.toReal) * R) := by
    let m : Vec3 → ℝ := mollify v.toFun (ε n) (hεpos n)
    have hm : ContDiff ℝ (⊤ : ℕ∞) m :=
      mollify_contDiff (hεpos n)
        ((h2_memLp_value v).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    have hm2 : MemLp m 2 volume := by
      simpa [m] using h2_mollify_memLp (by norm_num) (by norm_num) hv2 (hεpos n)
    have hD (i : Fin 3) : MemLp
        (fun x => (fderiv ℝ m x) (basisVec i))
        (ENNReal.ofReal (6 : ℝ)) volume := by
      simpa [m] using h2_mollify_gradient_component_memLp (v := v)
        (hεpos n) i (by simpa using hVcomp6 i)
    have hpoint := hcore hm hm2 hD
    have hm2real : lpNorm m 2 volume ≤ R := by
      change (eLpNorm m 2 volume).toReal ≤ R
      apply ENNReal.toReal_mono hS_top
      have hconv := young_convolution_nonneg_integral_one_of_aemeasurable
        (p := (2 : ENNReal)) (by norm_num) ENNReal.coe_ne_top
        (mollifier_nonneg (hεpos n))
        ((mollifier_contDiff (hεpos n) (n := 0)).continuous.integrable_of_hasCompactSupport
          (mollifier_hasCompactSupport (hεpos n)))
        (mollifier_integral_one (hεpos n))
        (mollifier_contDiff (hεpos n) (n := 0)).continuous.measurable
        hv2.aestronglyMeasurable.aemeasurable
      have hle : eLpNorm m 2 volume ≤ eLpNorm v.toFun 2 volume := by
        simpa [m, mollify] using hconv
      exact hle.trans (by
        dsimp [S]
        calc
          _ ≤ eLpNorm v.toFun 2 volume +
              eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume :=
            le_add_of_nonneg_right (by positivity)
          _ ≤ _ := by
            have hsum : 0 ≤ ∑ i : Fin 3,
                eLpNorm (fun x => vec3EuclideanNorm ((G i).grad x)) 2 volume := by
              positivity
            exact le_add_of_nonneg_right hsum)
    have hDsum : (∑ i : Fin 3, lpNorm
        (fun x => (fderiv ℝ m x) (basisVec i)) 6 volume) ≤ C₆.toReal * R := by
      apply le_trans (Finset.sum_le_sum (fun i hi => ?_)) hderivSum
      have hdi := h2_mollify_gradient_component_memLp (v := v)
        (hεpos n) i (by simpa using hVcomp6 i)
      have hconv := young_convolution_nonneg_integral_one_of_aemeasurable
        (p := (ENNReal.ofReal (6 : ℝ))) (by norm_num) (by norm_num)
        (mollifier_nonneg (hεpos n))
        ((mollifier_contDiff (hεpos n) (n := 0)).continuous.integrable_of_hasCompactSupport
          (mollifier_hasCompactSupport (hεpos n)))
        (mollifier_integral_one (hεpos n))
        (mollifier_contDiff (hεpos n) (n := 0)).continuous.measurable
        (hVcomp6 i).aestronglyMeasurable.aemeasurable
      have hle : eLpNorm (fun x => (fderiv ℝ m x) (basisVec i))
          (ENNReal.ofReal (6 : ℝ)) volume ≤
          eLpNorm (fun x => v.grad x i) (ENNReal.ofReal (6 : ℝ)) volume := by
        rw [show (fun x => (fderiv ℝ m x) (basisVec i)) =
            mollify (fun x => v.grad x i) (ε n) (hεpos n) by
          simpa [m] using h2_mollify_component_derivative (v := v) (hεpos n) i]
        simpa [mollify] using hconv
      exact ENNReal.toReal_mono (hVcomp6 i).eLpNorm_ne_top (by simpa using hle)
    have hsumNonneg : 0 ≤ lpNorm m 2 volume +
        ∑ i : Fin 3, lpNorm (fun x => (fderiv ℝ m x) (basisVec i)) 6 volume := by
      apply add_nonneg
      · exact ENNReal.toReal_nonneg
      · apply Finset.sum_nonneg
        intro i hi
        exact ENNReal.toReal_nonneg
    have hinside : lpNorm m 2 volume +
        ∑ i : Fin 3, lpNorm (fun x => (fderiv ℝ m x) (basisVec i)) 6 volume ≤
        (1 + C₆.toReal) * R := by
      calc
        _ ≤ R + C₆.toReal * R := add_le_add hm2real hDsum
        _ = (1 + C₆.toReal) * R := by ring
    have hK : 0 ≤ Cstar * (1 + C₆.toReal) * R := by
      positivity
    have hpoint' : ∀ x, |m x| ≤ Cstar * (1 + C₆.toReal) * R := by
      intro x
      simpa [mul_assoc] using
        (hpoint x).trans (mul_le_mul_of_nonneg_left hinside hCstar)
    have hmono : eLpNorm m ⊤ volume ≤
        eLpNorm (fun _ : Vec3 => Cstar * (1 + C₆.toReal) * R) ⊤ volume :=
      eLpNorm_mono_ae hm.continuous.aestronglyMeasurable (by
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg hK] using hpoint' x)
    exact hmono.trans_eq (h2_constant_top_norm hK)
  obtain ⟨ns, hns_mono, hns_ae⟩ :=
    CKN.Foundation.Euclidean.ae_subsequence_of_eLpNorm_tendsto_zero
      (p := (2 : ENNReal)) (by norm_num) hvApprox
  have hlim := MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
    (Filter.Eventually.of_forall (fun n => hMbound (ns n)))
    (fun n => (mollify_contDiff (hεpos (ns n)) (n := 0)
      ((h2_memLp_value v).locallyIntegrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2))).continuous.aestronglyMeasurable)
    hv2.aestronglyMeasurable hns_ae
  have hKnonneg : 0 ≤ Cstar * (1 + C₆.toReal) := by positivity
  have hfinal : eLpNorm v.toFun ⊤ volume ≤
      ENNReal.ofReal (Cstar * (1 + C₆.toReal)) * S := by
    rw [← ENNReal.ofReal_toReal hS_top, ← ENNReal.ofReal_mul hKnonneg]
    exact hlim
  change eLpNorm v.toFun ⊤ volume ≤
    ENNReal.ofReal (Cstar * (1 + C₆.toReal)) * S
  exact hfinal

end

end CKN
