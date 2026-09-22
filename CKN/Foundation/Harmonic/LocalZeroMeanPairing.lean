-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.RadialZeroMeanPairing
import CKN.Foundation.Harmonic.SmoothEuclideanCutoff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Defs

open MeasureTheory
open Set Filter
open scoped Topology
open CKN.Foundation.Parabolic CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

/-!
# Local harmonic pairing with radial zero-mass data

A cutoff extends a locally defined harmonic function to a global smooth function on the
support of a radial test source. The Newtonian-potential pairing then applies locally.
-/

namespace CKN.Foundation.Harmonic

private theorem spatialLaplacian_comp_add_left (f : Vec3 → ℝ) (x z : Vec3) :
    CKN.spatialLaplacian (fun y => f (x + y)) z =
      CKN.spatialLaplacian f (x + z) := by
  have hfirst (i : Fin 3) :
      CKN.spatialDeriv (fun y => f (x + y)) i =
        fun y => CKN.spatialDeriv f i (x + y) := by
    funext y
    simp [CKN.spatialDeriv, fderiv_comp_add_left]
  rw [CKN.spatialLaplacian, CKN.spatialLaplacian]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfirst i]
  change (fderiv ℝ (fun y => CKN.spatialDeriv f i (x + y)) z)
    (CKN.basisVec i) = _
  rw [fderiv_comp_add_left]
  rfl

private theorem spatialLaplacian_eq_of_eqOn_open
    {f g : Vec3 → ℝ} {V : Set Vec3} {x : Vec3}
    (hV : IsOpen V) (hx : x ∈ V)
    (hf : ContDiffOn ℝ 2 f V) (hg : ContDiffOn ℝ 2 g V)
    (heq : EqOn f g V) :
    CKN.spatialLaplacian f x = CKN.spatialLaplacian g x := by
  have hfirst (y : Vec3) (hy : y ∈ V) (i : Fin 3) :
      CKN.spatialDeriv f i y = CKN.spatialDeriv g i y := by
    have hfy : ContDiffAt ℝ 2 f y := hf.contDiffAt (hV.mem_nhds hy)
    have hgy : ContDiffAt ℝ 2 g y := hg.contDiffAt (hV.mem_nhds hy)
    have hEq : f =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact heq hz
    have hF : HasFDerivAt f (fderiv ℝ f y) y :=
      (hfy.differentiableAt (by norm_num)).hasFDerivAt
    have hG : HasFDerivAt g (fderiv ℝ f y) y :=
      hF.congr_of_eventuallyEq hEq.symm
    have hFderiv : fderiv ℝ f y = fderiv ℝ g y := by
      rw [hF.fderiv, hG.fderiv]
    change (fderiv ℝ f y) (CKN.basisVec i) =
      (fderiv ℝ g y) (CKN.basisVec i)
    rw [hFderiv]
  have hevent (i : Fin 3) :
      CKN.spatialDeriv f i =ᶠ[𝓝 x] CKN.spatialDeriv g i := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hfirst y hy i
  have hsecond (i : Fin 3) :
      CKN.spatialDeriv (CKN.spatialDeriv f i) i x =
        CKN.spatialDeriv (CKN.spatialDeriv g i) i x := by
    have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hV.mem_nhds hx)
    have hgx : ContDiffAt ℝ 2 g x := hg.contDiffAt (hV.mem_nhds hx)
    have hfdiff : DifferentiableAt ℝ (CKN.spatialDeriv f i) x := by
      have hder := hfx.fderiv_right (m := 1) (by norm_num)
      have happly := hder.clm_apply
        (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : Vec3 => CKN.basisVec i) x)
      exact happly.differentiableAt (by norm_num)
    have hgdiff : DifferentiableAt ℝ (CKN.spatialDeriv g i) x := by
      have hder := hgx.fderiv_right (m := 1) (by norm_num)
      have happly := hder.clm_apply
        (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : Vec3 => CKN.basisVec i) x)
      exact happly.differentiableAt (by norm_num)
    have hF : HasFDerivAt (CKN.spatialDeriv f i)
        (fderiv ℝ (CKN.spatialDeriv f i) x) x := hfdiff.hasFDerivAt
    have hG := hF.congr_of_eventuallyEq (hevent i).symm
    have hD : fderiv ℝ (CKN.spatialDeriv f i) x =
        fderiv ℝ (CKN.spatialDeriv g i) x := by
      rw [hF.fderiv, hG.fderiv]
    change (fderiv ℝ (CKN.spatialDeriv f i) x) (CKN.basisVec i) =
      (fderiv ℝ (CKN.spatialDeriv g i) x) (CKN.basisVec i)
    rw [hD]
  rw [CKN.spatialLaplacian]
  apply Finset.sum_congr rfl
  intro i hi
  exact hsecond i

/-- A locally `C²` harmonic function pairs to zero with a smooth, radial, zero-mass
source supported strictly inside a ball whose closure is contained in the harmonic region. -/
theorem local_harmonic_radial_zeroMean_pairing
    {U : Set Vec3} {f g : Vec3 → ℝ} {r a b s : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hHarm : ∀ y ∈ U, CKN.spatialLaplacian f y = 0)
    (hr : 0 < r) (hra : r < a) (hab : a < b) (hbs : b < s)
    (hball : closure (euclideanBall (0 : Vec3) s) ⊆ U)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hrad : ∀ y z, vec3EuclideanNorm y = vec3EuclideanNorm z → g y = g z)
    (hmean : ∫ y, g y = 0)
    (hsupp : tsupport g ⊆ euclideanClosedBall 0 r) :
    Integrable (fun y => f y * g y) volume ∧ ∫ y, f y * g y = 0 := by
  classical
  let η : Vec3 → ℝ := harmonicBumpCutoff a b (lt_trans hr hra) hab
  let H : Vec3 → ℝ := fun y => if y ∈ U then η y * f y else 0
  have hηcd : ContDiff ℝ (⊤ : ℕ∞) η := by
    exact harmonicBumpCutoff_contDiff a b (lt_trans hr hra) hab
  have hηc : Continuous η := hηcd.continuous
  have hηcompact : HasCompactSupport η :=
    harmonicBumpCutoff_hasCompactSupport a b (lt_trans hr hra) hab
  have hbpos : 0 < b := lt_trans (lt_trans hr hra) hab
  have hclosedb : euclideanClosedBall 0 b ⊆ U := by
    intro y hy
    apply hball
    exact subset_closure
      ((euclideanClosedBall_subset_euclideanBall (le_of_lt hbpos) hbs) hy)
  have hηtsupp : tsupport η ⊆ U :=
    (harmonicBumpCutoff_tsupport_subset a b (lt_trans hr hra) hab).trans hclosedb
  have hHcd : ContDiff ℝ 2 H := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · have hprod : ContDiffAt ℝ 2 (fun z => η z * f z) y := by
        exact hηcd.contDiffAt.of_le (by norm_num) |>.mul (hf.contDiffAt (hU.mem_nhds hy))
      apply hprod.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hy] with z hz
      change (if z ∈ U then η z * f z else 0) = η z * f z
      exact ite_eq_left hz
    · have hyη : y ∉ tsupport η := fun h => hy (hηtsupp h)
      have hηcomp : IsOpen ((tsupport η)ᶜ) := (isClosed_tsupport η).isOpen_compl
      have hzero : (fun z => H z) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [hηcomp.mem_nhds hyη] with z hz
        have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
        by_cases hzU : z ∈ U
        · change (if z ∈ U then η z * f z else 0) = 0
          rw [ite_eq_left hzU, hηz, zero_mul]
        · change (if z ∈ U then η z * f z else 0) = 0
          rw [ite_eq_right hzU]
      exact ContDiffAt.congr_of_eventuallyEq
        (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : Vec3 => (0 : ℝ)) y) hzero
  have hclosedr_subset_a : euclideanClosedBall (0 : Vec3) r ⊆ euclideanBall 0 a := by
    exact euclideanClosedBall_subset_euclideanBall hr.le hra
  have haU : euclideanBall 0 a ⊆ U := by
    intro y hy
    have has : a < s := lt_trans hab hbs
    have hys : y ∈ euclideanBall 0 s := by
      have hnorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt
        (lt_trans hr hra)).1 hy
      exact (mem_euclideanBall_iff_vecEuclideanNorm_lt
        (lt_trans (lt_trans hr hra) has)).2 (lt_trans hnorm has)
    exact hball (subset_closure hys)
  have hH_eq_f : EqOn H f (euclideanBall 0 a) := by
    intro y hy
    have hyU : y ∈ U := haU hy
    have hnorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt
      (lt_trans hr hra)).1 hy
    have hyclosed : y ∈ euclideanClosedBall (0 : Vec3) a :=
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (le_of_lt (lt_trans hr hra))).2
        hnorm.le
    have hηy : η y = 1 := by
      exact harmonicBumpCutoff_eq_one a b (lt_trans hr hra) hab hyclosed
    simp [H, hyU, hηy]
  have hHarmOnR : ∀ y ∈ euclideanClosedBall 0 r,
      CKN.spatialLaplacian H y = 0 := by
    intro y hy
    have hya : y ∈ euclideanBall 0 a := hclosedr_subset_a hy
    have hV : IsOpen (euclideanBall (0 : Vec3) a) := isOpen_euclideanBall 0 a
    have hfV : ContDiffOn ℝ 2 f (euclideanBall 0 a) := hf.mono haU
    have hHV : ContDiffOn ℝ 2 H (euclideanBall 0 a) := hHcd.contDiffOn
    have hEqLap := spatialLaplacian_eq_of_eqOn_open hV hya hfV hHV hH_eq_f.symm
    rw [← hEqLap]
    exact hHarm y (haU hya)
  have hpair := harmonic_radial_zeroMean_test_pairing hHcd hg hgc hrad hmean hr
    hsupp hHarmOnR
  have hmul : (fun y => f y * g y) = fun y => H y * g y := by
    funext y
    by_cases hgy : g y = 0
    · simp [hgy]
    · have hySupport : y ∈ Function.support g := Function.mem_support.mpr hgy
      have hyt : y ∈ tsupport g := subset_closure hySupport
      have hyr : y ∈ euclideanClosedBall 0 r := hsupp hyt
      have hya : y ∈ euclideanBall 0 a := hclosedr_subset_a hyr
      rw [hH_eq_f hya]
  have hprodCont : Continuous (fun y => H y * g y) := hHcd.continuous.mul hg.continuous
  have hprodCompact : HasCompactSupport (fun y => H y * g y) := hgc.mul_left (f := H)
  have hprodInt : Integrable (fun y => H y * g y) (volume : Measure Vec3) :=
    hprodCont.integrable_of_hasCompactSupport hprodCompact
  refine ⟨hprodInt.congr
    (ae_of_all volume (fun y => (congrFun hmul y).symm)), ?_⟩
  calc
    ∫ y, f y * g y = ∫ y, H y * g y :=
      integral_congr_ae (ae_of_all volume (fun y => congrFun hmul y))
    _ = 0 := hpair

/-- Translation of `local_harmonic_radial_zeroMean_pairing` to a ball with arbitrary
centre. -/
theorem local_harmonic_radial_zeroMean_pairing_at
    {U : Set Vec3} {f g : Vec3 → ℝ} {x : Vec3} {r a b s : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hHarm : ∀ y ∈ U, CKN.spatialLaplacian f y = 0)
    (hr : 0 < r) (hra : r < a) (hab : a < b) (hbs : b < s)
    (hball : closure (euclideanBall x s) ⊆ U)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hrad : ∀ y z, vec3EuclideanNorm (y - x) = vec3EuclideanNorm (z - x) →
      g y = g z)
    (hmean : ∫ y, g y = 0)
    (hsupp : tsupport g ⊆ euclideanClosedBall x r) :
    Integrable (fun y => f y * g y) volume ∧ ∫ y, f y * g y = 0 := by
  classical
  let trans : Vec3 → Vec3 := fun z => x + z
  let U₀ : Set Vec3 := trans ⁻¹' U
  let f₀ : Vec3 → ℝ := fun z => f (trans z)
  let g₀ : Vec3 → ℝ := fun z => g (trans z)
  have htransCD : ContDiff ℝ (⊤ : ℕ∞) trans := by
    dsimp [trans]
    fun_prop
  have htransC2 : ContDiff ℝ 2 trans := htransCD.of_le (by norm_num)
  have htransC : Continuous trans := htransCD.continuous
  have hU₀ : IsOpen U₀ := hU.preimage htransC
  have hf₀ : ContDiffOn ℝ 2 f₀ U₀ := by
    change ContDiffOn ℝ 2 (f ∘ trans) U₀
    exact hf.comp (htransC2.contDiffOn.mono (subset_univ U₀)) (fun z hz => hz)
  have hHarm₀ : ∀ z ∈ U₀, CKN.spatialLaplacian f₀ z = 0 := by
    intro z hz
    have h := hHarm (trans z) hz
    change CKN.spatialLaplacian (fun w => f (x + w)) z = 0
    rw [spatialLaplacian_comp_add_left]
    simpa [trans] using h
  have hballImage :
      (Homeomorph.addLeft x : Vec3 ≃ₜ Vec3) '' euclideanBall (0 : Vec3) s =
        euclideanBall x s := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [euclideanBall, euclideanSqDist] using hz
    · intro hy
      refine ⟨y - x, ?_, ?_⟩
      · simpa [euclideanBall, euclideanSqDist] using hy
      · simp
  have hclosureImage := (Homeomorph.addLeft x).image_closure
    (euclideanBall (0 : Vec3) s)
  rw [hballImage] at hclosureImage
  have hball₀ : closure (euclideanBall (0 : Vec3) s) ⊆ U₀ := by
    intro z hz
    change trans z ∈ U
    apply hball
    have hz' : trans z ∈ closure (euclideanBall x s) := by
      have hm : trans z ∈
          (Homeomorph.addLeft x : Vec3 ≃ₜ Vec3) '' closure (euclideanBall 0 s) :=
        ⟨z, hz, rfl⟩
      exact hclosureImage ▸ hm
    exact hz'
  have hg₀ : ContDiff ℝ (⊤ : ℕ∞) g₀ := by
    change ContDiff ℝ (⊤ : ℕ∞) (g ∘ trans)
    exact hg.comp htransCD
  have hrad₀ : ∀ y z, vec3EuclideanNorm y = vec3EuclideanNorm z → g₀ y = g₀ z := by
    intro y z hyz
    apply hrad (trans y) (trans z)
    simpa [trans, sub_add_cancel] using hyz
  have hgsupp₀ : Function.support g₀ ⊆ euclideanClosedBall (0 : Vec3) r := by
    intro z hz
    have hgzn : g (trans z) ≠ 0 := by
      simpa [g₀] using Function.mem_support.mp hz
    have hzt : trans z ∈ tsupport g := subset_closure (Function.mem_support.mpr hgzn)
    have hzball := hsupp hzt
    simpa [trans, euclideanClosedBall, euclideanSqDist] using hzball
  have hgtsupp₀ : tsupport g₀ ⊆ euclideanClosedBall (0 : Vec3) r :=
    closure_minimal hgsupp₀ (isClosed_euclideanClosedBall 0 r)
  have hgc₀ : HasCompactSupport g₀ :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_euclideanClosedBall 0 hr.le) hgsupp₀
  have hmean₀ : ∫ z, g₀ z = 0 := by
    calc
      ∫ z, g₀ z = ∫ z, g z := by
        exact (measurePreserving_add_left (volume : Measure Vec3) x).integral_comp
          (MeasurableEquiv.addLeft x).measurableEmbedding g
      _ = 0 := hmean
  have horigin := local_harmonic_radial_zeroMean_pairing hU₀ hf₀ hHarm₀
    hr hra hab hbs hball₀ hg₀ hgc₀ hrad₀ hmean₀ hgtsupp₀
  let P : Vec3 → ℝ := fun y => f y * g y
  have hQ : Integrable (fun z => P (trans z)) volume := by
    apply horigin.1.congr
    filter_upwards [] with z
    rfl
  have hPinv : Integrable (fun z => P (x + (-x + z))) volume :=
    (measurePreserving_add_left (volume : Measure Vec3) (-x)).integrable_comp_of_integrable hQ
  have hP : Integrable P volume := by
    apply hPinv.congr
    filter_upwards [] with z
    simp
  have hchange : ∫ z, P (trans z) = ∫ y, P y := by
    exact (measurePreserving_add_left (volume : Measure Vec3) x).integral_comp
      (MeasurableEquiv.addLeft x).measurableEmbedding P
  have hzero : ∫ z, P (trans z) = 0 := by
    simpa [P, f₀, g₀, trans] using horigin.2
  exact ⟨hP, by rw [← hchange]; exact hzero⟩

end CKN.Foundation.Harmonic
