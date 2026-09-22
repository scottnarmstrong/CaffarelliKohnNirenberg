-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.InteriorDisplayBounds
import CKN.Foundation.Parabolic.BallBasics
import CKN.Foundation.Sobolev.Cutoff.BallTopology
import CKN.Foundation.Sobolev.Cutoff.NormTriangle
import Mathlib.MeasureTheory.Measure.OpenPos

open scoped ENNReal Topology
open MeasureTheory MeasureTheory.Measure Set
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Heat

/-- A weakly harmonic `L^(3/2)` function has a smooth representative on the
three-quarter ball, with its a.e. identification and pointwise bound on that
same ball. -/
theorem weak_harmonic_interior_displays_outer
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h) :
    ∃ H : Vec3 → ℝ,
      ContDiffOn ℝ (1 : ℕ∞) H (euclideanBall x₀ (3 * ρ / 4)) ∧
      h =ᵐ[volume.restrict (euclideanBall x₀ (3 * ρ / 4))] H ∧
      (∀ x ∈ euclideanBall x₀ (3 * ρ / 4),
        |H x| ≤ harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) := by
  classical
  let U : Set Vec3 := euclideanBall x₀ ρ
  let O : Set Vec3 := euclideanBall x₀ (3 * ρ / 4)
  have hUopen : IsOpen U := by
    dsimp [U]
    exact CKN.isOpen_euclideanBall x₀ ρ
  have hOopen : IsOpen O := by
    dsimp [O]
    exact CKN.isOpen_euclideanBall x₀ (3 * ρ / 4)
  have hmargin : 0 < ρ / 4 := by positivity
  have hinnerRadius : 0 < (ρ / 4) / 2 := by positivity
  have hsmall : 0 < ρ / 32 := by positivity
  have hpatch : 0 < ρ / 16 := by positivity
  have hlocalCarrier (x : Vec3) (hx : x ∈ O) :
      euclideanBall x (ρ / 4) ⊆ U := by
    intro y hy
    have hyx : vecEuclideanNorm (y - x) < ρ / 4 := by
      exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hmargin).1 hy
    have hx₀ : vecEuclideanNorm (x - x₀) < 3 * ρ / 4 := by
      exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
    have htri : vecEuclideanNorm (y - x₀) ≤
        vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) := by
      rw [show y - x₀ = (y - x) + (x - x₀) by abel]
      exact CKN.vecEuclideanNorm_add_le _ _
    have hy₀ : vecEuclideanNorm (y - x₀) < ρ := by
      nlinarith only [htri, hyx, hx₀, hρ]
    exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2 hy₀
  let localWitness : ∀ (x : Vec3), x ∈ O →
      ∃ Hx : Vec3 → ℝ,
        ContDiffOn ℝ (1 : ℕ∞) Hx
          (euclideanBall x ((ρ / 4) / 2)) ∧
        h =ᵐ[volume.restrict (euclideanBall x ((ρ / 4) / 2))] Hx ∧
        (∀ y ∈ euclideanBall x ((ρ / 4) / 2),
          |Hx y| ≤ weakHarmonicInteriorSupConstant * ((ρ / 4) ^ 2)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x (ρ / 4)))) := by
    intro x hx
    have hsub := hlocalCarrier x hx
    obtain ⟨Hx, hHxcont, hHxae, hHxvalue, _hHxgrad⟩ :=
      weakly_harmonic_interior_smooth hmargin
        (hmem.mono_measure (Measure.restrict_mono_set volume hsub))
        (local_weak_harmonic hsub hweak)
    exact ⟨Hx, hHxcont, hHxae, hHxvalue⟩
  let localRep : ∀ (x : Vec3), x ∈ O → Vec3 → ℝ :=
    fun x hx => Classical.choose (localWitness x hx)
  have localRep_spec (x : Vec3) (hx : x ∈ O) :
      ContDiffOn ℝ (1 : ℕ∞) (localRep x hx)
          (euclideanBall x ((ρ / 4) / 2)) ∧
        h =ᵐ[volume.restrict (euclideanBall x ((ρ / 4) / 2))]
          (localRep x hx) ∧
        (∀ y ∈ euclideanBall x ((ρ / 4) / 2),
          |localRep x hx y| ≤
            weakHarmonicInteriorSupConstant * ((ρ / 4) ^ 2)⁻¹ *
              lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x (ρ / 4)))) :=
    Classical.choose_spec (localWitness x hx)
  let H : Vec3 → ℝ := fun y => if hy : y ∈ O then localRep y hy y else 0
  have hlocalEq (x : Vec3) (hx : x ∈ O) (y : Vec3) (hy : y ∈ O)
      (hyx : y ∈ euclideanBall x (ρ / 32)) :
      H y = localRep x hx y := by
    have hyx' : vecEuclideanNorm (y - x) < ρ / 32 :=
      (mem_euclideanBall_iff_vecEuclideanNorm_lt hsmall).1 hyx
    let V : Set Vec3 := euclideanBall y (ρ / 16)
    have hVopen : IsOpen V := by
      dsimp [V]
      exact CKN.isOpen_euclideanBall y (ρ / 16)
    have hVx : V ⊆ euclideanBall x ((ρ / 4) / 2) := by
      intro z hz
      have hzy : vecEuclideanNorm (z - y) < ρ / 16 :=
        (mem_euclideanBall_iff_vecEuclideanNorm_lt hpatch).1 hz
      have htri : vecEuclideanNorm (z - x) ≤
          vecEuclideanNorm (z - y) + vecEuclideanNorm (y - x) := by
        rw [show z - x = (z - y) + (y - x) by abel]
        exact CKN.vecEuclideanNorm_add_le _ _
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hinnerRadius).2
      nlinarith only [htri, hzy, hyx', hρ]
    have hVy : V ⊆ euclideanBall y ((ρ / 4) / 2) := by
      intro z hz
      have hzy : vecEuclideanNorm (z - y) < ρ / 16 :=
        (mem_euclideanBall_iff_vecEuclideanNorm_lt hpatch).1 hz
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hinnerRadius).2
      nlinarith only [hzy, hρ]
    have hxeq : h =ᵐ[volume.restrict V] localRep x hx :=
      ae_mono (Measure.restrict_mono_set volume hVx)
        (localRep_spec x hx).2.1
    have hyeq : h =ᵐ[volume.restrict V] localRep y hy :=
      ae_mono (Measure.restrict_mono_set volume hVy)
        (localRep_spec y hy).2.1
    have hxy : localRep x hx =ᵐ[volume.restrict V] localRep y hy :=
      hxeq.symm.trans hyeq
    have hxc : ContinuousOn (localRep x hx) V :=
      (localRep_spec x hx).1.continuousOn.mono hVx
    have hyc : ContinuousOn (localRep y hy) V :=
      (localRep_spec y hy).1.continuousOn.mono hVy
    have hpoint : localRep x hx y = localRep y hy y := by
      apply (eqOn_open_of_ae_eq hxy hVopen hxc hyc)
      exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hpatch).2 (by
        simpa [vecEuclideanNorm, vecNormSq, vecDot])
    simpa [H, hy] using hpoint.symm
  have hHcont : ContDiffOn ℝ (1 : ℕ∞) H O := by
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    refine ⟨euclideanBall x (ρ / 32), ?_, ?_, ?_⟩
    · exact CKN.isOpen_euclideanBall x (ρ / 32)
    · exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hsmall).2 (by
        simpa [vecEuclideanNorm, vecNormSq, vecDot])
    · apply ((localRep_spec x hx).1.mono ?_).congr
      · intro y hy
        rcases hy with ⟨hyO, hyx⟩
        exact hlocalEq x hx y hyO hyx
      · intro y hy
        have hy' : vecEuclideanNorm (y - x) < ρ / 32 :=
          (mem_euclideanBall_iff_vecEuclideanNorm_lt hsmall).1 hy.2
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hinnerRadius).2
        nlinarith only [hy', hρ]
  let bad : Set Vec3 := {x | x ∈ O ∧ H x ≠ h x}
  have hbadNull : volume bad = 0 := by
    apply MeasureTheory.measure_null_of_locally_null bad
    intro x hx
    have hxO : x ∈ O := hx.1
    have hloc : ∀ᵐ y ∂volume.restrict (euclideanBall x ((ρ / 4) / 2)),
        h y = localRep x hxO y := (localRep_spec x hxO).2.1
    have hlocalEq' : ∀ y ∈ O ∩ euclideanBall x (ρ / 32),
        H y = localRep x hxO y := by
      intro y hy
      exact hlocalEq x hxO y hy.1 hy.2
    have hbadLocalNull : volume
        (bad ∩ euclideanBall x (ρ / 32)) = 0 := by
      have hlocGlobal : ∀ᵐ y ∂volume,
          y ∈ euclideanBall x ((ρ / 4) / 2) →
            h y = localRep x hxO y := ae_imp_of_ae_restrict hloc
      have hnull : volume {y | ¬ (y ∈ euclideanBall x ((ρ / 4) / 2) →
          h y = localRep x hxO y)} = 0 := ae_iff.mp hlocGlobal
      apply measure_mono_null ?_ hnull
      rintro y ⟨⟨hyO, hneq⟩, hyx⟩
      have hyEq := hlocalEq' y ⟨hyO, hyx⟩
      have hyin : y ∈ euclideanBall x ((ρ / 4) / 2) := by
        have hy' : vecEuclideanNorm (y - x) < ρ / 32 :=
          (mem_euclideanBall_iff_vecEuclideanNorm_lt hsmall).1 hyx
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hinnerRadius).2
        nlinarith only [hy', hρ]
      intro hgood
      apply hneq
      calc
        H y = localRep x hxO y := hyEq
        _ = h y := (hgood hyin).symm
    refine ⟨bad ∩ euclideanBall x (ρ / 32), ?_, hbadLocalNull⟩
    refine mem_nhdsWithin.mpr ⟨euclideanBall x (ρ / 32),
      CKN.isOpen_euclideanBall x (ρ / 32), ?_, ?_⟩
    · exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hsmall).2 (by
        simpa [vecEuclideanNorm, vecNormSq, vecDot])
    · intro y hy
      exact ⟨hy.2, hy.1⟩
  have hAEglobal : ∀ᵐ x ∂volume, x ∈ O → h x = H x := by
    filter_upwards [compl_mem_ae_iff.mpr hbadNull] with x hx
    intro hxO
    have hxnot : ¬ (x ∈ O ∧ H x ≠ h x) := by simpa [bad] using hx
    by_contra hneq
    apply hxnot
    exact ⟨hxO, fun heq => hneq heq.symm⟩
  have hAE : h =ᵐ[volume.restrict O] H := by
    filter_upwards [hAEglobal.filter_mono ae_restrict_le,
      ae_restrict_mem hOopen.measurableSet] with x hx hxO
    exact hx hxO
  have hbound : ∀ x ∈ O,
      |H x| ≤ harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
    intro x hx
    have hxinner : x ∈ euclideanBall x ((ρ / 4) / 2) := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hinnerRadius).2
      simpa [vecEuclideanNorm, vecNormSq, vecDot]
    have hlocal := (localRep_spec x hx).2.2 x hxinner
    have hnormLocal : lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x (ρ / 4))) ≤
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
      rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
      exact ENNReal.toReal_mono hmem.eLpNorm_lt_top.ne
        (eLpNorm_mono_measure h
          (Measure.restrict_mono_set volume (hlocalCarrier x hx)))
    have hscale : ((ρ / 4) ^ 2)⁻¹ = 16 * (ρ ^ 2)⁻¹ := by
      field_simp [hρ.ne']
      ring
    rw [hscale] at hlocal
    have hlocal' : |localRep x hx x| ≤
        16 * weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x (ρ / 4))) := by
      calc
        |localRep x hx x| ≤ weakHarmonicInteriorSupConstant *
            (16 * (ρ ^ 2)⁻¹) *
              lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
                (volume.restrict (euclideanBall x (ρ / 4))) := hlocal
        _ = _ := by ring
    have hweak : 16 * weakHarmonicInteriorSupConstant ≤
        harmonicInteriorDisplayConstant := by
      have h16 : 16 * weakHarmonicInteriorSupConstant ≤
          576 * weakHarmonicInteriorSupConstant :=
        mul_le_mul_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 576)
          weakHarmonicInteriorSupConstant_nonneg
      exact h16.trans (le_trans (le_max_right _ _) (le_max_left _ _))
    have hinv : 0 ≤ (ρ ^ 2)⁻¹ := by positivity
    have hdisplay : 0 ≤ harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ :=
      mul_nonneg harmonicInteriorDisplayConstant_nonneg hinv
    have hweakScaled : 16 * weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ ≤
        harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hweak hinv
    have hHxeq : H x = localRep x hx x := by simp [H, hx]
    calc
      |H x| = |localRep x hx x| := by rw [hHxeq]
      _ ≤ 16 * weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x (ρ / 4))) := hlocal'
      _ ≤ harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x (ρ / 4))) :=
        mul_le_mul_of_nonneg_right hweakScaled lpNorm_nonneg
      _ ≤ harmonicInteriorDisplayConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
        exact mul_le_mul_of_nonneg_left hnormLocal hdisplay
  exact ⟨H, by simpa [O] using hHcont, by simpa [U, O] using hAE,
    by simpa [U, O] using hbound⟩

end CKN.Foundation.Heat
