-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Finiteness
import CKN.Foundation.Parabolic.Vec3Norm
import CKN.Foundation.Parabolic.BallBasics
import Mathlib.Topology.Order.Compact

/-! # Compact support localization inside a local parabolic box. -/
set_option autoImplicit false
open CKN.Foundation.Parabolic Set
namespace CKN

theorem shear_localBox_of_compact_tsupport {K : Set (Vec3 × ℝ)}
    (hK : IsCompact K) (hsub : K ⊆ vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 1) :
    ∃ Ω' J, localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J ∧
      K ⊆ Ω' ×ˢ J ∧ MeasurableSet (spaceTimeSet Ω' J) := by
  have hKx : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hKt : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  have hnormc : Continuous (fun x : Vec3 => vec3EuclideanNorm x) :=
    continuous_vec3EuclideanNorm
  have habsc : Continuous (fun t : ℝ => |t|) := continuous_abs
  have hconstruct (R T : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
      (hTpos : 0 < T) (hTlt : T < 1)
      (hKxR : Prod.fst '' K ⊆ vec3Ball 0 R)
      (hKtT : Prod.snd '' K ⊆ Ioo (-T) T) :
      ∃ Ω' J, localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J ∧
        K ⊆ Ω' ×ˢ J ∧ MeasurableSet (spaceTimeSet Ω' J) := by
    refine ⟨vec3Ball 0 R, Ioo (-T) T, ?_, ?_, ?_⟩
    · refine ⟨isOpen_vec3Ball _ _, isCompact_closure_vec3Ball hRpos, ?_,
        ordConnected_Ioo, ?_, ?_⟩
      · intro x hx
        rw [closure_vec3Ball hRpos] at hx
        change vec3EuclideanNorm (x - 0) < 1
        exact lt_of_le_of_lt (by simpa using hx) hRlt
      · rw [closure_Ioo (by linarith only [hTpos])]
        exact isCompact_Icc
      · rw [closure_Ioo (by linarith only [hTpos])]
        intro t ht
        exact ⟨by linarith only [ht.1, hTlt], by linarith only [ht.2, hTlt]⟩
    · intro z hz
      exact ⟨hKxR ⟨z, hz, rfl⟩, hKtT ⟨z, hz, rfl⟩⟩
    · change MeasurableSet (vec3Ball 0 R ×ˢ Ioo (-T) T)
      exact (isOpen_vec3Ball 0 R).measurableSet.prod measurableSet_Ioo
  by_cases hne : K.Nonempty
  · obtain ⟨xstar, hxstar, hmaxx⟩ :=
      hKx.exists_isMaxOn (hne.image Prod.fst) hnormc.continuousOn
    obtain ⟨tstar, htstar, hmaxt⟩ :=
      hKt.exists_isMaxOn (hne.image Prod.snd) habsc.continuousOn
    rcases hxstar with ⟨zx, hzx, hzxstar⟩
    rcases htstar with ⟨zt, hzt, hztstar⟩
    have hnx : vec3EuclideanNorm xstar < 1 := by
      simpa [hzxstar] using (hsub hzx).1
    have htint : tstar ∈ Ioo (-1 : ℝ) 1 := by
      simpa [hztstar] using (hsub hzt).2
    have hat : |tstar| < 1 := abs_lt.mpr htint
    let R := (vec3EuclideanNorm xstar + 1) / 2
    let T := (|tstar| + 1) / 2
    have hRpos : 0 < R := by
      have hnorm : 0 ≤ vec3EuclideanNorm xstar := vec3EuclideanNorm_nonneg xstar
      dsimp [R]
      positivity
    have hRlt : R < 1 := by dsimp [R]; linarith only [hnx]
    have hTpos : 0 < T := by dsimp [T]; positivity
    have hTlt : T < 1 := by dsimp [T]; linarith only [hat]
    have hKxR : Prod.fst '' K ⊆ vec3Ball 0 R := by
      intro x hx
      have hxmax := hmaxx hx
      change vec3EuclideanNorm x ≤ vec3EuclideanNorm xstar at hxmax
      change vec3EuclideanNorm (x - 0) < R
      dsimp [R]
      have hxnorm : vec3EuclideanNorm x ≤ vec3EuclideanNorm xstar := hxmax
      have hxnorm0 : vec3EuclideanNorm (x - 0) = vec3EuclideanNorm x := by simp
      rw [hxnorm0]
      linarith only [hxnorm, hnx]
    have hKtT : Prod.snd '' K ⊆ Ioo (-T) T := by
      intro t ht
      have htmax := hmaxt ht
      change |t| ≤ |tstar| at htmax
      dsimp [T]
      have habs : |t| < (|tstar| + 1) / 2 := by linarith only [htmax, hat]
      exact abs_lt.mp habs
    exact hconstruct R T hRpos hRlt hTpos hTlt hKxR hKtT
  · let R : ℝ := 1 / 2
    let T : ℝ := 1 / 2
    have hRpos : 0 < R := by norm_num [R]
    have hRlt : R < 1 := by norm_num [R]
    have hTpos : 0 < T := by norm_num [T]
    have hTlt : T < 1 := by norm_num [T]
    have hKxR : Prod.fst '' K ⊆ vec3Ball 0 R := by
      intro x hx
      rcases hx with ⟨z, hz, _hzx⟩
      exact False.elim (hne ⟨z, hz⟩)
    have hKtT : Prod.snd '' K ⊆ Ioo (-T) T := by
      intro t ht
      rcases ht with ⟨z, hz, _hzt⟩
      exact False.elim (hne ⟨z, hz⟩)
    exact hconstruct R T hRpos hRlt hTpos hTlt hKxR hKtT

end CKN
