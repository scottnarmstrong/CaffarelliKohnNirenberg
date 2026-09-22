-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.HolderGluing

/-! # Uniform Hölder gluing on compact sets

A finite cover by half-radius balls gives an explicit close-pair radius.
The final bound depends only on the common local radius and norm bound,
not on the number of balls or the representatives chosen on them.
-/

open Set MeasureTheory
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame

/-- Uniform local Hölder representatives on fixed-radius balls glue on
a compact set with an explicit norm bound. -/
theorem exists_holder_norm_on_compact_of_uniform_balls
    {K : Set ParabolicPoint} (hK : IsCompact K)
    {a C γ : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hγ : 0 < γ)
    {u : ParabolicPoint → Vec3}
    (hlocal : ∀ z ∈ K, ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (Metric.ball z a)] u ∧
        ParabolicHolderVecNormLE (Metric.ball z a) w γ C) :
    ∃ g : ParabolicPoint → Vec3,
      g =ᵐ[volume.restrict K] u ∧
        ParabolicHolderVecNormLE K g γ (C + max C (2 * C / (a / 2) ^ γ)) := by
  classical
  have hhalf : 0 < a / 2 := half_pos ha
  have hcover : K ⊆ ⋃ z : K, Metric.ball z.1 (a / 2) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self hhalf⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun z : K => Metric.ball z.1 (a / 2)) (fun _ => Metric.isOpen_ball) hcover
  have hhalfcover : ∀ x ∈ K, ∃ z : t, x ∈ Metric.ball z.1.1 (a / 2) := by
    intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hzt, hxz⟩ := mem_iUnion.mp hz
    exact ⟨⟨z, hzt⟩, hxz⟩
  choose w hw hnorm using fun z : t => hlocal z.1.1 z.1.2
  have hfullcover : K ⊆ ⋃ z : t, Metric.ball z.1.1 a := by
    intro x hx
    obtain ⟨z, hxz⟩ := hhalfcover x hx
    exact mem_iUnion.mpr ⟨z, Metric.ball_subset_ball (half_le_self ha.le) hxz⟩
  have hclose : ∀ x ∈ K, ∀ y ∈ K, parabolicDist x y < a / 2 →
      ∃ z : t, x ∈ Metric.ball z.1.1 a ∧ y ∈ Metric.ball z.1.1 a := by
    intro x hx y _hy hxy
    obtain ⟨z, hxz⟩ := hhalfcover x hx
    refine ⟨z, Metric.ball_subset_ball (half_le_self ha.le) hxz, ?_⟩
    apply Metric.mem_ball.mpr
    have hyx : dist y x < a / 2 := by
      rw [dist_comm, dist_eq_parabolicDist]
      exact hxy
    have hxz' : dist x z.1.1 < a / 2 := Metric.mem_ball.mp hxz
    have hsum := (dist_triangle y x z.1.1).trans_lt (add_lt_add hyx hxz')
    linarith only [hsum]
  obtain ⟨g, hgu, hg, _⟩ := exists_holder_norm_gluing
    (fun z : t => Metric.ball z.1.1 a) w hγ hC hhalf
    (fun _ => Metric.isOpen_ball) hnorm hw hfullcover hclose
  exact ⟨g, hgu, hg⟩

end CKN.Core.Endgame
