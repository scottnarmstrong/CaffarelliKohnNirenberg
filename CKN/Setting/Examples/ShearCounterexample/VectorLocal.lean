-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.SliceAE
import CKN.Statements.LocalVecLp
import CKN.Statements.LocalBox
import CKN.Statements.SpaceTimeSet
import CKN.Foundation.Parabolic.Vec3Norm

/-! # Local vector-valued Lp estimates for the shear fields. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

private theorem shearVecNorm_le_scalarNorm (z : ParabolicPoint) :
    ‖shearCounterexampleVelocity z‖ ≤ ‖shearFullScalar z‖ := by
  have hform : shearCounterexampleVelocity z =
      shearFullScalar z • basisVec (2 : Fin 3) := by
    ext i
    by_cases hi : i = 2
    · subst i
      simp [shearCounterexampleVelocity, basisVec_apply]
    · simp [shearCounterexampleVelocity, basisVec_apply, hi]
  rw [hform, norm_smul]
  simp [basisVec, Pi.norm_single]

private theorem shearDuNorm_le_gradientNormSum (z : ParabolicPoint) :
    ‖shearCounterexampleDu z‖ ≤
      ‖shearFullGradient 0 z‖ + ‖shearFullGradient 1 z‖ := by
  have houter : ‖shearCounterexampleDu z‖ ≤
      ∑ i : Fin 3, ‖shearCounterexampleDu z i‖ := by
    rw [Pi.norm_def]
    have hsup : (Finset.univ.sup fun i : Fin 3 =>
        ‖shearCounterexampleDu z i‖₊) ≤
        ∑ i : Fin 3, ‖shearCounterexampleDu z i‖₊ := by
      apply Finset.sup_le
      intro i hi
      exact Finset.single_le_sum
        (f := fun j : Fin 3 => ‖shearCounterexampleDu z j‖₊)
        (s := Finset.univ) (fun j hj => bot_le) (Finset.mem_univ i)
    exact_mod_cast hsup
  have hrow2 : ‖shearCounterexampleDu z 2‖ ≤
      ‖shearFullGradient 0 z‖ + ‖shearFullGradient 1 z‖ := by
    rw [Pi.norm_def]
    have hsup : (Finset.univ.sup fun j : Fin 3 =>
        ‖shearCounterexampleDu z 2 j‖₊) ≤
        ∑ j : Fin 3, ‖shearCounterexampleDu z 2 j‖₊ := by
      apply Finset.sup_le
      intro j hj
      exact Finset.single_le_sum
        (f := fun k : Fin 3 => ‖shearCounterexampleDu z 2 k‖₊)
        (s := Finset.univ) (fun k hk => bot_le) (Finset.mem_univ j)
    have hcast : (↑(∑ j : Fin 3, ‖shearCounterexampleDu z 2 j‖₊) : ℝ) =
        ‖shearFullGradient 0 z‖ + ‖shearFullGradient 1 z‖ := by
      simp only [NNReal.coe_sum]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp [shearCounterexampleDu, shearFullGradient]
    calc
      ‖shearCounterexampleDu z 2‖ =
          ↑(Finset.univ.sup fun j : Fin 3 =>
            ‖shearCounterexampleDu z 2 j‖₊) := by rw [Pi.norm_def]
      _ ≤ ↑(∑ j : Fin 3, ‖shearCounterexampleDu z 2 j‖₊) := by
        exact_mod_cast hsup
      _ = ‖shearFullGradient 0 z‖ + ‖shearFullGradient 1 z‖ := hcast
  have hrows : ∑ i : Fin 3, ‖shearCounterexampleDu z i‖ =
      ‖shearCounterexampleDu z 2‖ := by
    apply Finset.sum_eq_single 2
    · intro i _hi hne
      by_cases h : i = 2
      · exact (hne h).elim
      · have hzero : shearCounterexampleDu z i = 0 := by
          funext j
          simp [shearCounterexampleDu, h]
        rw [hzero]
        simp
    · simp
  calc
    ‖shearCounterexampleDu z‖ ≤
        ∑ i : Fin 3, ‖shearCounterexampleDu z i‖ := houter
    _ = ‖shearCounterexampleDu z 2‖ := hrows
    _ ≤ ‖shearFullGradient 0 z‖ + ‖shearFullGradient 1 z‖ := hrow2

theorem shearCounterexampleVelocity_memLp_on_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    MemLp shearCounterexampleVelocity 2
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hs : MemLp shearFullScalar 2 (volume.restrict (spaceTimeSet Ω' J)) :=
    shearFullScalar_memLp_on_localBox shearReducedBumpSeries_memLp hbox
  have hmeas := shearCounterexampleVelocity_measurable.aestronglyMeasurable
    (μ := volume.restrict (spaceTimeSet Ω' J))
  exact hs.mono hmeas (Filter.Eventually.of_forall shearVecNorm_le_scalarNorm)

theorem shearCounterexampleDu_memLp_on_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    MemLp shearCounterexampleDu 2
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have h0 : MemLp (shearFullGradient 0) 2
      (volume.restrict (spaceTimeSet Ω' J)) := shearFullGradient_memLp_on_localBox hbox
  have h1 : MemLp (shearFullGradient 1) 2
      (volume.restrict (spaceTimeSet Ω' J)) := shearFullGradient_memLp_on_localBox hbox
  have h0' : MemLp (fun z => ‖shearFullGradient 0 z‖) 2
      (volume.restrict (spaceTimeSet Ω' J)) := h0.norm
  have h1' : MemLp (fun z => ‖shearFullGradient 1 z‖) 2
      (volume.restrict (spaceTimeSet Ω' J)) := h1.norm
  have hmajor : MemLp (fun z => ‖shearFullGradient 0 z‖ +
      ‖shearFullGradient 1 z‖) 2
      (volume.restrict (spaceTimeSet Ω' J)) := h0'.add h1'
  have hmeas := shearCounterexampleDu_measurable.aestronglyMeasurable
    (μ := volume.restrict (spaceTimeSet Ω' J))
  have hb : ∀ᵐ z ∂volume.restrict (spaceTimeSet Ω' J),
      ‖shearCounterexampleDu z‖ ≤
        ‖(fun y => ‖shearFullGradient 0 y‖ + ‖shearFullGradient 1 y‖) z‖ := by
    filter_upwards [] with z
    have ht := shearDuNorm_le_gradientNormSum z
    have hn : 0 ≤ ‖shearFullGradient 0 z‖ + ‖shearFullGradient 1 z‖ := by positivity
    calc
      ‖shearCounterexampleDu z‖ ≤
          ‖shearFullGradient 0 z‖ + ‖shearFullGradient 1 z‖ := ht
      _ = ‖‖shearFullGradient 0 z‖ + ‖shearFullGradient 1 z‖‖ := by
        exact (Real.norm_of_nonneg hn).symm
  exact hmajor.mono hmeas hb

theorem shearCounterexamplePressure_memLp_on_localBox
    {Ω' : Set Vec3} {J : Set ℝ} :
    MemLp shearCounterexamplePressure (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
  change MemLp (fun _ : ParabolicPoint => (0 : ℝ))
    (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet Ω' J))
  rw [memLp_const_iff (by norm_num) (by norm_num)]
  exact Or.inl rfl

theorem shearCounterexampleForce_memLp_on_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    MemLp shearCounterexampleForce 2
      (volume.restrict (spaceTimeSet Ω' J)) := by
  have hs : MemLp shearFullForceScalar 2
      (volume.restrict (spaceTimeSet Ω' J)) :=
    shearFullForceScalar_memLp_on_localBox hbox
  have hmeas := shearCounterexampleForce_measurable.aestronglyMeasurable
    (μ := volume.restrict (spaceTimeSet Ω' J))
  have hb : ∀ z : ParabolicPoint, ‖shearCounterexampleForce z‖ ≤
      ‖shearFullForceScalar z‖ := by
    intro z
    have hform : shearCounterexampleForce z =
        shearFullForceScalar z • basisVec (2 : Fin 3) := by
      ext i
      by_cases hi : i = 2
      · subst i
        simp [shearCounterexampleForce, basisVec_apply]
      · simp [shearCounterexampleForce, basisVec_apply, hi]
    rw [hform, norm_smul]
    simp [basisVec, Pi.norm_single]
  exact hs.mono hmeas (Filter.Eventually.of_forall hb)

theorem shearCounterexampleForce_localVecLp_on_localBox
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    localVecLp (spaceTimeSet Ω' J) 2 shearCounterexampleForce := by
  intro i
  unfold localLp
  by_cases hi : i = 2
  · subst i
    have hs := shearFullForceScalar_memLp_on_localBox hbox
    have heq : (fun z => shearCounterexampleForce z 2) =
        shearFullForceScalar := by
      funext z
      simp [shearCounterexampleForce]
    simpa [localLp, heq] using hs
  · have hzero : (fun z => shearCounterexampleForce z i) =ᵐ[
        volume.restrict (spaceTimeSet Ω' J)] (fun _ => (0 : ℝ)) := by
      filter_upwards [] with z
      simp [shearCounterexampleForce, hi]
    exact (memLp_congr_ae hzero).2 (by simp)

end CKN
