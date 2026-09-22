-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.LocalTestBox
import CKN.Setting.Examples.ShearCounterexample.SWSLocalData
import CKN.Setting.Examples.ShearCounterexample.TestSupport
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # An integrable majorant for the shear momentum residual. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
open scoped ENNReal
namespace CKN

private theorem shear_spaceTime_restrict_finite {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) := by
  let K : Set ParabolicPoint :=
    parabolicHomeomorph ⁻¹' (closure Ω' ×ˢ closure J)
  have hK : IsCompact K :=
    parabolicHomeomorph.isCompact_preimage.2 (hbox.2.1.prod hbox.2.2.2.2.1)
  have hKtop : volume K < ⊤ := by
    change (volume : Measure (Vec3 × ℝ)) (closure Ω' ×ˢ closure J) < ⊤
    exact (hbox.2.1.prod hbox.2.2.2.2.1).measure_lt_top
  have hsub : spaceTimeSet Ω' J ⊆ K := by
    intro z hz
    change z.1 ∈ closure Ω' ∧ z.2 ∈ closure J
    exact ⟨subset_closure hz.1, subset_closure hz.2⟩
  exact isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono hsub) hKtop).ne

theorem shear_localBox_volume_restrict_finite {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J) :
    IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) :=
  shear_spaceTime_restrict_finite hbox

private def momentumTestValue (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : ℝ := φ z 2
private def momentumTestTime (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : ℝ :=
  timePartial (fun w => φ w 2) z
private def momentumTestSpace (φ : Vec3 × ℝ → Vec3) (i : Fin 3)
    (z : Vec3 × ℝ) : ℝ := spatialPartial (fun w => φ w 2) i z

def shearMomentumMajorant (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : ℝ :=
  |shearFullScalar z| * |momentumTestTime φ z| +
    |shearFullScalar z| ^ 2 * |momentumTestSpace φ 2 z| +
    |shearFullGradient 0 z| * |momentumTestSpace φ 0 z| +
    |shearFullGradient 1 z| * |momentumTestSpace φ 1 z| +
    |shearFullForceScalar z| * |momentumTestValue φ z|

private theorem momentumMajorant_integrable {Ω' : Set Vec3} {J : Set ℝ}
    [IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J))]
    [hOpen : OpensMeasurableSpace (Vec3 × ℝ)]
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    Integrable (shearMomentumMajorant φ)
      (volume.restrict (spaceTimeSet Ω' J)) := by
  let μ := volume.restrict (spaceTimeSet Ω' J)
  let P : Vec3 × ℝ → ℝ := fun z => φ z 2
  let PT : Vec3 × ℝ → ℝ := fun z => timePartial (fun w => φ w 2) z
  let P0 : Vec3 × ℝ → ℝ := fun z => spatialPartial (fun w => φ w 2) 0 z
  let P1 : Vec3 × ℝ → ℝ := fun z => spatialPartial (fun w => φ w 2) 1 z
  let P2 : Vec3 × ℝ → ℝ := fun z => spatialPartial (fun w => φ w 2) 2 z
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := by
    dsimp [P]
    exact component_contDiff hφ 2
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact component_hasCompactSupport hφc 2
  have hPTc : ContDiff ℝ (⊤ : ℕ∞) PT := by
    dsimp [PT]
    exact timePartial_contDiff hP
  have hPTsupp : HasCompactSupport PT := by
    dsimp [PT]
    exact timePartial_hasCompactSupport hP hPc
  have hP0c : ContDiff ℝ (⊤ : ℕ∞) P0 := by
    dsimp [P0]
    exact spatialPartial_contDiff hP 0
  have hP0supp : HasCompactSupport P0 := by
    dsimp [P0]
    exact spatialPartial_hasCompactSupport hP hPc 0
  have hP1c : ContDiff ℝ (⊤ : ℕ∞) P1 := by
    dsimp [P1]
    exact spatialPartial_contDiff hP 1
  have hP1supp : HasCompactSupport P1 := by
    dsimp [P1]
    exact spatialPartial_hasCompactSupport hP hPc 1
  have hP2c : ContDiff ℝ (⊤ : ℕ∞) P2 := by
    dsimp [P2]
    exact spatialPartial_contDiff hP 2
  have hP2supp : HasCompactSupport P2 := by
    dsimp [P2]
    exact spatialPartial_hasCompactSupport hP hPc 2
  have hPTtop : MemLp PT ⊤ μ := by
    exact @Continuous.memLp_top_of_hasCompactSupport ℝ _ (Vec3 × ℝ) _ _ hOpen PT
      hPTc.continuous hPTsupp μ
  have hP0top : MemLp P0 ⊤ μ := by
    exact @Continuous.memLp_top_of_hasCompactSupport ℝ _ (Vec3 × ℝ) _ _ hOpen P0
      hP0c.continuous hP0supp μ
  have hP1top : MemLp P1 ⊤ μ := by
    exact @Continuous.memLp_top_of_hasCompactSupport ℝ _ (Vec3 × ℝ) _ _ hOpen P1
      hP1c.continuous hP1supp μ
  have hP2top : MemLp P2 ⊤ μ := by
    exact @Continuous.memLp_top_of_hasCompactSupport ℝ _ (Vec3 × ℝ) _ _ hOpen P2
      hP2c.continuous hP2supp μ
  have hPtop : MemLp P ⊤ μ := by
    exact @Continuous.memLp_top_of_hasCompactSupport ℝ _ (Vec3 × ℝ) _ _ hOpen P
      hP.continuous hPc μ
  have hW3 : MemLp shearFullScalar 3 μ :=
    shearFullScalar_memLp_on_localBox shearReducedBumpSeries_memLp_three hbox
  have hW2 : MemLp shearFullScalar 2 μ := hW3.mono_exponent (by norm_num)
  have hWabs2 : MemLp (fun z => |shearFullScalar z|) 2 μ := hW2.abs
  have hWsq1 : MemLp (fun z => |shearFullScalar z| ^ 2) 1 μ := by
    have hmul : MemLp
        (fun z => |shearFullScalar z| * |shearFullScalar z|) 1 μ :=
      hWabs2.mul hWabs2
    convert hmul using 1
    funext z
    ring
  have hG0 : MemLp (shearFullGradient 0) 2 μ :=
    shearFullGradient_memLp_on_localBox (i := 0) hbox
  have hG1 : MemLp (shearFullGradient 1) 2 μ :=
    shearFullGradient_memLp_on_localBox (i := 1) hbox
  have hF : MemLp shearFullForceScalar 2 μ :=
    shearFullForceScalar_memLp_on_localBox hbox
  have hA : Integrable (fun z => |shearFullScalar z| * |PT z|) μ := by
    apply MemLp.integrable (q := 2) (by norm_num)
    exact hWabs2.mul hPTtop.abs
  have hB : Integrable (fun z => |shearFullScalar z| ^ 2 * |P2 z|) μ := by
    apply MemLp.integrable (q := 1) (by norm_num)
    exact hWsq1.mul hP2top.abs
  have hC : Integrable (fun z => |shearFullGradient 0 z| * |P0 z|) μ := by
    apply MemLp.integrable (q := 2) (by norm_num)
    exact hG0.abs.mul hP0top.abs
  have hD : Integrable (fun z => |shearFullGradient 1 z| * |P1 z|) μ := by
    apply MemLp.integrable (q := 2) (by norm_num)
    exact hG1.abs.mul hP1top.abs
  have hE : Integrable (fun z => |shearFullForceScalar z| * |P z|) μ := by
    apply MemLp.integrable (q := 2) (by norm_num)
    exact hF.abs.mul hPtop.abs
  change Integrable (fun z => |shearFullScalar z| * |PT z| +
    |shearFullScalar z| ^ 2 * |P2 z| +
    |shearFullGradient 0 z| * |P0 z| +
    |shearFullGradient 1 z| * |P1 z| +
    |shearFullForceScalar z| * |P z|) μ
  exact (((hA.add hB).add hC).add hD).add hE

theorem shearMomentumMajorant_integrable_on_localBox {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 1) Ω' J)
    (φ : Vec3 × ℝ → Vec3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    Integrable (shearMomentumMajorant φ)
      (volume.restrict (spaceTimeSet Ω' J)) := by
  let hμ : IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) :=
    shear_spaceTime_restrict_finite hbox
  exact @momentumMajorant_integrable Ω' J hμ inferInstance hbox φ hφ hφc

end CKN
