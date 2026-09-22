-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.Lin34Slices
import CKN.Pressure.OscillationLin34
import CKN.Pressure.PkBoundsUnconditionalP234
import CKN.Pressure.PkBoundsUnconditionalP56
import CKN.Pressure.PkBoundsUnconditionalP8
import CKN.Setting.SliceNormBounds
import CKN.Setting.TimeHolder
import CKN.Foundation.Parabolic.Integration.Average

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN

private lemma inner_ball_subset_annulus_complement
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : y ∈ euclideanBall x₀ (13 * ρ / 20)) :
    y ∈ (euclideanBall x₀ (3 * ρ / 4) \
      euclideanClosedBall x₀ (13 * ρ / 20))ᶜ := by
  intro hyann
  apply hyann.2
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
  exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy).le

theorem pressure_harmonic_potential_data_ae_of_sws_inner
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      PressureHarmonicPotentialData
        (euclideanBall z.1 (13 * ρ / 20))
        (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p s := by
  have hdata := pressure_harmonic_potential_data_ae_of_sws_annulus
    hsol hρ hsub (fun y hy => pressure_cutoff_derivatives_vanish z.1 hρ hy)
  filter_upwards [hdata] with s hs
  refine
    { p2_integrable := hs.p2_integrable
      p2_compactSupport := hs.p2_compactSupport
      p2_vanishes := ?_
      p3_integrable := hs.p3_integrable
      p3_compactSupport := hs.p3_compactSupport
      p3_vanishes := ?_
      p4_integrable := hs.p4_integrable
      p4_compactSupport := hs.p4_compactSupport
      p4_vanishes := ?_
      p5_integrable := hs.p5_integrable
      p5_compactSupport := hs.p5_compactSupport
      p5_vanishes := ?_
      p6_integrable := hs.p6_integrable
      p6_compactSupport := hs.p6_compactSupport
      p6_vanishes := ?_ }
  · intro i j y hy
    exact hs.p2_vanishes i j y (inner_ball_subset_annulus_complement hρ hy)
  · intro i j y hy
    exact hs.p3_vanishes i j y (inner_ball_subset_annulus_complement hρ hy)
  · intro i j y hy
    exact hs.p4_vanishes i j y (inner_ball_subset_annulus_complement hρ hy)
  · intro y hy
    exact hs.p5_vanishes y (inner_ball_subset_annulus_complement hρ hy)
  · intro j y hy
    exact hs.p6_vanishes j y (inner_ball_subset_annulus_complement hρ hy)

theorem pressureD_eq_time_slice_integral
    {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hint : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ))
      (parabolicCylinder z.1 z.2 r) volume) :
    pressureD p z r =
      ∫ s in Ioc (z.2 - r ^ 2) z.2,
        r⁻¹ ^ 2 * ∫ x in vec3Ball z.1 r, |p (x, s)| ^ (3 / 2 : ℝ) := by
  unfold pressureD
  rw [integral_parabolicCylinder hint, integral_const_mul]

theorem pressureChat_eq_time_slice_integral
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ}
    (hint : IntegrableOn
      (fun w => vec3EuclideanNorm (meanFreeVec u z.1 r w.2 w.1) ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume) :
    pressureChat u z r =
      ∫ s in Ioc (z.2 - r ^ 2) z.2,
        r⁻¹ ^ 2 * ∫ x in vec3Ball z.1 r,
          vec3EuclideanNorm (meanFreeVec u z.1 r s x) ^ (3 : ℕ) := by
  unfold pressureChat
  rw [integral_parabolicCylinder hint, integral_const_mul]

end CKN
