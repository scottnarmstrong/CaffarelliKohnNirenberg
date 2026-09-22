-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.AdamsAEMeasurable
import CKN.Core.Endgame.BootstrapPotential
import CKN.Core.Step4.Bootstrap
import CKN.Core.Step4.BootstrapFaithfulPotential
import CKN.Core.Endgame.CarrierLocalAE
import CKN.Core.Endgame.CutoffDerivatives
import CKN.Core.Endgame.SourceComponents
import CKN.Core.Endgame.TheoremBCloser
import CKN.Core.Endgame.CompactBall
import CKN.Core.Step3.GradientSlotDuhamel
import CKN.Core.Step3.LocalizedEquationBasics
import CKN.Core.Step4.LocalizedEquationGradientData
import CKN.Core.Step4.LocalizedEquationGradientMeasurability
import CKN.Core.Step4.PointwisePotential
import CKN.Core.Step4.RouteAGradientProducerUniform
import CKN.Core.Step4.SourceMorreyGradientPackage
import CKN.Core.Step4.SourceMorreyKernels
import CKN.Core.Step4.SourceMorreyFirstRoundCutoff
import CKN.Core.Step4.SourceMorreyFirstRoundSupport
import CKN.Core.Step4.SourceMorreyData
import CKN.Core.Step4.WeakGradientGluingTCollarAssembly
import CKN.Core.Step4.WeakGradientGluingTRemainderMajorant
import CKN.Foundation.Parabolic.Morrey.AdamsM4
import CKN.Foundation.Parabolic.Morrey.BallVariants
import CKN.Foundation.Parabolic.Morrey.LowerBounds
import CKN.Foundation.Parabolic.Morrey.Neg
import CKN.Foundation.Parabolic.Morrey.VecMem

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3
open CKN.Core.Step4
open CKN.Core.Endgame

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4


/-! # Faithful statement of one bootstrap round

The proof combines local source estimates with a finite covering argument to
establish the arbitrary-exponent conclusion from the Step 2 data.
-/
set_option linter.style.haveILetI false in
private theorem bootstrap_local_round
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hq : 5 / 2 < q)
    {z : ParabolicPoint} {R τ : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z (2 * R) ⊆ spaceTimeSet Ω I)
    (hτlo : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    (hτ : 5 < τ)
    (hcond : 1 / (25 / 8 : ℝ) + 1 / τ > 2 / 5)
    (hU : morreyVecMem 3 τ (Metric.ball z R) u)
    (hDu : ∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z R) (fun w => Du w i)) :
    morreyVecMem 3 (bootstrapOutputExponent τ) (Metric.ball z (R / 4)) u := by
  let κ := bootstrapPressureExponent τ
  let θ := bootstrapDerivativeExponent τ
  let σ := bootstrapOutputExponent τ
  have hexp := bootstrap_exponent_facts hτ hcond
  rcases hexp with ⟨hτpos, hτtop, hκlo, hκlo', hκhi, hθlo, hθhi, hσlo⟩
  have hids := bootstrap_adams_exponent_identities hτ hcond
  have hκτ : κ ≤ τ := by
    dsimp [κ]
    have hκlt : bootstrapPressureExponent τ < 5 / 2 := hκhi
    linarith only [hκlt, hτlo]
  have hθτ : θ ≤ τ := by
    dsimp [θ]
    linarith only [hθhi, hτlo]
  have hκrecip : 1 / κ = 1 / τ + 8 / 25 := by
    simp [κ, bootstrapPressureExponent]
  have hθrecip : 1 / θ = 1 / τ + 3 / 25 := by
    simp [θ, bootstrapDerivativeExponent]
  obtain ⟨φ, hφ, hφrange, hφone, hφsupport, hbox, hφbox⟩ :=
    exists_first_round_cutoff hR hdom
  let Q : Set ParabolicPoint := Metric.ball z (R / 2)
  have hQeq : spaceTimeSet (vec3Ball z.1 (R / 2))
      (Ioo (z.2 - (R / 2) ^ 2) (z.2 + (R / 2) ^ 2)) = Q :=
    parabolic_box_eq_ball z (R / 2)
  have hQgeom : Q ⊆ parabolicCylinder z.1 (z.2 + (R / 2) ^ 2) R := by
    change Metric.ball z (R / 2) ⊆ _
    have hgeom := metricBall_subset_parabolicCylinder_doubled z
      (r := R / 2) (by positivity)
    simpa only [show 2 * (R / 2) = R by ring] using hgeom
  have hUQ : morreyVecMem 3 τ Q u :=
    CKN.Core.Endgame.morreyVecMem_mono_carrier (by norm_num)
      (Metric.ball_subset_ball (by linarith only [hR])) hU
  have hDuQ : ∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ) Q
      (fun w => Du w i) := fun i =>
    CKN.Core.Endgame.morreyVecMem_mono_carrier (by norm_num)
      (Metric.ball_subset_ball (by linarith only [hR])) (hDu i)
  obtain ⟨Dp, hDpAE, hDpWeak, hDpN⟩ :=
    bootstrap_routeA_uniform q τ hq hτlo hτhi hsol z R hR hdom hU hDu
  have hκq : κ < q := lt_trans hκhi hq
  have hκq' : (1 / τ + 8 / 25)⁻¹ < q := by
    simpa [κ, bootstrapPressureExponent] using hκq
  have hDpN'' : morreyVecMem (6 / 5 : ℝ)
      ((1 / τ + 8 / 25)⁻¹) (Metric.ball z (R / 2)) Dp := by
    rw [min_eq_left hκq'.le] at hDpN
    exact hDpN
  have hDpN' : morreyVecMem (6 / 5 : ℝ) κ Q Dp := by
    simpa only [Q, κ, bootstrapPressureExponent] using hDpN''
  have hforceRaw (i : Fin 3) : morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun w => φ w * f w i) < ⊤ :=
    localized_gradient_force_morrey_of_sws hsol hφ hbox hφbox i
  have hκ25 : κ ≤ 25 / 9 := by
    have hlt : (5 / 2 : ℝ) < 25 / 9 := by norm_num
    exact le_trans (le_of_lt hκhi) hlt.le
  have hκmin : κ ≤ min q (25 / 9 : ℝ) := le_min hκq.le hκ25
  have hminlo : 6 / 5 ≤ min q (25 / 9 : ℝ) := by
    apply le_min
    · linarith only [hq]
    · norm_num
  have hDpAEBox : ∀ i : Fin 3, AEMeasurable (fun w => Dp w i)
      (volume.restrict (spaceTimeSet (vec3Ball z.1 (R / 2))
        (Ioo (z.2 - (R / 2) ^ 2) (z.2 + (R / 2) ^ 2)))) := by
    intro i
    simpa only [hQeq] using hDpAE i
  have hsourceAE := localized_gradient_source_aemeasurable_of_sws
    hsol hφ hbox hφbox hDpAEBox
  letI : IsFiniteMeasure (volume.restrict Q) := by
    rw [← hQeq]
    exact CKN.Core.Step3.local_box_isFiniteMeasure
      hbox.2.1 hbox.2.2.2.2.1
  have hDpInt (i : Fin 3) : Integrable (fun w => Dp w i)
      (volume.restrict Q) :=
    bootstrap_integrable_of_ball_morrey (by positivity) (hDpAE i) (hDpN' i)
  have hDpIntBox : ∀ i : Fin 3, Integrable (fun w => Dp w i)
      (volume.restrict (spaceTimeSet (vec3Ball z.1 (R / 2))
        (Ioo (z.2 - (R / 2) ^ 2) (z.2 + (R / 2) ^ 2)))) := by
    intro i
    simpa only [hQeq] using hDpInt i
  have hDpWeakBox : ∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport ψ ⊆ vec3Ball z.1 (R / 2) ×ˢ
        Ioo (z.2 - (R / 2) ^ 2) (z.2 + (R / 2) ^ 2) →
      (∫ w : ParabolicPoint, p w * spatialPartial ψ i w) =
        -(∫ w : ParabolicPoint, Dp w i * ψ w) := by
    intro i ψ hψ hψsupport
    exact hDpWeak i ψ hψ (hψsupport.trans
      (parabolic_box_subset_ball_preimage z (R / 2)))
  have hrepHeat := localized_gradient_slot_duhamel_of_sws
    hsol hφ hbox hφbox hDpIntBox hDpWeakBox
  let g : ParabolicPoint → Vec3 := fun w i =>
    localizedGradientSourceG φ u Du f Dp w i
  let H : Fin 3 → ParabolicPoint → Vec3 := fun j w i =>
    localizedGradientSourceH φ u j w i
  let h : Fin 3 → ParabolicPoint → Vec3 := fun j w i => -H j w i
  have hrep : localizedVelocity φ u =ᵐ[volume] duhamelPotential g h := by
    filter_upwards [hrepHeat] with w hw
    change localizedVelocity φ u w = vectorHeatPotential g H w at hw
    have hsign := vectorHeatPotential_eq_duhamelPotential_neg w (F := g) (G := H)
    have hneg : (fun j v => -H j v) = h := by
      funext j v i
      rfl
    calc
      localizedVelocity φ u w = vectorHeatPotential g H w := hw
      _ = duhamelPotential g h w := by rw [← hneg]; exact hsign
  rcases hsol with ⟨_, _, _, _, _, hdata, _, _, _⟩
  let J : Set ℝ := Ioo (z.2 - R ^ 2) (z.2 + R ^ 2)
  have hboxOuter : localBox Ω I (vec3Ball z.1 R) J :=
    localBox_of_parabolic_ball hR hdom
  have hOuterEq : spaceTimeSet (vec3Ball z.1 R) J = Metric.ball z R := by
    simpa only [J] using parabolic_box_eq_ball z R
  obtain ⟨huLocal, hDuLocal, _, hfLocal, _, _, _, _, _⟩ :=
    hdata (vec3Ball z.1 R) J hboxOuter
  have hQsubOuter : Q ⊆ Metric.ball z R :=
    Metric.ball_subset_ball (by linarith only [hR])
  have huAE (i : Fin 3) : AEMeasurable
      (Q.indicator (fun w => u w i)) volume := by
    apply (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
    have houter := aemeasurable_pi_iff.mp huLocal.aemeasurable i
    have houter' : AEMeasurable (fun w => u w i)
        (volume.restrict (Metric.ball z R)) := by simpa only [hOuterEq] using houter
    exact houter'.mono_measure (Measure.restrict_mono hQsubOuter le_rfl)
  have hDuAE (i j : Fin 3) : AEMeasurable
      (Q.indicator (fun w => Du w i j)) volume := by
    apply (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
    have houter := aemeasurable_pi_iff.mp
      (aemeasurable_pi_iff.mp hDuLocal.aemeasurable i) j
    have houter' : AEMeasurable (fun w => Du w i j)
        (volume.restrict (Metric.ball z R)) := by simpa only [hOuterEq] using houter
    exact houter'.mono_measure (Measure.restrict_mono hQsubOuter le_rfl)
  have hfAE (i : Fin 3) : AEMeasurable
      (Q.indicator (fun w => f w i)) volume := by
    apply (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
    have houter := aemeasurable_pi_iff.mp hfLocal.aemeasurable i
    have houter' : AEMeasurable (fun w => f w i)
        (volume.restrict (Metric.ball z R)) := by simpa only [hOuterEq] using houter
    exact houter'.mono_measure (Measure.restrict_mono hQsubOuter le_rfl)
  have hφae : AEMeasurable φ volume :=
    (hφ.1.continuous.comp continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have htimeae : AEMeasurable (fun w => timePartial φ w) volume :=
    (timePartial_contDiff_full hφ.1).continuous.comp
      continuous_parabolicPoint_to_prod |>.measurable.aemeasurable
  have hlapae : AEMeasurable (fun w : ParabolicPoint =>
      spatialLaplacian (fun x => φ (x, w.2)) w.1) volume := by
    change AEMeasurable (fun w : ParabolicPoint =>
      ∑ j : Fin 3, spatialSecondPartial
        (show ParabolicPoint → ℝ from φ) j j w) volume
    exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun j _ =>
      (spatialSecondPartial_contDiff_full hφ.1 j j).continuous.comp
        continuous_parabolicPoint_to_prod |>.measurable.aemeasurable)
  obtain ⟨C, hC, hcoeff⟩ := exists_cutoff_derivative_bound hφ.1 hφ.2.1
  have hnotφ (w : ParabolicPoint) (hw : w ∉ Q) :
      (w.1, w.2) ∉ tsupport φ := by
    intro hs
    have hs' := hφsupport hs
    change w ∈ Metric.ball z (3 * R / 8) at hs'
    exact hw (Metric.ball_subset_ball (by linarith only [hR]) hs')
  have hφzero (w : ParabolicPoint) (hw : w ∉ Q) : φ w = 0 := by
    change φ (w.1, w.2) = 0
    exact image_eq_zero_of_notMem_tsupport (hnotφ w hw)
  have htimezero (w : ParabolicPoint) (hw : w ∉ Q) : timePartial φ w = 0 :=
    timePartial_zero_of_not_mem_tsupport_public hφ.1 (hnotφ w hw)
  have hlapzero (w : ParabolicPoint) (hw : w ∉ Q) :
      spatialLaplacian (fun x => φ (x, w.2)) w.1 = 0 := by
    change (∑ j : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from φ) j j w) = 0
    exact Finset.sum_eq_zero (fun j _ =>
      spatialSecondPartial_zero_of_not_mem_tsupport_public hφ.1 (hnotφ w hw) j j)
  have hspzero (j : Fin 3) (w : ParabolicPoint) (hw : w ∉ Q) :
      spatialPartial φ j w = 0 :=
    spatialPartial_zero_of_not_mem_tsupport_public hφ.1 (hnotφ w hw) j
  have hφbound (w : ParabolicPoint) : |φ w| ≤ C := (hcoeff (w.1, w.2)).1
  have htimebound (w : ParabolicPoint) : |timePartial φ w| ≤ C := by
    simpa only [timePartial] using (hcoeff (w.1, w.2)).2.1
  have hlapbound (w : ParabolicPoint) :
      |spatialLaplacian (fun x => φ (x, w.2)) w.1| ≤ C :=
    (hcoeff (w.1, w.2)).2.2.2
  have hspbound (j : Fin 3) (w : Vec3 × ℝ) :
      |spatialPartial φ j w| ≤ C := (hcoeff w).2.2.1 j
  have hforceAE (i : Fin 3) : AEMeasurable
      (fun w => φ w * f w i) volume := by
    have h : AEMeasurable
        (fun w => φ w * Q.indicator (fun v => f v i) w) volume := hφae.mul (hfAE i)
    have heq : (fun w => φ w * f w i) =
        (fun w => φ w * Q.indicator (fun v => f v i) w) := by
      funext w
      by_cases hw : w ∈ Q
      · change w ∈ Metric.ball z (R / 2) at hw
        have hval : (Metric.ball z (R / 2)).indicator
            (fun v => f v i) w = f w i := Set.indicator_of_mem hw _
        exact congrArg (fun a : ℝ => φ w * a) hval.symm
      · have hφw := hφzero w hw
        change w ∉ Metric.ball z (R / 2) at hw
        have hval : (Metric.ball z (R / 2)).indicator
            (fun v => f v i) w = 0 := Set.indicator_of_notMem hw _
        calc
          φ w * f w i = 0 := by rw [hφw]; simp
          _ = φ w * (Metric.ball z (R / 2)).indicator
              (fun v => f v i) w := by rw [hval, hφw]; simp
    rw [heq]
    exact h
  have hforce (i : Fin 3) : morreyNorm (6 / 5 : ℝ) κ
      (fun w => φ w * f w i) < ⊤ := by
    apply morreyNorm_lt_top_of_lower_exponents (P := (6 / 5 : ℝ))
      (P₀ := (6 / 5 : ℝ)) (θ := κ) (θ₀ := min q (25 / 9 : ℝ))
      (B := Q) (z₀ := (z.1, z.2 + (R / 2) ^ 2)) (R := R)
      (by norm_num) (by norm_num) hminlo hκlo hκmin hR hQgeom
      (hforceAE i) (fun w hw => by rw [hφzero w hw]; simp) (hforceRaw i)
  have hUindicatorNorm (i : Fin 3) : morreyNorm 3 τ
      (Q.indicator (fun w => u w i)) < ⊤ :=
    (morreyNorm_le_morreyBallNorm (by norm_num)
      (by linarith only [hτlo]) (Q.indicator (fun w => u w i))).trans_lt (hUQ i)
  have hDindicatorNorm (i j : Fin 3) : morreyNorm 2 (25 / 8 : ℝ)
      (Q.indicator (fun w => Du w i j)) < ⊤ :=
    (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num)
      (Q.indicator (fun w => Du w i j))).trans_lt (hDuQ i j)
  have hsourceNorm := bootstrap_source_bounds
    (τ := τ) (κ := κ) (θ := θ) (C := C) (R₀ := R)
    (z₀ := (z.1, z.2 + (R / 2) ^ 2)) (Q := Q) (φ := φ) (u := u)
    (Du := Du) (f := f) (Dp := Dp) hκlo (by linarith only [hτlo]) hκτ hθlo.le hθτ hκrecip
    hC huAE hDuAE hDindicatorNorm hUindicatorNorm hR hQgeom hφbound hφae
    htimeae hlapae (fun i =>
      (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr (hDpAE i))
    hforceAE hforce hφzero htimebound hlapbound hspbound htimezero hlapzero
    (fun j w hw => hspzero j w hw) (fun i =>
      (morreyNorm_le_morreyBallNorm (by norm_num)
        (by linarith only [hκlo])
        (Q.indicator (fun w => Dp w i))).trans_lt (hDpN' i))
  rcases hsourceAE with ⟨hgAE, hhAE⟩
  have hgNorm : morreyNorm (6 / 5 : ℝ) κ
      (fun w => vec3EuclideanNorm (g w)) < ⊤ :=
    CKN.Core.Endgame.morrey_norm_euclidean_lt_top_of_components
      (by norm_num) (fun i => by simpa [g] using hgAE i) hsourceNorm.1
  have hhNorm : ∀ j : Fin 3, morreyNorm 3 θ
      (fun w => vec3EuclideanNorm (h j w)) < ⊤ := by
    intro j
    apply CKN.Core.Endgame.morrey_norm_euclidean_lt_top_of_components (by norm_num)
    · intro i
      simpa [h, H] using hhAE j i
    · exact hsourceNorm.2 j
  have hGzero (w : ParabolicPoint) (hw : w ∉ Q) : g w = 0 := by
    funext i
    simp [g, localizedGradientSourceG, localizedEquationG, localizedConvection,
      hφzero w hw, htimezero w hw, hlapzero w hw]
  have hHzero (j : Fin 3) (w : ParabolicPoint) (hw : w ∉ Q) : h j w = 0 := by
    funext i
    simp [h, H, localizedGradientSourceH, localizedEquationH, hspzero j w hw]
  have hgSupport : ∀ w ∉ parabolicCylinder z.1 (z.2 + (R / 2) ^ 2) R,
      vec3EuclideanNorm (g w) = 0 := by
    intro w hw
    have hzero := hGzero w (by
      intro hmem
      exact hw (hQgeom hmem))
    rw [hzero, vec3EuclideanNorm_zero]
  have hhSupport : ∀ j w,
      w ∉ parabolicCylinder z.1 (z.2 + (R / 2) ^ 2) R →
        vec3EuclideanNorm (h j w) = 0 := by
    intro j w hw
    have hzero := hHzero j w (by
      intro hmem
      exact hw (hQgeom hmem))
    rw [hzero, vec3EuclideanNorm_zero]
  have hgEuclideanAE : AEMeasurable
      (fun w => vec3EuclideanNorm (g w)) volume :=
    aemeasurable_euclidean_norm_of_components (fun i => by simpa [g] using hgAE i)
  have hhEuclideanAE (j : Fin 3) : AEMeasurable
      (fun w => vec3EuclideanNorm (h j w)) volume :=
    aemeasurable_euclidean_norm_of_components (fun i => by
      simpa [h, H] using hhAE j i)
  have hgRiesz := CKN.Core.Endgame.riesz_potential_ae_lt_top_of_aemeasurable_morrey
    (β := (2 : ℝ)) (P := (6 / 5 : ℝ)) (τ := κ) (R := R)
    (z₀ := (z.1, z.2 + (R / 2) ^ 2))
    (by norm_num) (by norm_num) hκlo (by nlinarith only [hκhi]) hR
    hgEuclideanAE hgNorm hgSupport
  have hhRiesz (j : Fin 3) :=
    CKN.Core.Endgame.riesz_potential_ae_lt_top_of_aemeasurable_morrey
      (β := (1 : ℝ)) (P := (3 : ℝ)) (τ := θ) (R := R)
      (z₀ := (z.1, z.2 + (R / 2) ^ 2))
      (by norm_num) (by norm_num) hθlo.le (by simpa using hθhi) hR
      (hhEuclideanAE j) (hhNorm j) (hhSupport j)
  have hpotentialNorm := bootstrap_pointwise_majorant_finite
    (κ := κ) (θ := θ) (σ := σ) (by linarith only [hκlo']) hκhi
    hθlo.le hθhi (by simpa [κ, θ, σ] using hids.1)
    (by simpa [κ, θ, σ] using hids.2)
    (fun i => by simpa [g] using hgAE i)
    (fun j i => by simpa [h, H] using hhAE j i) hgNorm hhNorm
  have hpoint := pointwisePotentialBound_ae
    (fun i => by simpa [g] using hgAE i)
    (fun j i => by simpa [h, H] using hhAE j i)
    hgEuclideanAE hhEuclideanAE hgRiesz hhRiesz hrep
  have hmajorNonneg (w : ParabolicPoint) :
      0 ≤ pointwisePotentialMajorant g h w := by
    unfold pointwisePotentialMajorant
    positivity
  have hvelocityNorm (i : Fin 3) :
      morreyNorm 3 σ (fun w => localizedVelocity φ u w i) < ⊤ := by
    apply (routeA_morreyNorm_mono_ae (by norm_num : (0 : ℝ) ≤ 3) ?_).trans_lt
      hpotentialNorm
    filter_upwards [hpoint] with w hw
    calc
      |localizedVelocity φ u w i| ≤ vec3EuclideanNorm (localizedVelocity φ u w) :=
        bootstrap_component_le_norm _ _
      _ ≤ pointwisePotentialMajorant g h w := hw
      _ = |pointwisePotentialMajorant g h w| :=
        (abs_of_nonneg (hmajorNonneg w)).symm
  have hlocal : u =ᵐ[volume.restrict (Metric.ball z (R / 4))]
      localizedVelocity φ u := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with w hw
    have hone := hφone w hw
    symm
    change φ (w.1, w.2) • u w = u w
    rw [hone, one_smul]
  exact CKN.Core.Endgame.morreyVecMem_of_ae_eq_restrict
    (by norm_num) (by linarith only [hσlo])
    Metric.isOpen_ball.measurableSet hlocal hvelocityNorm

private theorem bootstrap_finite_cover_morrey
    {P κ : ℝ} (hP : 1 ≤ P) {K : Set ParabolicPoint}
    {D : ParabolicPoint → ℝ} (hD : AEMeasurable D volume)
    {ι : Type*} (s : Finset ι) (U : ι → Set ParabolicPoint)
    (hU : ∀ a ∈ s, MeasurableSet (U a))
    (hcover : K ⊆ ⋃ a ∈ s, U a)
    (hN : ∀ a ∈ s, morreyNorm P κ ((U a).indicator D) < ⊤) :
    morreyNorm P κ (K.indicator D) < ⊤ := by
  classical
  let Dm := hD.mk D
  have hDm : Measurable Dm := hD.measurable_mk
  have hDeq : D =ᵐ[volume] Dm := hD.ae_eq_mk
  have hNmeas (a : ι) (ha : a ∈ s) :
      morreyNorm P κ ((U a).indicator Dm) < ⊤ := by
    have hEq : (U a).indicator D =ᵐ[volume] (U a).indicator Dm := by
      filter_upwards [hDeq] with w hw
      by_cases hwa : w ∈ U a <;> simp [hwa, hw]
    rw [← CKN.Core.Endgame.morreyNorm_eq_of_ae_eq hEq]
    exact hN a ha
  have hsum : morreyNorm P κ
      (fun w => ∑ a ∈ s, |(U a).indicator Dm w|) < ⊤ := by
    apply finite_sum_morreyNorm_lt_top hP s
      (fun a ha => by
        simpa only [Real.norm_eq_abs] using (hDm.indicator (hU a ha)).norm)
    intro a ha
    rw [morreyNorm_abs]
    exact hNmeas a ha
  have hpoint : ∀ᵐ w ∂(volume : Measure ParabolicPoint),
      |K.indicator D w| ≤ abs (∑ a ∈ s, abs ((U a).indicator Dm w)) := by
    filter_upwards [hDeq] with w hwD
    have hsumNonneg : 0 ≤ ∑ a ∈ s, |(U a).indicator Dm w| :=
      Finset.sum_nonneg (fun a _ => abs_nonneg _)
    by_cases hwK : w ∈ K
    · obtain ⟨a, ha, hwa⟩ := mem_iUnion₂.mp (hcover hwK)
      rw [indicator_of_mem hwK, abs_of_nonneg hsumNonneg]
      have hterm : (U a).indicator Dm w = Dm w := indicator_of_mem hwa _
      calc
        |D w| = |(U a).indicator Dm w| := by rw [hwD, hterm]
        _ ≤ ∑ b ∈ s, |(U b).indicator Dm w| :=
          Finset.single_le_sum (f := fun b => |(U b).indicator Dm w|)
            (fun _ _ => abs_nonneg _) ha
    · rw [indicator_of_notMem hwK, abs_zero, abs_of_nonneg hsumNonneg]
      exact hsumNonneg
  exact (routeA_morreyNorm_mono_ae (le_trans zero_le_one hP) hpoint).trans_lt hsum

/-- One arbitrary-exponent bootstrap round from the Step 2 Morrey data. -/
theorem bootstrap_round_of_step2
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (r₂ r₃ : ℝ)
    (hr₂ : 0 < r₂) (hr₃ : 0 < r₃) (hr₃₂ : r₃ < r₂ / 4)
    (hdom : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hq : 5 / 2 < q)
    (hStep2 : Step2MorreySources
      (Q₂ := Metric.ball z₀ (r₂ / 4)) (u := u) (Du := Du) (p := p))
    (τ : ℝ) (hτ : 5 < τ)
    (huτ : CKN.morreyVecMem 3 τ (Metric.ball z₀ (r₂ / 4)) u)
    (hcond : 1 / (25 / 8 : ℝ) + 1 / τ > 2 / 5) :
    ∃ varsigma : ℝ,
      1 / varsigma = 1 / τ - ((1 / 5 : ℝ) - 1 / (25 / 3 : ℝ)) ∧
      CKN.morreyVecMem 3 varsigma (Metric.ball z₀ r₃) u := by
  obtain ⟨hτpos, hτtop, _, _, _, _, _, hσlo⟩ :=
    bootstrap_exponent_facts hτ hcond
  have hgainpos : 0 < 1 / τ - 2 / 25 := by
    have hrecip : 2 / 25 < 1 / τ := by
      norm_num at hcond ⊢
      linarith only [hcond]
    linarith only [hrecip]
  refine ⟨bootstrapOutputExponent τ, ?_, ?_⟩
  · calc
      1 / bootstrapOutputExponent τ = 1 / τ - 2 / 25 := by
        simp [bootstrapOutputExponent]
      _ = 1 / τ - ((1 / 5 : ℝ) - 1 / (25 / 3 : ℝ)) := by norm_num
  let Q₂ : Set ParabolicPoint := Metric.ball z₀ (r₂ / 4)
  let Q₃ : Set ParabolicPoint := Metric.ball z₀ r₃
  let J₂ : Set ℝ := Ioo (z₀.2 - r₂ ^ 2) (z₀.2 + r₂ ^ 2)
  have hbox₂ : localBox Ω I (vec3Ball z₀.1 r₂) J₂ := by
    simpa only [J₂] using localBox_of_parabolic_ball hr₂ hdom
  have houterEq : spaceTimeSet (vec3Ball z₀.1 r₂) J₂ = Metric.ball z₀ r₂ := by
    simpa only [J₂] using parabolic_box_eq_ball z₀ r₂
  have hdata₂ := hsol.2.2.2.2.2.1 (vec3Ball z₀.1 r₂) J₂ hbox₂
  have huOuterAE (i : Fin 3) : AEMeasurable (fun w => u w i)
      (volume.restrict (Metric.ball z₀ r₂)) := by
    have h := aemeasurable_pi_iff.mp hdata₂.1.aemeasurable i
    simpa only [houterEq] using h
  have hQ₂sub : Q₂ ⊆ Metric.ball z₀ r₂ :=
    Metric.ball_subset_ball (by linarith only [hr₂])
  have huQ₂AE (i : Fin 3) : AEMeasurable
      (Q₂.indicator (fun w => u w i)) volume := by
    apply (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
    exact (huOuterAE i).mono_measure (Measure.restrict_mono hQ₂sub le_rfl)
  let τin : ℝ := max τ (25 / 3)
  have hτinlo : 25 / 3 ≤ τin := le_max_right _ _
  have hτinhi : τin ≤ 25 := max_le
    (le_trans hτtop.le (by norm_num : (25 / 2 : ℝ) ≤ 25)) (by norm_num)
  have hτin : 5 < τin := lt_of_lt_of_le (by norm_num) hτinlo
  have hτincond : 1 / (25 / 8 : ℝ) + 1 / τin > 2 / 5 := by
    by_cases hbase : 25 / 3 ≤ τ
    · have heq : τin = τ := by simp [τin, max_eq_left hbase]
      simpa only [heq] using hcond
    · have heq : τin = 25 / 3 := by
        dsimp [τin]
        exact max_eq_right (le_of_not_ge hbase)
      rw [heq]
      norm_num
  have hUinQ₂ : morreyVecMem 3 τin Q₂ u := by
    by_cases hbase : 25 / 3 ≤ τ
    · have heq : τin = τ := by simp [τin, max_eq_left hbase]
      simpa only [heq] using huτ
    · have heq : τin = 25 / 3 := by
        dsimp [τin]
        exact max_eq_right (le_of_not_ge hbase)
      simpa only [heq] using hStep2.velocity
  have hDuQ₂ : ∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ) Q₂
      (fun w => Du w i) := hStep2.gradient
  let δ : ℝ := r₂ / 4 - r₃
  let R : ℝ := δ / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hr₃₂, hr₃]
  have hR : 0 < R := by dsimp [R]; positivity
  have hroom : 2 * R + r₃ < r₂ / 4 := by
    dsimp [R, δ]
    nlinarith only [hr₃₂]
  have hcenterQ₂ (y : Metric.closedBall z₀ r₃) :
      Metric.ball y.1 (2 * R) ⊆ Q₂ := by
    intro w hw
    have htri := dist_triangle w y.1 z₀
    change dist w z₀ < r₂ / 4
    calc
      dist w z₀ ≤ dist w y.1 + dist y.1 z₀ := htri
      _ < 2 * R + r₃ := add_lt_add_of_lt_of_le hw y.2
      _ < r₂ / 4 := hroom
  have hQ₂domain : Q₂ ⊆ Metric.ball z₀ (2 * r₂) := by
    change Metric.ball z₀ (r₂ / 4) ⊆ Metric.ball z₀ (2 * r₂)
    exact Metric.ball_subset_ball (by nlinarith only [hr₂])
  have hcenterDomain (y : Metric.closedBall z₀ r₃) :
      Metric.ball y.1 (2 * R) ⊆ spaceTimeSet Ω I :=
    ((hcenterQ₂ y).trans hQ₂domain).trans hdom
  have hcenterVel (y : Metric.closedBall z₀ r₃) : Metric.ball y.1 R ⊆ Q₂ :=
    (Metric.ball_subset_ball (by linarith only [hR])).trans (hcenterQ₂ y)
  have hUinLocal (y : Metric.closedBall z₀ r₃) :
      morreyVecMem 3 τin (Metric.ball y.1 R) u :=
    CKN.Core.Endgame.morreyVecMem_mono_carrier (by norm_num)
      (hcenterVel y) hUinQ₂
  have hDuLocal (y : Metric.closedBall z₀ r₃) (i : Fin 3) :
      morreyVecMem 2 (25 / 8 : ℝ) (Metric.ball y.1 R) (fun w => Du w i) :=
    CKN.Core.Endgame.morreyVecMem_mono_carrier (by norm_num)
      (hcenterVel y) (hDuQ₂ i)
  let U : Metric.closedBall z₀ r₃ → Set ParabolicPoint :=
    fun y => Metric.ball y.1 (R / 4)
  have hcoverClosed : Metric.closedBall z₀ r₃ ⊆ ⋃ y, U y := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (by positivity : 0 < R / 4)⟩
  obtain ⟨s, hs⟩ :=
    (CKN.Core.Endgame.isCompact_parabolic_closedBall z₀ r₃).elim_finite_subcover
      U (fun _ => Metric.isOpen_ball) hcoverClosed
  have hcenterClosed : z₀ ∈ Metric.closedBall z₀ r₃ := by
    rw [Metric.mem_closedBall]
    simpa only [dist_self] using hr₃.le
  have hcenterCover : z₀ ∈ ⋃ y ∈ s, U y := hs hcenterClosed
  have hcoverQ₃ : Q₃ ⊆ ⋃ y ∈ s, U y := by
    intro w hw
    by_cases hwcenter : w = z₀
    · simpa [hwcenter] using hcenterCover
    · have hwClosed : w ∈ Metric.closedBall z₀ r₃ :=
        Metric.mem_closedBall.mpr (le_of_lt hw)
      exact hs hwClosed
  have hlocalOutput (y : Metric.closedBall z₀ r₃) :
      morreyVecMem 3 (bootstrapOutputExponent τ) (U y) u := by
    have hRound := bootstrap_local_round hsol hq (z := y.1) hR
      (hcenterDomain y) hτinlo hτinhi hτin hτincond (hUinLocal y)
      (hDuLocal y)
    by_cases hbase : 25 / 3 ≤ τ
    · have heq : τin = τ := by simp [τin, max_eq_left hbase]
      simpa [U, heq] using hRound
    · have heq : τin = 25 / 3 := by
        dsimp [τin]
        exact max_eq_right (le_of_not_ge hbase)
      have hRound25 : morreyVecMem 3 25 (U y) u := by
        have hEq : bootstrapOutputExponent τin = 25 := by
          rw [heq]
          norm_num [bootstrapOutputExponent]
        simpa only [U, hEq] using hRound
      have hτσ : bootstrapOutputExponent τ ≤ 25 := by
        have hτsmall : τ < 25 / 3 := lt_of_not_ge hbase
        have hrecip := one_div_lt_one_div_of_lt hτpos hτsmall
        have hrecip' : (3 / 25 : ℝ) < 1 / τ := by norm_num at hrecip ⊢; exact hrecip
        have hgain : 1 / 25 < 1 / τ - 2 / 25 := by linarith only [hrecip']
        have hlt := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1 / 25) hgain
        have hout : bootstrapOutputExponent τ < 25 := by
          simpa [bootstrapOutputExponent] using hlt
        exact hout.le
      exact morreyVecMem_ball_of_exponent_le (by norm_num)
        (by linarith only [hσlo]) hτσ (by positivity) hRound25
  have hQ₃subQ₂ : Q₃ ⊆ Q₂ :=
    Metric.ball_subset_ball hr₃₂.le
  have hnormQ₃ (i : Fin 3) :
      morreyNorm 3 (bootstrapOutputExponent τ)
        (Q₃.indicator (fun w => u w i)) < ⊤ := by
    let D : ParabolicPoint → ℝ := Q₂.indicator (fun w => u w i)
    have hD : AEMeasurable D volume := by simpa [D] using huQ₂AE i
    have hlocalN : ∀ y ∈ s,
        morreyNorm 3 (bootstrapOutputExponent τ) ((U y).indicator D) < ⊤ := by
      intro y hy
      have hu := hlocalOutput y
      have hbound : morreyNorm 3 (bootstrapOutputExponent τ)
          ((U y).indicator (fun w => u w i)) < ⊤ :=
        (morreyNorm_le_morreyBallNorm (by norm_num)
          (by linarith only [hσlo]) _).trans_lt (hu i)
      have heq : (U y).indicator D =
          (U y).indicator (fun w => u w i) := by
        funext w
        by_cases hw : w ∈ U y
        · have hsub := hcenterVel y
            (Metric.ball_subset_ball (by linarith only [hR]) hw)
          change (U y).indicator (Q₂.indicator (fun v => u v i)) w =
            (U y).indicator (fun v => u v i) w
          simp only [indicator_of_mem hw, indicator_of_mem hsub]
        · change (U y).indicator (Q₂.indicator (fun v => u v i)) w =
            (U y).indicator (fun v => u v i) w
          simp only [indicator_of_notMem hw]
      rw [heq]
      exact hbound
    have hcoverProxy : Q₃ ⊆ ⋃ y ∈ s, U y := hcoverQ₃
    have hproxy := bootstrap_finite_cover_morrey (P := 3)
      (κ := bootstrapOutputExponent τ) (by norm_num) hD s U
      (fun _ _ => Metric.isOpen_ball.measurableSet) hcoverProxy hlocalN
    have heq : Q₃.indicator D = Q₃.indicator (fun w => u w i) := by
      funext w
      by_cases hw : w ∈ Q₃
      · change Q₃.indicator (Q₂.indicator (fun v => u v i)) w =
          Q₃.indicator (fun v => u v i) w
        simp only [indicator_of_mem hw, indicator_of_mem (hQ₃subQ₂ hw)]
      · change Q₃.indicator (Q₂.indicator (fun v => u v i)) w =
          Q₃.indicator (fun v => u v i) w
        simp only [indicator_of_notMem hw]
    rw [heq] at hproxy
    exact hproxy
  apply (morreyVecMem_iff_cylinder_lt_top (by norm_num)
    (by linarith only [hσlo]) Q₃ u).2
  exact hnormQ₃

end CKN.Core.Step4

end
