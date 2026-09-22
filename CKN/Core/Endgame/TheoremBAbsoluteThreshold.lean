-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.TheoremBUnconditional
import CKN.Core.Step2.ThetaDecayAbsoluteConstant

/-!
# The gradient regularity criterion with an absolute threshold

The proof of paper theorem `thm:B`: the threshold is taken
to be `ε₁ = ε_*`, the **absolute** constant of `conv:kappa`, and the printed
chain is the Morrey-decay estimate → the Step 2 velocity estimate → the
bootstrap proposition → the one-round corollary → the endgame theorem.

`CKN.Core.Endgame.epsilonRegularityGradient_unconditional` runs exactly that
chain, but its `ε₁` is produced after the force exponent `q` has been fixed,
because the combined decay inequality it uses quantifies `q` first.  The
theorem below is the same chain with the decay input taken from
`CKN.thetaDecay_T_of_sws_absolute`, whose constant `C₂₇` is absolute; the
threshold `ε₁ = iterationEpsilonStar C₂₇` is then fixed before `q`, as
printed.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step3 CKN.Core.Step4

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Endgame

/-- The proof of paper theorem `thm:B`: the `ε`-regularity criterion of `thm:B`
with the threshold `ε₁ = ε_*` fixed **before** the force exponent `q`. -/
theorem epsilonRegularityGradient_absolute :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ q : ℝ, 5 / 2 < q →
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          IsRegularPoint Ω I u z₀ := by
  obtain ⟨C₂₇, hC₂₇, hdecay⟩ := CKN.thetaDecay_T_of_sws_absolute
  refine ⟨iterationEpsilonStar C₂₇, iterationEpsilonStar_pos hC₂₇, ?_⟩
  intro q hq Ω I u Du p f hsol z₀ hz₀ hgradient
  obtain ⟨C₂₈, hC₂₈, hThetaDecay⟩ := hdecay q
  have hG := theoremB_gradient_producer_of_small_cell_majorant
    (shared_binder_of_remainder_majorant fixed_remainder_temporal_majorant_of_sws)
  obtain ⟨r₂, M, hr₂, _hM, hcarrier, _hdec, hu, hDu, _hp⟩ :=
    morrey_sources_of_gradient_limsup hsol hq hz₀ hC₂₇ hC₂₈
      (hThetaDecay Ω I u Du p f hsol) hgradient
  exact regular_point_of_local_producers q hq hG
    (routeA_one_round_velocity_improvement_of_gradient_inputs
      (by
        intro q' hq'
        exact hG q' (25 / 3) hq' (by norm_num) (by norm_num))
      CKN.Core.Step3.localized_gradient_slot_duhamel_of_sws)
    CKN.Core.Step3.localized_gradient_slot_duhamel_of_sws
    localized_gradient_source_package_of_sws
    hsol z₀ (r₂ / 4) (by positivity)
    ((Metric.ball_subset_ball (by linarith only [hr₂])).trans hcarrier) hu hDu

end CKN.Core.Endgame
