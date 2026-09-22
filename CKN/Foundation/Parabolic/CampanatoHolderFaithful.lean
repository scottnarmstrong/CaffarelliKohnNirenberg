-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.CampanatoHolderConverseScope

/-!
# Parabolic Campanato characterization

The representative and its local supremum bound require the Campanato
hypothesis; the converse Hölder-to-Campanato estimate does not.
-/

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- The global Campanato estimate with its forward hypothesis scoped only to
the representative and local supremum conclusions. -/
theorem campanato_holder_source :
    ∀ {f : ParabolicPoint → ℝ} {α K p : ℝ},
      0 < α → α < 1 → 1 ≤ p → 0 ≤ K →
      LocallyIntegrable f volume → GlobalParabolicBallLpData f p →
      (GlobalParabolicBallCampanatoBound f α K p →
        ∃ g : ParabolicPoint → ℝ,
          g =ᵐ[volume] f ∧
          ParabolicHolderSeminormLE Set.univ g α
            (parabolicCampanatoHolderConstant α p * K) ∧
          (∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
            ∀ w ∈ Metric.ball z R, |g w| ≤
              2 ^ α * parabolicCampanatoHolderConstant α p * K * R ^ α +
                (⨍ x in Metric.ball z R, |f x| ^ p) ^ (1 / p))) ∧
      (∀ L : ℝ, 0 ≤ L → ParabolicHolderSeminormLE Set.univ f α L →
        GlobalParabolicBallCampanatoBound f α (2 ^ α * L) p) := by
  exact repair_lem_campanato

end CKN.Foundation.Parabolic
