-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.CampanatoHolderFaithful

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic

/-- The scalar Campanato-to-Hölder conversion used by heat-potential estimates.
The coefficient depends only on the Campanato exponent, the integrability
exponent, and the supplied Campanato bound. -/
theorem heat_holder_from_campanato
    {f : ParabolicPoint → ℝ} {α K p : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hf : LocallyIntegrable f volume)
    (hdata : GlobalParabolicBallLpData f p)
    (hcamp : GlobalParabolicBallCampanatoBound f α K p) :
    ∃ g : ParabolicPoint → ℝ,
      g =ᵐ[volume] f ∧
      ParabolicHolderSeminormLE Set.univ g α
        (parabolicCampanatoHolderConstant α p * K) ∧
      (∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
        ∀ w ∈ Metric.ball z R, |g w| ≤
          2 ^ α * parabolicCampanatoHolderConstant α p * K * R ^ α +
            (⨍ x in Metric.ball z R, |f x| ^ p) ^ (1 / p)) := by
  exact (campanato_holder_source hα hα1 hp hK hf hdata).1 hcamp

/-- The Campanato representative may be transferred across an almost-everywhere
equal common representative without changing its Hölder estimate. -/
theorem heat_holder_from_campanato_common
    {f h : ParabolicPoint → ℝ} {α K p : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hf : LocallyIntegrable f volume)
    (hdata : GlobalParabolicBallLpData f p)
    (hcamp : GlobalParabolicBallCampanatoBound f α K p)
    (hcommon : f =ᵐ[volume] h) :
    ∃ g : ParabolicPoint → ℝ,
      g =ᵐ[volume] h ∧
      ParabolicHolderSeminormLE Set.univ g α
        (parabolicCampanatoHolderConstant α p * K) ∧
      (∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
        ∀ w ∈ Metric.ball z R, |g w| ≤
          2 ^ α * parabolicCampanatoHolderConstant α p * K * R ^ α +
            (⨍ x in Metric.ball z R, |f x| ^ p) ^ (1 / p)) := by
  rcases heat_holder_from_campanato hα hα1 hp hK hf hdata hcamp with
    ⟨g, hgf, hholder, hbound⟩
  exact ⟨g, hgf.trans hcommon, hholder, hbound⟩

/-- The multiplicative Campanato coefficient is nonnegative in the range used
by the heat estimates. -/
theorem heat_holder_campanato_coefficient_nonneg
    {α p K : ℝ} (hα : 0 < α) (hK : 0 ≤ K) :
    0 ≤ parabolicCampanatoHolderConstant α p * K := by
  have htail : 0 ≤ parabolicCampanatoTailConstant α := by
    unfold parabolicCampanatoTailConstant
    exact one_div_nonneg.mpr (sub_nonneg.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (by linarith only [hα])).le)
  have hconstant : 0 ≤ parabolicCampanatoHolderConstant α p := by
    unfold parabolicCampanatoHolderConstant
    exact mul_nonneg (mul_nonneg (by linarith only [htail])
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (by norm_num) _)
  exact mul_nonneg hconstant hK

/-- Every member of a family with the same Campanato bound receives the same
Hölder coefficient. -/
theorem heat_holder_from_campanato_family
    {ι : Type*} {f : ι → ParabolicPoint → ℝ} {α K p : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hf : ∀ i, LocallyIntegrable (f i) volume)
    (hdata : ∀ i, GlobalParabolicBallLpData (f i) p)
    (hcamp : ∀ i, GlobalParabolicBallCampanatoBound (f i) α K p) :
    ∀ i, ∃ g : ParabolicPoint → ℝ,
      g =ᵐ[volume] f i ∧
      ParabolicHolderSeminormLE Set.univ g α
        (parabolicCampanatoHolderConstant α p * K) ∧
      (∀ (z : ParabolicPoint) (R : ℝ), 0 < R →
        ∀ w ∈ Metric.ball z R, |g w| ≤
          2 ^ α * parabolicCampanatoHolderConstant α p * K * R ^ α +
            (⨍ x in Metric.ball z R, |f i x| ^ p) ^ (1 / p)) := by
  intro i
  exact heat_holder_from_campanato hα hα1 hp hK (hf i) (hdata i) (hcamp i)

end CKN.Core.HeatPotential
