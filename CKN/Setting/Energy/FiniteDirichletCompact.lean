-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Caccioppoli.LocalBox
import CKN.Core.Caccioppoli.CaccioppoliEnergyTools

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN

/-- A suitable weak solution has finite Dirichlet energy on every compact subset
of its domain.  That is, `spatialGradientSq u Du` is integrable on `K` with respect
to Lebesgue volume whenever `K` is compact and contained in the space-time
carrier. -/
theorem spatialGradientSq_integrableOn_compact
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun z => spatialGradientSq u Du z) K volume := by
  obtain ⟨Ω', J, hbox, hKbox⟩ := caccioppoli_localBox_of_compact_subset
    hsol.1 hsol.2.1 hsol.2.2.1 hK hKsub
  have hDu : AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.1
  have hDumeas : AEMeasurable (fun z : ParabolicPoint => spatialGradientSq u Du z)
      (volume.restrict K) := by
    have hcont : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ)) := by
      fun_prop
    have h := hcont.comp_aestronglyMeasurable hDu
    exact h.aemeasurable.mono_measure (Measure.restrict_mono hKbox le_rfl)
  have henergy : (∫⁻ z in K, ‖Du z‖ₑ ^ (2 : ℝ)) ≠ ∞ := by
    have h := (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.2.2.1
    have hle : (∫⁻ z in K, ‖Du z‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) := by
      calc
        (∫⁻ z in K, ‖Du z‖ₑ ^ (2 : ℝ)) ≤
            ∫⁻ z in K, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) := by
          apply lintegral_mono
          intro z
          exact le_add_left le_rfl
        _ ≤ ∫⁻ z in spaceTimeSet Ω' J,
            ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) :=
          lintegral_mono_set hKbox
    exact ne_of_lt (hle.trans_lt h)
  have hpoint : ∀ z : ParabolicPoint,
      ENNReal.ofReal (spatialGradientSq u Du z) ≤
        9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
    intro z
    have hterm : ∀ i : Fin 3, ∀ j : Fin 3,
        (Du z i j) ^ (2 : ℕ) ≤ ‖Du z‖ ^ (2 : ℕ) := by
      intro i j
      rw [← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact le_trans (norm_le_pi_norm (Du z i) j) (norm_le_pi_norm (Du z) i)
    have hsum : spatialGradientSq u Du z ≤
        ∑ i : Fin 3, ∑ j : Fin 3, ‖Du z‖ ^ (2 : ℕ) := by
      unfold spatialGradientSq
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    have hsum' : spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ (2 : ℕ) := by
      calc
        spatialGradientSq u Du z ≤
            ∑ i : Fin 3, ∑ j : Fin 3, ‖Du z‖ ^ (2 : ℕ) := hsum
        _ = 9 * ‖Du z‖ ^ (2 : ℕ) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
    calc
      ENNReal.ofReal (spatialGradientSq u Du z) ≤
          ENNReal.ofReal (9 * ‖Du z‖ ^ (2 : ℕ)) :=
        ENNReal.ofReal_le_ofReal hsum'
      _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
          show ENNReal.ofReal (9 : ℝ) = 9 by norm_num]
        congr 1
        rw [← ofReal_norm]
        rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
        norm_num [Real.rpow_natCast]
  have hlin : (∫⁻ z in K, ENNReal.ofReal (spatialGradientSq u Du z)) ≠ ∞ := by
    have hle := lintegral_mono (μ := volume.restrict K) hpoint
    have htop : (∫⁻ z in K, 9 * ‖Du z‖ₑ ^ (2 : ℝ)) < ∞ := by
      apply lt_top_iff_ne_top.mpr
      rw [lintegral_const_mul' 9 _ (by norm_num)]
      exact ENNReal.mul_ne_top (by norm_num) henergy
    exact ne_of_lt (hle.trans_lt htop)
  have hnonneg : ∀ z : ParabolicPoint, 0 ≤ spatialGradientSq u Du z := by
    intro z
    unfold spatialGradientSq
    positivity
  exact caccioppoli_integrable_of_lintegral_abs_ne_top hDumeas (by
    simpa only [abs_of_nonneg (hnonneg _)] using hlin)

end CKN
