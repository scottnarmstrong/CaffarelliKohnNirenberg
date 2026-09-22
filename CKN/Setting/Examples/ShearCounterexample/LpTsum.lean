-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! # Lp convergence of the shear series. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace CKN

theorem memLp_tsum_of_summable_eLpNorm_bound
    {X E : Type} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [CompleteSpace E]
    {p : ENNReal} [Fact (1 ≤ p)]
    (g : ℕ → X → E) (A : ℕ → ℝ)
    (hmem : ∀ n, MemLp (g n) p μ)
    (hbound : ∀ n, eLpNorm (g n) p μ ≤ ENNReal.ofReal (A n))
    (hA_sum : Summable A) :
    MemLp (fun x => ∑' n, g n x) p μ := by
  let t : ℕ → Lp E p μ := fun n => MemLp.toLp (g n) (hmem n)
  have ht_norm (n : ℕ) : ‖t n‖ₑ = eLpNorm (g n) p μ := by
    dsimp [t]
    rw [← enorm_norm, Lp.norm_toLp]
    calc
      ‖(eLpNorm (g n) p μ).toReal‖ₑ =
          ENNReal.ofReal (eLpNorm (g n) p μ).toReal :=
        Real.enorm_of_nonneg (by positivity : 0 ≤ (eLpNorm (g n) p μ).toReal)
      _ = eLpNorm (g n) p μ := ENNReal.ofReal_toReal (hmem n).ne
  have hsum_bound : (∑' n, ‖t n‖ₑ) ≤ ∑' n, ENNReal.ofReal (A n) := by
    apply ENNReal.tsum_le_tsum
    intro n
    rw [ht_norm]
    exact hbound n
  have hsum_ne : (∑' n, ‖t n‖ₑ) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (hA_sum.tsum_ofReal_ne_top)
    exact hsum_bound
  have hEq := Lp.coeFn_tsum hsum_ne
  have hrep : ∀ᵐ x ∂μ, ∀ n, (t n : X → E) x = g n x := by
    rw [ae_all_iff]
    intro n
    exact MemLp.coeFn_toLp (hmem n)
  have hEq' : (↑↑(∑' n, t n) : X → E) =ᵐ[μ]
      (fun x => ∑' n, g n x) := by
    filter_upwards [hEq, hrep] with x hsum hx
    rw [hsum]
    exact tsum_congr (fun n => hx n)
  exact (memLp_congr_ae hEq').1 (Lp.memLp (∑' n, t n))

end CKN
