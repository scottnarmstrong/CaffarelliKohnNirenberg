-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Morrey.Basic

/-!
# Scalar homogeneity of the parabolic Morrey seminorm

A nonnegative scalar may be pulled out of the parabolic Morrey seminorm: for
`0 ≤ c` the seminorm of `z ↦ c * f z` is at most `c` times the seminorm of
`f`.  This is the homogeneity step that lets a cutoff derivative bound be
factored away from the source estimates of paper label `thm:endgame`.
-/

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Endgame

/-- A nonnegative scalar factors out of the parabolic Morrey seminorm up to
the expected constant: `morreyNorm (c * f) ≤ ofReal c * morreyNorm f`.  This is
how the cutoff derivative bound leaves the source estimates of paper label
`thm:endgame`. -/
theorem morreyNorm_const_mul_le_of_nonneg {p q c : ℝ} (hp : 0 < p) (hc : 0 ≤ c)
    (f : ParabolicPoint → ℝ) :
    morreyNorm p q (fun z => c * f z) ≤ ENNReal.ofReal c * morreyNorm p q f := by
  have hconst : ENNReal.ofReal c ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  have hcell : ∀ (z : ParabolicPoint) (r : {r : ℝ // 0 < r}),
      morreyCell p q (fun z => c * f z) z r.1 ≤ ENNReal.ofReal c * morreyNorm p q f := by
    intro z r
    have hint : cylinderPowerIntegral p (fun z => c * f z) z r.1 =
        ENNReal.ofReal c ^ p * cylinderPowerIntegral p f z r.1 := by
      unfold cylinderPowerIntegral
      calc
        ∫⁻ w in parabolicCylinder z.1 z.2 r.1, ENNReal.ofReal |c * f w| ^ p =
            ∫⁻ w in parabolicCylinder z.1 z.2 r.1,
              ENNReal.ofReal c ^ p * ENNReal.ofReal |f w| ^ p := by
          apply lintegral_congr
          intro w
          rw [abs_mul, abs_of_nonneg hc, ENNReal.ofReal_mul hc,
            ENNReal.mul_rpow_of_nonneg _ _ hp.le]
        _ = ENNReal.ofReal c ^ p *
            ∫⁻ w in parabolicCylinder z.1 z.2 r.1, ENNReal.ofReal |f w| ^ p :=
          lintegral_const_mul' _ _ hconst
    have hcell_eq : morreyCell p q (fun z => c * f z) z r.1 =
        ENNReal.ofReal c * morreyCell p q f z r.1 := by
      unfold morreyCell
      rw [hint, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p)]
      have hpp : p * (1 / p) = 1 := by field_simp
      rw [← ENNReal.rpow_mul, hpp, ENNReal.rpow_one, mul_left_comm]
    calc
      morreyCell p q (fun z => c * f z) z r.1 =
          ENNReal.ofReal c * morreyCell p q f z r.1 := hcell_eq
      _ ≤ ENNReal.ofReal c * morreyNorm p q f := by
        apply mul_le_mul_of_nonneg_left _ zero_le
        unfold morreyNorm
        exact le_iSup_of_le z
          (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p q f z s.1) r)
  unfold morreyNorm
  exact iSup_le fun z => iSup_le fun r => hcell z r

end CKN.Core.Endgame
