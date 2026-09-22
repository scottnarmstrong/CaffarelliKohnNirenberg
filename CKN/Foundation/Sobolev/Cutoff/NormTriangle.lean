-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Cutoff.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

set_option autoImplicit false

namespace CKN

/-- The Euclidean norm on native coordinate vectors coincides with the `L²`
norm of `WithLp.toLp 2 x`. -/
theorem vecEuclideanNorm_eq_norm_toLp {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [vecEuclideanNorm, vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The triangle inequality for the Euclidean norm on native coordinate vectors. -/
theorem vecEuclideanNorm_add_le {d : ℕ} (x y : Vec d) :
    vecEuclideanNorm (x + y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  rw [vecEuclideanNorm_eq_norm_toLp, vecEuclideanNorm_eq_norm_toLp, vecEuclideanNorm_eq_norm_toLp]
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

end CKN
