-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Foundation.Sobolev.Cutoff.Basic

set_option autoImplicit false

namespace CKN

/-- The sup norm of a vector of `Vec d` is at most its Euclidean norm. -/
theorem pi_norm_le_vecEuclideanNorm {d : ℕ} (x : Vec d) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i _
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

end CKN
