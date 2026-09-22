-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.CylinderCentered
import CKN.Foundation.Heat.Smooth

open Set
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN.Foundation.Heat

/-- The centred backward Gaussian test function `ψ_r(x,t) = r² G(x − x₀, r² − (t − t₀))`
is `C^∞` on the open half-space `t < t₀ + r²`. -/
theorem contDiffOn_centeredBackwardHeatTest (x₀ : Vec3) (t₀ r : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => centeredBackwardHeatTest x₀ t₀ r p)
      {p : Vec3 × ℝ | p.2 < t₀ + r ^ 2} := by
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => heatKernel p.1 p.2) (univ ×ˢ Ioi (0 : ℝ)) :=
    heatKernel_contDiffOn_pos.of_le le_top
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Vec3 × ℝ => ((p.1 - x₀, r ^ 2 - (p.2 - t₀)) : Vec3 × ℝ)) := by
    fun_prop
  have hmaps : MapsTo (fun p : Vec3 × ℝ => ((p.1 - x₀, r ^ 2 - (p.2 - t₀)) : Vec3 × ℝ))
      {p : Vec3 × ℝ | p.2 < t₀ + r ^ 2} (univ ×ˢ Ioi (0 : ℝ)) := by
    intro p hp
    have hp' : p.2 < t₀ + r ^ 2 := by simpa using hp
    have hpos : 0 < r ^ 2 - (p.2 - t₀) := by linarith only [hp']
    exact ⟨mem_univ _, by simpa [mem_Ioi] using hpos⟩
  have hcomp := hG.comp hA.contDiffOn hmaps
  have hfun : (fun p : Vec3 × ℝ => centeredBackwardHeatTest x₀ t₀ r p) =
      fun p => r ^ 2 * heatKernel (p.1 - x₀) (r ^ 2 - (p.2 - t₀)) := by
    funext p; rfl
  rw [hfun]
  exact contDiffOn_const.mul hcomp

end CKN.Foundation.Heat
