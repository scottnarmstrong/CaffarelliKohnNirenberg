-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Setting.Examples.ShearCounterexample.SliceFullWeak

/-! # Almost-everywhere convergence statements for shear slices. -/
set_option autoImplicit false
noncomputable section
open CKN.Foundation.Parabolic Set MeasureTheory
namespace CKN

theorem shearCounterexampleSlice_hasWeakGradient_ae
    {Ω' : Set Vec3} {J : Set ℝ} (hΩ' : IsOpen Ω') :
    ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
      HasWeakGradientOn Ω'
        (fun x : Vec3 => shearCounterexampleVelocity ((x, s) : ParabolicPoint) i)
        (fun x j => shearCounterexampleDu ((x, s) : ParabolicPoint) i j) := by
  intro i
  filter_upwards [ae_restrict_of_ae (MeasureTheory.Measure.ae_ne volume 0)] with s hs
  exact shearCounterexampleSlice_hasWeakGradientOn_of_time_nezero hΩ' s hs i

end CKN
