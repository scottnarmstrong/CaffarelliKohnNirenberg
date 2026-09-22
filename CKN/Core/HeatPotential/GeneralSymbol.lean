-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierKernel
import CKN.Core.HeatPotential.Kernel

open scoped BigOperators

open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean
open CKN.Foundation.Heat CKN.Foundation.Parabolic

/-! The finite general-symbol heat potential used in the heat-kernel family.

This is the potential from `eq:heat-potential` in `paper/ckn.tex`, with the
real-valued source data paired against the complex-valued causal kernels.
-/

def multiplierHeatPotential {K : ℕ} (σ : Fin K → Vec3 → ℂ)
    (F : ParabolicPoint → ℝ) (G : Fin K → ParabolicPoint → ℝ)
    (w : ParabolicPoint) : ℂ :=
  (∫ v, (heatKernelPlus (pointSub w v) : ℂ) * (F v : ℂ)) +
    ∑ k, ∫ v,
      spatialMultiplierHeatKernel (σ k) (pointSub w v).1 (pointSub w v).2 *
        (G k v : ℂ)

end CKN.Core.HeatPotential
