-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.GeneralSymbolHeatKernelSplit
import CKN.Core.HeatPotential.GeneralSymbolHeatNearOscillation
import CKN.Core.HeatPotential.SubordinatedNear
import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelLocalIntegrable

open scoped BigOperators ENNReal NNReal Topology Distributions

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

def multiplierHeatPairOscillation (h : ParabolicPoint → ℂ)
    (z : ParabolicPoint) (r p : ℝ) : ℝ :=
  (⨍ w in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
    ⨍ w' in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
      ‖h w - h w'‖ ^ p) ^ (1 / p)

def multiplierHeatSourceSize {K : ℕ} (P θ₀ θ₁ : ℝ)
    (F : ParabolicPoint → ℝ) (G : Fin K → ParabolicPoint → ℝ) : ℝ :=
  (morreyNorm P θ₀ F).toReal +
    ∑ k, (morreyNorm P θ₁ (G k)).toReal







end CKN.Core.HeatPotential
