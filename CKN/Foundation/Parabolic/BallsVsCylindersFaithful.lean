-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

/-!
# Same-centre inclusion of a parabolic cylinder in a parabolic ball

`CKN/Foundation/Parabolic/Basic.lean` records the two re-centred inclusions
between `parabolicCylinder x t r` and the metric ball around
`(x, t - r ^ 2 / 2)`.  The remark `rem:balls-vs-cylinders` of `paper/ckn.tex`
uses the sharper *same-centre* inclusion `Q_r(z) ⊆ 𝔅_r(z)`, which is what links
a cylinder-stated defect inequality to a ball-run covering argument.  This file
records that inclusion.
-/

open MeasureTheory Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- `rem:balls-vs-cylinders`: the parabolic cylinder of radius `r` centred at
`(x, t)` is contained in the parabolic metric ball of radius `r` around the very
same centre. -/
theorem parabolicCylinder_subset_metricBall_same_center
    {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    parabolicCylinder x t r ⊆
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace (x, t) r := by
  rintro p hp
  change @dist ParabolicPoint
    (PseudoMetricSpace.toDist (self := parabolicPseudoMetricSpace))
    p ((x, t) : ParabolicPoint) < r
  rw [dist_eq_parabolicDist p ((x, t) : ParabolicPoint)]
  obtain ⟨y, s⟩ := p
  obtain ⟨hspace, hlow, hupp⟩ := mem_parabolicCylinder.mp hp
  refine max_lt hspace ?_
  refine (Real.sqrt_lt' hr).mpr ?_
  rw [abs_of_nonpos (by linarith only [hupp] : s - t ≤ 0)]
  linarith only [hlow]

end CKN.Foundation.Parabolic
