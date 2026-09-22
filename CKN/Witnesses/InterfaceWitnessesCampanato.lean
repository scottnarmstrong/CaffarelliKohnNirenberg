-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Campanato
import CKN.Foundation.Parabolic.CampanatoHolder

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Parabolic

/-- The global ball Campanato bound is satisfied by the zero function. -/
theorem GlobalParabolicBallCampanatoBound_satisfiable :
    ∃ (f : ParabolicPoint → ℝ) (α K p : ℝ),
      GlobalParabolicBallCampanatoBound f α K p := by
  refine ⟨fun _ => 0, 1, 0, 1, ?_⟩
  intro z r hr
  simp [ParabolicBallLpOscillation]

/-- The global ball integrability data are satisfied by the zero function. -/
theorem GlobalParabolicBallLpData_satisfiable :
    ∃ (f : ParabolicPoint → ℝ) (p : ℝ), GlobalParabolicBallLpData f p := by
  refine ⟨fun _ => 0, 1, ?_⟩
  intro z r hr
  constructor <;> simp

/-- The local ball Campanato bound is satisfied by zero data. -/
theorem ParabolicBallCampanatoBoundOn_satisfiable :
    ∃ (f : ParabolicPoint → ℝ) (U : Set ParabolicPoint)
      (R α K p : ℝ), ParabolicBallCampanatoBoundOn f U R α K p := by
  refine ⟨fun _ => 0, Set.univ, 1, 1, 0, 1, ?_⟩
  intro z hz r hr hrR
  simp [ParabolicBallLpOscillation]

/-- The local ball integrability data are satisfied by zero data. -/
theorem ParabolicBallLpDataOn_satisfiable :
    ∃ (f : ParabolicPoint → ℝ) (U : Set ParabolicPoint)
      (R p : ℝ), ParabolicBallLpDataOn f U R p := by
  refine ⟨fun _ => 0, Set.univ, 1, 1, ?_⟩
  intro z hz r hr hrR
  constructor <;> simp

/-- The local cylinder Campanato bound is satisfied by the zero function. -/
theorem ParabolicCylinderCampanatoBoundOn_satisfiable :
    ∃ (f : ParabolicPoint → ℝ) (U : Set ParabolicPoint)
      (R α K p : ℝ), ParabolicCylinderCampanatoBoundOn f U R α K p := by
  refine ⟨fun _ => 0, Set.univ, 1, 1, 0, 1, ?_⟩
  intro z hz r hr hrR
  simp [ParabolicCylinderLpOscillation, Integration.cylinderAverage]

end CKN.Foundation.Parabolic
