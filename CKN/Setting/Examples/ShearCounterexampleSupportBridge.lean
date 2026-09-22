-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.


import CKN.Foundation.Parabolic.Topology
import CKN.Foundation.Parabolic.Integration.Average
import CKN.Statements.SpaceTimeTestFunction

/-! # Support and product-measure transfer identities for parabolic tests. -/


set_option autoImplicit false
noncomputable section

open CKN.Foundation.Parabolic Set MeasureTheory

namespace CKN

theorem tsupport_parabolic_eq_product_test (f : Vec3 × ℝ → ℝ) :
    @tsupport ParabolicPoint ℝ Real.instZero
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (show ParabolicPoint → ℝ from f) =
      @tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd f := by
  have hsupp : Function.support (show ParabolicPoint → ℝ from f) =
      parabolicHomeomorph ⁻¹' Function.support f := by
    ext z
    rfl
  rw [tsupport, tsupport, hsupp, ← parabolicHomeomorph.preimage_closure,
    parabolicHomeomorph_preimage]

theorem tsupport_parabolic_eq_product_vec (f : Vec3 × ℝ → Vec3) :
    @tsupport ParabolicPoint Vec3 (inferInstance : Zero Vec3)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (show ParabolicPoint → Vec3 from f) =
      @tsupport (Vec3 × ℝ) Vec3 (inferInstance : Zero Vec3) instTopologicalSpaceProd f := by
  have hsupp : Function.support (show ParabolicPoint → Vec3 from f) =
      parabolicHomeomorph ⁻¹' Function.support f := by
    ext z
    rfl
  rw [tsupport, tsupport, hsupp, ← parabolicHomeomorph.preimage_closure,
    parabolicHomeomorph_preimage]

theorem integrableOn_parabolic_of_product_test (f : Vec3 × ℝ → ℝ)
    (h : IntegrableOn f
      (@tsupport (Vec3 × ℝ) ℝ Real.instZero instTopologicalSpaceProd f)
      (volume : Measure (Vec3 × ℝ))) :
    IntegrableOn (show ParabolicPoint → ℝ from f)
      (@tsupport ParabolicPoint ℝ Real.instZero
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (show ParabolicPoint → ℝ from f)) (volume : Measure ParabolicPoint) := by
  rw [tsupport_parabolic_eq_product_test,
    CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  exact h

theorem integrableOn_parabolic_set_of_product_test {S : Set (Vec3 × ℝ)}
    (f : Vec3 × ℝ → ℝ)
    (h : IntegrableOn f S (volume : Measure (Vec3 × ℝ))) :
    IntegrableOn (show ParabolicPoint → ℝ from f) S
      (volume : Measure ParabolicPoint) := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  exact h

theorem setIntegral_parabolic_eq_product_test (f : Vec3 × ℝ → ℝ) :
    ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1 : ℝ) 1),
        (show ParabolicPoint → ℝ from f) z =
      ∫ z in (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 1), f z := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  change ∫ z in (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 1), f z
      ∂(volume : Measure (Vec3 × ℝ)) = _
  rfl

end CKN
