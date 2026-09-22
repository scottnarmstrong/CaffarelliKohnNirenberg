-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false

namespace CKN

/-- The topological support of a separated product ψ(x) θ(y) on a product space is the product
of the two topological supports. -/
theorem tsupport_mul_prod_eq {X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MulZeroClass M] [NoZeroDivisors M] (ψ : X → M) (θ : Y → M) :
    tsupport (fun z : X × Y => ψ z.1 * θ z.2) = tsupport ψ ×ˢ tsupport θ := by
  have hsupp : Function.support (fun z : X × Y => ψ z.1 * θ z.2)
      = Function.support ψ ×ˢ Function.support θ := by
    ext z
    simp only [Function.mem_support, Set.mem_prod, mul_ne_zero_iff]
  rw [tsupport, tsupport, tsupport, hsupp, closure_prod_eq]

end CKN
