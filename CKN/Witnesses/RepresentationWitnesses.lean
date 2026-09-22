-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.PressureMultiplierSymbol
import CKN.Foundation.Euclidean.SpatialMultiplierKernel

/-!
# The pressure symbol inhabits the degree-one symbol class

External Input `ext:heat-kernel` of `paper/ckn.tex` quantifies over the Fourier
multipliers `ς(D)` whose symbol is smooth on `ℝ³ ∖ {0}` and homogeneous of
degree one, and the manuscript's pressure-multiplier discussion uses the concrete symbols
`ς_{jl}(ξ) = i ξ ξ_j ξ_l / |ξ|²` of that class.  This file records that the
class is inhabited by the paper's own symbol, and that the inhabitant is not
the zero symbol, which also satisfies the homogeneity identity but carries no
multiplier.  The frequency integral defining `ς(D)W₊` converges absolutely for
that same symbol, so the kernel of `SpatialMultiplierKernel` is meaningful at
the paper's object and not only at a hypothetical one.
-/

open scoped BigOperators
open Set MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- The degree-one homogeneity of External Input `ext:heat-kernel` is satisfied
by the paper's pressure symbol `ς_{jl}`, for every choice of the three indices.
-/
theorem IsDegreeOneHomogeneous_satisfiable (j l m : Fin 3) :
    IsDegreeOneHomogeneous (pressureMultiplierSymbol j l m) :=
  pressureMultiplierSymbol_isDegreeOneHomogeneous j l m

/-- The inhabitant is nontrivial: `ς_{jl}` takes the value `i/3` at the vector
with all three coordinates equal to one, so it is not the zero symbol, which
satisfies degree-one homogeneity vacuously. -/
theorem pressureMultiplierSymbol_ne_zero (j l m : Fin 3) :
    pressureMultiplierSymbol j l m ≠ 0 := by
  intro hzero
  have hval := congrFun hzero (fun _ : Fin 3 => (1 : ℝ))
  have hnorm : vec3EuclideanNorm (fun _ : Fin 3 => (1 : ℝ)) ^ 2 = 3 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    norm_num
  rw [pressureMultiplierSymbol, hnorm, Pi.zero_apply] at hval
  norm_num at hval

/-- The value of `ς_{jl}` at the vector with all coordinates one, which is what
witnesses nontriviality above. -/
theorem pressureMultiplierSymbol_apply_one (j l m : Fin 3) :
    pressureMultiplierSymbol j l m (fun _ : Fin 3 => (1 : ℝ)) =
      Complex.I * ((1 / 3 : ℝ) : ℂ) := by
  have hnorm : vec3EuclideanNorm (fun _ : Fin 3 => (1 : ℝ)) ^ 2 = 3 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    norm_num
  rw [pressureMultiplierSymbol, hnorm]
  norm_num

/-- The linear growth bound of the symbol class is available at the paper's
symbol: there is one constant, fixed before the frequency, with
`‖ς_{jl} ξ‖ ≤ C |ξ|` for every `ξ`. -/
theorem exists_norm_le_pressureMultiplierSymbol (j l m : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Vec3,
      ‖pressureMultiplierSymbol j l m ξ‖ ≤ C * vec3EuclideanNorm ξ :=
  norm_le_of_isDegreeOneHomogeneous
    (pressureMultiplierSymbol_contDiffOn j l m).continuousOn
    (pressureMultiplierSymbol_isDegreeOneHomogeneous j l m)

/-- The frequency integral defining `ς(D)W₊` converges absolutely at the
paper's symbol, so `spatialMultiplierHeatKernel` is given by an honest Bochner
integral there and not by the junk value of a divergent one. -/
theorem integrable_spatialMultiplierHeatIntegrand_pressure (j l m : Fin 3)
    (x : Vec3) {t : ℝ} (ht : 0 < t) :
    Integrable (spatialMultiplierHeatIntegrand (pressureMultiplierSymbol j l m) x t)
      volume :=
  integrable_spatialMultiplierHeatIntegrand
    (pressureMultiplierSymbol_contDiffOn j l m).continuousOn
    (pressureMultiplierSymbol_isDegreeOneHomogeneous j l m) x ht

end CKN.Foundation.Euclidean
