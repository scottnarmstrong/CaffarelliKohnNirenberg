-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Snowflaking

/-!
# The Caffarelli–Kohn–Nirenberg theorems

Theorems A, B and C of the accompanying manuscript, with their definitions
stated using Mathlib alone. The three selected theorem proofs are intentional
placeholders. Comparator compares this environment with `Solution.lean`,
which proves the same named declarations from the CKN library.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKNChallenge

/-! ### Ambient parabolic geometry -/

/-- The spatial carrier: three real coordinates. -/
abbrev Vec3 := Fin 3 → ℝ

/-- The same three coordinates carrying the Euclidean (`L^2`) norm. -/
abbrev L2Vec3 := PiLp 2 (fun _ : Fin 3 => ℝ)

/-- A point of space-time. -/
def ParabolicPoint := Vec3 × ℝ

theorem half_pos : 0 < (1 / 2 : ℝ) := by norm_num

theorem half_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num

/-- The time line with its square-root (parabolic) metric. -/
abbrev SnowTime := Metric.Snowflaking ℝ (1 / 2 : ℝ) half_pos half_le_one

/-- The Euclidean norm of a spatial vector, from the sum of squares. -/
def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)

instance : MeasurableSpace ParabolicPoint := inferInstanceAs (MeasurableSpace (Vec3 × ℝ))

instance : MeasurableSpace SnowTime := borel SnowTime

instance : BorelSpace SnowTime := ⟨rfl⟩

/-- Space-time as a measurable copy of Euclidean space times snowflaked time. -/
def parabolicMeasurableEquiv : ParabolicPoint ≃ᵐ L2Vec3 × SnowTime :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 Vec3) {
    toEquiv := Metric.Snowflaking.toSnowflaking
    measurable_toFun := Metric.Snowflaking.continuous_toSnowflaking.measurable
    measurable_invFun := Metric.Snowflaking.homeomorph.continuous.measurable }

/-- The underlying map of `parabolicMeasurableEquiv`. -/
def parabolicMap (p : ParabolicPoint) :
    L2Vec3 × SnowTime := parabolicMeasurableEquiv p

lemma parabolicMap_injective : Function.Injective parabolicMap := by
  intro p q h
  exact parabolicMeasurableEquiv.injective h

/-- The parabolic metric on space-time, pulled back along `parabolicMap`. -/
noncomputable instance parabolicMetricSpace : MetricSpace ParabolicPoint :=
  MetricSpace.induced parabolicMap parabolicMap_injective inferInstance

/-- The pseudometric underlying `parabolicMetricSpace`. -/
abbrev parabolicPseudoMetricSpace : PseudoMetricSpace ParabolicPoint :=
  MetricSpace.toPseudoMetricSpace (self := parabolicMetricSpace)

instance : SecondCountableTopology ParabolicPoint :=
  Topology.IsInducing.secondCountableTopology (Topology.IsInducing.induced parabolicMap)

instance : BorelSpace ParabolicPoint :=
  MeasurableEmbedding.borelSpace parabolicMeasurableEquiv.measurableEmbedding
    (Topology.IsInducing.induced parabolicMap)

/-- The explicit parabolic distance: space in the Euclidean norm, time in the
square-root metric. -/
def parabolicDist (p q : ParabolicPoint) : ℝ :=
  max (vec3EuclideanNorm (p.1 - q.1)) (Real.sqrt |p.2 - q.2|)

/-- The open Euclidean ball of radius `r` about `x` in space. -/
def vec3Ball (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) < r}

/-- The backward parabolic cylinder of radius `r` with top `(x, t)`. -/
def parabolicCylinder (x : Vec3) (t r : ℝ) : Set ParabolicPoint :=
  vec3Ball x r ×ˢ Ioc (t - r ^ 2) t

instance : MeasureSpace ParabolicPoint := inferInstanceAs (MeasureSpace (Vec3 × ℝ))

/-- The `d`-dimensional Hausdorff measure of the parabolic metric on space-time. -/
def parabolicHausdorffMeasure (d : ℝ≥0∞) : Measure ParabolicPoint :=
  MeasureTheory.Measure.hausdorffMeasure d.toReal

/-! ### Space-time domains and test functions -/

/-- The space-time carrier `Ω × I`. -/
def spaceTimeSet (Ω : Set Vec3) (I : Set ℝ) : Set ParabolicPoint := Ω ×ˢ I

/-- Compactly interior spatial and time subdomains of `Ω` and `I`. -/
def localBox (Ω : Set Vec3) (I : Set ℝ) (Ω' : Set Vec3) (J : Set ℝ) : Prop :=
  IsOpen Ω' ∧ IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω ∧
    OrdConnected J ∧ IsCompact (closure J) ∧ closure J ⊆ I

/-- Smooth compactly supported test functions on `Ω × I`, valued in `V`. -/
def spaceTimeTestFunction {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Ω : Set Vec3) (I : Set ℝ) : Set (Vec3 × ℝ → V) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ spaceTimeSet Ω I}

/-- Local scalar `L^p` membership on a space-time set. -/
def localLp (E : Set ParabolicPoint) (p : ℝ) (g : ParabolicPoint → ℝ) : Prop :=
  MeasureTheory.MemLp g (ENNReal.ofReal p) (volume.restrict E)

/-- Componentwise local vector `L^p` membership on a space-time set. -/
def localVecLp (E : Set ParabolicPoint) (p : ℝ)
    (g : ParabolicPoint → Vec3) : Prop :=
  ∀ i : Fin 3, localLp E p (fun z => g z i)

/-! ### Classical and weak derivatives -/

/-- The `i`th coordinate basis vector of `Vec3`. -/
def basisVec (i : Fin 3) : Vec3 := Pi.single i (1 : ℝ)

/-- The spatial derivative of `g` in the `i`th coordinate, taken on the spatial
factor with the time coordinate frozen. -/
def spatialPartial (g : ParabolicPoint → ℝ) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  (fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) (basisVec i)

/-- The time derivative of `g`, taken on the time factor with the spatial
coordinate frozen. -/
def timePartial (g : ParabolicPoint → ℝ) (z : ParabolicPoint) : ℝ :=
  (fderiv ℝ (fun s : ℝ => g (z.1, s)) z.2) 1

/-- The iterated spatial derivative `∂_j ∂_i g`. -/
def spatialSecondPartial (g : ParabolicPoint → ℝ) (i j : Fin 3)
    (z : ParabolicPoint) : ℝ :=
  spatialPartial (fun w => spatialPartial g i w) j z

/-- The squared spatial-gradient density of the explicit gradient datum `Du`. -/
def spatialGradientSq (_u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) : ℝ :=
  ∑ i, ∑ j, (Du z i j) ^ (2 : ℕ)

/-- `gi` is the `i`th weak derivative of `u` on the spatial open set `U`. -/
def HasWeakPartialDerivOn (U : Set Vec3) (i : Fin 3)
    (u gi : Vec3 → ℝ) : Prop :=
  ∀ φ : Vec3 → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume

/-- `Du` is a coordinate weak gradient of `u` on the spatial open set `U`. -/
def HasWeakGradientOn
    (U : Set Vec3) (u : Vec3 → ℝ) (Du : Vec3 → Vec3) : Prop :=
  ∀ i : Fin 3, HasWeakPartialDerivOn U i u (fun x => Du x i)

/-! ### Suitable weak solutions -/

/-- The suitable weak-solution class of the manuscript: a divergence-free
distributional solution of the forced Navier-Stokes system with an explicit
gradient datum, finite local energies, and the local energy inequality against
nonnegative test functions.

The clauses are the four of the manuscript's definition, in order: the
regularity class, the incompressibility identity, the weak momentum identity
and the local energy inequality.  The last three carry no integrability side
condition on the integrand they test; the integrals appearing there are simply
asserted to vanish, or to satisfy an inequality. -/
def IsSuitableWeakSolution (Ω : Set Vec3) (I : Set ℝ) (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) : Prop :=
  IsOpen Ω ∧ IsOpen I ∧ OrdConnected I ∧ 5 / 2 < q ∧
    (∀ Ω' J, localBox Ω I Ω' J → localVecLp (spaceTimeSet Ω' J) q f) ∧
    (∀ Ω' J, localBox Ω I Ω' J →
      AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω' J)) ∧
      essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
          (volume.restrict J) < ⊤ ∧
      (∫⁻ z in spaceTimeSet Ω' J,
          ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (spaceTimeSet Ω' J)) ∧
      MemLp f (ENNReal.ofReal q)
          (volume.restrict (spaceTimeSet Ω' J)) ∧
      ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i)) ∧
    (∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      ∫ z in spaceTimeSet Ω I,
        ∑ i, u z i * spatialPartial ψ i z = 0) ∧
    (∀ φ : Vec3 × ℝ → Vec3, φ ∈ spaceTimeTestFunction (V := Vec3) Ω I →
      ∫ z in spaceTimeSet Ω I,
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, f z i * φ z i = 0) ∧
    (∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z)

/-! ### Regular points and parabolic Hoelder classes -/

/-- Vector-valued parabolic Hoelder control on `U` with exponent `γ`. -/
def ParabolicHolderVecOn (U : Set ParabolicPoint) (g : ParabolicPoint → Vec3)
    (γ : ℝ) : Prop :=
  ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧
    (∀ z ∈ U, vec3EuclideanNorm (g z) ≤ B) ∧
    (∀ z ∈ U, ∀ w ∈ U,
      vec3EuclideanNorm (g z - g w) ≤ K * parabolicDist z w ^ γ)

/-- The same Hoelder control with the sum of the sup norm and the seminorm bounded by `C`. -/
def ParabolicHolderVecNormLE (U : Set ParabolicPoint) (g : ParabolicPoint → Vec3)
    (γ C : ℝ) : Prop :=
  ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ B + K ≤ C ∧
    (∀ z ∈ U, vec3EuclideanNorm (g z) ≤ B) ∧
    (∀ z ∈ U, ∀ w ∈ U,
      vec3EuclideanNorm (g z - g w) ≤ K * parabolicDist z w ^ γ)

/-- `z₀` is a regular point of `u`: on some space-time neighbourhood of `z₀`,
`u` agrees almost everywhere with a parabolically Hoelder continuous field. -/
def IsRegularPoint (Ω : Set Vec3) (I : Set ℝ)
    (u : ParabolicPoint → Vec3) (z₀ : ParabolicPoint) : Prop :=
  z₀ ∈ spaceTimeSet Ω I ∧
    ∃ N : Set ParabolicPoint, IsOpen N ∧ z₀ ∈ N ∧
      N ⊆ spaceTimeSet Ω I ∧ ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict N] u ∧ ParabolicHolderVecOn N w γ

/-- The singular set of `u`: the points of the space-time domain that are not
regular points. -/
def SingularSet (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3) :
    Set ParabolicPoint :=
  {z | z ∈ spaceTimeSet Ω I ∧ ¬ IsRegularPoint Ω I u z}

/-! ### Theorem A -/

/-- Epsilon-regularity under the `L^3` smallness condition: there are constants
`ε₀ > 0`, `γ₀ ∈ (0, 2/3]` and `C₄ ≥ 0`, depending only on `q`, such that any
suitable weak solution on a space-time domain containing the closed unit
parabolic cylinder, whose velocity, pressure and force are small there in the
natural scale-invariant norms, has a parabolically Hoelder continuous
representative on the half cylinder, with an explicit bound on its Hoelder
norm, and every point of the interior half cylinder is a regular point. -/
theorem epsilonRegularityL3 (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolution Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z :=
  by sorry

/-! ### Theorem B -/

/-- Epsilon-regularity under the scaled-gradient smallness condition: there is
a constant `ε₁ > 0` depending only on `q` such that a point of the space-time domain of a
suitable weak solution at which the scaled gradient energy on shrinking
parabolic cylinders has limsup below `ε₁ ^ 2` is a regular point. -/
theorem epsilonRegularityGradient (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        (hsol : IsSuitableWeakSolution Ω I q u Du p f) →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          IsRegularPoint Ω I u z₀ :=
  by sorry

/-! ### Theorem C -/

/-- The singular set of a suitable weak solution is null for the
one-dimensional parabolic Hausdorff measure. -/
theorem caffarelliKohnNirenberg (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolution Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 :=
  by sorry

end CKNChallenge
