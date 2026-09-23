-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.Snowflaking

/-!
# The Caffarelli–Kohn–Nirenberg theorems

A standalone, Mathlib-only statement of Theorems A, B and C. Space-time has
ordinary coordinates for the Navier–Stokes equations and the parabolic metric
only where that metric is mathematically relevant.
-/

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Gradient InnerProductSpace NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKNChallenge

/-! ## Local weak Navier–Stokes solutions -/

/-- Three-dimensional Euclidean space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The usual notation for a Hilbert-valued `L²` space. -/
local notation "L²(" α ", " E ")" => Lp E 2 (volume : Measure α)

/-! ### Test functions and spatial differential operators -/

/-- Smooth compactly supported `Y`-valued functions supported in `Ω`. -/
def testFunctions
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ω : Set X) : Set (X → Y) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω}

local notation "Dₓ" g:arg z:arg =>
  fderiv ℝ (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "∂ₜ" g:arg z:arg =>
  fderiv ℝ (fun t : ℝ ↦ g (Prod.fst z, t)) (Prod.snd z) 1
local notation "∇ₓ" g:arg z:arg =>
  gradient (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "divₓ" g:arg z:arg =>
  LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap (Dₓ g z))
local notation "Δₓ" g:arg z:arg =>
  Laplacian.laplacian (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "⟪" A ", " B "⟫ₕₛ" =>
  LinearMap.trace ℝ ℝ³
    (ContinuousLinearMap.toLinearMap (ContinuousLinearMap.adjoint A ∘L B))
local infixr:100 " ⊗ᵣ " => InnerProductSpace.rankOne ℝ

/-- `Du` is the weak derivative of `u` on `U` for the ambient measure. The
definition is coordinate-free for real Hilbert spaces equipped with a measure.
For the Euclidean spaces and volume used below, almost-everywhere
uniqueness on open sets follows from Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
structure HasWeakDerivativeOn
    {X Y : Type*}
    [MeasureSpace X]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (u : X → Y) (Du : X → (X →L[ℝ] Y)) : Prop where
  functionLocallyIntegrable : LocallyIntegrableOn u U volume
  derivativeLocallyIntegrable : LocallyIntegrableOn Du U volume
  integral_eq : ∀ φ ∈ testFunctions ℝ U, ∀ v (y' : Y →L[ℝ] ℝ),
    ∫ x in U, φ x * y' (Du x v) ∂volume =
      -∫ x in U, ⟪∇ φ x, v⟫_ℝ * y' (u x) ∂volume

/-! ### The solution class -/

/-- The fields of the Navier–Stokes system together with a chosen global weak
spatial gradient of the velocity. -/
structure NSEData (Ω : Set ℝ³) (I : Set ℝ) where
  isOpenSpace : IsOpen Ω
  isOpenTime : IsOpen I
  ordConnectedTime : OrdConnected I
  u : ℝ³ × ℝ → ℝ³
  Dxu : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)
  p : ℝ³ × ℝ → ℝ
  f : ℝ³ × ℝ → ℝ³
  weakDerivative :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakDerivativeOn Ω (fun x ↦ u (x, t)) (fun x ↦ Dxu (x, t))

/-- `U ⋐ Ω` means that the closure of `U` is compact and contained in `Ω`. -/
def IsCompactlyContained
    {X : Type*} [TopologicalSpace X] (U Ω : Set X) : Prop :=
  IsCompact (closure U) ∧ closure U ⊆ Ω

local infix:50 " ⋐ " => IsCompactlyContained

/-- The energy-class bounds on a fixed space-time product set `U × J`. -/
structure HasEnergyRegularityOn
    {Ω : Set ℝ³} {I : Set ℝ} (data : NSEData Ω I) (q : ℝ≥0)
    (U : Set ℝ³) (J : Set ℝ) : Prop where
  velocityTimeBound :
    essSup (fun t ↦ eLpNorm (fun x ↦ data.u (x, t)) 2
      (volume.restrict U)) (volume.restrict J) < ∞
  velocityMemLp : MemLp data.u 2 (volume.restrict (U ×ˢ J))
  gradientMemLp : MemLp data.Dxu 2 (volume.restrict (U ×ˢ J))
  pressureMemLp : MemLp data.p (3 / 2) (volume.restrict (U ×ˢ J))
  forceMemLp : MemLp data.f q (volume.restrict (U ×ˢ J))

/-- The incompressibility and momentum equations in distributional form. -/
structure SolvesDistributionalNSE
    {Ω : Set ℝ³} {I : Set ℝ} (data : NSEData Ω I) : Prop where
  incompressible : ∀ ψ ∈ testFunctions ℝ (Ω ×ˢ I),
    ∫ z in Ω ×ˢ I, ⟪data.u z, ∇ₓ ψ z⟫_ℝ = 0
  momentum : ∀ φ ∈ testFunctions ℝ³ (Ω ×ˢ I),
    ∫ z in Ω ×ˢ I,
      ⟪data.u z, ∂ₜ φ z⟫_ℝ
        + ⟪data.u z ⊗ᵣ data.u z, Dₓ φ z⟫ₕₛ
        - ⟪data.Dxu z, Dₓ φ z⟫ₕₛ
        + data.p z * divₓ φ z
        + ⟪data.f z, φ z⟫_ℝ = 0

/-- The local energy inequality for nonnegative test functions. -/
def SatisfiesLocalEnergyInequality
    {Ω : Set ℝ³} {I : Set ℝ} (data : NSEData Ω I) : Prop :=
  ∀ ψ ∈ testFunctions ℝ (Ω ×ˢ I), (∀ z, 0 ≤ ψ z) →
    2 * ∫ z in Ω ×ˢ I, ⟪data.Dxu z, data.Dxu z⟫ₕₛ * ψ z ≤
      ∫ z in Ω ×ˢ I,
        ‖data.u z‖ ^ 2 * (∂ₜ ψ z + Δₓ ψ z)
          + (‖data.u z‖ ^ 2 + 2 * data.p z) * ⟪data.u z, ∇ₓ ψ z⟫_ℝ
          + 2 * ⟪data.f z, data.u z⟫_ℝ * ψ z

/-- A local suitable weak solution: finite-energy data satisfying the
distributional Navier–Stokes equations and the local energy inequality. -/
structure LocalWeakNSESolution
    (Ω : Set ℝ³) (I : Set ℝ) (q : ℝ≥0)
    extends NSEData Ω I where
  energyRegularity : ∀ (U : Set ℝ³) (J : Set ℝ),
    IsOpen U ∧ U ⋐ Ω ∧ OrdConnected J ∧ J ⋐ I →
      HasEnergyRegularityOn toNSEData q U J
  equations : SolvesDistributionalNSE toNSEData
  energyInequality : SatisfiesLocalEnergyInequality toNSEData

/-! ## Parabolic geometry and regularity -/

/-- `ℝ` equipped with the metric `dist s t = |s - t|^(1/2)`, used to define
the parabolic Hausdorff dimension. -/
abbrev Rpar :=
  Metric.Snowflaking ℝ (1 / 2 : ℝ) (by norm_num) (by norm_num)

instance : MeasurableSpace Rpar := borel Rpar
instance : BorelSpace Rpar := ⟨rfl⟩

/-- Hausdorff measure for the parabolic metric, written in ordinary
space-time coordinates. -/
def parabolicHausdorffMeasure (d : ℝ) : Measure (ℝ³ × ℝ) :=
  Measure.map
    ((Homeomorph.refl ℝ³).prodCongr
      (Metric.Snowflaking.homeomorph : Rpar ≃ₜ ℝ)).toMeasurableEquiv
    (Measure.hausdorffMeasure d : Measure (ℝ³ × Rpar))

/-- The backward cylinder `Qᵣ(z₀) = Bᵣ(x₀) × (t₀-r²,t₀]`, with optional top
centre `z₀ = (x₀,t₀)` defaulting to the origin. -/
abbrev Q (r : ℝ) (z₀ : ℝ³ × ℝ := 0) : Set (ℝ³ × ℝ) :=
  Metric.ball z₀.1 r ×ˢ Ioc (z₀.2 - r ^ 2) z₀.2

/-- The Hölder norm of an almost-everywhere equivalence class: the infimum,
over all representatives, of the supremum norm plus Hölder seminorm. -/
def aeHolderNormOn
    {X Y : Type*} [PseudoEMetricSpace X] [MeasureSpace X]
    [SeminormedAddCommGroup Y]
    (U : Set X) (g : X → Y) (γ : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (w : X → Y) (_ : w =ᵐ[volume.restrict U] g),
    (⨆ x : U, ‖w x‖ₑ) + eHolderNorm γ (U.domRestrict w)

/-- Local Hölder regularity at a point, for arbitrary metric-measure spaces. -/
def IsHolderRegularPoint
    {X Y : Type*} [PseudoEMetricSpace X] [MeasureSpace X]
    [SeminormedAddCommGroup Y]
    (u : X → Y) (x₀ : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
    ∃ γ : ℝ≥0, 0 < γ ∧ γ ≤ 1 ∧ aeHolderNormOn U u γ < ∞

/-- The points of `Ω` where `u` has no local Hölder representative. Ordinary
space-time Hölder regularity is used here; on bounded cylinders it is
equivalent to parabolic Hölder regularity after halving the exponent. -/
def singularSet
    (Ω : Set ℝ³) (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) : Set (ℝ³ × ℝ) :=
  {z ∈ Ω ×ˢ I | ¬IsHolderRegularPoint u z}

/-! ## The three theorems -/

/-- Theorem A: scale-invariant smallness on the unit cylinder gives a
quantitatively Hölder representative on the half-cylinder. -/
theorem epsilonRegularityL3 (q : ℝ≥0) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ≥0,
      0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧
      ∀ (Ω : Set ℝ³) (I : Set ℝ) (sol : LocalWeakNSESolution Ω I q),
        closure (Q 1) ⊆ Ω ×ˢ I →
        (∫⁻ z in Q 1,
          ‖sol.u z‖ₑ ^ (3 : ℝ) + ‖sol.p z‖ₑ ^ (3 / 2 : ℝ) +
            ‖sol.f z‖ₑ ^ (q : ℝ)) ≤ ε₀ →
        aeHolderNormOn (closure (Q (1 / 2))) sol.u γ₀ ≤ C₄ :=
  by sorry

/-- The squared scale-invariant Dirichlet energy
`β(z₀,r)² = r⁻¹ ∫∫_{Qᵣ(z₀)} |∇u|²` from Theorem B. -/
def betaSq
    (Dₓu : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) (z₀ : ℝ³ × ℝ) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ *
    ∫⁻ z in Q r z₀, ENNReal.ofReal ⟪Dₓu z, Dₓu z⟫ₕₛ

local notation "β²" => betaSq

/-- Theorem B: sufficiently small limiting scaled gradient energy makes an
interior point regular. -/
theorem epsilonRegularityGradient (q : ℝ≥0) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ≥0, 0 < ε₁ ∧
      ∀ (Ω : Set ℝ³) (I : Set ℝ) (sol : LocalWeakNSESolution Ω I q),
        ∀ z₀ ∈ Ω ×ˢ I,
        limsup (β² sol.Dxu z₀) (𝓝[>] (0 : ℝ)) < ε₁ ^ 2 →
        z₀ ∉ singularSet Ω I sol.u :=
  by sorry

/-- Theorem C: the singular set has zero one-dimensional parabolic Hausdorff
measure. -/
theorem caffarelliKohnNirenberg (q : ℝ≥0) (hq : 5 / 2 < q) :
    ∀ (Ω : Set ℝ³) (I : Set ℝ) (sol : LocalWeakNSESolution Ω I q),
      parabolicHausdorffMeasure 1 (singularSet Ω I sol.u) = 0 :=
  by sorry

end CKNChallenge
