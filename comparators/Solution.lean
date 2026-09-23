-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.


import CKN.Statements.TheoremA
import CKN.Statements.TheoremB
import CKN.Statements.TheoremC
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

/-- The squared scale-invariant Dirichlet energy
`β(z₀,r)² = r⁻¹ ∫∫_{Qᵣ(z₀)} |∇u|²` from Theorem B. -/
def betaSq
    (Dₓu : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) (z₀ : ℝ³ × ℝ) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ *
    ∫⁻ z in Q r z₀, ENNReal.ofReal ⟪Dₓu z, Dₓu z⟫ₕₛ

local notation "β²" => betaSq
abbrev RawSpace := CKN.Foundation.Parabolic.Vec3
abbrev RawPoint := CKN.Foundation.Parabolic.ParabolicPoint

theorem volume_rawPoint_eq_product :
    (volume : Measure RawPoint) =
      (volume : Measure (RawSpace × ℝ)) := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod,
    MeasureTheory.Measure.volume_eq_prod]

theorem ofReal_three_halves :
    ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_ofReal (by norm_num)]
  norm_num

def rawToEuclidean : RawSpace ≃L[ℝ] ℝ³ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm


def rawSpaceTimeLinear : (RawSpace × ℝ) ≃L[ℝ] (ℝ³ × ℝ) :=
  rawToEuclidean.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] theorem rawSpaceTimeLinear_apply (z : RawSpace × ℝ) :
    rawSpaceTimeLinear z = (rawToEuclidean z.1, z.2) := by
  rfl

@[simp] theorem rawToEuclidean_prodCongr_refl_apply (z : RawSpace × ℝ) :
    (rawToEuclidean.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)) z =
      (rawToEuclidean z.1, z.2) := by
  rfl

def rawSpaceTimeToEuclidean : (RawSpace × ℝ) ≃ₜ (ℝ³ × ℝ) :=
  rawSpaceTimeLinear.toHomeomorph

/-- The identity on space-time coordinates, first forgetting the old
parabolic topology and then using Euclidean spatial coordinates. -/
def parabolicToEuclideanHomeomorph : RawPoint ≃ₜ (ℝ³ × ℝ) :=
  CKN.Foundation.Parabolic.parabolicHomeomorph.trans
    rawSpaceTimeToEuclidean

@[simp] theorem parabolicToEuclideanHomeomorph_apply (z : RawPoint) :
    parabolicToEuclideanHomeomorph z = (rawToEuclidean z.1, z.2) := by
  rfl

/-- The old parabolic metric is exactly the product of Euclidean space with
snowflaked time used by the comparator. -/
def rawParabolicIsometry : RawPoint ≃ᵢ (ℝ³ × Rpar) where
  toEquiv := CKN.Foundation.Parabolic.parabolicMeasurableEquiv.toEquiv
  isometry_toFun := fun _ _ ↦ rfl

@[simp] theorem rawParabolicIsometry_apply (z : RawPoint) :
    rawParabolicIsometry z =
      (rawToEuclidean z.1, Metric.Snowflaking.toSnowflaking z.2) := by
  rfl

@[simp] theorem rawSpaceTimeToEuclidean_fst (z : RawSpace × ℝ) :
    (rawSpaceTimeToEuclidean z).1 = rawToEuclidean z.1 := by
  rfl

@[simp] theorem rawSpaceTimeToEuclidean_snd (z : RawSpace × ℝ) :
    (rawSpaceTimeToEuclidean z).2 = z.2 := by
  rfl

@[simp] theorem rawSpaceTimeToEuclidean_apply (z : RawSpace × ℝ) :
    rawSpaceTimeToEuclidean z = (rawToEuclidean z.1, z.2) := by
  rfl

theorem rawSpaceTimeToEuclidean_measurePreserving :
    MeasurePreserving rawSpaceTimeToEuclidean := by
  change MeasurePreserving (Prod.map (WithLp.toLp 2) id)
    (volume.prod volume) (volume.prod volume)
  exact (PiLp.volume_preserving_toLp (Fin 3)).prod (MeasurePreserving.id volume)

theorem parabolicToEuclidean_measurePreserving :
    MeasurePreserving parabolicToEuclideanHomeomorph
      (volume : Measure RawPoint) (volume : Measure (ℝ³ × ℝ)) := by
  refine ⟨parabolicToEuclideanHomeomorph.continuous.measurable, ?_⟩
  rw [volume_rawPoint_eq_product]
  exact rawSpaceTimeToEuclidean_measurePreserving.map_eq

theorem rawToEuclidean_measurePreserving : MeasurePreserving rawToEuclidean := by
  change MeasurePreserving (WithLp.toLp 2) volume volume
  exact PiLp.volume_preserving_toLp (Fin 3)

@[simp] theorem vec3EuclideanNorm_rawToEuclidean_symm (v : ℝ³) :
    CKN.Foundation.Parabolic.vec3EuclideanNorm (rawToEuclidean.symm v) = ‖v‖ := by
  rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  rfl

def euclideanSpace (U : Set RawSpace) : Set ℝ³ := rawToEuclidean '' U

def rawSpace (Ω : Set ℝ³) : Set RawSpace := rawToEuclidean ⁻¹' Ω

@[simp] theorem euclideanSpace_rawSpace (Ω : Set ℝ³) :
    euclideanSpace (rawSpace Ω) = Ω := by
  exact Equiv.image_preimage rawToEuclidean.toEquiv Ω

@[simp] theorem rawToEuclidean_preimage_euclideanSpace (U : Set RawSpace) :
    rawToEuclidean ⁻¹' euclideanSpace U = U := by
  exact Equiv.preimage_image rawToEuclidean.toEquiv U

@[simp] theorem rawSpaceTime_preimage_product (U : Set RawSpace) (J : Set ℝ) :
    rawSpaceTimeToEuclidean ⁻¹' (euclideanSpace U ×ˢ J) = U ×ˢ J := by
  ext z
  simp [rawSpaceTimeToEuclidean, rawSpaceTimeLinear, euclideanSpace]

theorem rawToEuclidean_restrict_measurePreserving (U : Set RawSpace) :
    MeasurePreserving rawToEuclidean
      (volume.restrict U) (volume.restrict (euclideanSpace U)) := by
  simpa using rawToEuclidean_measurePreserving.restrict_preimage_emb
    rawToEuclidean.toHomeomorph.measurableEmbedding (euclideanSpace U)

theorem rawSpaceTime_restrict_measurePreserving (U : Set RawSpace) (J : Set ℝ) :
    MeasurePreserving rawSpaceTimeToEuclidean
      (volume.restrict (U ×ˢ J))
      (volume.restrict (euclideanSpace U ×ˢ J)) := by
  simpa using rawSpaceTimeToEuclidean_measurePreserving.restrict_preimage_emb
    rawSpaceTimeToEuclidean.measurableEmbedding (euclideanSpace U ×ˢ J)

theorem energyRegularity_on_euclideanBox
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q)
    {U : Set RawSpace} {J : Set ℝ}
    (hbox : CKN.localBox (rawSpace Ω) I U J) :
    HasEnergyRegularityOn sol.toNSEData q (euclideanSpace U) J := by
  rcases hbox with ⟨hUopen, hUcompact, hUΩ, hJconn, hJcompact, hJI⟩
  apply sol.energyRegularity (euclideanSpace U) J
  refine ⟨rawToEuclidean.toHomeomorph.isOpenMap U hUopen, ⟨?_, ?_⟩,
    hJconn, hJcompact, hJI⟩
  · change IsCompact (closure (rawToEuclidean '' U))
    have hclosure : closure (rawToEuclidean '' U) =
        rawToEuclidean '' closure U := by
      exact rawToEuclidean.toHomeomorph.image_closure U |>.symm
    rw [hclosure]
    exact hUcompact.image rawToEuclidean.continuous
  · change closure (rawToEuclidean '' U) ⊆ Ω
    have hclosure : closure (rawToEuclidean '' U) =
        rawToEuclidean '' closure U := by
      exact rawToEuclidean.toHomeomorph.image_closure U |>.symm
    rw [hclosure]
    rintro _ ⟨x, hx, rfl⟩
    exact hUΩ hx

def pullVelocity (u : ℝ³ × ℝ → ℝ³) : RawSpace × ℝ → RawSpace :=
  fun z ↦ rawToEuclidean.symm (u (rawSpaceTimeToEuclidean z))

def pullScalar (g : ℝ³ × ℝ → ℝ) : RawSpace × ℝ → ℝ :=
  fun z ↦ g (rawSpaceTimeToEuclidean z)

def pushScalar (g : RawSpace × ℝ → ℝ) : ℝ³ × ℝ → ℝ :=
  fun z ↦ g (rawSpaceTimeToEuclidean.symm z)

def pushVector (g : RawSpace × ℝ → RawSpace) : ℝ³ × ℝ → ℝ³ :=
  fun z ↦ rawToEuclidean (g (rawSpaceTimeToEuclidean.symm z))

@[simp] theorem pushScalar_rawSpaceTimeToEuclidean
    (g : RawSpace × ℝ → ℝ) (z : RawSpace × ℝ) :
    pushScalar g (rawSpaceTimeToEuclidean z) = g z := by
  change g (rawSpaceTimeToEuclidean.symm (rawSpaceTimeToEuclidean z)) = g z
  rw [rawSpaceTimeToEuclidean.symm_apply_apply]

@[simp] theorem pushVector_rawSpaceTimeToEuclidean
    (g : RawSpace × ℝ → RawSpace) (z : RawSpace × ℝ) :
    pushVector g (rawSpaceTimeToEuclidean z) = rawToEuclidean (g z) := by
  change rawToEuclidean
    (g (rawSpaceTimeToEuclidean.symm (rawSpaceTimeToEuclidean z))) = _
  rw [rawSpaceTimeToEuclidean.symm_apply_apply]

@[simp] theorem pushScalar_rawCoordinates
    (g : RawSpace × ℝ → ℝ) (z : RawSpace × ℝ) :
    pushScalar g (rawToEuclidean z.1, z.2) = g z := by
  rw [← rawSpaceTimeToEuclidean_apply z]
  exact pushScalar_rawSpaceTimeToEuclidean g z

@[simp] theorem pushVector_rawCoordinates
    (g : RawSpace × ℝ → RawSpace) (z : RawSpace × ℝ) :
    pushVector g (rawToEuclidean z.1, z.2) = rawToEuclidean (g z) := by
  rw [← rawSpaceTimeToEuclidean_apply z]
  exact pushVector_rawSpaceTimeToEuclidean g z

@[simp] theorem rawToEuclidean_pullVelocity
    (u : ℝ³ × ℝ → ℝ³) (z : RawSpace × ℝ) :
    rawToEuclidean (pullVelocity u z) = u (rawToEuclidean z.1, z.2) := by
  simp [pullVelocity]

theorem pushScalar_testFunction
    {Ω : Set ℝ³} {I : Set ℝ} {ψ : RawSpace × ℝ → ℝ}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (rawSpace Ω) I) :
    pushScalar ψ ∈ testFunctions ℝ (Ω ×ˢ I) := by
  rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hψdiff.comp rawSpaceTimeLinear.symm.contDiff
  · exact hψcompact.comp_homeomorph rawSpaceTimeToEuclidean.symm
  · change tsupport (ψ ∘ rawSpaceTimeToEuclidean.symm) ⊆ Ω ×ˢ I
    rw [tsupport_comp_eq_preimage ψ rawSpaceTimeToEuclidean.symm]
    intro z hz
    have hz' := hψsupport hz
    exact hz'

theorem pushVector_testFunction
    {Ω : Set ℝ³} {I : Set ℝ} {φ : RawSpace × ℝ → RawSpace}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (rawSpace Ω) I) :
    pushVector φ ∈ testFunctions ℝ³ (Ω ×ˢ I) := by
  rcases hφ with ⟨hφdiff, hφcompact, hφsupport⟩
  refine ⟨rawToEuclidean.contDiff.comp
    (hφdiff.comp rawSpaceTimeLinear.symm.contDiff), ?_, ?_⟩
  · rw [HasCompactSupport,
      show pushVector φ = rawToEuclidean ∘
        (φ ∘ rawSpaceTimeToEuclidean.symm) by rfl,
      tsupport_comp_eq (fun {_} ↦ rawToEuclidean.map_eq_zero_iff)
        (φ ∘ rawSpaceTimeToEuclidean.symm)]
    exact hφcompact.comp_homeomorph rawSpaceTimeToEuclidean.symm
  · rw [show pushVector φ = rawToEuclidean ∘
        (φ ∘ rawSpaceTimeToEuclidean.symm) by rfl,
      tsupport_comp_eq (fun {_} ↦ rawToEuclidean.map_eq_zero_iff)
        (φ ∘ rawSpaceTimeToEuclidean.symm),
      tsupport_comp_eq_preimage φ rawSpaceTimeToEuclidean.symm]
    intro z hz
    exact hφsupport hz

theorem pushScalar_gradient_apply
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) (i : Fin 3) :
    (gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
      (rawToEuclidean z.1)) i =
        fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) z.1 (CKN.basisVec i) := by
  calc
    _ = ⟪gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1), EuclideanSpace.single i 1⟫_ℝ := by
      symm
      simpa using EuclideanSpace.inner_single_right i 1
        (gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
          (rawToEuclidean z.1))
    _ = fderiv ℝ (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1) (EuclideanSpace.single i 1) := inner_gradient_left
    _ = fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) z.1
        (CKN.basisVec i) := by
      change fderiv ℝ (fun x : ℝ³ ↦ ψ (rawToEuclidean.symm x, z.2))
        (rawToEuclidean z.1) (EuclideanSpace.single i 1) = _
      let g : ℝ³ → RawSpace × ℝ := fun x ↦ (rawToEuclidean.symm x, z.2)
      have hg : DifferentiableAt ℝ g (rawToEuclidean z.1) := by
        dsimp [g]
        fun_prop
      have hc : fderiv ℝ (ψ ∘ g) (rawToEuclidean z.1) =
          fderiv ℝ ψ z ∘L fderiv ℝ g (rawToEuclidean z.1) := by
        simpa [g] using fderiv_comp (rawToEuclidean z.1)
          ((hψ.differentiable (by simp)) z) hg
      change (fderiv ℝ (ψ ∘ g) (rawToEuclidean z.1))
        (EuclideanSpace.single i 1) = _
      rw [hc]
      let k : RawSpace → RawSpace × ℝ := fun x ↦ (x, z.2)
      have hk : DifferentiableAt ℝ k z.1 := by
        dsimp [k]
        fun_prop
      have hc' : fderiv ℝ (ψ ∘ k) z.1 =
          fderiv ℝ ψ z ∘L fderiv ℝ k z.1 := by
        simpa [k] using fderiv_comp z.1 ((hψ.differentiable (by simp)) z) hk
      rw [show (fun x : RawSpace ↦ ψ (x, z.2)) = ψ ∘ k by rfl, hc']
      rw [(rawToEuclidean.symm.hasFDerivAt.prodMk
          (hasFDerivAt_const z.2 (rawToEuclidean z.1))).fderiv]
      have hkf : fderiv ℝ k z.1 =
          (ContinuousLinearMap.id ℝ RawSpace).prod 0 := by
        simpa [k] using ((hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk
          (hasFDerivAt_const z.2 z.1)).fderiv
      rw [hkf]
      have hb : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ))
          (EuclideanSpace.single i 1) = CKN.basisVec i := by
        classical
        ext j
        by_cases hji : j = i
        · subst j
          simp [CKN.basisVec, EuclideanSpace.single]
        · simp [CKN.basisVec, EuclideanSpace.single, hji]
      simp [rawToEuclidean, hb]

theorem inner_pushScalar_gradient
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) (v : RawSpace) :
    ⟪rawToEuclidean v,
      gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1)⟫_ℝ =
      ∑ i, v i * fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2))
        z.1 (CKN.basisVec i) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [pushScalar_gradient_apply ψ hψ z i]
  simp [rawToEuclidean, mul_comm]

def rawGradient (D : ℝ³ →L[ℝ] ℝ³) : Fin 3 → RawSpace :=
  fun i j ↦ WithLp.ofLp (D (EuclideanSpace.single j 1)) i

def rawGradientLinear : (ℝ³ →L[ℝ] ℝ³) →ₗ[ℝ] (Fin 3 → RawSpace) where
  toFun := rawGradient
  map_add' D E := by
    ext i j
    simp [rawGradient]
  map_smul' c D := by
    ext i j
    simp [rawGradient]

def rawGradientCLM : (ℝ³ →L[ℝ] ℝ³) →L[ℝ] (Fin 3 → RawSpace) :=
  LinearMap.toContinuousLinearMap rawGradientLinear

theorem rawGradient_pushVector
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) (i j : Fin 3) :
    rawGradient
        (fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, z.2))
          (rawToEuclidean z.1)) i j =
      fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1
        (CKN.basisVec j) := by
  let F : ℝ³ → ℝ³ := fun x ↦ pushVector φ (x, z.2)
  let proj : ℝ³ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i
  have hF : DifferentiableAt ℝ F (rawToEuclidean z.1) := by
    have hpush : ContDiff ℝ (⊤ : ℕ∞) (pushVector φ) :=
      rawToEuclidean.contDiff.comp
        (hφ.comp rawSpaceTimeLinear.symm.contDiff)
    have hfull : DifferentiableAt ℝ (pushVector φ)
        (rawToEuclidean z.1, z.2) :=
      (hpush.differentiable (by simp)) (rawToEuclidean z.1, z.2)
    exact DifferentiableAt.comp (x := rawToEuclidean z.1)
      (f := fun x : ℝ³ ↦ (x, z.2)) (g := pushVector φ)
      hfull (by fun_prop)
  have hcomp : fderiv ℝ (proj ∘ F) (rawToEuclidean z.1) =
      proj ∘L fderiv ℝ F (rawToEuclidean z.1) := by
    simpa using fderiv_comp (rawToEuclidean z.1) proj.differentiableAt hF
  have hφi : ContDiff ℝ (⊤ : ℕ∞) (fun w ↦ φ w i) := by fun_prop
  have hscalar := pushScalar_gradient_apply (fun w ↦ φ w i) hφi z j
  rw [← hscalar]
  change (proj (fderiv ℝ F (rawToEuclidean z.1)
    (EuclideanSpace.single j 1))) = _
  rw [← ContinuousLinearMap.comp_apply, ← hcomp]
  change fderiv ℝ (fun x : ℝ³ ↦ pushScalar (fun w ↦ φ w i) (x, z.2))
      (rawToEuclidean z.1) (EuclideanSpace.single j 1) = _
  symm
  calc
    _ = ⟪gradient (fun x : ℝ³ ↦ pushScalar (fun w ↦ φ w i) (x, z.2))
        (rawToEuclidean z.1), EuclideanSpace.single j 1⟫_ℝ := by
      symm
      simpa using EuclideanSpace.inner_single_right j 1
        (gradient (fun x : ℝ³ ↦ pushScalar (fun w ↦ φ w i) (x, z.2))
          (rawToEuclidean z.1))
    _ = _ := inner_gradient_left

theorem timeDerivative_pushVector_apply
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) (i : Fin 3) :
    (rawToEuclidean.symm
      (fderiv ℝ (fun t : ℝ ↦ pushVector φ (rawToEuclidean z.1, t)) z.2 1)) i =
      fderiv ℝ (fun t : ℝ ↦ φ (z.1, t) i) z.2 1 := by
  let F : ℝ → ℝ³ := fun t ↦ pushVector φ (rawToEuclidean z.1, t)
  let proj : ℝ³ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i
  have hpush : ContDiff ℝ (⊤ : ℕ∞) (pushVector φ) :=
    rawToEuclidean.contDiff.comp
      (hφ.comp rawSpaceTimeLinear.symm.contDiff)
  have hF : DifferentiableAt ℝ F z.2 := by
    exact DifferentiableAt.comp (x := z.2)
      (f := fun t : ℝ ↦ (rawToEuclidean z.1, t)) (g := pushVector φ)
      ((hpush.differentiable (by simp)) (rawToEuclidean z.1, z.2))
      (by fun_prop)
  have hcomp : fderiv ℝ (proj ∘ F) z.2 = proj ∘L fderiv ℝ F z.2 := by
    simpa using fderiv_comp z.2 proj.differentiableAt hF
  change proj (fderiv ℝ F z.2 1) = _
  rw [← ContinuousLinearMap.comp_apply, ← hcomp]
  congr 1


def pullGradient (D : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    RawSpace × ℝ → Fin 3 → RawSpace :=
  fun z ↦ rawGradient (D (rawSpaceTimeToEuclidean z))

theorem transported_memLp
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q)
    {U : Set RawSpace} {J : Set ℝ}
    (hbox : CKN.localBox (rawSpace Ω) I U J) :
    MemLp (pullVelocity sol.u) 2 (volume.restrict (U ×ˢ J)) ∧
      MemLp (pullGradient sol.Dxu) 2 (volume.restrict (U ×ˢ J)) ∧
      MemLp (pullScalar sol.p) (3 / 2)
        (volume.restrict (U ×ˢ J)) ∧
      MemLp (pullVelocity sol.f) q (volume.restrict (U ×ˢ J)) := by
  have hreg := energyRegularity_on_euclideanBox sol hbox
  have hmp := rawSpaceTime_restrict_measurePreserving U J
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply memLp_pi_iff.mpr
    intro i
    have h := (hreg.velocityMemLp.eval_piLp i).comp_measurePreserving hmp
    simpa [Function.comp_def, pullVelocity, rawToEuclidean] using h
  · apply memLp_pi_iff.mpr
    intro i
    apply memLp_pi_iff.mpr
    intro j
    let evalEntry : (ℝ³ →L[ℝ] ℝ³) →L[ℝ] ℝ :=
      (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i).comp
        (ContinuousLinearMap.apply ℝ ℝ³ (EuclideanSpace.single j 1))
    have h := hreg.gradientMemLp.continuousLinearMap_comp evalEntry
    have h' := h.comp_measurePreserving hmp
    simpa [Function.comp_def, pullGradient, rawGradient, evalEntry] using h'
  · change MemLp (fun z ↦ sol.p (rawSpaceTimeToEuclidean z)) (3 / 2)
      (volume.restrict (U ×ˢ J))
    exact hreg.pressureMemLp.comp_measurePreserving hmp
  · apply memLp_pi_iff.mpr
    intro i
    have h := (hreg.forceMemLp.eval_piLp i).comp_measurePreserving hmp
    simpa [Function.comp_def, pullVelocity, rawToEuclidean] using h

def pushSpatialScalar (g : RawSpace → ℝ) : ℝ³ → ℝ :=
  fun x ↦ g (rawToEuclidean.symm x)

theorem pushSpatialScalar_testFunction
    {U : Set RawSpace} {g : RawSpace → ℝ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgcompact : HasCompactSupport g) (hgsupport : tsupport g ⊆ U) :
    pushSpatialScalar g ∈ testFunctions ℝ (euclideanSpace U) := by
  refine ⟨hgdiff.comp rawToEuclidean.symm.contDiff,
    hgcompact.comp_homeomorph rawToEuclidean.symm.toHomeomorph, ?_⟩
  change tsupport (g ∘ ⇑rawToEuclidean.symm.toHomeomorph) ⊆ euclideanSpace U
  rw [tsupport_comp_eq_preimage g rawToEuclidean.symm.toHomeomorph]
  intro x hx
  exact ⟨rawToEuclidean.symm x, hgsupport hx,
    rawToEuclidean.apply_symm_apply x⟩

theorem fderiv_pushSpatialScalar_basis
    (g : RawSpace → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : RawSpace) (j : Fin 3) :
    fderiv ℝ (pushSpatialScalar g) (rawToEuclidean x)
        (EuclideanSpace.single j 1) =
      fderiv ℝ g x (CKN.basisVec j) := by
  have hc := fderiv_comp (rawToEuclidean x)
    ((hg.differentiable (by simp)) x)
    rawToEuclidean.symm.differentiableAt
  change fderiv ℝ (g ∘ (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace))
      (rawToEuclidean x) = _ at hc
  rw [show pushSpatialScalar g =
      g ∘ (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace) by rfl,
    hc, rawToEuclidean.symm.fderiv]
  simp only [rawToEuclidean.symm_apply_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

theorem HasWeakDerivativeOn.restrict
    {X Y : Type*}
    [MeasureSpace X]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U V : Set X} (hVU : V ⊆ U)
    {u : X → Y} {Du : X → (X →L[ℝ] Y)}
    (h : HasWeakDerivativeOn U u Du) :
    HasWeakDerivativeOn V u Du := by
  refine ⟨h.functionLocallyIntegrable.mono_set hVU,
    h.derivativeLocallyIntegrable.mono_set hVU, ?_⟩
  intro φ hφ v y'
  have hφU : φ ∈ testFunctions ℝ U :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩
  have hWeak := h.integral_eq φ hφU v y'
  have hLeftZero :
      ∀ x, x ∉ V → φ x * y' (Du x v) = 0 := by
    intro x hx
    have hxNotIn : x ∉ tsupport φ := fun hx' ↦ hx (hφ.2.2 hx')
    simp [image_eq_zero_of_notMem_tsupport hxNotIn]
  have hRightZero :
      ∀ x, x ∉ V → ⟪∇ φ x, v⟫_ℝ * y' (u x) = 0 := by
    intro x hx
    have hxNotIn : x ∉ tsupport φ := fun hx' ↦ hx (hφ.2.2 hx')
    have hφEq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hxNotIn |>.mono
        (fun y hy ↦ image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.gradient_eq hφEq]
    simp
  have hLeftZeroU :
      ∀ x, x ∉ U → φ x * y' (Du x v) = 0 :=
    fun x hx ↦ hLeftZero x (fun hx' ↦ hx (hVU hx'))
  have hRightZeroU :
      ∀ x, x ∉ U → ⟪∇ φ x, v⟫_ℝ * y' (u x) = 0 :=
    fun x hx ↦ hRightZero x (fun hx' ↦ hx (hVU hx'))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hLeftZero,
    setIntegral_eq_integral_of_forall_compl_eq_zero hRightZero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hLeftZeroU,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hRightZeroU,
    hWeak]

theorem weakGradient_transport
    {U : Set RawSpace} {t : ℝ}
    {u : ℝ³ × ℝ → ℝ³}
    {D : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)}
    (hD : HasWeakDerivativeOn (euclideanSpace U)
      (fun x ↦ u (x, t)) (fun x ↦ D (x, t))) :
    ∀ i, CKN.HasWeakGradientOn U
      (fun x ↦ pullVelocity u (x, t) i)
      (fun x ↦ pullGradient D (x, t) i) := by
  intro i j g hgdiff hgcompact hgsupport
  let ge := pushSpatialScalar g
  have hge : ge ∈ testFunctions ℝ (euclideanSpace U) :=
    pushSpatialScalar_testFunction hgdiff hgcompact hgsupport
  have hscalar := hD.integral_eq ge hge
    (EuclideanSpace.single j 1)
    (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i)
  simp_rw [inner_gradient_left] at hscalar
  have hmp := rawToEuclidean_restrict_measurePreserving U
  have hemb := rawToEuclidean.toHomeomorph.measurableEmbedding
  rw [← hmp.integral_comp hemb, ← hmp.integral_comp hemb] at hscalar
  have hderiv (x : RawSpace) :
      fderiv ℝ ge (rawToEuclidean x) (EuclideanSpace.single j 1) =
        fderiv ℝ g x (CKN.basisVec j) :=
    fderiv_pushSpatialScalar_basis g hgdiff x j
  have hge_apply (x : RawSpace) : ge (rawToEuclidean x) = g x := by
    simp [ge, pushSpatialScalar]
  simp_rw [hge_apply, hderiv] at hscalar
  simp only [PiLp.proj_apply] at hscalar
  have hscalar' :
      (∫ x in U, g x * pullGradient D (x, t) i j) =
        -∫ x in U,
          fderiv ℝ g x (CKN.basisVec j) * pullVelocity u (x, t) i := by
    simpa [pullVelocity, pullGradient, rawGradient,
      rawSpaceTimeToEuclidean, rawSpaceTimeLinear, rawToEuclidean,
      hderiv] using hscalar
  change
    ∫ x in U,
        pullVelocity u (x, t) i * fderiv ℝ g x (CKN.basisVec j) =
      -∫ x in U, pullGradient D (x, t) i j * g x
  calc
    _ = ∫ x in U,
        fderiv ℝ g x (CKN.basisVec j) * pullVelocity u (x, t) i := by
      congr 1
      funext x
      ring
    _ = -∫ x in U, g x * pullGradient D (x, t) i j := by
      linarith
    _ = _ := by
      congr 2
      funext x
      ring

theorem weakDerivative_on_euclideanBox
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q)
    {U : Set RawSpace} {J : Set ℝ}
    (hbox : CKN.localBox (rawSpace Ω) I U J) :
    ∀ᵐ t ∂volume.restrict J,
      HasWeakDerivativeOn (euclideanSpace U)
        (fun x ↦ sol.u (x, t)) (fun x ↦ sol.Dxu (x, t)) := by
  rcases hbox with ⟨_, _, hUΩ, _, _, hJI⟩
  have hJsubset : J ⊆ I := subset_closure.trans hJI
  have hweak := ae_restrict_of_ae_restrict_of_subset hJsubset sol.weakDerivative
  filter_upwards [hweak] with t ht
  apply ht.restrict
  rintro _ ⟨x, hx, rfl⟩
  exact hUΩ (subset_closure hx)

theorem raw_sliceEnergy_le_eLpNorm_sq
    (U : Set RawSpace) (t : ℝ) (u : ℝ³ × ℝ → ℝ³)
    (hu : AEStronglyMeasurable (fun x ↦ u (x, t))
      (volume.restrict (euclideanSpace U))) :
    (∫⁻ x in U, ‖pullVelocity u (x, t)‖ₑ ^ (2 : ℝ)) ≤
      eLpNorm (fun x ↦ u (x, t)) 2
        (volume.restrict (euclideanSpace U)) ^ (2 : ℝ) := by
  let hmp := rawToEuclidean_restrict_measurePreserving U
  calc
    (∫⁻ x in U, ‖pullVelocity u (x, t)‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ x in U, ‖u (rawToEuclidean x, t)‖ₑ ^ (2 : ℝ) := by
      apply lintegral_mono
      intro x
      apply ENNReal.rpow_le_rpow
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal <| by
        calc
          ‖pullVelocity u (x, t)‖ ≤
              CKN.Foundation.Parabolic.vec3EuclideanNorm
                (pullVelocity u (x, t)) :=
            CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm _
          _ = ‖rawToEuclidean (pullVelocity u (x, t))‖ :=
            CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2 _
          _ = ‖u (rawToEuclidean x, t)‖ := by
            simp [pullVelocity, rawSpaceTimeToEuclidean, rawSpaceTimeLinear]
      norm_num
    _ = ∫⁻ x in euclideanSpace U, ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
      exact hmp.lintegral_comp_emb
        rawToEuclidean.toHomeomorph.measurableEmbedding
          (fun x ↦ ‖u (x, t)‖ₑ ^ (2 : ℝ))
    _ = eLpNorm (fun x ↦ u (x, t)) 2
        (volume.restrict (euclideanSpace U)) ^ (2 : ℝ) := by
      symm
      exact eLpNorm_nnreal_pow_eq_lintegral (by norm_num) hu

theorem transported_sliceEnergy_bound
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q)
    {U : Set RawSpace} {J : Set ℝ}
    (hbox : CKN.localBox (rawSpace Ω) I U J) :
    essSup (fun t ↦ ∫⁻ x in U,
      ‖pullVelocity sol.u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict J) < ∞ := by
  have hreg := energyRegularity_on_euclideanBox sol hbox
  let G : ℝ → ℝ≥0∞ := fun t ↦
    eLpNorm (fun x ↦ sol.u (x, t)) 2
      (volume.restrict (euclideanSpace U))
  let M : ℝ≥0∞ := essSup G (volume.restrict J)
  have hM : M < ∞ := hreg.velocityTimeBound
  have hG : ∀ᵐ t ∂volume.restrict J, G t ≤ M := ENNReal.ae_le_essSup G
  have hweak := weakDerivative_on_euclideanBox sol hbox
  have hA : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in U, ‖pullVelocity sol.u (x, t)‖ₑ ^ (2 : ℝ)) ≤
        M ^ (2 : ℝ) := by
    filter_upwards [hweak, hG] with t hweak hGt
    exact (raw_sliceEnergy_le_eLpNorm_sq U t sol.u
      hweak.functionLocallyIntegrable.aestronglyMeasurable).trans
        (ENNReal.rpow_le_rpow hGt (by norm_num))
  exact lt_of_le_of_lt (essSup_le_of_ae_le (M ^ (2 : ℝ)) hA)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne)

theorem transported_jointEnergy_bound
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q)
    {U : Set RawSpace} {J : Set ℝ}
    (hbox : CKN.localBox (rawSpace Ω) I U J) :
    (∫⁻ z in U ×ˢ J,
      ‖pullVelocity sol.u z‖ₑ ^ (2 : ℝ) +
        ‖pullGradient sol.Dxu z‖ₑ ^ (2 : ℝ)) < ∞ := by
  have hmem := transported_memLp sol hbox
  have hu : (∫⁻ z in U ×ˢ J,
      ‖pullVelocity sol.u z‖ₑ ^ (2 : ℝ)) < ∞ := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hmem.1.eLpNorm_lt_top
  have hD : (∫⁻ z in U ×ˢ J,
      ‖pullGradient sol.Dxu z‖ₑ ^ (2 : ℝ)) < ∞ := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hmem.2.1.eLpNorm_lt_top
  rw [lintegral_add_left'
    (hmem.1.aestronglyMeasurable.enorm.pow_const (2 : ℝ))]
  exact ENNReal.add_lt_top.mpr ⟨hu, hD⟩

theorem rawSuitableData
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (hq : 5 / 2 < (q : ℝ)) (sol : LocalWeakNSESolution Ω I q) :
    CKN.IsSuitableWeakSolutionData (rawSpace Ω) I (q : ℝ)
      (pullVelocity sol.u) (pullGradient sol.Dxu)
      (pullScalar sol.p) (pullVelocity sol.f) := by
  refine ⟨?_, sol.isOpenTime, sol.ordConnectedTime, hq, ?_, ?_⟩
  · exact sol.isOpenSpace.preimage rawToEuclidean.continuous
  · intro U J hbox i
    have hi := memLp_pi_iff.mp (transported_memLp sol hbox).2.2.2 i
    unfold CKN.localLp CKN.spaceTimeSet
    rw [volume_rawPoint_eq_product]
    rw [ENNReal.ofReal_coe_nnreal]
    change MemLp (fun z : RawSpace × ℝ ↦ pullVelocity sol.f z i)
      (q : ℝ≥0∞) (volume.restrict (U ×ˢ J))
    exact hi
  · intro U J hbox
    have hmem := transported_memLp sol hbox
    have hweak := weakDerivative_on_euclideanBox sol hbox
    refine ⟨hmem.1.aestronglyMeasurable,
      hmem.2.1.aestronglyMeasurable,
      hmem.2.2.1.aestronglyMeasurable,
      hmem.2.2.2.aestronglyMeasurable,
      transported_sliceEnergy_bound sol hbox,
      transported_jointEnergy_bound sol hbox, ?_, ?_, ?_⟩
    · unfold CKN.spaceTimeSet
      rw [ofReal_three_halves]
      rw [volume_rawPoint_eq_product]
      change MemLp (fun z : RawSpace × ℝ ↦ pullScalar sol.p z)
        (3 / 2) (volume.restrict (U ×ˢ J))
      exact hmem.2.2.1
    · unfold CKN.spaceTimeSet
      rw [ENNReal.ofReal_coe_nnreal]
      rw [volume_rawPoint_eq_product]
      change MemLp (fun z : RawSpace × ℝ ↦ pullVelocity sol.f z)
        (q : ℝ≥0∞) (volume.restrict (U ×ˢ J))
      exact hmem.2.2.2
    · intro i
      filter_upwards [hweak] with t ht
      exact weakGradient_transport ht i

theorem rawGradient_sq (D : ℝ³ →L[ℝ] ℝ³) :
    ∑ i, ∑ j, (rawGradient D i j) ^ 2 =
      LinearMap.trace ℝ ℝ³
        (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint D ∘L D)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace]
  calc
    ∑ i, ∑ j, rawGradient D i j ^ 2 =
        ∑ j, ∑ i, rawGradient D i j ^ 2 := Finset.sum_comm
    _ = ∑ j, ⟪D (EuclideanSpace.single j 1),
          D (EuclideanSpace.single j 1)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [PiLp.inner_apply]
      simp [rawGradient, pow_two]
    _ = ∑ j, ⟪EuclideanSpace.single j 1,
          (ContinuousLinearMap.adjoint D) (D (EuclideanSpace.single j 1))⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (ContinuousLinearMap.adjoint_inner_right D _ _).symm
    _ = ∑ j, ((ContinuousLinearMap.adjoint D)
          (D (EuclideanSpace.single j 1))) j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [EuclideanSpace.inner_single_left]
      simp

theorem rawGradient_pair (D E : ℝ³ →L[ℝ] ℝ³) :
    ∑ i, ∑ j, rawGradient D i j * rawGradient E i j =
      LinearMap.trace ℝ ℝ³
        (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint D ∘L E)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace]
  calc
    ∑ i, ∑ j, rawGradient D i j * rawGradient E i j =
        ∑ j, ∑ i, rawGradient D i j * rawGradient E i j := Finset.sum_comm
    _ = ∑ j, ⟪D (EuclideanSpace.single j 1),
          E (EuclideanSpace.single j 1)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [PiLp.inner_apply]
      simp [rawGradient, mul_comm]
    _ = ∑ j, ⟪EuclideanSpace.single j 1,
          (ContinuousLinearMap.adjoint D) (E (EuclideanSpace.single j 1))⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (ContinuousLinearMap.adjoint_inner_right D _ _).symm
    _ = ∑ j, ((ContinuousLinearMap.adjoint D)
          (E (EuclideanSpace.single j 1))) j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [EuclideanSpace.inner_single_left]
      simp

theorem rawGradient_rankOne (v : RawSpace) (i j : Fin 3) :
    rawGradient (InnerProductSpace.rankOne ℝ
      (rawToEuclidean v) (rawToEuclidean v)) i j = v i * v j := by
  simp [rawGradient, rawToEuclidean, InnerProductSpace.rankOne_apply,
    PiLp.inner_apply, mul_comm]

theorem trace_eq_sum_rawGradient_diagonal (D : ℝ³ →L[ℝ] ℝ³) :
    LinearMap.trace ℝ ℝ³ D.toLinearMap = ∑ i, rawGradient D i i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace]
  rfl

theorem momentum_integrand_transport
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) (u f : RawSpace) (p : ℝ)
    (D : ℝ³ →L[ℝ] ℝ³) :
    let ze := rawSpaceTimeToEuclidean z
    let Dφ := fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, ze.2)) ze.1
    let dtφ := fderiv ℝ (fun t : ℝ ↦ pushVector φ (ze.1, t)) ze.2 1
    ⟪rawToEuclidean u, dtφ⟫_ℝ
        + LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint
            (InnerProductSpace.rankOne ℝ (rawToEuclidean u) (rawToEuclidean u)) ∘L Dφ))
        - LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint D ∘L Dφ))
        + p * LinearMap.trace ℝ ℝ³ Dφ.toLinearMap
        + ⟪rawToEuclidean f, pushVector φ ze⟫_ℝ =
      -(-∑ i, u i * fderiv ℝ (fun t : ℝ ↦ φ (z.1, t) i) z.2 1
        - ∑ i, ∑ j, u i * u j *
            fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1 (CKN.basisVec j)
        + ∑ i, ∑ j, rawGradient D i j *
            fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1 (CKN.basisVec j)
        - p * ∑ i,
            fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1 (CKN.basisVec i)
        - ∑ i, f i * φ z i) := by
  dsimp only
  simp only [rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply]
  rw [← rawGradient_pair, ← rawGradient_pair,
    trace_eq_sum_rawGradient_diagonal]
  simp_rw [rawGradient_rankOne]
  simp_rw [rawGradient_pushVector φ hφ z]
  have ht (i : Fin 3) := timeDerivative_pushVector_apply φ hφ z i
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [show ∀ i, (fderiv ℝ
      (fun t : ℝ ↦ pushVector φ (rawToEuclidean z.1, t)) z.2 1) i =
      fderiv ℝ (fun t : ℝ ↦ φ (z.1, t) i) z.2 1 by
    intro i
    simpa [rawToEuclidean] using ht i]
  have hzraw : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ))
      (WithLp.toLp 2 z.1) = z.1 := by
    ext i
    simp [PiLp.continuousLinearEquiv_apply]
  simp [pushVector, rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    rawToEuclidean, hzraw, mul_comm, mul_assoc]
  ring

theorem iteratedFDeriv_two_same
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x b : E) :
    iteratedFDeriv ℝ 2 g x ![b, b] =
      fderiv ℝ (fun y ↦ fderiv ℝ g y b) x b := by
  rw [iteratedFDeriv_two_apply]
  have hg2 : ContDiff ℝ (1 + 1) g := hg.of_le (by simp)
  have hfd_cont : ContDiff ℝ 1 (fderiv ℝ g) :=
    (contDiff_succ_iff_fderiv.mp hg2).2.2
  have hfd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hfd_cont.differentiable (by norm_num)) x
  have hc := fderiv_clm_apply hfd
    (differentiableAt_const (c := b) (x := x))
  rw [hc]
  simp

theorem laplacian_pushScalar
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) :
    Laplacian.laplacian (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1) =
      ∑ i, fderiv ℝ
        (fun y : RawSpace ↦
          fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) y (CKN.basisVec i))
        z.1 (CKN.basisVec i) := by
  let g : RawSpace → ℝ := fun x ↦ ψ (x, z.2)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact hψ.comp (by fun_prop)
  change Laplacian.laplacian (g ∘ rawToEuclidean.symm)
      (rawToEuclidean z.1) = _
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (g ∘ rawToEuclidean.symm) (EuclideanSpace.basisFun (Fin 3) ℝ))
    (rawToEuclidean z.1)]
  apply Finset.sum_congr rfl
  intro i _
  change (iteratedFDeriv ℝ 2
      (g ∘ (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace))
      (rawToEuclidean z.1))
      ![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
        (EuclideanSpace.basisFun (Fin 3) ℝ) i] = _
  rw [rawToEuclidean.symm.toContinuousLinearMap.iteratedFDeriv_comp_right
    hg (rawToEuclidean z.1) (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hb : rawToEuclidean.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) i) =
      CKN.basisVec i := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [rawToEuclidean, CKN.basisVec, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single]
    · simp [rawToEuclidean, CKN.basisVec, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single, hji]
  have hx : (rawToEuclidean.symm : ℝ³ → RawSpace) (rawToEuclidean z.1) = z.1 :=
    rawToEuclidean.symm_apply_apply z.1
  change (iteratedFDeriv ℝ 2 g
      ((rawToEuclidean.symm : ℝ³ → RawSpace) (rawToEuclidean z.1)))
      (fun k ↦ (rawToEuclidean.symm : ℝ³ → RawSpace)
        (![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          (EuclideanSpace.basisFun (Fin 3) ℝ) i] k)) = _
  rw [hx]
  have hm : (fun k ↦ (rawToEuclidean.symm : ℝ³ → RawSpace)
      (![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
        (EuclideanSpace.basisFun (Fin 3) ℝ) i] k)) =
      ![CKN.basisVec i, CKN.basisVec i] := by
    funext k
    fin_cases k <;> exact hb
  rw [hm, iteratedFDeriv_two_same g hg z.1 (CKN.basisVec i)]

theorem timeDerivative_pushScalar
    (ψ : RawSpace × ℝ → ℝ) (z : RawSpace × ℝ) :
    fderiv ℝ (fun t : ℝ ↦ pushScalar ψ (rawToEuclidean z.1, t)) z.2 1 =
      fderiv ℝ (fun t : ℝ ↦ ψ (z.1, t)) z.2 1 := by
  congr 2

theorem energy_integrand_transport
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) (u f : RawSpace) (p : ℝ) :
    let ze := rawSpaceTimeToEuclidean z
    ‖rawToEuclidean u‖ ^ 2 *
          (fderiv ℝ (fun t : ℝ ↦ pushScalar ψ (ze.1, t)) ze.2 1 +
            Laplacian.laplacian (fun x : ℝ³ ↦ pushScalar ψ (x, ze.2)) ze.1)
        + (‖rawToEuclidean u‖ ^ 2 + 2 * p) *
            ⟪rawToEuclidean u,
              gradient (fun x : ℝ³ ↦ pushScalar ψ (x, ze.2)) ze.1⟫_ℝ
        + 2 * ⟪rawToEuclidean f, rawToEuclidean u⟫_ℝ * pushScalar ψ ze =
      (CKN.Foundation.Parabolic.vec3EuclideanNorm u) ^ 2 *
          (fderiv ℝ (fun t : ℝ ↦ ψ (z.1, t)) z.2 1 +
            ∑ i, fderiv ℝ
              (fun y : RawSpace ↦
                fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) y (CKN.basisVec i))
              z.1 (CKN.basisVec i))
        + ((CKN.Foundation.Parabolic.vec3EuclideanNorm u) ^ 2 + 2 * p) *
            ∑ i, u i * fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2))
              z.1 (CKN.basisVec i)
        + 2 * (∑ i, f i * u i) * ψ z := by
  dsimp only
  simp only [rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply]
  rw [timeDerivative_pushScalar, laplacian_pushScalar ψ hψ z,
    inner_pushScalar_gradient ψ hψ z u,
    ← CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  rw [PiLp.inner_apply]
  have hzraw : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ))
      (WithLp.toLp 2 z.1) = z.1 := by
    ext i
    simp [PiLp.continuousLinearEquiv_apply]
  simp [pushScalar, rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    rawToEuclidean, hzraw, mul_comm]

theorem rawDivergenceFree
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q) :
    ∀ ψ : RawPoint → ℝ,
      ψ ∈ CKN.spaceTimeTestFunction (V := ℝ) (rawSpace Ω) I →
      ∫ z in CKN.spaceTimeSet (rawSpace Ω) I,
        ∑ i, pullVelocity sol.u z i * CKN.spatialPartial ψ i z = 0 := by
  intro ψ hψ
  have hnew := sol.equations.incompressible (pushScalar ψ)
    (pushScalar_testFunction hψ)
  have hmp := rawSpaceTime_restrict_measurePreserving (rawSpace Ω) I
  have hemb := rawSpaceTimeToEuclidean.measurableEmbedding
  simp only [euclideanSpace_rawSpace] at hmp
  rw [← hmp.integral_comp hemb] at hnew
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  change (∫ z : RawSpace × ℝ in rawSpace Ω ×ˢ I,
    ∑ i, pullVelocity sol.u z i * CKN.spatialPartial ψ i z) = 0
  calc
    _ = ∫ z in rawSpace Ω ×ˢ I,
        ⟪sol.u (rawToEuclidean z.1, z.2),
          gradient (fun x : ℝ³ ↦
            pushScalar ψ (x, z.2)) (rawToEuclidean z.1)⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards with z
      have hi := inner_pushScalar_gradient ψ hψ.1 z (pullVelocity sol.u z)
      rw [rawToEuclidean_pullVelocity] at hi
      simpa [rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
        ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.refl_apply, CKN.spatialPartial] using
          hi.symm
    _ = 0 := by
      simpa [rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
        ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.refl_apply] using hnew

theorem rawMomentum
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q) :
    ∀ φ : RawPoint → RawSpace,
      φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) (rawSpace Ω) I →
      ∫ z in CKN.spaceTimeSet (rawSpace Ω) I,
        (-(∑ i, pullVelocity sol.u z i *
            CKN.timePartial (fun w ↦ φ w i) z))
          - ∑ i, ∑ j, pullVelocity sol.u z i * pullVelocity sol.u z j *
              CKN.spatialPartial (fun w ↦ φ w i) j z
          + ∑ i, ∑ j, pullGradient sol.Dxu z i j *
              CKN.spatialPartial (fun w ↦ φ w i) j z
          - pullScalar sol.p z * ∑ i,
              CKN.spatialPartial (fun w ↦ φ w i) i z
          - ∑ i, pullVelocity sol.f z i * φ z i = 0 := by
  intro φ hφ
  have hnew := sol.equations.momentum (pushVector φ) (pushVector_testFunction hφ)
  have hmp := rawSpaceTime_restrict_measurePreserving (rawSpace Ω) I
  have hemb := rawSpaceTimeToEuclidean.measurableEmbedding
  simp only [euclideanSpace_rawSpace] at hmp
  rw [← hmp.integral_comp hemb] at hnew
  let old : RawSpace × ℝ → ℝ := fun z ↦
    (-(∑ i, pullVelocity sol.u z i *
        CKN.timePartial (fun w ↦ φ w i) z))
      - ∑ i, ∑ j, pullVelocity sol.u z i * pullVelocity sol.u z j *
          CKN.spatialPartial (fun w ↦ φ w i) j z
      + ∑ i, ∑ j, pullGradient sol.Dxu z i j *
          CKN.spatialPartial (fun w ↦ φ w i) j z
      - pullScalar sol.p z * ∑ i,
          CKN.spatialPartial (fun w ↦ φ w i) i z
      - ∑ i, pullVelocity sol.f z i * φ z i
  let new : RawSpace × ℝ → ℝ := fun z ↦
    let ze := rawSpaceTimeToEuclidean z
    let Dφ := fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, ze.2)) ze.1
    let dtφ := fderiv ℝ (fun t : ℝ ↦ pushVector φ (ze.1, t)) ze.2 1
    ⟪sol.u ze, dtφ⟫_ℝ
      + LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint
            (InnerProductSpace.rankOne ℝ (sol.u ze) (sol.u ze)) ∘L Dφ))
      - LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint (sol.Dxu ze) ∘L Dφ))
      + sol.p ze * LinearMap.trace ℝ ℝ³ Dφ.toLinearMap
      + ⟪sol.f ze, pushVector φ ze⟫_ℝ
  have hnew' : ∫ z in rawSpace Ω ×ˢ I, new z = 0 := by
    simpa [new] using hnew
  have hpoint (z : RawSpace × ℝ) : new z = -old z := by
    simpa [new, old, pullGradient, pullScalar, CKN.timePartial,
      CKN.spatialPartial] using
      momentum_integrand_transport φ hφ.1 z
        (pullVelocity sol.u z) (pullVelocity sol.f z)
        (pullScalar sol.p z) (sol.Dxu (rawSpaceTimeToEuclidean z))
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  change (∫ z : RawSpace × ℝ in rawSpace Ω ×ˢ I, old z) = 0
  calc
    _ = ∫ z in rawSpace Ω ×ˢ I, -new z := by
      apply integral_congr_ae
      filter_upwards with z
      rw [hpoint]
      simp
    _ = -∫ z in rawSpace Ω ×ˢ I, new z := integral_neg _
    _ = 0 := by rw [hnew']; simp

theorem rawLocalEnergy
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q) :
    ∀ ψ : RawPoint → ℝ,
      ψ ∈ CKN.spaceTimeTestFunction (V := ℝ) (rawSpace Ω) I →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in CKN.spaceTimeSet (rawSpace Ω) I,
          CKN.spatialGradientSq (pullVelocity sol.u)
            (pullGradient sol.Dxu) z * ψ z ≤
        ∫ z in CKN.spaceTimeSet (rawSpace Ω) I,
          (CKN.Foundation.Parabolic.vec3EuclideanNorm
              (pullVelocity sol.u z)) ^ 2 *
              (CKN.timePartial ψ z + ∑ i,
                CKN.spatialSecondPartial ψ i i z)
            + ((CKN.Foundation.Parabolic.vec3EuclideanNorm
                (pullVelocity sol.u z)) ^ 2 + 2 * pullScalar sol.p z) *
                ∑ i, pullVelocity sol.u z i * CKN.spatialPartial ψ i z
            + 2 * (∑ i, pullVelocity sol.f z i *
                pullVelocity sol.u z i) * ψ z := by
  intro ψ hψ hψnonneg
  have htest := pushScalar_testFunction hψ
  have hnonneg : ∀ z, 0 ≤ pushScalar ψ z := by
    intro z
    exact hψnonneg (rawSpaceTimeToEuclidean.symm z)
  have hnew := sol.energyInequality (pushScalar ψ) htest hnonneg
  have hmp := rawSpaceTime_restrict_measurePreserving (rawSpace Ω) I
  have hemb := rawSpaceTimeToEuclidean.measurableEmbedding
  simp only [euclideanSpace_rawSpace] at hmp
  rw [← hmp.integral_comp hemb, ← hmp.integral_comp hemb] at hnew
  let oldD : RawSpace × ℝ → ℝ := fun z ↦
    CKN.spatialGradientSq (pullVelocity sol.u) (pullGradient sol.Dxu) z * ψ z
  let newD : RawSpace × ℝ → ℝ := fun z ↦
    let ze := rawSpaceTimeToEuclidean z
    LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
      (ContinuousLinearMap.adjoint (sol.Dxu ze) ∘L sol.Dxu ze)) *
        pushScalar ψ ze
  let oldR : RawSpace × ℝ → ℝ := fun z ↦
    (CKN.Foundation.Parabolic.vec3EuclideanNorm
        (pullVelocity sol.u z)) ^ 2 *
        (CKN.timePartial ψ z + ∑ i, CKN.spatialSecondPartial ψ i i z)
      + ((CKN.Foundation.Parabolic.vec3EuclideanNorm
          (pullVelocity sol.u z)) ^ 2 + 2 * pullScalar sol.p z) *
          ∑ i, pullVelocity sol.u z i * CKN.spatialPartial ψ i z
      + 2 * (∑ i, pullVelocity sol.f z i * pullVelocity sol.u z i) * ψ z
  let newR : RawSpace × ℝ → ℝ := fun z ↦
    let ze := rawSpaceTimeToEuclidean z
    ‖sol.u ze‖ ^ 2 *
        (fderiv ℝ (fun t : ℝ ↦ pushScalar ψ (ze.1, t)) ze.2 1 +
          Laplacian.laplacian
            (fun x : ℝ³ ↦ pushScalar ψ (x, ze.2)) ze.1)
      + (‖sol.u ze‖ ^ 2 + 2 * sol.p ze) *
          ⟪sol.u ze,
            gradient (fun x : ℝ³ ↦ pushScalar ψ (x, ze.2)) ze.1⟫_ℝ
      + 2 * ⟪sol.f ze, sol.u ze⟫_ℝ * pushScalar ψ ze
  have hnew' :
      2 * ∫ z in rawSpace Ω ×ˢ I, newD z ≤
        ∫ z in rawSpace Ω ×ˢ I, newR z := by
    simpa [newD, newR] using hnew
  have hDpoint (z : RawSpace × ℝ) : oldD z = newD z := by
    change (∑ i, ∑ j,
        (rawGradient (sol.Dxu (rawSpaceTimeToEuclidean z)) i j) ^ 2) * ψ z =
      LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
        (ContinuousLinearMap.adjoint
          (sol.Dxu (rawSpaceTimeToEuclidean z)) ∘L
            sol.Dxu (rawSpaceTimeToEuclidean z))) *
        pushScalar ψ (rawSpaceTimeToEuclidean z)
    rw [rawGradient_sq]
    unfold pushScalar
    rw [rawSpaceTimeToEuclidean.symm_apply_apply]
  have hRpoint (z : RawSpace × ℝ) : newR z = oldR z := by
    simpa [newR, oldR, pullScalar, CKN.timePartial,
      CKN.spatialPartial, CKN.spatialSecondPartial] using
      energy_integrand_transport ψ hψ.1 z
        (pullVelocity sol.u z) (pullVelocity sol.f z) (pullScalar sol.p z)
  unfold CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product]
  change 2 * ∫ z : RawSpace × ℝ in rawSpace Ω ×ˢ I, oldD z ≤
    ∫ z : RawSpace × ℝ in rawSpace Ω ×ˢ I, oldR z
  calc
    _ = 2 * ∫ z in rawSpace Ω ×ˢ I, newD z := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      exact hDpoint z
    _ ≤ ∫ z in rawSpace Ω ×ˢ I, newR z := hnew'
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      exact hRpoint z

theorem rawSuitableWeakSolution
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (hq : 5 / 2 < (q : ℝ)) (sol : LocalWeakNSESolution Ω I q) :
    CKN.IsSuitableWeakSolution (rawSpace Ω) I (q : ℝ)
      (pullVelocity sol.u) (pullGradient sol.Dxu)
      (pullScalar sol.p) (pullVelocity sol.f) := by
  have hdata := rawSuitableData hq sol
  exact ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1,
    hdata.2.2.2.2.1, hdata.2.2.2.2.2,
    rawDivergenceFree sol, rawMomentum sol, rawLocalEnergy sol⟩

theorem rawSpaceTime_preimage_Q (r : ℝ) (z₀ : ℝ³ × ℝ) :
    rawSpaceTimeToEuclidean ⁻¹' Q r z₀ =
      CKN.Foundation.Parabolic.parabolicCylinder
        (rawToEuclidean.symm z₀.1) z₀.2 r := by
  ext z
  change
    (dist (rawToEuclidean z.1) z₀.1 < r ∧
      z.2 ∈ Ioc (z₀.2 - r ^ 2) z₀.2) ↔
    (CKN.Foundation.Parabolic.vec3EuclideanNorm
        (z.1 - rawToEuclidean.symm z₀.1) < r ∧
      z.2 ∈ Ioc (z₀.2 - r ^ 2) z₀.2)
  have hnorm : dist (rawToEuclidean z.1) z₀.1 =
      CKN.Foundation.Parabolic.vec3EuclideanNorm
        (z.1 - rawToEuclidean.symm z₀.1) := by
    rw [dist_eq_norm,
      CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
    change ‖rawToEuclidean z.1 - z₀.1‖ =
      ‖rawToEuclidean (z.1 - rawToEuclidean.symm z₀.1)‖
    rw [map_sub, rawToEuclidean.apply_symm_apply]
  rw [hnorm]

theorem rawSpaceTime_image_cylinder (x₀ : RawSpace) (t₀ r : ℝ) :
    rawSpaceTimeToEuclidean ''
        CKN.Foundation.Parabolic.parabolicCylinder x₀ t₀ r =
      Q r (rawToEuclidean x₀, t₀) := by
  have hpre := rawSpaceTime_preimage_Q r (rawToEuclidean x₀, t₀)
  simp only [rawToEuclidean.symm_apply_apply] at hpre
  unfold CKN.Foundation.Parabolic.parabolicCylinder at hpre ⊢
  rw [← hpre]
  exact Equiv.image_preimage rawSpaceTimeToEuclidean.toEquiv _

theorem closure_Q {r : ℝ} (hr : 0 < r) (z₀ : ℝ³ × ℝ) :
    closure (Q r z₀) =
      Metric.closedBall z₀.1 r ×ˢ Icc (z₀.2 - r ^ 2) z₀.2 := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  rw [Q, closure_prod_eq,
    closure_ball z₀.1 hr.ne',
    closure_Ioc (by linarith : z₀.2 - r ^ 2 ≠ z₀.2)]

theorem mem_closure_cylinder_iff_mem_closure_Q
    {r : ℝ} (hr : 0 < r) (z₀ : RawPoint) (z : RawPoint) :
    z ∈ closure (CKN.Foundation.Parabolic.parabolicCylinder z₀.1 z₀.2 r) ↔
      rawSpaceTimeToEuclidean z ∈
        closure (Q r (rawToEuclidean z₀.1, z₀.2)) := by
  rw [CKN.Foundation.Parabolic.closure_parabolicCylinder hr,
    closure_Q hr]
  change
    (CKN.Foundation.Parabolic.vec3EuclideanNorm (z.1 - z₀.1) ≤ r ∧
      z.2 ∈ Icc (z₀.2 - r ^ 2) z₀.2) ↔
    (dist (rawToEuclidean z.1) (rawToEuclidean z₀.1) ≤ r ∧
      z.2 ∈ Icc (z₀.2 - r ^ 2) z₀.2)
  have hnorm :
      CKN.Foundation.Parabolic.vec3EuclideanNorm (z.1 - z₀.1) =
        dist (rawToEuclidean z.1) (rawToEuclidean z₀.1) := by
    rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2,
      dist_eq_norm, ← map_sub]
    rfl
  rw [hnorm]

theorem Q_aeEq_closure {r : ℝ} (hr : 0 < r) (z₀ : ℝ³ × ℝ) :
    Q r z₀ =ᵐ[(volume : Measure (ℝ³ × ℝ))] closure (Q r z₀) := by
  rw [ae_eq_set]
  constructor
  · rw [sdiff_eq_empty.mpr subset_closure, measure_empty]
  · apply measure_mono_null (t :=
      (Metric.sphere z₀.1 r ×ˢ Icc (z₀.2 - r ^ 2) z₀.2) ∪
        (Metric.closedBall z₀.1 r ×ˢ {z₀.2 - r ^ 2}))
    · intro z hz
      rw [closure_Q hr] at hz
      rcases hz with ⟨⟨hx, ht⟩, hnQ⟩
      change ¬(dist z.1 z₀.1 < r ∧
        z.2 ∈ Ioc (z₀.2 - r ^ 2) z₀.2) at hnQ
      rcases not_and_or.mp hnQ with hnx | hnt
      · left
        refine ⟨?_, ht⟩
        rw [Metric.mem_sphere]
        exact le_antisymm hx (not_lt.mp hnx)
      · right
        refine ⟨hx, ?_⟩
        simp only [mem_singleton_iff]
        rcases ht with ⟨htlo, hthi⟩
        have hnotlo : ¬z₀.2 - r ^ 2 < z.2 := fun hz ↦ hnt ⟨hz, hthi⟩
        exact le_antisymm (not_lt.mp hnotlo) htlo
    · apply measure_union_null
      · rw [MeasureTheory.Measure.volume_eq_prod,
          MeasureTheory.Measure.prod_prod,
          MeasureTheory.Measure.addHaar_sphere, zero_mul]
      · rw [MeasureTheory.Measure.volume_eq_prod,
          MeasureTheory.Measure.prod_prod, measure_singleton, mul_zero]

theorem parabolicDist_le_sqrt_dist_on_halfCylinder
    {z w : RawPoint}
    (hz : rawSpaceTimeToEuclidean z ∈ closure (Q (1 / 2)))
    (hw : rawSpaceTimeToEuclidean w ∈ closure (Q (1 / 2))) :
    CKN.Foundation.Parabolic.parabolicDist z w ≤
      Real.sqrt (dist (rawSpaceTimeToEuclidean z)
        (rawSpaceTimeToEuclidean w)) := by
  rw [closure_Q (by norm_num : (0 : ℝ) < 1 / 2)] at hz hw
  change rawToEuclidean z.1 ∈ Metric.closedBall 0 (1 / 2) ∧
    z.2 ∈ Icc (0 - (1 / 2 : ℝ) ^ 2) 0 at hz
  change rawToEuclidean w.1 ∈ Metric.closedBall 0 (1 / 2) ∧
    w.2 ∈ Icc (0 - (1 / 2 : ℝ) ^ 2) 0 at hw
  rcases hz with ⟨hzx, hzt⟩
  rcases hw with ⟨hwx, hwt⟩
  have hx : dist (rawToEuclidean z.1) (rawToEuclidean w.1) ≤ 1 := by
    calc
      dist (rawToEuclidean z.1) (rawToEuclidean w.1) ≤
          dist (rawToEuclidean z.1) 0 + dist 0 (rawToEuclidean w.1) :=
        dist_triangle _ _ _
      _ ≤ 1 / 2 + 1 / 2 := by
        gcongr
        · simpa [Metric.mem_closedBall] using hzx
        · rw [dist_comm]
          simpa [Metric.mem_closedBall] using hwx
      _ = 1 := by norm_num
  have ht : dist z.2 w.2 ≤ 1 := by
    rw [Real.dist_eq, abs_le]
    constructor <;> rcases hzt with ⟨hztl, hztr⟩ <;>
      rcases hwt with ⟨hwtl, hwtr⟩ <;> norm_num at * <;> linarith
  let d := dist (rawSpaceTimeToEuclidean z) (rawSpaceTimeToEuclidean w)
  have hd : d = max (dist (rawToEuclidean z.1) (rawToEuclidean w.1))
      (dist z.2 w.2) := by
    rfl
  have hdle : d ≤ 1 := by rw [hd]; exact max_le hx ht
  have hspace : dist (rawToEuclidean z.1) (rawToEuclidean w.1) ≤
      Real.sqrt d := by
    exact (hd.symm ▸ le_max_left _ _).trans
      (Real.le_sqrt_self_iff.mpr hdle)
  have htime : Real.sqrt (dist z.2 w.2) ≤ Real.sqrt d := by
    apply Real.sqrt_le_sqrt
    exact hd.symm ▸ le_max_right _ _
  rw [CKN.Foundation.Parabolic.parabolicDist,
    CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  have hspace_eq : ‖WithLp.toLp 2 (z.1 - w.1)‖ =
      dist (rawToEuclidean z.1) (rawToEuclidean w.1) := by
    rw [dist_eq_norm, ← map_sub]
    rfl
  rw [hspace_eq, ← Real.dist_eq]
  exact max_le hspace htime

theorem parabolicDist_le_sqrt_dist_of_dist_le_one
    (z w : RawPoint)
    (hd : dist (rawSpaceTimeToEuclidean z)
      (rawSpaceTimeToEuclidean w) ≤ 1) :
    CKN.Foundation.Parabolic.parabolicDist z w ≤
      Real.sqrt (dist (rawSpaceTimeToEuclidean z)
        (rawSpaceTimeToEuclidean w)) := by
  let d := dist (rawSpaceTimeToEuclidean z) (rawSpaceTimeToEuclidean w)
  have hspace : dist (rawToEuclidean z.1) (rawToEuclidean w.1) ≤
      Real.sqrt d := by
    exact (le_max_left _ _).trans
      (Real.le_sqrt_self_iff.mpr hd)
  have htime : Real.sqrt (dist z.2 w.2) ≤ Real.sqrt d := by
    apply Real.sqrt_le_sqrt
    exact le_max_right _ _
  rw [CKN.Foundation.Parabolic.parabolicDist,
    CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  have hspace_eq : ‖WithLp.toLp 2 (z.1 - w.1)‖ =
      dist (rawToEuclidean z.1) (rawToEuclidean w.1) := by
    rw [dist_eq_norm, ← map_sub]
    rfl
  rw [hspace_eq, ← Real.dist_eq]
  exact max_le hspace htime

theorem pushVector_dist_eq_vec3EuclideanNorm
    (w : RawSpace × ℝ → RawSpace) (z z' : RawSpace × ℝ) :
    dist (pushVector w (rawSpaceTimeToEuclidean z))
        (pushVector w (rawSpaceTimeToEuclidean z')) =
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') := by
  rw [pushVector_rawSpaceTimeToEuclidean,
    pushVector_rawSpaceTimeToEuclidean, dist_eq_norm,
    CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  change ‖rawToEuclidean (w z) - rawToEuclidean (w z')‖ =
    ‖rawToEuclidean (w z - w z')‖
  rw [map_sub]

theorem pushVector_holderOnWith_image
    {N : Set RawPoint} {w : RawSpace × ℝ → RawSpace} {γ B K : ℝ}
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hsup : ∀ z ∈ N,
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) ≤ B)
    (hseminorm : ∀ z ∈ N, ∀ z' ∈ N,
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
        K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ) :
    HolderOnWith ⟨max K (2 * B), hK.trans (le_max_left _ _)⟩
      ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩ (pushVector w)
      (parabolicToEuclideanHomeomorph '' N) := by
  intro x hx x' hx'
  rcases hx with ⟨z, hz, hzx⟩
  rcases hx' with ⟨z', hz', hzx'⟩
  have hxcoord : x = rawSpaceTimeToEuclidean z := by rw [← hzx]; rfl
  have hx'coord : x' = rawSpaceTimeToEuclidean z' := by rw [← hzx']; rfl
  rw [hxcoord, hx'coord]
  have hout := pushVector_dist_eq_vec3EuclideanNorm w z z'
  let d := dist (rawSpaceTimeToEuclidean z) (rawSpaceTimeToEuclidean z')
  have hreal :
      dist (pushVector w (rawSpaceTimeToEuclidean z))
          (pushVector w (rawSpaceTimeToEuclidean z')) ≤
        max K (2 * B) * d ^ (γ / 2) := by
    rw [hout]
    by_cases hd : d ≤ 1
    · have hpar := parabolicDist_le_sqrt_dist_of_dist_le_one z z' hd
      have hpar0 : 0 ≤ CKN.Foundation.Parabolic.parabolicDist z z' := by
        unfold CKN.Foundation.Parabolic.parabolicDist
        positivity
      have hpow := Real.rpow_le_rpow hpar0 hpar hγ.le
      calc
        _ ≤ K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ :=
          hseminorm z hz z' hz'
        _ ≤ K * Real.sqrt d ^ γ :=
          mul_le_mul_of_nonneg_left hpow hK
        _ = K * d ^ (γ / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (dist_nonneg : 0 ≤ d)]
          congr 2
          ring
        _ ≤ max K (2 * B) * d ^ (γ / 2) := by
          gcongr
          exact le_max_left _ _
    · have hnorm :
          CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
            CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) +
              CKN.Foundation.Parabolic.vec3EuclideanNorm (w z') := by
          simp only [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2,
            WithLp.toLp_sub]
          exact norm_sub_le _ _
      have hd1 : 1 ≤ d := le_of_not_ge hd
      have hpow1 : 1 ≤ d ^ (γ / 2) := by
        exact Real.one_le_rpow hd1 (div_nonneg hγ.le (by norm_num))
      calc
        _ ≤ 2 * B := by linarith [hsup z hz, hsup z' hz']
        _ ≤ max K (2 * B) := le_max_right _ _
        _ ≤ max K (2 * B) * d ^ (γ / 2) := by
          nlinarith [hK.trans (le_max_left K (2 * B))]
  rw [edist_dist, edist_dist]
  let C : ℝ≥0 :=
    ⟨max K (2 * B), hK.trans (le_max_left _ _)⟩
  change ENNReal.ofReal
      (dist (pushVector w (rawSpaceTimeToEuclidean z))
        (pushVector w (rawSpaceTimeToEuclidean z'))) ≤
    (C : ℝ≥0∞) * ENNReal.ofReal d ^ (γ / 2)
  rw [show (C : ℝ≥0∞) = ENNReal.ofReal (max K (2 * B)) by
      rw [ENNReal.ofReal_eq_coe_nnreal
        (hK.trans (le_max_left K (2 * B)))]; rfl,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg
      (div_nonneg hγ.le (by norm_num)),
    ← ENNReal.ofReal_mul (hK.trans (le_max_left K (2 * B)))]
  exact ENNReal.ofReal_le_ofReal hreal

theorem pushVector_holder_dist_half
    {w : RawSpace × ℝ → RawSpace} {γ K : ℝ}
    (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hw : ∀ z ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      ∀ z' ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
        K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ) :
    ∀ z ∈ closure (Q (1 / 2)), ∀ z' ∈ closure (Q (1 / 2)),
      dist (pushVector w z) (pushVector w z') ≤
        K * dist z z' ^ (γ / 2) := by
  intro ze hze we hwe
  let z : RawPoint := rawSpaceTimeToEuclidean.symm ze
  let z' : RawPoint := rawSpaceTimeToEuclidean.symm we
  have hzmap : rawSpaceTimeToEuclidean z = ze := by
    exact rawSpaceTimeToEuclidean.apply_symm_apply ze
  have hz'map : rawSpaceTimeToEuclidean z' = we := by
    exact rawSpaceTimeToEuclidean.apply_symm_apply we
  have hzraw : z ∈ closure
      (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)) := by
    have hzq := (mem_closure_cylinder_iff_mem_closure_Q
      (by norm_num : (0 : ℝ) < 1 / 2) ((0 : RawSpace), 0) z).mpr
    apply hzq
    rw [hzmap]
    have hc : (rawToEuclidean (0 : RawSpace), (0 : ℝ)) =
        (0 : ℝ³ × ℝ) := by ext <;> simp
    rw [hc]
    exact hze
  have hz'raw : z' ∈ closure
      (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)) := by
    have hzq := (mem_closure_cylinder_iff_mem_closure_Q
      (by norm_num : (0 : ℝ) < 1 / 2) ((0 : RawSpace), 0) z').mpr
    apply hzq
    rw [hz'map]
    have hc : (rawToEuclidean (0 : RawSpace), (0 : ℝ)) =
        (0 : ℝ³ × ℝ) := by ext <;> simp
    rw [hc]
    exact hwe
  have hpar := parabolicDist_le_sqrt_dist_on_halfCylinder
    (z := z) (w := z') (hzmap.symm ▸ hze) (hz'map.symm ▸ hwe)
  have hpar_nonneg :
      0 ≤ CKN.Foundation.Parabolic.parabolicDist z z' := by
    unfold CKN.Foundation.Parabolic.parabolicDist
    positivity
  have hpow := Real.rpow_le_rpow hpar_nonneg hpar hγ
  have hout : dist (pushVector w ze) (pushVector w we) =
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') := by
    rw [dist_eq_norm,
      CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
    change ‖rawToEuclidean (w z) - rawToEuclidean (w z')‖ =
      ‖rawToEuclidean (w z - w z')‖
    rw [map_sub]
  rw [hout]
  calc
    _ ≤ K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ :=
      hw z hzraw z' hz'raw
    _ ≤ K * Real.sqrt (dist ze we) ^ γ := by
      rw [← hzmap, ← hz'map]
      exact mul_le_mul_of_nonneg_left hpow hK
    _ = K * dist ze we ^ (γ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (dist_nonneg : 0 ≤ dist ze we)]
      congr 2
      ring

theorem pushVector_holderOnWith_half
    {w : RawSpace × ℝ → RawSpace} {γ K : ℝ}
    (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hw : ∀ z ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      ∀ z' ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
        K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ) :
    HolderOnWith ⟨K, hK⟩ ⟨γ / 2, div_nonneg hγ (by norm_num)⟩
      (pushVector w) (closure (Q (1 / 2))) := by
  intro z hz z' hz'
  have hreal := pushVector_holder_dist_half hγ hK hw z hz z' hz'
  rw [edist_dist, edist_dist]
  let Kpos : ℝ≥0 := ⟨K, hK⟩
  change ENNReal.ofReal (dist (pushVector w z) (pushVector w z')) ≤
    (Kpos : ℝ≥0∞) *
      ENNReal.ofReal (dist z z') ^ (γ / 2)
  rw [show (Kpos : ℝ≥0∞) = ENNReal.ofReal K by
      rw [ENNReal.ofReal_eq_coe_nnreal hK]; rfl,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg
      (div_nonneg hγ (by norm_num)),
    ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal hreal

theorem pushVector_aeEq_on_Q
    {r : ℝ} {z₀ : ℝ³ × ℝ} {w : RawSpace × ℝ → RawSpace}
    {u : ℝ³ × ℝ → ℝ³}
    (hw : w =ᵐ[(volume : Measure RawPoint).restrict
        (CKN.Foundation.Parabolic.parabolicCylinder
          (rawToEuclidean.symm z₀.1) z₀.2 r)] pullVelocity u) :
    pushVector w =ᵐ[(volume : Measure (ℝ³ × ℝ)).restrict (Q r z₀)] u := by
  rw [volume_rawPoint_eq_product] at hw
  unfold CKN.Foundation.Parabolic.parabolicCylinder at hw
  let hmp := rawSpaceTimeToEuclidean_measurePreserving.restrict_preimage_emb
    rawSpaceTimeToEuclidean.measurableEmbedding (Q r z₀)
  rw [← hmp.map_eq]
  apply rawSpaceTimeToEuclidean.measurableEmbedding.ae_map_iff.mpr
  rw [rawSpaceTime_preimage_Q]
  filter_upwards [hw] with z hz
  rw [pushVector_rawSpaceTimeToEuclidean, hz,
    rawToEuclidean_pullVelocity]
  rfl

theorem pushVector_aeEq_on_image
    {N : Set RawPoint} {w : RawSpace × ℝ → RawSpace}
    {u : ℝ³ × ℝ → ℝ³}
    (hw : w =ᵐ[(volume : Measure RawPoint).restrict N] pullVelocity u) :
    pushVector w =ᵐ[(volume : Measure (ℝ³ × ℝ)).restrict
      (parabolicToEuclideanHomeomorph '' N)] u := by
  let hmp := parabolicToEuclidean_measurePreserving.restrict_preimage_emb
    parabolicToEuclideanHomeomorph.measurableEmbedding
      (parabolicToEuclideanHomeomorph '' N)
  have hpre : parabolicToEuclideanHomeomorph ⁻¹'
      (parabolicToEuclideanHomeomorph '' N) = N :=
    Equiv.preimage_image parabolicToEuclideanHomeomorph.toEquiv N
  rw [hpre] at hmp
  rw [← hmp.map_eq]
  apply parabolicToEuclideanHomeomorph.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hw] with z hz
  change rawToEuclidean (w z) = u (rawToEuclidean z.1, z.2)
  rw [hz]
  change rawToEuclidean
    (rawToEuclidean.symm (u (rawToEuclidean z.1, z.2))) = _
  rw [rawToEuclidean.apply_symm_apply]

theorem pushVector_enorm_le_image
    {N : Set RawPoint} {w : RawSpace × ℝ → RawSpace} {B : ℝ}
    (hw : ∀ z ∈ N,
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) ≤ B) :
    ∀ z : parabolicToEuclideanHomeomorph '' N,
      ‖pushVector w z‖ₑ ≤ ENNReal.ofReal B := by
  rintro ⟨ze, z, hz, hze⟩
  subst ze
  change ‖rawToEuclidean (w z)‖ₑ ≤ ENNReal.ofReal B
  rw [← ofReal_norm,
    show ‖rawToEuclidean (w z)‖ =
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) by
        exact (CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2 _).symm]
  exact ENNReal.ofReal_le_ofReal (hw z hz)

theorem pushVector_aeHolderNormOn_image_lt_top
    {N : Set RawPoint} {u : ℝ³ × ℝ → ℝ³}
    {w : RawSpace × ℝ → RawSpace} {γ : ℝ} (hγ : 0 < γ)
    (hae : w =ᵐ[(volume : Measure RawPoint).restrict N] pullVelocity u)
    (hholder : CKN.ParabolicHolderVecOn N w γ) :
    aeHolderNormOn (parabolicToEuclideanHomeomorph '' N) u
      ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩ < ∞ := by
  rcases hholder with ⟨B, K, hB, hK, hsup, hseminorm⟩
  have haeImage := pushVector_aeEq_on_image hae
  have hHolder :=
    (pushVector_holderOnWith_image hγ hK hsup hseminorm).holderWith
  let C : ℝ≥0 := ⟨max K (2 * B), hK.trans (le_max_left _ _)⟩
  have hHolderNorm :
      eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
          ((parabolicToEuclideanHomeomorph '' N).domRestrict
            (pushVector w)) ≤ (C : ℝ≥0∞) :=
    hHolder.eHolderNorm_le
  unfold aeHolderNormOn
  calc
    (⨅ (v : ℝ³ × ℝ → ℝ³)
        (_ : v =ᵐ[volume.restrict
          (parabolicToEuclideanHomeomorph '' N)] u),
        (⨆ z : parabolicToEuclideanHomeomorph '' N, ‖v z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((parabolicToEuclideanHomeomorph '' N).domRestrict v)) ≤
        (⨆ z : parabolicToEuclideanHomeomorph '' N,
          ‖pushVector w z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((parabolicToEuclideanHomeomorph '' N).domRestrict
              (pushVector w)) :=
      iInf_le_of_le (pushVector w) (iInf_le_of_le haeImage le_rfl)
    _ ≤ ENNReal.ofReal B + (C : ℝ≥0∞) :=
      add_le_add (iSup_le (pushVector_enorm_le_image hsup)) hHolderNorm
    _ < ∞ := ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, ENNReal.coe_lt_top⟩

theorem isHolderRegularPoint_of_rawRegular
    {Ω : Set ℝ³} {I : Set ℝ} {u : ℝ³ × ℝ → ℝ³} {z₀ : RawPoint}
    (hreg : CKN.IsRegularPoint (rawSpace Ω) I (pullVelocity u) z₀) :
    IsHolderRegularPoint u (parabolicToEuclideanHomeomorph z₀) := by
  rcases hreg with ⟨_, N, hNopen, hzN, _, γ, hγ, hγle, w, hae, hholder⟩
  refine ⟨parabolicToEuclideanHomeomorph '' N,
    parabolicToEuclideanHomeomorph.isOpenMap N hNopen,
    ⟨z₀, hzN, rfl⟩,
    ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩, ?_, ?_, ?_⟩
  · exact div_pos hγ (by norm_num)
  · change γ / 2 ≤ (1 : ℝ)
    linarith
  · exact pushVector_aeHolderNormOn_image_lt_top hγ hae hholder

theorem pushVector_enorm_le_half
    {w : RawSpace × ℝ → RawSpace} {B : ℝ}
    (hw : ∀ z ∈ closure
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)),
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) ≤ B) :
    ∀ z : closure (Q (1 / 2)), ‖pushVector w z‖ₑ ≤
      ENNReal.ofReal B := by
  intro ze
  let z : RawPoint := rawSpaceTimeToEuclidean.symm ze
  have hzmap : rawSpaceTimeToEuclidean z = ze := by
    exact rawSpaceTimeToEuclidean.apply_symm_apply ze
  have hzraw : z ∈ closure
      (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)) := by
    have hzq := (mem_closure_cylinder_iff_mem_closure_Q
      (by norm_num : (0 : ℝ) < 1 / 2) ((0 : RawSpace), 0) z).mpr
    apply hzq
    rw [hzmap]
    have hc : (rawToEuclidean (0 : RawSpace), (0 : ℝ)) =
        (0 : ℝ³ × ℝ) := by ext <;> simp
    rw [hc]
    exact ze.property
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖pushVector w ze‖ =
        CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) := by
      rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
      change ‖rawToEuclidean
        (w (rawSpaceTimeToEuclidean.symm ze))‖ = ‖rawToEuclidean (w z)‖
      rw [show rawSpaceTimeToEuclidean.symm ze = z by rfl]
    _ ≤ B := hw z hzraw

theorem pushVector_aeHolderNorm_half
    {u : ℝ³ × ℝ → ℝ³} {w : RawSpace × ℝ → RawSpace}
    {γ C : ℝ} (hγ : 0 < γ)
    (hae : w =ᵐ[(volume : Measure RawPoint).restrict
        (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2))]
      pullVelocity u)
    (hholder : CKN.ParabolicHolderVecNormLE
      (closure (CKN.Foundation.Parabolic.parabolicCylinder 0 0 (1 / 2)))
      w γ C) :
    aeHolderNormOn (closure (Q (1 / 2))) u
      ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩ ≤ ENNReal.ofReal C := by
  rcases hholder with ⟨B, K, hB, hK, hBKC, hsup, hseminorm⟩
  have haeQ : pushVector w =ᵐ[
      (volume : Measure (ℝ³ × ℝ)).restrict (Q (1 / 2))] u := by
    apply pushVector_aeEq_on_Q (r := 1 / 2) (z₀ := 0)
    have hc : rawToEuclidean.symm (0 : ℝ³) = (0 : RawSpace) := by simp
    simpa only [Prod.fst_zero, Prod.snd_zero, hc] using hae
  have haeClosure : pushVector w =ᵐ[
      (volume : Measure (ℝ³ × ℝ)).restrict (closure (Q (1 / 2)))] u := by
    have hmeas := Measure.restrict_congr_set
      (Q_aeEq_closure (by norm_num : (0 : ℝ) < 1 / 2) (0 : ℝ³ × ℝ))
    rw [← hmeas]
    exact haeQ
  have hHolder := (pushVector_holderOnWith_half hγ.le hK hseminorm).holderWith
  have hHolderNorm :
      eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
          ((closure (Q (1 / 2))).domRestrict (pushVector w)) ≤
        ENNReal.ofReal K := by
    rw [ENNReal.ofReal_eq_coe_nnreal hK]
    exact hHolder.eHolderNorm_le
  unfold aeHolderNormOn
  calc
    (⨅ (v : ℝ³ × ℝ → ℝ³)
        (_ : v =ᵐ[volume.restrict (closure (Q (1 / 2)))] u),
        (⨆ z : closure (Q (1 / 2)), ‖v z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((closure (Q (1 / 2))).domRestrict v)) ≤
        (⨆ z : closure (Q (1 / 2)), ‖pushVector w z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((closure (Q (1 / 2))).domRestrict (pushVector w)) :=
      iInf_le_of_le (pushVector w) (iInf_le_of_le haeClosure le_rfl)
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal K :=
      add_le_add (iSup_le (pushVector_enorm_le_half hsup))
        hHolderNorm
    _ = ENNReal.ofReal (B + K) := by
      rw [ENNReal.ofReal_add hB hK]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hBKC

theorem smallness_integral_transport
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q) :
    (∫⁻ z : RawPoint in
        CKN.Foundation.Parabolic.parabolicCylinder 0 0 1,
        ENNReal.ofReal
              (CKN.Foundation.Parabolic.vec3EuclideanNorm
                (pullVelocity sol.u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |pullScalar sol.p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal
              (CKN.Foundation.Parabolic.vec3EuclideanNorm
                (pullVelocity sol.f z)) ^ (q : ℝ)) =
      ∫⁻ z in Q 1,
        ‖sol.u z‖ₑ ^ (3 : ℝ) + ‖sol.p z‖ₑ ^ (3 / 2 : ℝ) +
          ‖sol.f z‖ₑ ^ (q : ℝ) := by
  rw [volume_rawPoint_eq_product]
  unfold CKN.Foundation.Parabolic.parabolicCylinder
  change
    (∫⁻ z : RawSpace × ℝ in
        CKN.Foundation.Parabolic.vec3Ball 0 1 ×ˢ Ioc (0 - 1 ^ 2) 0,
        ENNReal.ofReal
              (CKN.Foundation.Parabolic.vec3EuclideanNorm
                (pullVelocity sol.u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |pullScalar sol.p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal
              (CKN.Foundation.Parabolic.vec3EuclideanNorm
                (pullVelocity sol.f z)) ^ (q : ℝ)) = _
  let hmp := rawSpaceTimeToEuclidean_measurePreserving.restrict_preimage_emb
    rawSpaceTimeToEuclidean.measurableEmbedding (Q 1)
  have hchange := hmp.lintegral_comp_emb
    rawSpaceTimeToEuclidean.measurableEmbedding
    (fun z ↦ ‖sol.u z‖ₑ ^ (3 : ℝ) +
      ‖sol.p z‖ₑ ^ (3 / 2 : ℝ) + ‖sol.f z‖ₑ ^ (q : ℝ))
  rw [rawSpaceTime_preimage_Q] at hchange
  unfold CKN.Foundation.Parabolic.parabolicCylinder at hchange
  simp only [Prod.fst_zero, Prod.snd_zero, map_zero] at hchange
  norm_num only [one_pow, zero_sub]
  calc
    _ = ∫⁻ z in CKN.Foundation.Parabolic.vec3Ball 0 1 ×ˢ Ioc (-1) 0,
        (‖sol.u (rawSpaceTimeToEuclidean z)‖ₑ ^ (3 : ℝ) +
          ‖sol.p (rawSpaceTimeToEuclidean z)‖ₑ ^ (3 / 2 : ℝ) +
          ‖sol.f (rawSpaceTimeToEuclidean z)‖ₑ ^ (q : ℝ)) := by
      apply lintegral_congr
      intro z
      simp only [pullVelocity, pullScalar,
        vec3EuclideanNorm_rawToEuclidean_symm, Real.norm_eq_abs,
        ← ofReal_norm]
    _ = _ := by simpa only [one_div, one_pow, zero_sub] using hchange

theorem gradient_integral_transport
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q) (z₀ : RawPoint) (r : ℝ) :
    (∫⁻ z : RawPoint in
        CKN.Foundation.Parabolic.parabolicCylinder z₀.1 z₀.2 r,
        ENNReal.ofReal
          (CKN.spatialGradientSq (pullVelocity sol.u)
            (pullGradient sol.Dxu) z)) =
      ∫⁻ z in Q r (rawToEuclidean z₀.1, z₀.2),
        ENNReal.ofReal
          (LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
            (ContinuousLinearMap.adjoint (sol.Dxu z) ∘L sol.Dxu z))) := by
  rw [volume_rawPoint_eq_product]
  unfold CKN.Foundation.Parabolic.parabolicCylinder
  change
    (∫⁻ z : RawSpace × ℝ in
        CKN.Foundation.Parabolic.vec3Ball z₀.1 r ×ˢ
          Ioc (z₀.2 - r ^ 2) z₀.2,
        ENNReal.ofReal
          (CKN.spatialGradientSq (pullVelocity sol.u)
            (pullGradient sol.Dxu) z)) = _
  let hmp := rawSpaceTimeToEuclidean_measurePreserving.restrict_preimage_emb
    rawSpaceTimeToEuclidean.measurableEmbedding
      (Q r (rawToEuclidean z₀.1, z₀.2))
  have hchange := hmp.lintegral_comp_emb
    rawSpaceTimeToEuclidean.measurableEmbedding
    (fun z ↦ ENNReal.ofReal
      (LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
        (ContinuousLinearMap.adjoint (sol.Dxu z) ∘L sol.Dxu z))))
  rw [rawSpaceTime_preimage_Q] at hchange
  unfold CKN.Foundation.Parabolic.parabolicCylinder at hchange
  simp only [rawToEuclidean.symm_apply_apply] at hchange
  calc
    _ = ∫⁻ z in CKN.Foundation.Parabolic.vec3Ball z₀.1 r ×ˢ
          Ioc (z₀.2 - r ^ 2) z₀.2,
        ENNReal.ofReal
          (LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
            (ContinuousLinearMap.adjoint
              (sol.Dxu (rawSpaceTimeToEuclidean z)) ∘L
                sol.Dxu (rawSpaceTimeToEuclidean z)))) := by
      apply lintegral_congr
      intro z
      congr 1
      exact rawGradient_sq (sol.Dxu (rawSpaceTimeToEuclidean z))
    _ = _ := hchange

theorem betaSq_transport
    {Ω : Set ℝ³} {I : Set ℝ} {q : ℝ≥0}
    (sol : LocalWeakNSESolution Ω I q) (z₀ : RawPoint) (r : ℝ) :
    betaSq sol.Dxu (parabolicToEuclideanHomeomorph z₀) r =
      (ENNReal.ofReal r)⁻¹ *
        ∫⁻ z : RawPoint in
          CKN.Foundation.Parabolic.parabolicCylinder z₀.1 z₀.2 r,
          ENNReal.ofReal
            (CKN.spatialGradientSq (pullVelocity sol.u)
              (pullGradient sol.Dxu) z) := by
  unfold betaSq
  rw [gradient_integral_transport]
  rfl

theorem parabolicHausdorffMeasure_one_image (S : Set RawPoint) :
    parabolicHausdorffMeasure 1
        (parabolicToEuclideanHomeomorph '' S) =
      CKN.Foundation.Parabolic.parabolicHausdorffMeasure 1 S := by
  let e : (ℝ³ × Rpar) ≃ₜ (ℝ³ × ℝ) :=
    (Homeomorph.refl ℝ³).prodCongr
      (Metric.Snowflaking.homeomorph : Rpar ≃ₜ ℝ)
  have he (z : RawPoint) : e (rawParabolicIsometry z) =
      parabolicToEuclideanHomeomorph z := by
    rfl
  have hpre : e.toMeasurableEquiv ⁻¹'
      (parabolicToEuclideanHomeomorph '' S) = rawParabolicIsometry '' S := by
    ext y
    constructor
    · rintro ⟨z, hz, heq⟩
      refine ⟨z, hz, ?_⟩
      apply e.injective
      exact (he z).trans heq
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, (he z).symm⟩
  unfold parabolicHausdorffMeasure
  change Measure.map e.toMeasurableEquiv
      (Measure.hausdorffMeasure 1 : Measure (ℝ³ × Rpar))
        (parabolicToEuclideanHomeomorph '' S) = _
  rw [MeasurableEquiv.map_apply, hpre,
    rawParabolicIsometry.hausdorffMeasure_image]
  rfl

theorem epsilonRegularityL3 (q : ℝ≥0) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ≥0,
      0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧
      ∀ (Ω : Set ℝ³) (I : Set ℝ) (sol : LocalWeakNSESolution Ω I q),
        closure (Q 1) ⊆ Ω ×ˢ I →
        (∫⁻ z in Q 1,
          ‖sol.u z‖ₑ ^ (3 : ℝ) + ‖sol.p z‖ₑ ^ (3 / 2 : ℝ) +
            ‖sol.f z‖ₑ ^ (q : ℝ)) ≤ ε₀ →
        aeHolderNormOn (closure (Q (1 / 2))) sol.u γ₀ ≤ C₄ := by
  rcases CKN.epsilonRegularityL3 (q : ℝ) hq with
    ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄, hold⟩
  refine ⟨⟨ε₀, hε₀.le⟩, ⟨γ₀ / 2, div_nonneg hγ₀.le (by norm_num)⟩,
    ⟨C₄, hC₄⟩, ?_, ?_, ?_, ?_⟩
  · exact hε₀
  · exact div_pos hγ₀ (by norm_num)
  · change γ₀ / 2 ≤ (2 / 3 : ℝ)
    linarith
  · intro Ω I sol hdomain hsmall
    have hdomainRaw :
        closure (CKN.Foundation.Parabolic.parabolicCylinder 0 0 1) ⊆
          CKN.spaceTimeSet (rawSpace Ω) I := by
      intro z hz
      have hznew : rawSpaceTimeToEuclidean z ∈ closure (Q 1) := by
        apply (mem_closure_cylinder_iff_mem_closure_Q one_pos
          ((0 : RawSpace), 0) z).mp hz
      have hzdomain := hdomain hznew
      change rawToEuclidean z.1 ∈ Ω ∧ z.2 ∈ I
      exact ⟨hzdomain.1, hzdomain.2⟩
    have hsmallRaw :
        (∫⁻ z : RawPoint in
            CKN.Foundation.Parabolic.parabolicCylinder 0 0 1,
            ENNReal.ofReal
                  (CKN.Foundation.Parabolic.vec3EuclideanNorm
                    (pullVelocity sol.u z)) ^ (3 : ℝ) +
              ENNReal.ofReal |pullScalar sol.p z| ^ (3 / 2 : ℝ) +
              ENNReal.ofReal
                  (CKN.Foundation.Parabolic.vec3EuclideanNorm
                    (pullVelocity sol.f z)) ^ (q : ℝ)) ≤
          ENNReal.ofReal ε₀ := by
      rw [smallness_integral_transport]
      rw [ENNReal.ofReal_eq_coe_nnreal hε₀.le]
      exact hsmall
    rcases hold (rawSpace Ω) I (pullVelocity sol.u)
      (pullGradient sol.Dxu) (pullScalar sol.p) (pullVelocity sol.f)
      (rawSuitableWeakSolution (by exact_mod_cast hq) sol)
      hdomainRaw hsmallRaw with ⟨w, hae, hholder, _⟩
    have hnorm := pushVector_aeHolderNorm_half hγ₀ hae hholder
    rw [ENNReal.ofReal_eq_coe_nnreal hC₄] at hnorm
    exact hnorm

theorem epsilonRegularityGradient (q : ℝ≥0) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ≥0, 0 < ε₁ ∧
      ∀ (Ω : Set ℝ³) (I : Set ℝ) (sol : LocalWeakNSESolution Ω I q),
        ∀ z₀ ∈ Ω ×ˢ I,
        limsup (β² sol.Dxu z₀) (𝓝[>] (0 : ℝ)) < ε₁ ^ 2 →
        z₀ ∉ singularSet Ω I sol.u := by
  rcases CKN.epsilonRegularityGradient (q : ℝ) hq with
    ⟨ε₁, hε₁, hold⟩
  refine ⟨⟨ε₁, hε₁.le⟩, hε₁, ?_⟩
  intro Ω I sol z₀ hz₀ hlim
  let zRaw : RawPoint := (rawToEuclidean.symm z₀.1, z₀.2)
  have hzRaw : zRaw ∈ CKN.spaceTimeSet (rawSpace Ω) I := by
    change rawToEuclidean zRaw.1 ∈ Ω ∧ zRaw.2 ∈ I
    exact ⟨by simpa [zRaw] using hz₀.1, by simpa [zRaw] using hz₀.2⟩
  have hzMap : parabolicToEuclideanHomeomorph zRaw = z₀ := by
    change (rawToEuclidean (rawToEuclidean.symm z₀.1), z₀.2) = z₀
    rw [rawToEuclidean.apply_symm_apply]
  have hlimRaw :
      limsup (fun r : ℝ =>
        (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w : RawPoint in
            CKN.Foundation.Parabolic.parabolicCylinder
              zRaw.1 zRaw.2 r,
            ENNReal.ofReal
              (CKN.spatialGradientSq (pullVelocity sol.u)
                (pullGradient sol.Dxu) w))
        (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) := by
    have hfun : (fun r : ℝ =>
        (ENNReal.ofReal r)⁻¹ *
          ∫⁻ w : RawPoint in
            CKN.Foundation.Parabolic.parabolicCylinder
              zRaw.1 zRaw.2 r,
            ENNReal.ofReal
              (CKN.spatialGradientSq (pullVelocity sol.u)
                (pullGradient sol.Dxu) w)) =
        betaSq sol.Dxu z₀ := by
      funext r
      rw [← betaSq_transport sol zRaw r, hzMap]
    rw [hfun, ENNReal.ofReal_pow hε₁.le,
      ENNReal.ofReal_eq_coe_nnreal hε₁.le]
    exact hlim
  have hrawReg := hold (rawSpace Ω) I (pullVelocity sol.u)
    (pullGradient sol.Dxu) (pullScalar sol.p) (pullVelocity sol.f)
    (rawSuitableWeakSolution (by exact_mod_cast hq) sol)
    zRaw hzRaw hlimRaw
  have hnewReg := isHolderRegularPoint_of_rawRegular hrawReg
  rw [hzMap] at hnewReg
  intro hsing
  exact hsing.2 hnewReg

theorem caffarelliKohnNirenberg (q : ℝ≥0) (hq : 5 / 2 < q) :
    ∀ (Ω : Set ℝ³) (I : Set ℝ) (sol : LocalWeakNSESolution Ω I q),
      parabolicHausdorffMeasure 1 (singularSet Ω I sol.u) = 0 := by
  intro Ω I sol
  have hold := CKN.caffarelliKohnNirenberg (q : ℝ)
    (by exact_mod_cast hq) (rawSpace Ω) I (pullVelocity sol.u)
    (pullGradient sol.Dxu) (pullScalar sol.p) (pullVelocity sol.f)
    (rawSuitableWeakSolution (by exact_mod_cast hq) sol)
  let Sraw := CKN.SingularSet (rawSpace Ω) I (pullVelocity sol.u)
  have hsubset : singularSet Ω I sol.u ⊆
      parabolicToEuclideanHomeomorph '' Sraw := by
    intro z hz
    let zRaw : RawPoint := (rawToEuclidean.symm z.1, z.2)
    have hzMap : parabolicToEuclideanHomeomorph zRaw = z := by
      change (rawToEuclidean (rawToEuclidean.symm z.1), z.2) = z
      rw [rawToEuclidean.apply_symm_apply]
    refine ⟨zRaw, ?_, hzMap⟩
    refine ⟨?_, ?_⟩
    · change rawToEuclidean zRaw.1 ∈ Ω ∧ zRaw.2 ∈ I
      exact ⟨by simpa [zRaw] using hz.1.1, by simpa [zRaw] using hz.1.2⟩
    · intro hregRaw
      have hregNew := isHolderRegularPoint_of_rawRegular hregRaw
      rw [hzMap] at hregNew
      exact hz.2 hregNew
  apply le_antisymm
  · calc
    parabolicHausdorffMeasure 1 (singularSet Ω I sol.u) ≤
        parabolicHausdorffMeasure 1
          (parabolicToEuclideanHomeomorph '' Sraw) := measure_mono hsubset
    _ = CKN.Foundation.Parabolic.parabolicHausdorffMeasure 1 Sraw :=
      parabolicHausdorffMeasure_one_image Sraw
    _ = 0 := hold
  · exact bot_le

end CKNChallenge
