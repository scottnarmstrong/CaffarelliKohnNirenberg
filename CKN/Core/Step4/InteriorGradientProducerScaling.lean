-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.ForceSlotNumericalPressureTransport
import CKN.Setting.ScalingInvariance

/-! # Parabolic dilations about the space-time origin

The quantitative interior pressure-gradient estimate is available on one pair
of radii.  A parabolic dilation centred at the space-time origin moves that
pair inward: the dilated solution carries the Morrey data of the original one
on a proportionally larger cylinder, and its selected pressure gradient
transports back to a selected pressure gradient of the original pressure.

This module collects the transport statements used by that change of
variables: the geometry of the dilated cylinders, the dilated closed unit
cylinder, the dilated cubic data, the dilated Morrey seminorms, and the
backward transport of a selected weak pressure gradient with all of the
clauses in which it is consumed.

Only dilations by a factor at most one are used, so that the dilated unit
cylinder lies inside the original one and no data outside the original unit
cylinder is ever required.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Core.Endgame

set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4

/-- The origin of space-time, the centre of every dilation used here. -/
def originPoint : ParabolicPoint := ((0 : Vec3), (0 : ℝ))

/-- The spatial component of the origin. -/
theorem originPoint_fst : (originPoint.1 : Vec3) = 0 := rfl

/-- The temporal component of the origin. -/
theorem originPoint_snd : (originPoint.2 : ℝ) = 0 := rfl

/-- The spatial component of a dilation about the origin. -/
theorem originScaling_fst (μ : ℝ) (w : ParabolicPoint) :
    (scalingParabolic μ originPoint w).1 = μ • w.1 := by
  simp [scalingParabolic, parabolicTranslate, parabolicScale, originPoint]

/-- The temporal component of a dilation about the origin. -/
theorem originScaling_snd (μ : ℝ) (w : ParabolicPoint) :
    (scalingParabolic μ originPoint w).2 = μ ^ 2 * w.2 := by
  simp [scalingParabolic, parabolicTranslate, parabolicScale, originPoint]

/-- A dilation about the origin fixes the origin. -/
theorem originScaling_origin (μ : ℝ) :
    scalingParabolic μ originPoint originPoint = originPoint := by
  refine Prod.ext ?_ ?_
  · rw [originScaling_fst]; simp [originPoint]
  · rw [originScaling_snd]; simp [originPoint]

/-- The inverse affine centre of a dilation about the origin is the origin. -/
theorem forceSlotInverseCenter_origin (μ : ℝ) :
    forceSlotInverseCenter μ originPoint = originPoint := by
  refine Prod.ext ?_ ?_
  · show -μ⁻¹ • (0 : Vec3) = (0 : Vec3)
    rw [smul_zero]
  · show -(μ⁻¹ ^ 2) * (0 : ℝ) = (0 : ℝ)
    rw [mul_zero]

/-- A dilation about the origin is measurable. -/
theorem originScaling_measurable (μ : ℝ) :
    Measurable (scalingParabolic μ originPoint) := by
  rw [scalingParabolic_eq]
  have hs : Measurable (scalingSpace μ originPoint.1) :=
    (measurable_const_add _).comp (measurable_const_smul μ)
  have ht : Measurable (scalingTime μ originPoint.2) :=
    (measurable_const_add _).comp (measurable_const_mul (μ ^ 2))
  exact (hs.comp measurable_fst).prodMk (ht.comp measurable_snd)

/-- A dilation about the origin scales the radius of every origin cylinder. -/
theorem originScaling_cylinder {μ : ℝ} (hμ : 0 < μ) (r : ℝ) :
    scalingParabolic μ originPoint '' parabolicCylinder (0 : Vec3) 0 r =
      parabolicCylinder (0 : Vec3) 0 (μ * r) := by
  have h : scalingParabolic μ originPoint '' parabolicCylinder (0 : Vec3) 0 r =
      parabolicCylinder (scalingParabolic μ originPoint originPoint).1
        (scalingParabolic μ originPoint originPoint).2 (μ * r) :=
    force_slot_cylinder_image hμ originPoint originPoint r
  rw [originScaling_origin] at h
  exact h

/-- A nonzero spatial dilation about the origin is injective. -/
theorem scalingSpace_origin_injective {a : ℝ} (ha : a ≠ 0) :
    Function.Injective (scalingSpace a (0 : Vec3)) := by
  intro y z h
  have h' : a • y = a • z := by
    simpa only [scalingSpace, zero_add] using h
  calc y = a⁻¹ • (a • y) := by rw [inv_smul_smul₀ ha]
    _ = a⁻¹ • (a • z) := by rw [h']
    _ = z := by rw [inv_smul_smul₀ ha]

/-- A nonzero temporal dilation about the origin is injective. -/
theorem scalingTime_origin_injective {a : ℝ} (ha : a ≠ 0) :
    Function.Injective (scalingTime a (0 : ℝ)) := by
  intro s t h
  have h' : a ^ 2 * s = a ^ 2 * t := by
    simpa only [scalingTime, zero_add] using h
  exact mul_left_cancel₀ (pow_ne_zero 2 ha) h'

/-- The reciprocal spatial dilation undoes a spatial dilation of a set. -/
theorem rescaledSpace_origin_inv {μ : ℝ} (hμ : 0 < μ) (Ω : Set Vec3) :
    rescaledSpace μ⁻¹ (0 : Vec3) (rescaledSpace μ (0 : Vec3) Ω) = Ω := by
  ext y
  simp only [rescaledSpace, mem_preimage, scalingSpace, zero_add, smul_smul]
  rw [mul_inv_cancel₀ hμ.ne', one_smul]

/-- The reciprocal temporal dilation undoes a temporal dilation of a set. -/
theorem rescaledTime_origin_inv {μ : ℝ} (hμ : 0 < μ) (I : Set ℝ) :
    rescaledTime μ⁻¹ (0 : ℝ) (rescaledTime μ (0 : ℝ) I) = I := by
  ext s
  simp only [rescaledTime, mem_preimage, scalingTime, zero_add, ← mul_assoc]
  rw [show μ ^ 2 * (μ⁻¹) ^ 2 = 1 by field_simp, one_mul]

/-- A spatial dilation of an origin ball is the origin ball of scaled radius. -/
theorem rescaledSpace_origin_ball {a r : ℝ} (ha : 0 < a) :
    rescaledSpace a (0 : Vec3) (vec3Ball (0 : Vec3) r) =
      vec3Ball (0 : Vec3) (a⁻¹ * r) := by
  ext y
  simp only [rescaledSpace, mem_preimage, scalingSpace, zero_add, mem_vec3Ball,
    sub_zero]
  rw [vec3EuclideanNorm_smul, abs_of_pos ha]
  constructor
  · intro h
    have h' : a⁻¹ * (a * vec3EuclideanNorm y) < a⁻¹ * r :=
      mul_lt_mul_of_pos_left h (inv_pos.mpr ha)
    rwa [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at h'
  · intro h
    have h' : a * vec3EuclideanNorm y < a * (a⁻¹ * r) :=
      mul_lt_mul_of_pos_left h ha
    rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at h'

/-- The closed unit cylinder of the dilated solution sits inside the interior
containment hypothesis of the original one, for every dilation factor at most
one. -/
theorem interior_rescaled_domain {Ω : Set Vec3} {I : Set ℝ} {μ : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I) :
    closure (parabolicCylinder (0 : Vec3) 0 1) ⊆
      spaceTimeSet (rescaledSpace μ originPoint.1 Ω)
        (rescaledTime μ originPoint.2 I) := by
  intro z hz
  rw [rescaledSpaceTimeSet_eq_preimage μ originPoint Ω I]
  refine hdom ?_
  rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)] at hz ⊢
  obtain ⟨hx, ht⟩ := hz
  have hx' : vec3EuclideanNorm (z.1 - 0) ≤ 1 := hx
  rw [sub_zero] at hx'
  have hμ2 : (0 : ℝ) < μ ^ 2 := by positivity
  have hμ2le : μ ^ 2 ≤ 1 := by nlinarith only [hμ, hμ1]
  refine ⟨?_, ?_, ?_⟩
  · show vec3EuclideanNorm ((scalingParabolic μ originPoint z).1 - 0) ≤ 1
    rw [originScaling_fst, sub_zero, vec3EuclideanNorm_smul, abs_of_pos hμ]
    nlinarith only [hx', hμ, hμ1, vec3EuclideanNorm_nonneg z.1]
  · show (0 : ℝ) - 1 ^ 2 ≤ (scalingParabolic μ originPoint z).2
    rw [originScaling_snd]
    have h1 : (0 : ℝ) - 1 ^ 2 ≤ z.2 := ht.1
    nlinarith only [h1, ht.2, hμ2, hμ2le]
  · show (scalingParabolic μ originPoint z).2 ≤ 0
    rw [originScaling_snd]
    nlinarith only [ht.2, hμ2]

/-- A Morrey bound on an origin cylinder controls the dilated field on every
origin cylinder whose dilated image stays inside it. -/
theorem rescaled_indicator_morrey_le
    {μ c P τ R R' : ℝ} {K : ℝ≥0∞} (hμ : 0 < μ) (hP : 0 < P)
    (hR' : 0 ≤ μ * R') (hR : μ * R' ≤ R)
    (g : ParabolicPoint → ℝ)
    (hN : morreyNorm P τ ((parabolicCylinder (0 : Vec3) 0 R).indicator g) ≤ K) :
    morreyNorm P τ ((parabolicCylinder (0 : Vec3) 0 R').indicator
      (fun w => c * g (scalingParabolic μ originPoint w))) ≤
      ENNReal.ofReal |c| * (ENNReal.ofReal μ ^ (-5 / τ : ℝ) * K) := by
  refine force_slot_subcarrier_scaling_le μ c P τ K hμ hP originPoint _ _ g ?_ hN
  rw [originScaling_cylinder hμ]
  exact parabolicCylinder_mono hR' hR

/-- The cubic velocity, pressure and force data of the dilated solution on the
unit cylinder are bounded by the inverse square of the dilation factor times
the same data of the original solution. -/
theorem rescaled_unit_data_le
    {q ε μ : ℝ} {u f : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hq : 5 / 2 < q)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ originPoint u z)) ^ (3 : ℝ) +
      ENNReal.ofReal |rescalePressure μ originPoint p z| ^ (3 / 2 : ℝ) +
      ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ originPoint f z)) ^ q) ≤
      ENNReal.ofReal (μ⁻¹ ^ 2 * ε) := by
  classical
  set T := scalingParabolic μ originPoint with hT
  set G : ParabolicPoint → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
      ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
      ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q with hG
  set κ : ℝ≥0∞ := ENNReal.ofReal μ ^ (3 : ℝ) with hκ
  have hμ0 : ENNReal.ofReal μ ≠ 0 := (ENNReal.ofReal_pos.mpr hμ).ne'
  have hμtop : ENNReal.ofReal μ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμle1 : ENNReal.ofReal μ ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hμ1
  have hpt : ∀ w : ParabolicPoint,
      ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ originPoint u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |rescalePressure μ originPoint p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ originPoint f w)) ^ q ≤
        κ * G (T w) := by
    intro w
    have hu : ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ originPoint u w)) ^ (3 : ℝ)
        = κ * ENNReal.ofReal (vec3EuclideanNorm (u (T w))) ^ (3 : ℝ) := by
      have hnorm : vec3EuclideanNorm (rescaleVelocity μ originPoint u w) =
          μ * vec3EuclideanNorm (u (T w)) := by
        show vec3EuclideanNorm (μ • u (T w)) = μ * vec3EuclideanNorm (u (T w))
        rw [vec3EuclideanNorm_smul, abs_of_pos hμ]
      rw [hnorm, ENNReal.ofReal_mul hμ.le,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
    have hp : ENNReal.ofReal |rescalePressure μ originPoint p w| ^ (3 / 2 : ℝ)
        = κ * ENNReal.ofReal |p (T w)| ^ (3 / 2 : ℝ) := by
      have habs : |rescalePressure μ originPoint p w| = μ ^ 2 * |p (T w)| := by
        show |μ ^ 2 * p (T w)| = μ ^ 2 * |p (T w)|
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < μ ^ 2)]
      rw [habs, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ ^ 2),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      congr 1
      rw [ENNReal.ofReal_pow hμ.le, ← ENNReal.rpow_natCast (ENNReal.ofReal μ) 2,
        ← ENNReal.rpow_mul, hκ]
      norm_num
    have hf : ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ originPoint f w)) ^ q
        ≤ κ * ENNReal.ofReal (vec3EuclideanNorm (f (T w))) ^ q := by
      have hnorm : vec3EuclideanNorm (rescaleForce μ originPoint f w) =
          μ ^ 3 * vec3EuclideanNorm (f (T w)) := by
        show vec3EuclideanNorm (μ ^ 3 • f (T w)) = μ ^ 3 * vec3EuclideanNorm (f (T w))
        rw [vec3EuclideanNorm_smul, abs_of_pos (by positivity : (0 : ℝ) < μ ^ 3)]
      rw [hnorm, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ ^ 3),
        ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (by linarith only [hq] : (0 : ℝ) < q))]
      have hcoef : ENNReal.ofReal (μ ^ 3) ^ q = ENNReal.ofReal μ ^ (3 * q) := by
        rw [ENNReal.ofReal_pow hμ.le, ← ENNReal.rpow_natCast (ENNReal.ofReal μ) 3,
          ← ENNReal.rpow_mul]
        norm_num
      have hle : ENNReal.ofReal (μ ^ 3) ^ q ≤ κ := by
        rw [hcoef, hκ]
        exact ENNReal.rpow_le_rpow_of_exponent_ge hμle1 (by linarith only [hq])
      gcongr
    rw [hu, hp, hG]
    calc κ * ENNReal.ofReal (vec3EuclideanNorm (u (T w))) ^ (3 : ℝ) +
          κ * ENNReal.ofReal |p (T w)| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ originPoint f w)) ^ q
        ≤ κ * ENNReal.ofReal (vec3EuclideanNorm (u (T w))) ^ (3 : ℝ) +
          κ * ENNReal.ofReal |p (T w)| ^ (3 / 2 : ℝ) +
          κ * ENNReal.ofReal (vec3EuclideanNorm (f (T w))) ^ q := by
          gcongr
      _ = κ * (ENNReal.ofReal (vec3EuclideanNorm (u (T w))) ^ (3 : ℝ) +
            ENNReal.ofReal |p (T w)| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f (T w))) ^ q) := by
          rw [mul_add, mul_add]
  have hstep1 : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (rescaleVelocity μ originPoint u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |rescalePressure μ originPoint p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (rescaleForce μ originPoint f z)) ^ q) ≤
      ∫⁻ z in parabolicCylinder (0 : Vec3) 0 1, κ * G (T z) :=
    lintegral_mono (fun w => hpt w)
  have hstep2 : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1, κ * G (T z)) =
      κ * ∫⁻ z in parabolicCylinder (0 : Vec3) 0 1, G (T z) :=
    lintegral_const_mul' _ _ (by
      rw [hκ]
      exact ENNReal.rpow_ne_top_of_ne_zero hμ0 hμtop)
  have hstep3 : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1, G (T z)) =
      ENNReal.ofReal (μ⁻¹ ^ 5) *
        ∫⁻ z in parabolicCylinder (0 : Vec3) 0 (μ * 1), G z := by
    have h := force_slot_lintegral_scaling hμ originPoint originPoint 1 G
    rw [originScaling_origin] at h
    exact h
  have hstep4 : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 (μ * 1), G z) ≤
      ENNReal.ofReal ε := by
    refine le_trans (lintegral_mono_set ?_) hsmall
    exact parabolicCylinder_mono (by positivity) (by linarith only [hμ1])
  have hκ' : κ = ENNReal.ofReal (μ ^ 3) := by
    rw [hκ, ENNReal.ofReal_pow hμ.le, ← ENNReal.rpow_natCast (ENNReal.ofReal μ) 3]
    norm_num
  have hcalc : μ ^ 3 * (μ⁻¹ ^ 5 * ε) = μ⁻¹ ^ 2 * ε := by
    field_simp
  refine le_trans hstep1 ?_
  rw [hstep2, hstep3]
  calc κ * (ENNReal.ofReal (μ⁻¹ ^ 5) *
        ∫⁻ z in parabolicCylinder (0 : Vec3) 0 (μ * 1), G z)
      ≤ κ * (ENNReal.ofReal (μ⁻¹ ^ 5) * ENNReal.ofReal ε) := by gcongr
    _ = ENNReal.ofReal (μ ^ 3 * (μ⁻¹ ^ 5 * ε)) := by
        rw [hκ', ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ⁻¹ ^ 5),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ ^ 3)]
    _ = ENNReal.ofReal (μ⁻¹ ^ 2 * ε) := by rw [hcalc]

/-- A dilation about the origin pulls an origin cylinder back into any origin
cylinder whose dilated radius dominates it. -/
theorem originScaling_cylinder_preimage_subset {μ r r' : ℝ} (hμ : 0 < μ)
    (hr : 0 ≤ r) (h : r ≤ μ * r') :
    scalingParabolic μ originPoint ⁻¹' parabolicCylinder (0 : Vec3) 0 r ⊆
      parabolicCylinder (0 : Vec3) 0 r' := by
  intro w hw
  obtain ⟨hw1, hw2, hw3⟩ := hw
  have hx : vec3EuclideanNorm ((scalingParabolic μ originPoint w).1 - 0) < r := hw1
  rw [originScaling_fst, sub_zero, vec3EuclideanNorm_smul, abs_of_pos hμ] at hx
  have ht₁ : (0 : ℝ) - r ^ 2 < (scalingParabolic μ originPoint w).2 := hw2
  have ht₂ : (scalingParabolic μ originPoint w).2 ≤ 0 := hw3
  rw [originScaling_snd] at ht₁ ht₂
  have hμ2 : (0 : ℝ) < μ ^ 2 := by positivity
  have hr' : 0 ≤ r' := by nlinarith only [hr, h, hμ]
  refine ⟨?_, ?_, ?_⟩
  · show vec3EuclideanNorm (w.1 - 0) < r'
    rw [sub_zero]
    nlinarith only [hx, h, hμ, vec3EuclideanNorm_nonneg w.1]
  · show (0 : ℝ) - r' ^ 2 < w.2
    nlinarith only [ht₁, h, hμ, hμ2, hr, hr']
  · show w.2 ≤ 0
    nlinarith only [ht₂, hμ2]

end CKN.Core.Step4
