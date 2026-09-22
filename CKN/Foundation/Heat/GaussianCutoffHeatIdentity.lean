-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Heat.GaussianSmooth
import CKN.Pressure.LeibnizLaplacian

open scoped BigOperators NNReal Topology

open Set
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Heat

private lemma timePartial_mul_of_contDiffAt
    {a b : Vec3 × ℝ → ℝ} {z : ParabolicPoint}
    (ha : ContDiffAt ℝ (⊤ : ℕ∞) a (z.1, z.2))
    (hb : ContDiffAt ℝ (⊤ : ℕ∞) b (z.1, z.2)) :
    timePartial (fun w => a w * b w) z =
      timePartial a z * b z + a z * timePartial b z := by
  unfold timePartial
  have ha' : DifferentiableAt ℝ (fun s : ℝ => a (z.1, s)) z.2 := by
    exact (ha.differentiableAt (by simp)).comp z.2 (by fun_prop)
  have hb' : DifferentiableAt ℝ (fun s : ℝ => b (z.1, s)) z.2 := by
    exact (hb.differentiableAt (by simp)).comp z.2 (by fun_prop)
  change (fderiv ℝ ((fun s => a (z.1, s)) * (fun s => b (z.1, s))) z.2) 1 = _
  rw [fderiv_mul ha' hb']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  change a (z.1, z.2) * (fderiv ℝ (fun s : ℝ => b (z.1, s)) z.2) 1 +
      b (z.1, z.2) * (fderiv ℝ (fun s : ℝ => a (z.1, s)) z.2) 1 =
    (fderiv ℝ (fun s : ℝ => a (z.1, s)) z.2) 1 * b (z.1, z.2) +
      a (z.1, z.2) * (fderiv ℝ (fun s : ℝ => b (z.1, s)) z.2) 1
  ring

/-- The backward Gaussian multiplied by a smooth cutoff obeys the heat-product
identity at every point strictly before its pole. -/
theorem backward_heat_cutoff_identity
    (η : Vec3 × ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (z : ParabolicPoint) (hz : z.2 ≤ t₀) :
    let ψ := centeredBackwardHeatTest x₀ t₀ r
    timePartial (fun w => η w * ψ w) z +
      ∑ i : Fin 3, spatialSecondPartial (fun w => η w * ψ w) i i z =
    ψ z * (timePartial η z + ∑ i : Fin 3, spatialSecondPartial η i i z) +
      2 * ∑ i : Fin 3, spatialPartial η i z * spatialPartial ψ i z := by
  let ψ : Vec3 × ℝ → ℝ := centeredBackwardHeatTest x₀ t₀ r
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hzt : z.2 < t₀ + r ^ 2 := by
    nlinarith only [hz, hr2]
  have hUopen : IsOpen {w : Vec3 × ℝ | w.2 < t₀ + r ^ 2} :=
    isOpen_lt continuous_snd continuous_const
  have hψOn := contDiffOn_centeredBackwardHeatTest x₀ t₀ r
  have hψAt : ContDiffAt ℝ (⊤ : ℕ∞) ψ (z.1, z.2) := by
    apply hψOn.contDiffAt
    exact hUopen.mem_nhds (by simpa [ψ] using hzt)
  have htime := timePartial_mul_of_contDiffAt hη.contDiffAt hψAt
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => (x, z.2)) := by
    fun_prop
  have hηslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => η (x, z.2)) :=
    hη.comp hmap
  have hmaps : MapsTo (fun x : Vec3 => (x, z.2)) Set.univ
      {w : Vec3 × ℝ | w.2 < t₀ + r ^ 2} := by
    intro x hx
    exact hzt
  have hmapOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => (x, z.2)) Set.univ := contDiffOn_univ.mpr hmap
  have hψsliceOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => ψ (x, z.2)) Set.univ := hψOn.comp hmapOn hmaps
  have hψslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ (x, z.2)) :=
    contDiffOn_univ.mp hψsliceOn
  have hspace := congrFun
    (CKN.spatialLaplacian_mul_smooth hηslice hψslice) z.1
  have hspace' :
      (∑ i : Fin 3, spatialSecondPartial (fun w => η w * ψ w) i i z) =
        η z * (∑ i : Fin 3, spatialSecondPartial ψ i i z) +
          2 * ∑ i : Fin 3, spatialPartial η i z * spatialPartial ψ i z +
          ψ z * (∑ i : Fin 3, spatialSecondPartial η i i z) := by
    change CKN.spatialLaplacian
        (fun x : Vec3 => η (x, z.2) * ψ (x, z.2)) z.1 =
      η (z.1, z.2) * CKN.spatialLaplacian
          (fun x : Vec3 => ψ (x, z.2)) z.1 +
        2 * CKN.spatialGradDot (fun x : Vec3 => η (x, z.2))
          (fun x : Vec3 => ψ (x, z.2)) z.1 +
        ψ (z.1, z.2) * CKN.spatialLaplacian
          (fun x : Vec3 => η (x, z.2)) z.1
    exact hspace
  have hheat := centeredBackwardHeatTest_heat_equation
    (x₀ := x₀) (t₀ := t₀) (r := r) hzt
  change timePartial (fun w => η w * ψ w) z +
      ∑ i : Fin 3, spatialSecondPartial (fun w => η w * ψ w) i i z =
    ψ z * (timePartial η z +
      ∑ i : Fin 3, spatialSecondPartial η i i z) +
      2 * ∑ i : Fin 3, spatialPartial η i z * spatialPartial ψ i z
  rw [htime, hspace']
  calc
    timePartial η z * ψ z + η z * timePartial ψ z +
        (η z * (∑ i : Fin 3, spatialSecondPartial ψ i i z) +
          2 * ∑ i : Fin 3, spatialPartial η i z * spatialPartial ψ i z +
          ψ z * (∑ i : Fin 3, spatialSecondPartial η i i z))
        = ψ z * (timePartial η z +
            ∑ i : Fin 3, spatialSecondPartial η i i z) +
            2 * ∑ i : Fin 3, spatialPartial η i z * spatialPartial ψ i z +
            η z * (timePartial ψ z +
              ∑ i : Fin 3, spatialSecondPartial ψ i i z) := by ring
    _ = ψ z * (timePartial η z +
          ∑ i : Fin 3, spatialSecondPartial η i i z) +
          2 * ∑ i : Fin 3, spatialPartial η i z * spatialPartial ψ i z := by
      rw [hheat, mul_zero, add_zero]

end CKN.Foundation.Heat

end
