-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.NewtonianRepresentationGeneralCore

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace CKN

open CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

/-- Faithful Newtonian representation for the distributional equation with compactly supported
data. The second-order singular-integral term is expressed through the completed double-Riesz
extension used by the global pressure construction. -/
theorem newtonian_representation_of_distributional
    {v K : Vec3 → ℝ} {G : Vec3 → Fin 3 → Fin 3 → ℝ} {H : Vec3 → Fin 3 → ℝ}
    {m m' : ℝ} (hm : 1 < m) (hm3 : m < 3) (hm' : 1 < m') (hm'3 : m' < 3 / 2)
    (hv : MemLp v (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hvc : HasCompactSupport v)
    (hG : ∀ i j, MemLp (fun x => G x i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hGc : ∀ i j, HasCompactSupport (fun x => G x i j))
    (hH : ∀ j, MemLp (fun x => H x j) (ENNReal.ofReal m) volume)
    (hHc : ∀ j, HasCompactSupport (fun x => H x j))
    (hK : MemLp K (ENNReal.ofReal m') volume) (hKc : HasCompactSupport K)
    (heq : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, v x * spatialLaplacian ψ x) =
        (∫ x, ∑ i, ∑ j, G x i j * mixedSecond ψ i j x)
          - (∫ x, ∑ j, H x j * spatialDeriv ψ j x)
          + ∫ x, K x * ψ x) :
    v =ᵐ[volume] fun x =>
      pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
        (fun i j y => G y i j) x -
      (∑ j, pressureNewtonianDerivativePotential j (fun y => H y j) x) +
      pressureNewtonianPotential K x := by
  have _hm3 : m < 3 := hm3
  have _hm'3 : m' < 3 / 2 := hm'3
  have _hvc : HasCompactSupport v := hvc
  have _hGc : ∀ i j, HasCompactSupport (fun x => G x i j) := hGc
  let Gtensor : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j x => G x i j
  let T : Vec3 → ℝ := pressureSecondExtensionOperator rieszSecondL2Input
    rieszSecondL2_weak_type Gtensor
  let D : Vec3 → ℝ := fun x => ∑ j, pressureNewtonianDerivativePotential j
    (fun y => H y j) x
  let P : Vec3 → ℝ := pressureNewtonianPotential K
  let W : Vec3 → ℝ := fun x => T x - D x + P x
  have hTensorLp : ∀ i j, MemLp (Gtensor i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro i j
    simpa only [Gtensor] using hG i j
  have hTmem : MemLp T (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    dsimp [T]
    exact pressureSecondExtension_memLp rieszSecondL2Input rieszSecondL2_weak_type hTensorLp

  have hHradius : ∀ j : Fin 3, ∃ R : ℝ, 0 < R ∧
      tsupport (fun x => H x j) ⊆ Metric.closedBall (0 : Vec3) R := by
    intro j
    obtain ⟨r, hr⟩ := (hHc j).isCompact.isBounded.subset_closedBall (0 : Vec3)
    refine ⟨max r 1, by positivity, ?_⟩
    exact hr.trans (Metric.closedBall_subset_closedBall (le_max_left r 1))
  choose RH hRHpos hRHsupp using hHradius
  have hKradius : ∃ R : ℝ, 0 < R ∧ tsupport K ⊆ Metric.closedBall (0 : Vec3) R := by
    obtain ⟨r, hr⟩ := hKc.isCompact.isBounded.subset_closedBall (0 : Vec3)
    refine ⟨max r 1, by positivity, ?_⟩
    exact hr.trans (Metric.closedBall_subset_closedBall (le_max_left r 1))
  obtain ⟨RK, hRKpos, hRKsupp⟩ := hKradius
  have hHzero : ∀ j, ∀ y, y ∉ Metric.closedBall (0 : Vec3) (RH j) → H y j = 0 := by
    intro j y hy
    exact image_eq_zero_of_notMem_tsupport (f := fun z : Vec3 => H z j) (by
      intro hs
      exact hy (hRHsupp j hs))
  have hKzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) RK → K y = 0 := by
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (f := K) (by
      intro hs
      exact hy (hRKsupp hs))
  have hHint : ∀ j, Integrable (fun y => H y j) volume := by
    intro j
    exact integrable_of_memLp_ofReal_of_support (by linarith only [hm]) (hH j)
      (hHzero j)
  have hKint : Integrable K volume :=
    integrable_of_memLp_ofReal_of_support (by linarith only [hm']) hK hKzero

  have hHgrowth : ∀ j, (∀ ρ : ℝ, 0 < ρ → MemLp
        (pressureNewtonianDerivativePotential j (fun y => H y j))
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ → lpNorm
        (pressureNewtonianDerivativePotential j (fun y => H y j))
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        newtonianDerivativePotentialGrowthConstant j (fun y => H y j) (RH j) *
          (1 + ρ) := by
    intro j
    exact pressureNewtonianDerivativePotential_growth_of_memLp_gt_one j hm
      (hRHpos j) (hRHsupp j) (hH j)
  have hKgrowth : (∀ ρ : ℝ, 0 < ρ → MemLp (pressureNewtonianPotential K)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
    ∀ ρ : ℝ, 0 < ρ → lpNorm (pressureNewtonianPotential K)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
      newtonianPotentialGrowthConstant K RK * (1 + ρ) :=
    pressureNewtonianPotential_growth_of_memLp_gt_one hm' hRKpos hRKsupp hK

  have hTlocal : ∀ ρ : ℝ, 0 < ρ → MemLp T (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
    fun ρ _ => memLp_euclideanBall_of_memLp_volume hTmem ρ
  have hDlocal : ∀ ρ : ℝ, 0 < ρ → MemLp D (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by
    intro ρ hρ
    change MemLp (∑ j, pressureNewtonianDerivativePotential j (fun y => H y j))
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ))
    have hsum := memLp_euclideanBall_family_sum (s := Finset.univ)
        (f := fun j x => pressureNewtonianDerivativePotential j (fun y => H y j) x)
        (by intro j hj r hr; exact (hHgrowth j).1 r hr)
    simpa [D] using hsum ρ hρ
  have hPlocal : ∀ ρ : ℝ, 0 < ρ → MemLp P (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by
    intro ρ hρ
    exact (hKgrowth.1 ρ hρ)
  have hWlocal : ∀ ρ : ℝ, 0 < ρ → MemLp W (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by
    intro ρ hρ
    change MemLp (T - D + P) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ))
    exact ((hTlocal ρ hρ).sub (hDlocal ρ hρ)).add (hPlocal ρ hρ)
  have hVlocal : ∀ ρ : ℝ, 0 < ρ → MemLp v (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
    fun ρ _ => memLp_euclideanBall_of_memLp_volume hv ρ
  have hResidualMem : ∀ ρ : ℝ, 0 < ρ → MemLp (fun x => v x - W x)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by
    intro ρ hρ
    exact (hVlocal ρ hρ).sub (hWlocal ρ hρ)

  let CT : ℝ := lpNorm T (ENNReal.ofReal (3 / 2 : ℝ)) volume
  let CV : ℝ := lpNorm v (ENNReal.ofReal (3 / 2 : ℝ)) volume
  let CD : ℝ := ∑ j, newtonianDerivativePotentialGrowthConstant j
    (fun y => H y j) (RH j)
  let CK : ℝ := newtonianPotentialGrowthConstant K RK
  let C : ℝ := CV + ((CT + CD) + CK)
  have hTgrowth : ∀ ρ : ℝ, 0 < ρ → lpNorm T (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ CT * (1 + ρ) := by
    intro ρ hρ
    dsimp only [CT]
    exact lpNorm_euclideanBall_le_of_memLp_volume hTmem hρ
  have hDgrowth : ∀ ρ : ℝ, 0 < ρ → lpNorm D (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ CD * (1 + ρ) := by
    intro ρ hρ
    change lpNorm (∑ j, pressureNewtonianDerivativePotential j (fun y => H y j))
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ _
    have hsum := lpNorm_euclideanBall_growth_sum
      (s := Finset.univ)
      (f := fun j x => pressureNewtonianDerivativePotential j (fun y => H y j) x)
      (C := fun j => newtonianDerivativePotentialGrowthConstant j
        (fun y => H y j) (RH j))
      (by intro j hj r hr; exact (hHgrowth j).1 r hr)
      (by intro j hj r hr; exact (hHgrowth j).2 r hr) hρ
    simpa only [CD] using hsum
  have hPgrowth : ∀ ρ : ℝ, 0 < ρ → lpNorm P (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ CK * (1 + ρ) := by
    intro ρ hρ
    exact hKgrowth.2 ρ hρ
  have hTDlocal : ∀ ρ : ℝ, 0 < ρ → MemLp (T - D)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by
    intro ρ hρ
    exact (hTlocal ρ hρ).sub (hDlocal ρ hρ)
  have hTDgrowth : ∀ ρ : ℝ, 0 < ρ → lpNorm (T - D)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ (CT + CD) * (1 + ρ) := by
    intro ρ hρ
    exact lpNorm_euclideanBall_growth_sub hTlocal hTgrowth hDgrowth hρ
  have hWgrowth : ∀ ρ : ℝ, 0 < ρ → lpNorm W (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ ((CT + CD) + CK) * (1 + ρ) := by
    intro ρ hρ
    change lpNorm (T - D + P) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ _
    exact lpNorm_euclideanBall_growth_add hTDlocal hTDgrowth hPgrowth hρ
  have hVgrowth : ∀ ρ : ℝ, 0 < ρ → lpNorm v (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ CV * (1 + ρ) := by
    intro ρ hρ
    dsimp only [CV]
    exact lpNorm_euclideanBall_le_of_memLp_volume hv hρ
  have hCnonneg : 0 ≤ C := by
    have hCV : 0 ≤ CV := by dsimp only [CV]; exact lpNorm_nonneg
    have hCT : 0 ≤ CT := by dsimp only [CT]; exact lpNorm_nonneg
    have hCD : 0 ≤ CD := Finset.sum_nonneg (fun j _ =>
      newtonianDerivativePotentialGrowthConstant_nonneg j (hRHpos j) (fun y => H y j))
    have hCK : 0 ≤ CK := newtonianPotentialGrowthConstant_nonneg K RK
    dsimp only [C]
    exact add_nonneg hCV (add_nonneg (add_nonneg hCT hCD) hCK)
  have hResidualGrowth : ∀ ρ : ℝ, 0 < ρ → lpNorm (fun x => v x - W x)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ) := by
    intro ρ hρ
    change lpNorm (v - W) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ)
    exact lpNorm_euclideanBall_growth_sub hVlocal hVgrowth hWgrowth hρ

  have hWpair : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      ∫ x, W x * spatialLaplacian ψ x =
        (∫ x, ∑ i, ∑ j, G x i j * mixedSecond ψ i j x)
          - (∫ x, ∑ j, H x j * spatialDeriv ψ j x)
          + ∫ x, K x * ψ x := by
    intro ψ hψ hψc
    have hψLap : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
      contDiff_spatialLaplacian_smooth hψ
    have hψLapc : HasCompactSupport (spatialLaplacian ψ) :=
      hasCompactSupport_spatialLaplacian hψc
    have hψLap3 : MemLp (spatialLaplacian ψ) (ENNReal.ofReal (3 : ℝ)) volume :=
      hψLap.continuous.memLp_of_hasCompactSupport hψLapc
    have hTloc : LocallyIntegrable T volume :=
      hTmem.locallyIntegrable (ENNReal.one_le_ofReal.2 (by norm_num))
    have hTint : Integrable (fun x => T x * spatialLaplacian ψ x) volume := by
      simpa only [smul_eq_mul] using
        hTloc.integrable_smul_right_of_hasCompactSupport hψLap.continuous hψLapc
    have hDcomponent : ∀ j, Integrable
        (fun x => pressureNewtonianDerivativePotential j (fun y => H y j) x *
          spatialLaplacian ψ x) volume := by
      intro j
      exact pressureNewtonianDerivativePotential_mul_smooth_integrable
        (hHint j) (hHc j) hψLap hψLapc
    have hDint : Integrable (fun x => D x * spatialLaplacian ψ x) volume := by
      change Integrable (fun x =>
        (∑ j, pressureNewtonianDerivativePotential j (fun y => H y j) x) *
          spatialLaplacian ψ x) volume
      simp only [Finset.sum_mul]
      exact integrable_finsetSum _ (fun j _ => hDcomponent j)
    have hPint : Integrable (fun x => P x * spatialLaplacian ψ x) volume := by
      exact pressureNewtonianPotential_mul_smooth_integrable hKint hKc hψLap hψLapc
    have hDrightInt : ∀ j, Integrable
        (fun x => H x j * spatialDeriv ψ j x) volume := by
      intro j
      let φ : Vec3 → ℝ := spatialDeriv ψ j
      have hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
        simpa [φ] using contDiff_spatialDeriv_smooth hψ j
      have hφc : HasCompactSupport φ := by
        simpa [φ] using hasCompactSupport_spatialDeriv hψc j
      obtain ⟨B, hB⟩ := hφc.exists_bound_of_continuous hφsmooth.continuous
      exact (hHint j).mul_bdd hφsmooth.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => hB x)
    have hDpair : ∫ x, D x * spatialLaplacian ψ x =
        ∫ x, ∑ j, H x j * spatialDeriv ψ j x := by
      calc
        _ = ∑ j, ∫ x,
            pressureNewtonianDerivativePotential j (fun y => H y j) x *
              spatialLaplacian ψ x := by
          change ∫ x, (∑ j, pressureNewtonianDerivativePotential j
            (fun y => H y j) x) * spatialLaplacian ψ x = _
          simp only [Finset.sum_mul]
          rw [integral_finsetSum _ (fun j _ => hDcomponent j)]
        _ = ∑ j, ∫ x, H x j * spatialDeriv ψ j x := by
          apply Finset.sum_congr rfl
          intro j _hj
          exact pressureNewtonianDerivativePotential_distributional_pairing_smooth
            (hHint j) (hHc j) hψ hψc
        _ = ∫ x, ∑ j, H x j * spatialDeriv ψ j x := by
          symm
          rw [integral_finsetSum _ (fun j _ => hDrightInt j)]
    have hTpair : ∫ x, T x * spatialLaplacian ψ x =
        ∫ x, ∑ i, ∑ j, G x i j * mixedSecond ψ i j x := by
      simpa only [T, Gtensor] using pressureSecondExtension_distributional_identity
        rieszSecondL2Input rieszSecondL2_weak_type hTensorLp hψ hψc
    have hPpair : ∫ x, P x * spatialLaplacian ψ x = ∫ x, K x * ψ x := by
      exact pressureNewtonianPotential_distributional_pairing hKint hKc hψ hψc
    have hWfactor : (fun x => W x * spatialLaplacian ψ x) =
        (fun x => (T x * spatialLaplacian ψ x - D x * spatialLaplacian ψ x) +
          P x * spatialLaplacian ψ x) := by
      funext x
      dsimp [W]
      ring
    have hWint : Integrable (fun x => W x * spatialLaplacian ψ x) volume := by
      rw [hWfactor]
      exact (hTint.sub hDint).add hPint
    calc
      ∫ x, W x * spatialLaplacian ψ x =
          (∫ x, T x * spatialLaplacian ψ x - D x * spatialLaplacian ψ x) +
            ∫ x, P x * spatialLaplacian ψ x := by
        calc
          ∫ x, W x * spatialLaplacian ψ x =
              ∫ x, ((fun x => T x * spatialLaplacian ψ x -
                D x * spatialLaplacian ψ x) x +
                (fun x => P x * spatialLaplacian ψ x) x) := by
            rw [hWfactor]
          _ = (∫ x, T x * spatialLaplacian ψ x - D x * spatialLaplacian ψ x) +
              ∫ x, P x * spatialLaplacian ψ x := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (integral_add (hTint.sub hDint) hPint)
      _ = (∫ x, ∑ i, ∑ j, G x i j * mixedSecond ψ i j x)
          - (∫ x, ∑ j, H x j * spatialDeriv ψ j x) + ∫ x, K x * ψ x := by
        rw [integral_sub hTint hDint, hTpair, hDpair, hPpair]

  have hweak : WeaklyHarmonicOn (Set.univ : Set Vec3) (fun x => v x - W x) := by
    intro ψ hψ hψc _hψuniv
    rw [Measure.restrict_univ]
    have hψLap : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
      contDiff_spatialLaplacian_smooth hψ
    have hψLapc : HasCompactSupport (spatialLaplacian ψ) :=
      hasCompactSupport_spatialLaplacian hψc
    have hψLap3 : MemLp (spatialLaplacian ψ) (ENNReal.ofReal (3 : ℝ)) volume :=
      hψLap.continuous.memLp_of_hasCompactSupport hψLapc
    have hvloc : LocallyIntegrable v volume :=
      hv.locallyIntegrable (ENNReal.one_le_ofReal.2 (by norm_num))
    have hvint : Integrable (fun x => v x * spatialLaplacian ψ x) volume := by
      simpa only [smul_eq_mul] using
        hvloc.integrable_smul_right_of_hasCompactSupport hψLap.continuous hψLapc
    have hTloc : LocallyIntegrable T volume :=
      hTmem.locallyIntegrable (ENNReal.one_le_ofReal.2 (by norm_num))
    have hTint : Integrable (fun x => T x * spatialLaplacian ψ x) volume := by
      simpa only [smul_eq_mul] using
        hTloc.integrable_smul_right_of_hasCompactSupport hψLap.continuous hψLapc
    have hwint : Integrable (fun x => W x * spatialLaplacian ψ x) volume := by
      have hDcomponent : ∀ j, Integrable
          (fun x => pressureNewtonianDerivativePotential j (fun y => H y j) x *
            spatialLaplacian ψ x) volume := by
        intro j
        exact pressureNewtonianDerivativePotential_mul_smooth_integrable
          (hHint j) (hHc j) hψLap hψLapc
      have hDint : Integrable (fun x => D x * spatialLaplacian ψ x) volume := by
        change Integrable (fun x =>
          (∑ j, pressureNewtonianDerivativePotential j (fun y => H y j) x) *
            spatialLaplacian ψ x) volume
        simp only [Finset.sum_mul]
        exact integrable_finsetSum _ (fun j _ => hDcomponent j)
      have hPint : Integrable (fun x => P x * spatialLaplacian ψ x) volume :=
        pressureNewtonianPotential_mul_smooth_integrable hKint hKc hψLap hψLapc
      have hWfactor : (fun x => W x * spatialLaplacian ψ x) =
          (fun x => (T x * spatialLaplacian ψ x - D x * spatialLaplacian ψ x) +
            P x * spatialLaplacian ψ x) := by
        funext x
        dsimp [W]
        ring
      rw [hWfactor]
      exact (hTint.sub hDint).add hPint
    rw [show (fun x => (v x - W x) * spatialLaplacian ψ x) =
        (fun x => v x * spatialLaplacian ψ x - W x * spatialLaplacian ψ x) by
      funext x
      ring]
    rw [integral_sub hvint hwint, heq ψ hψ hψc, hWpair ψ hψ hψc]
    ring

  have hzero := weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth hCnonneg
    hResidualMem hweak hResidualGrowth
  filter_upwards [hzero] with x hx
  have hx' : v x = W x := sub_eq_zero.mp hx
  simpa [W, D, T, Gtensor, P] using hx'

end CKN
