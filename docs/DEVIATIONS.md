# Mathematical differences between the paper and the Lean development

This document distinguishes changes of representation, alternative proofs,
specializations, and corrections to the paper. References such as
`prop:lin34` are the paper's labels. Lean names identify the definitions or
results concerned; a conditional helper is not a proof of its hypotheses.
Entries are numbered in the order they were written and are not renumbered.
This account is not a claim that every auxiliary display in the paper has
been formalized in its full printed generality.

Paper labels refer to the included manuscript, `paper/ckn.tex`. References to
earlier drafts describe the mathematical changes summarized in the entries
below. The numbered entries are not a list of outstanding errors in the
current manuscript. Implementation choices do not by themselves assert a
defect in the manuscript.

## Conventions and scope

- **Weak gradients (`def:sws`).**
  `IsSuitableWeakSolution` carries a separate field `Du`, tied to the
  velocity by slice weak-derivative identities. Gradients are determined
  almost everywhere, not by pointwise classical differentiation.
- **Smooth tests (`def:sws`).** Tests are functions on `Vec3 × ℝ`, where
  `Vec3 = Fin 3 → ℝ`, with compact support inside the domain.
  Smoothness is `ContDiff ℝ (⊤ : ℕ∞)`. Analytic regularity is not a
  substitute: a compactly supported analytic test would vanish identically.
- **Finite scale quantities (`eq:alpha-beta`, `eq:morrey-decay-hyp`).**
  Nonnegative integrals are first taken in `ℝ≥0∞`. The real-valued
  `alpha`, `beta`, `gamma`, `delta`, and `lambda` use conversion to real
  numbers only with the necessary finiteness justification. Compactly
  interior cylinders supply that justification from suitability.
- **Gradient smallness (`thm:B`, `eq:morrey-decay-hyp`).**
  `epsilonRegularityGradient` uses the extended nonnegative limsup of
  the scaled gradient mass, with threshold ε₁². This represents the
  squared β condition without assigning zero to an infinite mass.
- **Space and geometry (`def:parabolic-morrey`, `lem:morrey-cylinders`).**
  The ambient function space has the supremum norm; `vec3Ball` and
  `euclideanBall` specify Euclidean balls explicitly. `morreyNorm` uses
  one-sided cylinders, whereas `morreyBallNorm` uses parabolic metric
  balls. Their comparison carries the factor 2^{5(1/P−1/τ)}.
  Supremum and Euclidean spatial norms are compared explicitly. The energy
  finiteness clauses of `IsSuitableWeakSolution` use the ambient supremum
  norms on `Vec3` and its gradient arrays. Their finiteness is equivalent to
  Euclidean energy finiteness in these fixed finite dimensions; quantitative
  estimates use the explicit Euclidean norms and comparison constants.
- **Potential gauge (`lem:hedberg`).** The sum gauge |x|+√|t| and the
  maximum gauge max(|x|,√|t|) are comparable, not identical. Their powers
  introduce factors bounded by the corresponding powers of 2.
- **Time and null sets (`lem:lei-pointwise`, `eq:delta-p`).** The local
  energy argument uses an almost-everywhere-in-time inequality rather
  than a weak-time-continuous representative. Test-dependent null sets
  are replaced, where needed, by one common null set using translated mollifier bumps centred
  at a countable dense set of translation points, continuity in the centre, and dominated convergence;
  see `CKN.pressure_delta_p_meanFree_ae_forall_of_sws` and `CKN.pressure_delta_p_common_null_set`.
- **Spacetime selection (`eq:local-equation`).** Slice weak gradients
  are selected through spatial mollification and an almost-everywhere
  limit. Joint measurability, integrability on a box, and the passage
  from iterated integrals to product integrals are separate requirements.
  `HasWeakPartialDerivOn` alone does not imply spacetime integrability.
- **Interior containment (`lem:delta-p`, `prop:pressure-decomposition`,
  `lem:U-bounds`, `eq:slice-norm-bounds`, `lem:pk-bounds`, `thm:pressure-decay`,
  `cor:CZ-harmonic`, `prop:lin34`, `lem:theta-decay`, `prop:iteration`,
  `lem:caccioppoli`, `lem:caccioppoli-gamma`).** Internal results
  including `caccioppoli` require the closure of the cylinder to lie in
  the open solution domain. This is stronger than bare containment of a
  half-open cylinder. It is available locally at every interior point;
  it should not be suppressed when quoting those internal results. For slice
  identities the corresponding condition may instead be that the closure of
  the spatial ball lies in Ω. Compact support inside Ω also suffices for
  fixed-test distributional identities; these conditions should be read from
  the particular declaration rather than imposed indiscriminately.
- **Dyadic cubes (`ext:CZ`).** The decomposition uses half-open cubes.
  The inscribed supremum-norm ball is centred at the cube centre, not
  at an arbitrary point of the cube; see `supBall_subset_dyadicCubeCenter`.

## Proof differences and corrections

### B1 — Campanato regularity

Paper: `lem:campanato`, `eq:campanato-cauchy`, `eq:campanato-points`,
`eq:campanato-scales`, `eq:campanato-quantity`.
Lean: `campanato_holder`, `campanato_holder_source`.
The Hölder representative is constructed from dyadic ball averages and a
telescoping estimate, rather than successive mollifications. The four
mollification displays are not steps of this alternative proof.
The corrected manuscript now includes this dyadic alternative after
`prop:heat-morrey-hoelder`; it retains the mollification proof as well.

### B2 — Localization of Theorem C

Paper: `thm:C`.
Lean: `singularSet_null_of_gradient_criterion`.
A countable cover by local product boxes replaces compact exhaustion of
the full spacetime domain. The singular-set conclusion is unchanged.
The corrected proof of `thm:C` explicitly records the local-box reduction.

### B3 — From parabolic measure to volume

Paper: `lem:P1-implies-null`.
Lean: `parabolicHausdorffMeasure_one_lt_top_imp_volume_zero`.
The proof uses the comparison of five-dimensional parabolic Hausdorff
measure with Lebesgue measure rather than repeating the cover-volume count.
The corrected `lem:P1-implies-null` also records this alternative.

### B4 — Harmonic interior estimates

Paper: `lem:harmonic-interior`, `eq:harm-sup`.
Lean: `smooth_harmonic_annular_representation`, `weak_harmonic_interior_displays`.
An annular Newtonian representation of a cut-off harmonic function,
followed by mollification for weakly harmonic data, replaces the direct
mean-value argument. Representative regularity and the smaller ball on
which each bound holds remain explicit.

### B5 — Duhamel representation

Paper: `eq:duhamel`, `lem:local-equation`.
Lean: `localized_duhamel_from_leibniz_of_sws`.
The representation is proved by testing against a backward heat potential,
using its adjoint equation and Fubini, and identifying the resulting
distribution with an almost-everywhere function. It does not use unrestricted
uniqueness among distributions supported in a lower time half-space.
The corrected `lem:local-equation` now gives this adjoint proof;
`ext:heat-kernel` restricts its separate uniqueness assertion to tempered data.

### B6 — Mean subtraction in the energy estimate

Paper: `lem:caccioppoli`.
Lean: `caccioppoli`, with the slice identities underlying its centred terms.
Spatial incompressibility is extended from a countable dense family of
tests to all required tests. This replaces an implicit interchange of
the test-function quantifier with the almost-everywhere time quantifier;
it is not a time-mollification argument.

### B7 — Cancellation of commutator kernels

The unused commutator route requires this cancellation calculation.
Current related input: `ext:CZ`.
Lean: `integral_vec_gaussian_homogeneous`, `vecEuclideanSphereMeasure`.
Gaussian moments of the homogeneous polynomial associated with the kernel,
followed by polar decomposition, provide the sphere-moment calculation.
Transport to Euclidean geometry uses `WithLp.toLp 2`. This supports the
commutator calculation, not the commutator-free proof described in B13.

### B8 — Adjoint identity for the Newtonian derivative

Paper: `eq:delta-p`, `prop:pressure-decomposition`.
Lean: `pressure_newtonian_derivative_adjoint`.
The identity pairing ∂ⱼN with Δψ is proved through heat-kernel subordination:
integration by parts is performed for each smooth positive-time heat kernel
before integration in time. No divergence theorem on a punctured domain
is needed.

### B9 — Ball Sobolev–Poincaré proved internally

Paper: `ext:sobolev-ball`.
Lean: `sobolevPoincare_L6_ball_weak`.
A two-reflection extension, the Gagliardo–Nirenberg–Sobolev inequality,
unit-ball Poincaré and scaling prove the same-ball estimate. The weak H¹
version follows by increasing inner balls. This external input of the
paper is therefore not an additional axiom.

### B10 — A specialized Hardy–Littlewood–Sobolev estimate

Paper: `ext:riesz`.
Lean: `rieszPotentialOne_hls`, `newtonian_first_derivative_hls`.
The pressure argument proves the required 5/2→15 estimate by maximal-function
bounds and Hedberg's method. The corrected `ext:riesz` states exactly this
specialization, unlike the original's full family of exponents. The present
estimate is not a proof of that larger family. A Young inequality with kernel exponent below
one would not justify this step or its scaling power.

### B11 — Calderón–Zygmund bounds proved internally

Paper: `ext:CZ`, `eq:CZ-harmonic`.
Lean: `rieszSecondL2_weak_type`, `hCZ_p1_unconditional`.
The second Riesz transform is treated by an L² estimate, Calderón–Zygmund
decomposition, the Hörmander weak (1,1) argument and interpolation. In
particular the L^{3/2} pressure estimate is derived, not assumed as an axiom.

### B12 — Divergence-form convection

Paper: `lem:local-equation`, `eq:local-equation`.
Lean: `localizedDivergenceG`, `localizedDivergenceH`, `duhamelPotential`.
The convection term is kept in divergence form where the localized equation
requires it. The convention `duhamelPotential F h` uses the heat sources
(F,−h); this sign must be transported when rewriting the differentiated source.
These divergence-form sources are distinct from the gradient-source pair
used in B13, which keeps convection in the undifferentiated source.

### B13 — A commutator-free bootstrap

Paper: `prop:bootstrap`, `eq:local-equation`. The current proof does not
use the commutator reduction described in B7.
Lean: `routeA_one_round_velocity_improvement_of_gradient_inputs`.
The proof keeps φ∇p in the undifferentiated source. It estimates
the weak pressure gradient by the completed L^{6/5} Riesz operator,
harmonic interior estimates and local growth bounds, then applies the
order-two potential estimate. The representation is whole-space Newtonian
potential plus harmonic remainder, not a cube Dirichlet construction.
The gradient exponent is determined by 1/κ=1/τ+1/τ₃.
The first improvement reaches velocity
exponent 25 with gain 2/25. The final source exponents remain
θ₀=min(q,25/9), θ₁=25/3, with γ₀=min(2−5/q,1/5).
The commutator expansion is not needed by this route. Moving φp into the
differentiated source is not an equivalent substitute: spatially constant
pressures such as |t|^{−3/5} obstruct the required time estimate.
The current manuscript uses this proof and removes the itemized multiplier
argument; B54 describes the replacement. The removed estimates are not
claimed proved by the two-source argument.

### B14 — The operator, not a totalized kernel integral

Paper: `ext:CZ`.
Lean: `hCZ_grad_of_rieszSecond_inputs`, `rieszSecond_convolution_sublinear_of_integrable`.
Abstract interpolation requires sublinearity on its stated domain.
A non-integrable Bochner integral is assigned zero in Lean, so a literal
integral formula is not automatically additive on all inputs. The concrete
operator is defined coherently on L² and extended by continuity; a separate
literal-convolution argument applies only when its integrals exist.

### B15 — Interpolation on the classes actually used

Paper: `ext:CZ`.
Lean: `interpolation_weak11_strong22_of_classes`,
`interpolation_weak11_strong22_of_l2_classes`.
Weak and strong bounds and sublinearity are required only on the input
classes used in the proof. The L²-class version handles Lᵖ∩L² first,
and density gives the extension. The other version explicitly requires
measurability of the output on the general Lᵖ input.

### B16 — Potential decay and Liouville growth

Paper: `prop:pressure-decomposition`, `eq:pk`.
Lean: `pressureNewtonianPotential_tail_bound_centre`,
`pressureNewtonianDerivativePotential_tail_bound_centre`,
`memLp_and_lpNorm_linear_growth_of_inv_norm_decay`, `invNormBallConstant`.
Far-field inverse-power bounds are first proved in the ambient supremum
norm and converted to Euclidean balls. Exact scaling of the integral of
|x|^{−3/2} replaces a dyadic shell sum in the linear L^{3/2}-growth bound.
Recentering changes the decay constant and radius explicitly. Near-field
membership is supplied separately, not inferred from a tail bound.

### B17 — All-order kernel estimates

Paper: `cor:CZ-harmonic`, `eq:har-Ck`, `lem:cutoff`.
Lean: `exists_norm_iteratedFDeriv_newtonianKernel_le`,
`exists_norm_iteratedFDeriv_pressureNewtonianPotential_annulus_le`.
Homogeneity and compactness of the unit sphere give constants depending
only on derivative order. Recursive differentiation under the integral
replaces a general multilinear-valued integral formula. Natural powers and
real powers are related explicitly. The annular separation is 3ρ/20;
vanishing off the source set, rather than closedness of that set, suffices.

### B18 — An explicit admissible energy test

Paper: `lem:caccioppoli`, `eq:phi-heat`.
Lean: `backwardHeat_cutoff`, `backwardHeat_cutoff_testFunction`, `caccioppoli`.
A mollified spatial cutoff and an asymmetric time cutoff, including an
auxiliary future interval, make the backward heat test admissible.
Smoothness, nonnegativity, support and the lower bound 1/(2000r) are proved.
The choices of smoothing radius and future interval are internal choices,
not extra hypotheses of the final Caccioppoli estimate.

### B19 — Centred slice means

Paper: `lem:caccioppoli`.
Lean: `caccioppoli_gamma_display`.
The mean is the Euclidean-ball average. Its normalization and Jensen bound,
and the common-null-set argument for centred slice identities, are explicit.
The solution and cylinder geometry supply the construction.

### B20 — Almost-everywhere energy assembly

Paper: `lem:lei-pointwise`, `eq:caccioppoli`.
Lean: `caccioppoli`, `caccioppoli_theta_display`.
The proof takes an essential supremum of the almost-everywhere time
inequality and tracks numerical factors 2000, 1000 and 6000. This exposes
endpoint and null-set bookkeeping suppressed in the original. The corrected
`lem:lei-pointwise` explicitly concludes its inequality at almost every time.

### B21 — Pressure and theta-decay assembly

Paper: `thm:pressure-decay`, `lem:theta-decay`.
Lean: `pressureDecay_one_scale_T`.
The eight pressure terms are assembled using the solution-level bounds,
measurability and the p₇ potential estimate. An earlier theta-decay helper
named the p₁ estimate as a hypothesis; it did not itself prove that estimate. The completed pressure identification
and operator bounds are separate ingredients.

### B22 — Weak differentiation of first potentials

Paper: `eq:local-equation`, `ext:CZ`.
Lean: `rieszSecondGradientExtension_weak_gradient_pairing`.
For compactly supported L^{6/5} data, both sides of the derivative pairing
are rewritten against N*∂ᵢ∂ⱼψ. This is an L^{6/5}-continuous functional,
since that test potential belongs to L⁶. Smooth density then gives the
identity. No pointwise differentiation of a singular integral is asserted.

### B23 — Local integrability of Newtonian potentials

Paper: `ext:newtonian`, `prop:pressure-decomposition`.
Lean: `pressureNewtonianPotential_memLp_ball`,
`pressureNewtonianDerivativePotential_memLp_ball`,
`pressureNewtonianPotential_memLp_ball_of_memLp_gt_one`,
`pressureNewtonianDerivativePotential_memLp_ball_of_memLp_gt_one`,
`pressureNewtonianPotential_growth_of_memLp_gt_one`,
`pressureNewtonianDerivativePotential_growth_of_memLp_gt_one`.
The first two helpers use Young's inequality L^{6/5}*L^{6/5}→L^{3/2}.
The general versions prove that, for every real p>1, a measurable L^p source
vanishing outside a closed ambient ball of radius R>0 has both its Newtonian
potential and each first-derivative potential in L^{3/2} on every ambient
ball centred at the origin with positive radius. For 1<p<6/5 the proof
chooses a matching truncated-kernel Young exponent; for p≥6/5 it lowers
the source exponent on bounded support. The companion growth theorems,
assuming the source's topological support lies in that closed ball, give
local L^{3/2} membership on Euclidean balls and a bound C(g,R)(1+ρ) for
the local L^{3/2} norm (also depending on the component for ∂ᵢN).
Bounded support supplies L¹ for the far-field estimate. The p=1 endpoint
for N is not included in these results.

### B24 — Quantitative final Hölder estimate

Paper: `thm:endgame`.
Lean: `endgameHolderBound`, `endgame_holder_norm_of_force_producer`.
The bound is linear in the two source Morrey bounds, with weights determined
by γ₀, θ₀, θ₁ and 6/5. Its radius dependence is through r₂/4−r₃, not
a cover cardinality. Bounding those source norms is a separate proof step.
The representative is controlled on a closed inner region.

### B25 — Uniform localization cutoffs

Paper: `lem:cutoff`, `thm:endgame`.
Lean: `endgameCutoff`, `uniformCutoffConstant`.
The cutoff is a spatial convolution cutoff times a rescaled smooth time
profile. One may take the common coefficient to be the maximum of the
spatial first- and second-derivative constants and 16. Support lies in
|x−x₀|<3a/2, |t−t₀|≤2a², inside the parabolic ball of radius 2a;
derivative bounds scale as a^{−1} and a^{−2}.

### B26 — The oscillation pressure estimate

Paper: `prop:lin34`, `lem:delta-p-centred`, `eq:lin34-pointwise`.
Lean: `lin34CentredP1`, `lin34PointwiseConstant`, `lin34ForceCylinderConstant`.
The source uses the doubly centred velocity tensor. The p₂–p₆ terms are
estimated directly by `lem:pk-bounds`, as in the paper itself. This is
not a departure from that printed proof; it distinguishes it from an
unsuitable harmonic-interior alternative, whose force term would have
the wrong power of r/ρ and the wrong spatial region.

### B27 — The contraction scale used by iteration

Paper: `lem:theta-decay`, `eq:theta-decay-1`, `eq:theta-decay-2`, `conv:kappa`.
Lean: `thetaDecay_T_of_inputs`, `iterationKappa`.
These helpers establish the displays at the selected contraction
κ=min(1/2,(8C₂₇)^{−1/(2/3−2/5)}). This suffices for their iteration
iteration, but is not the assertion for every κ∈(0,1/2] with common constants.
The specialization must remain visible when citing these helpers.

### B28 — Whole-space pressure tests and a common null set

Paper: `eq:laplace-etap`, `eq:delta-p`.
Lean: `pressureP1_distributional_identity_of_sws`,
`slice_second_pairing_zero_of_mollifier_family`.
A test is split into a part localized near the cutoff support and its
complement, extending the identity to whole-space tests. A countable
second-order mollifier family then makes the exceptional time set independent
of the test. The tensor source must be the same in identification,
integrability and growth estimates; neither extension changes the PDE.
The direct statement `pressure_laplace_cutoff_identity_ae` for
`eq:laplace-etap` fixes the spatial test before its almost-everywhere time
quantifier. Its `_ae_all_tests` variant permits arbitrary compactly supported
spatial tests, but still fixes each test before that quantifier. It does not
by its name assert one common exceptional set for all tests. Common-null-set
pressure consequences are obtained separately, for example by
`pressure_delta_p_meanFree_ae_forall_of_sws` and
`pressure_delta_p_common_null_set`.

### B29 — The harmonic/CZ splitting and its conditional special case

Paper: `cor:CZ-harmonic`, `eq:har-Ck`.
Lean: `czHarmonic_decomposition_on_inner_ball`,
`czHarmonic_harmonicPart_weaklyHarmonicOn_ae_of_sws`,
`exists_harmonicPressurePart_Ck_ae_of_sws`,
`czHarmonic_forcePart_local_growth_ae_of_sws`.
These component statements distinguish the unconditional splitting and
harmonic estimates from force cancellation, which requires div f=0.
The older combined `czHarmonic_corollary` has additional hypotheses and
should not replace that distinction. Weak harmonicity and a smooth inner
representative are separate statements. Constants depending on cutoff
derivatives become absolute once the explicit cutoff is fixed. The paper's
constant-pressure example explaining the derivative-order scaling is a
separate observation, not a consequence of the combined helper's name.

### B30 — Which centred pressure enters the initial estimate

Paper: `prop:lin34`, `eq:Uhat`, `lem:thmA-start`.
Lean: `lin34_hCZ_p1_ae_of_sws`, `thmA_start_of_CZ`.
The canonical source is the doubly centred tensor, summed over all nine
index pairs. A bound for one indexed operator applied to a singly centred
tensor is not this identity. Earlier helpers using that mismatched identification are not the
justification for the initial estimate. The factor 9 from the tensor sum is already present
in the paper, not a new loss.

### B31 — The selected pressure-gradient bound

Paper: `eq:local-equation`, `cor:CZ-harmonic`, `eq:harm-grad`.
Lean: `slice_selected_gradient_ae_of_sws`,
`slice_selected_gradient_of_potential_representation`.
The bound sums three coordinate L^{6/5} norms of compactly supported sources;
conversion to a vector norm costs at most 3. The harmonic remainder is
p−p₁−(p₇+p₈), so its bound includes the p₁ and force-potential L^{3/2}
norms as well as the pressure norm, and a separate term controls ∇(p₇+p₈).
These terms are not removable by simply renaming the remainder. The concrete
application uses the same half-radius ball for the identity and norm estimate;
a generic helper's second region must be chosen accordingly. An absolute
factor 1000 in the harmonic constant absorbs geometric norm conversions.

### B32 — The force is not assumed divergence-free

Paper: `def:sws`, `eq:pk`.
Lean: `exists_slice_force_weak_gradient_ae_of_sws`, `sliceForceGradientBound`.
The original incorrectly attributed div f=0 to suitability:
incompressibility concerns u. The corrected `prop:pressure-decomposition`
now says “If, in addition” and states local distributional div f=0;
`cor:CZ-harmonic` likewise keeps force cancellation conditional.
The unrestricted proof keeps p₇+p₈ and its gradient. A cancellation result
assuming whole-space slice divergence-freedom is stronger in hypothesis
than the paper's local divergence condition and is only a special case.

### B33 — Identifying the doubly centred pressure

Paper: `lem:delta-p-centred`, `eq:Uhat`.
Lean: `lin34_centredP1_pairing_of_slice_data`, `lin34_centredP1_cz_data_ae_of_sws`.
The singly centred identity cannot be applied by treating the centred
velocity as a new suitable solution. Instead the difference of the two
pressure pairings is computed, and its constant-vector Hessian contribution
vanishes by incompressibility and Hessian symmetry. The direct centered
identity `pressure_delta_p_centred_ae` fixes the test before the a.e. time
quantifier, as does `pressure_delta_p_meanFree_ae_of_sws`. The latter's
common-null-set version is `pressure_delta_p_meanFree_ae_forall_of_sws`;
these are distinct statement strengths, not interchangeable quantifier orders.

### B34 — Tensor-valued CZ assembly

Paper: `prop:lin34`, `ext:CZ`.
Lean: `hCZ_p1_unconditional`, `pressureP1_hident_of_pressureSecondExtension_unconditional`.
The proof applies the indexed scalar second-Riesz extensions to the nine
tensor entries and then sums them. A generic one-component scalar estimate
does not by itself supply this tensor identification.

### B35 — The centred CZ constant

Paper: `prop:lin34`.
Lean: `lin34CZConstant`.
With V=∫|u−average(u)|³, the source majorant is E=27V, so
E^{2/3}=9V^{2/3}. Thus the constant is 9 times the scalar operator constant,
matching the paper's 9C₁₁ rather than claiming a sharper estimate.

### B36 — Retaining the local oscillation norm

Paper: `prop:lin34`, `eq:Uhat`.
Lean: `lin34_hCZ_p1_slice_of_identification`.
The centred proof keeps the source majorant explicit and bounds it by the
oscillation integral on Bρ. This avoids replacing locally given data by an
unjustified whole-space velocity norm.

### B37 — Growth of the pressure residual

Paper: `prop:pressure-decomposition`, `prop:lin34`.
Lean: `pressureSecondExtension_residual_growth_of_decomposition`,
`pressure_force_memLp_and_lpNorm_growth_ae_of_sws`.
The residual comparison uses the solution-level membership and growth
of p₇+p₈ directly. It does not need to reconstruct their lower-level source
assumptions. The Liouville conclusion is unchanged.

### B38 — Growth of the five non-force potentials

Paper: `eq:pk`, `prop:lin34`.
Lean: `lin34_centred_potentials_memLp_and_growth`.
Compact support and the Newtonian-potential estimates supply local
L^{3/2} membership and linear growth on every centred ball for p₂+⋯+p₆.
This supplies hypotheses of the residual argument, not a changed estimate.

### B39 — A force gradient without cancellation

Paper: `eq:pk`, `cor:CZ-harmonic`.
Lean: `exists_slice_force_weak_gradient_ae_of_sws`, `sliceForceGradientConstant`.
The bound for ∇(p₇+p₈) has the form
C_CZ Σⱼ‖ηfⱼ‖_{6/5}+C₈ρ^{−1/2}∫_{Bρ}|f|,
where C₈ is at least `sliceForceGradientConstant`.
The theorem selects a time-indexed field with the required properties for
almost every slice; that selection alone is not joint measurability.
No force-divergence hypothesis is added.

### B40 — Local quantitative inputs on a collar

Paper: `thm:endgame`.
Lean: `endgame_source_target_of_force_producer`, `endgameForceSlotBound`.
The proof uses a uniform cutoff on each small ball centred in a closed
inner collar and pressure-gradient data on a larger concentric ball.
The cutoff coefficient is fixed before the solution; the source constant
is computed from it and the listed velocity, gradient, pressure and force
bounds. These local requirements are proved from the ambient containment,
not added to the final Hölder conclusion.

### B41 — Identifying the field before transferring estimates

Paper: `prop:bootstrap`, `eq:local-equation`.
Earlier intermediate statements allowed an arbitrary extended-valued majorant before
choosing the field. Taking it identically infinite made the bound vacuous,
so it could not imply integrability. The replacement argument identifies
one weak gradient on overlapping regions by almost-everywhere uniqueness
and transfers estimates at each cell's own radius to that same field.
The ball reached by a slice estimate must be respected: using outer radius
3R/2 gives an inner ball of radius 3R/4, not R.

### B42 — The force-free centred source for p₁

Paper: `eq:Uij`, `eq:pk`.
Lean: `pressureDivergenceCutoffSourceCentredTensor`, `sourceMorreyCutoffVCentredTensor`.
For Uᵢⱼ=−uᵢ(uⱼ−cⱼ), the p₁ source is
V⁰ᵢ=Σⱼ[ηDuᵢⱼ(uⱼ−cⱼ)+(∂ⱼη)uᵢ(uⱼ−cⱼ)].
It contains no −ηf. Adding that term while retaining the separate force
potential would count p₇ twice. The pairing and identification must use
this same corrected source, not only its norm estimate.

### B43 — Origin-centred intermediate statements

Paper: `prop:bootstrap`, `thm:A`.
An origin-centred pressure-gradient construction is not the proposition's
velocity improvement on nested cylinders, and no such construction is used
as evidence for either conclusion. The origin-centred region that the proof
of Theorem A does use (`CKN/Core/Endgame/GAAdaptersCell.lean` and the
`originASlot` modules) uses the past-time data controlled by `thm:A`; see
B58.

### B44 — Elementary proof support

Paper: `prop:bootstrap`, `lem:morrey-minkowski`, `lem:cutoff`.
Lean example: `min_q_twentyFive_div_eleven`.
Auxiliary arithmetic, Hölder-pair, Morrey, cutoff, local-box and test-function
lemmas make elementary proof steps explicit. They introduce no mathematical
departure or new hypothesis.

### B45 — Removal of unrestricted-majorant transfers

Paper: `prop:bootstrap`, `eq:local-equation`.
The concrete slice result is `slice_selected_gradient_ae_of_sws`.
The unrestricted-majorant statements of B41 are replaced by a field-first
statement: one field is fixed together with its measurability,
integrability, pressure pairing and cell estimates. Sound auxiliary source
and exponent estimates do not establish that transfer on their own.

### B46 — Constants and geometric helper statements

Paper: `lem:pk-bounds`, `lem:cutoff`, `lem:morrey-cylinders`.
Lean: `pressureP234Constant_nonneg'`, `pressureP56Constant_nonneg'`,
`pressureP13Constant_nonneg'`.
Further elementary geometry and constant lemmas do not change paper-facing
statements. In particular these nonnegativity declarations omit irrelevant
centre and radius hypotheses of earlier versions. Redundant or more weakly
stated helper results are not stronger mathematical evidence merely because
their names sound general.

### B47 — Positivity as well as finiteness of a Sobolev constant

Paper: `ext:sobolev-ball`, `thm:B`.
Lean: `sobolevPoincareL6Constant`, `sobolevPoincareL6Constant_pos`.
Finiteness of an extended nonnegative constant alone does not prove it is
positive: conversion to a real number sends both zero and infinity to zero.
The earlier positivity gap is now resolved by the displayed positivity
theorem. The distinction remains important when constructing a positive
smallness threshold; an upper-bound inequality alone would not establish it.

### B48 — Completed-operator representation of p₁

Paper: `eq:pk`, `eq:CZ-harmonic`.
Lean: `pressureSecondExtensionOperator`, `pressureP1_riesz_identity_of_sws`.
The singular integral is represented by the completed indexed L^{3/2}
second-Riesz operator. The residual definition of p₁ equals this operator
almost everywhere in time and space for the specified tensor source.
Literal Hessian-kernel formulas are exterior representations on sets
separated from support, not global absolutely convergent Bochner integrals;
see `pressureSecondExtensionOperator_agrees_exterior` and
`rieszSecondGradientExtensionOperator_agrees_exterior`.

### B49 — Radius and diameter Hausdorff gauges

Paper: `eq:gauge-comparison`, `thm:C`.
Lean: `parabolicBallRadiusContent`, `parabolicBallRadiusHausdorffContent`,
`parabolicHausdorffMeasure`.
Radius covers are indexed by subsets of ℕ, allowing finite and empty covers.
At dimension one, padding unused indices by a summable positive-radius tail
gives the same infimum as a fully ℕ-indexed cover. The radius gauge P¹ and
the arbitrary-set diameter gauge H¹ satisfy P¹≤H¹≤2P¹, not equality.
Thus null sets agree, but quantitative statements must retain the factors.
The radius-normalized cylinder gauge satisfies P¹≤P̂¹≤2P¹ as well;
substituting the diameter gauge into this display requires the comparison,
not an equality of normalizations (`lem:P1-cylinders`).
These sharp comparisons and the padding argument describe the mathematical
normalizations; they are not a claim of a named formal equality theorem.
`CKN.parabolic_spherical_hausdorff_comparison` in
`CKN/Covering/SphericalGaugeFull.lean` proves the two-sided factor-2^α
comparison for every real α≥0, including α=0 and arbitrary sets. Its
factor-2 specialization at dimension one suffices for null sets. This general
comparison is included by `CKN.lean` but is outside the main theorems'
import closure.
`parabolic_radius_hausdorff_content_comparison` supplies the ball/cylinder
comparison.
At exponent zero the finite/empty convention is essential: requiring
infinitely many positive-radius terms would force every cover cost to infinity.
The corrected `def:parabolic-hausdorff` already allows finite and empty
covers; `eq:gauge-comparison` states the two-sided factor-2^α comparison
for α≥0, specializing to factor 2 at dimension one and covering α=0
and the empty set as well.

### B50 — Historical correction to the pressure multiplier

An earlier version of the manuscript printed a positive Fourier multiplier for
the operator Tⱼₗ=−∇∂ⱼ∂ₗΔ⁻¹. With ∂ⱼ represented by iξⱼ and Δ⁻¹ by
−|ξ|⁻², its multiplier has the negative sign
−iξξⱼξₗ/|ξ|². An intermediate revision corrected that sign. A later revision
removed the pressure-representation lemma and its display from the manuscript;
this entry records the history rather than citing a current source label.
The kernel −∂ᵢ∂ⱼ∂ₗN confirms the corrected sign. The Lean definition
`pressureMultiplierSymbol` intentionally represents the original positive
symbol, hence −Tⱼₗ; its subordinated heat kernel has that same sign.
Negating that definition without changing the kernel would break their
identification. The smooth degree-one symbol class and its absolute-value
bounds are invariant under this sign change.

### B51 — Spatial multipliers on spacetime sources

Paper: `eq:heat-potential`, `eq:heat-kernel-bounds`.
Lean: `sliceMultiplierApply`, `integral_multiplierHeatKernel_eq_integral_sliceMultiplier`,
`causalMultiplierPotential_eq_slice_form`.
The multiplier acts on each spatial time slice. Commuting this action with
causal heat convolution requires integrability and the appropriate kernel
identity; these must be proved for the sources in use. The slice formula
for general Morrey sources is almost everywhere, not universally pointwise.
The Fourier normalization uses the inverse-transform factor (2π)⁻³;
no exceptional-input fallback changes the meaning of the operator.
The corrected `eq:heat-potential` explicitly includes the a.e. slice formula,
absolute integrability a.e., and the all-test distributional interpretation.

The declarations named above are faithful formalizations of the printed
statement that lie outside the import closure of the main theorems; see
B62 for what the main proof uses instead.

### B52 — The Sobolev domain needed by the proof

Paper: `ext:sobolev-ball`, clause (ii).
Lean: `sobolevPoincare_L6_ball_weak` and its ball embedding consequences.
The corrected external input is restricted from the original's bounded
Lipschitz domains to balls,
the only domains used here. Scaling gives the form
‖g‖_{L⁶(B_r)}≤C(‖∇g‖_{L²(B_r)}+r⁻¹‖g‖_{L²(B_r)}), with absolute C.
No general Lipschitz extension theorem is asserted or needed.
The corrected clause (iv) likewise uses a ball and retains its radius factors.

### B53 — Positive-time kernel bounds

Paper: `eq:heat-kernel-bounds`, `ext:heat-kernel`.
Lean: `exists_spatialMultiplierHeatKernel_bounds_of_degreeOne`, `spatialMultiplierHeatKernel`.
Derivative estimates hold for t>0; the causal kernel is zero for t<0.
A degree-one multiplier kernel can have a nonzero limit at t=0⁺ away
from the spatial origin, so its time derivative need not exist across
t=0. Almost-everywhere size bounds do not justify a mean-value argument
across that slice. Crossing-time integral estimates require a separate argument.
Both `eq:heat-kernel-bounds` and `ext:heat-kernel` in the corrected manuscript
already specify positive-time derivative bounds and negative-time vanishing.

The declarations named above are faithful formalizations of the printed
statement that lie outside the import closure of the main theorems; see
B62 for what the main proof uses instead.

### B54 — The manuscript adopts the pressure-gradient bootstrap

Paper: `lem:pressure-gradient-morrey`, `prop:bootstrap`,
`eq:bootstrap-gain`, `cor:one-round`, `thm:endgame`.
Lean: `CKN.Core.Step4.bootstrap_round_of_step2`,
`CKN.Core.Step4.bootstrap_routeA_uniform`.

The current manuscript proves the bootstrap round through a localized
Morrey estimate for one measurable weak pressure gradient. For velocity
exponent τ between 25/3 and 25, the gradient belongs to
M^(6/5,min(q,(1/τ+8/25)⁻¹)). Its proof uses the completed Riesz operators
and a fixed-scale harmonic and annular force remainder with finite
L^(3/2) time norm. It does not assume growth of raw pressure norms on
shrinking cylinders.

The localized heat sources are F=g−φDp and Gᵢ=−2(∂ᵢφ)u. Adams estimates
for I₂|F| and I₁|Gᵢ| give 1/ς=1/τ−2/25, hence 25/3→25 in one round.
For 5<τ<25/3 the proof first uses the stronger Step 2 exponent and then
lowers the output exponent. The final source exponents are min(q,25/9)
and 25/3, with the same Hölder exponent min(2−5/q,1/5).

The original manuscript's pressure representation, commutator/Taylor
argument and five-family pointwise-potential lemma are removed rather
than identified with this proof. None was needed by the proved main
theorems. The general Newtonian derivative identity `eq:third-derivative-N`
is retained. The proposition and main theorem statements are unchanged;
the earlier optimization over a variable iteration exponent is no longer
asserted. This replaces the description in B13 of two retained proofs.

The declarations named above are faithful formalizations of the printed
statement that lie outside the import closure of the main theorems; see
B62 for what the main proof uses instead.


### B55 — Equivalent Campanato representative construction

Paper: `eq:campanato-scales`, `eq:campanato-points`, `eq:campanato-cauchy` (the Hölder-representative construction).

The manuscript constructs the Hölder representative by scaled mollification with uniform convergence, while the formalization constructs it as the limit of dyadic closed-ball averages. Both routes prove the shared downstream conclusion: existence of an a.e.-equal representative with the Campanato-to-Hölder bound. This records an equivalent construction and does not claim that Lean formalizes the manuscript's scaled-mollifier proof.

### B56 — Equivalent common-null-set pressure construction

Paper: `lem:delta-p`.

The manuscript chooses a countable C^2-dense family of test functions and
extends the slice identity by continuity. The formalization uses translated
mollifier tests and the slice-distribution upgrade, exported by
`CKN.pressure_delta_p_meanFree_ae_forall_of_sws` and
`CKN.pressure_delta_p_common_null_set`; its countability is for a dense set of
translation points used by the mollifier construction. Both constructions
produce one exceptional time set for every admissible test, so this records an
equivalent construction rather than a difference in the proved conclusion.

The declarations named above are faithful formalizations of the printed
statement that lie outside the import closure of the main theorems; see
B62 for what the main proof uses instead.

### B57 — Integrability conjuncts of the suitable weak-solution class

Paper: `def:sws`.
Lean: `CKN.IsSuitableWeakSolution`
(`CKN/Statements/SuitableWeakSolution.lean`), `CKN.IsSuitableWeakSolutionIntegrable`
(`CKN/Statements/SuitableWeakSolutionIntegrable.lean`),
`CKN.isSuitableWeakSolution_iff_integrable` (`CKN/ClassEquivalence/MainTheorems.lean`).

The public class once listed integrability of the (S2)-(S4) integrands, on
`tsupport ψ` / `tsupport φ`, as four explicit conjuncts, where the paper's
(S2)-(S4) carry no such side condition. As stated, that class was a priori
narrower than the paper's.

The redundancy is now proved: `CKN/ClassEquivalence/` isolates the six data
clauses of `def:sws` as `CKN.IsSuitableWeakSolutionData`, whose body is the
definition block character for character and to which
`CKN.IsSuitableWeakSolutionIntegrable.toData` projects with no tactic; four lemmas derive
the conjuncts from those clauses alone; and
`CKN.isSuitableWeakSolutionIntegrable_of_identities` assembles the class from the data
clauses together with the three identities written without them.

The three main theorems were then restated to take
`CKN.IsSuitableWeakSolution`, which is the public file
`SuitableWeakSolutionIntegrable.lean` with exactly those four conjuncts deleted and
nothing else changed. `CKN.IsSuitableWeakSolutionIntegrable` is retained as the internal
working class, and the two are identified by
`CKN.isSuitableWeakSolution_iff_integrable`. The manuscript's hypothesis and the
public hypothesis now agree without appeal to this entry.

The first three conjuncts need no interpolation: a test function has compact
support, so every integral is taken over a set of finite measure and the
products are controlled by Cauchy-Schwarz from the (S1) energy bounds, using
only `q >= 1`. Only the local energy inequality's right-hand side needs the
parabolic `L^{10/3}` interpolation, for the cubic velocity term and for
`p * u`; it is obtained from `CKN.ball_time_sobolev` over a finite cover of the
compact support by balls.

Because Lean assigns the value zero to a Bochner integral whose integrand is
not integrable, the assembling theorem derives integrability from the data
clauses before it uses any identity, and the identities it uses are
written with the integral exactly as the public clauses write it.

### B58 — One-sided quantitative estimates for Theorem A

Paper: `thm:A`, `lem:pressure-gradient-past`, `prop:past-bootstrap`.
Lean: `pressure_gradient_quantitative_of_origin_cell_producer`,
`pressure_gradient_existential_of_origin_cell_producer`
(`CKN/Core/Endgame/GAAdaptersCell.lean`), and the quantitative instances in B60.

The quantitative proof of Theorem A uses origin-centred backward cylinders
and estimates controlled by the data on the unit backward cylinder. A
suitable solution is defined on an open neighbourhood of that cylinder's
closure, so a small future neighbourhood does exist. The hypotheses do not,
however, give a uniform future radius or a bound for the data there in terms
of the stated unit-cylinder smallness. One-sided estimates avoid needing
such additional quantitative information.

The manuscript now makes this route explicit in
`lem:pressure-gradient-past` and `prop:past-bootstrap`. The lemma allows
arbitrary nested backward-cylinder radii 0<r<R and every τ∈[25/3,25],
with quantitative bounds depending only on the specified past-time data.
An open time collar is used to obtain a locally integrable weak-gradient
representative; no quantitative future estimate is required. The proposition
first improves the velocity Morrey exponent to 25 on a smaller past
cylinder, then constructs a global Hölder function agreeing almost everywhere
with the solution on a still smaller past cylinder. Its conclusion does not
assert open-neighbourhood regularity on the top time face.

These manuscript statements are broader than the two quantitative Lean
instances listed in B60. Theorem A uses the corresponding one-sided
construction at its fixed radii; this does not identify those instances with
a formalization of the new lemma and proposition at every permitted radius.

The geometric facts `forwardTime_mem_metricBall` and
`metricBall_not_subset_closure_parabolicCylinder` express the difference
between symmetric balls and backward cylinders. A closed product used by
`exists_spaceTimeSet_without_symmetric_ball` is not an open suitable-solution
domain; it is not a counterexample to the neighbourhood supplied by
suitability. This geometric distinction does not limit the general qualitative
pressure-gradient result used for Theorem B; see B60.

### B59 — The affine origin pressure-gradient bound

Paper: `lem:pressure-gradient-past`; see B54 and B58.
Lean: `originKPAffineASlot`, `oneSidedPressureGradientKPAffine`
(`CKN/Core/Step4/PressureGradientOriginKPAffineSlot.lean`), used as the `KP` bound in
`CKN/Core/Endgame/TheoremAFullSumAssembly.lean` and
`CKN/Core/Endgame/TheoremACloser.lean`.

The `KP` bound used by the proof of Theorem A is affine in the source
bound `X = 3·KU·KD + forceSourceMorreyBound q ε`, not linear. The linear
form `oneSidedPressureGradientKP` is refuted by an explicit counterexample
recorded at `CKN/Core/Step4/PressureGradientOriginKPAffineSlot.lean`: the zero-velocity datum with linear pressure `a·x₀` and balancing
force `a·e₀` has cell integrals equal to `X^{6/5} r⁵` at the sharp data
size, exceeding any fixed multiple of `X` once `a` is large.
`originKPAffineASlot` repairs this by adding the source term's own `6/5`
power and a pressure-mass term `128·ε^{4/5}`.

### B60 — General pressure-gradient membership and the quantitative instances

Paper: `lem:pressure-gradient-morrey`, `lem:pressure-gradient-past`,
`prop:past-bootstrap`.
Lean: `CKN.Core.Step4.routeAGradientProducerUniform`,
`CKN.Core.Endgame.theoremB_gradient_producer_of_small_cell_majorant`,
`CKN.Core.Step4.bootstrap_routeA_uniform`,
`theoremA_aSlot_integral_instances`, `theoremA_bslot_integral_instances`.

The general qualitative result is formalized: for every centre z, positive
radius R with `Metric.ball z (2 * R)` inside the solution domain, and
τ∈[25/3,25], the velocity and gradient Morrey hypotheses yield a measurable
weak pressure gradient in M^(6/5,min((1/τ+8/25)⁻¹,q)) on the half-radius ball.
`routeAGradientProducerUniform` states this result. Theorem B constructs and
uses it in `CKN/Core/Endgame/TheoremBCloser.lean`; the remaining small-cell
hypothesis there is discharged in `TheoremBUnconditional.lean`.
`bootstrap_routeA_uniform` is a separately proved general instance.

The restricted results are the quantitative one-sided estimates used for
Theorem A. `theoremA_aSlot_integral_instances` and
`theoremA_bslot_integral_instances` carry the condition
`((τ = 25/3 ∧ R₀ = 11/16 ∧ R₁ = 43/64) ∨ (τ = 25 ∧ R₀ = 5/8 ∧ R₁ = 19/32))`.
They supply explicit bounds at the two exponent-radius triples used by that
proof. The general qualitative result establishes finite Morrey membership;
the quantitative instances additionally track explicit bounds from the
unit-cylinder data at those triples. The manuscript's
`lem:pressure-gradient-past` and `prop:past-bootstrap` permit general nested
past-cylinder radii; the two Lean instances do not establish that full
quantitative generality. The general qualitative result used by Theorem B
is the symmetric-ball result above, with a separate interface and scope.

### B61 — Absolute constants and the main proof's dependencies

Paper: `eq:thmA-morrey`, `lem:theta-decay`, `prop:iteration`,
`prop:morrey-decay`.

The library proves the absolute-constant statements. In
`CKN.thmA_morrey_absolute` (`CKN/Core/TheoremA/ThmAMorreyAbsoluteAdapter.lean`),
the radius r₅ and coefficient M are quantified before the force exponent q;
only the smallness threshold ε₀ is chosen after q. Likewise,
`CKN.theoremA_initial_morrey_absolute`
(`CKN/Core/TheoremA/InitialMorreyAbsolute.lean`) chooses finite initial
Morrey bounds before q. Its three conclusions bound the velocity, gradient,
and pressure on the backward cylinder of radius 5/8. The main Theorem A
assembly instead obtains initial velocity and gradient bounds on the cylinder
of radius 11/16 from
`CKN.Core.Endgame.theoremA_initial_uniform_of_displays`
(`CKN/Core/Endgame/InitialUniform.lean`), consumed by
`TheoremAClosersInstancesQ.lean`. That initial interface does not assert the
separate pressure Morrey bound; it should not be identified with the
three-component absolute statement.

`CKN.thetaDecay_T_of_sws_absolute`, `CKN.iteration_of_sws_absolute`, and
`CKN.morreyDecay_of_sws_absolute` in the corresponding `AbsoluteConstant`
modules under `CKN/Core/Step2/` choose C₂₇ before q. The contraction and
thresholds defined from C₂₇ consequently have the stated independence.

These modules are included by `CKN.lean` but lie outside the import closure
of the three main theorem statement modules. The main proof uses estimates
whose statement shapes permit q-dependent constants, which is sufficient
for its conclusions. This is a difference in dependencies, not a missing
proof of absoluteness.

## Constants and source conventions

The following conventions accompany the differences above.

- `morreyNorm_lower_integrability` corresponds to `lem:morrey-minkowski`
  (ii), lowering the integrability exponent at fixed Morrey exponent. Its
  factor is the unit backward cylinder's volume (4π/3)^(1/P′−1/P).
  The manuscript uses symmetric parabolic balls and therefore (8π/3)^(1/P′−1/P).
  `eq:morrey-lower` instead concerns lowering the Morrey exponent under a
  support restriction; `morreyNorm_lower_morrey_exponent` is the corresponding
  cylinder-supported estimate. These are different embeddings.
- Newtonian second- and third-derivative size estimates use explicit
  coefficients 24/(4π) and 204/(4π), respectively (`ext:newtonian`).
- `parabolicCampanatoHolderConstant` (`lem:campanato`) records the dependence
  on the exponent; the vector construction incurs a factor 3.
- `caccioppoliC₂₅` and `caccioppoliC₂₆` (`eq:caccioppoli`) are explicit
  square roots of sufficient square-size bounds. Integral addition and
  the square-sum estimate introduce the factor 6000. The resulting radius
  powers κ, κ⁻¹ and κ^{−1/2} are unchanged.
  Specifically C₂₅=√(6000·`caccioppoliC₂₅BaseSquared`), where the base is
  a nested maximum, and C₂₆(q)=√(6000·2000·(4π/3)^{1/(q/(q−1))−1/3}).
  Conversion to the gamma form is justified by separate square-size bounds
  for all four terms, rather than by silently reusing a too-small constant.
- `pressureP12Constant` and `pressureP13Constant` (`lem:pk-bounds`) dominate
  their component estimates. Pressure/theta assembly can further enlarge
  them by maxima with the p₁ constant and `pressureP7SolutionConstant`.
  This is a conservative choice of unnamed constants, not a sharper claim.
- In `lem:theta-decay`, the assembled constants are sums:
  C₂₇=3C₁₄²+C₂₅(1+2√C₉)+2C₂₅√C₉ and
  C₂₈=3C₁₅²+2C₂₆√C₉. Their hypotheses and selected contraction remain explicit.
- `localizedGradientSourceG` and `localizedGradientSourceH`
  (`eq:local-equation`, `thm:endgame`) put g−φ∇p in the undifferentiated
  source and −2(∂ᵢφ)u in the differentiated source. The Duhamel convention
  carries the corresponding sign. Final source parameters are
  (6/5,min(q,25/9)) and (6/5,25/3); the first bootstrap uses
  (6/5,25/11) and (3,25/6). Lowering an exponent on bounded support
  includes its volume factor.

## Statement conventions, corrections, and remaining scope differences

The rows below distinguish manuscript corrections from explicit choices in
Lean. They do not assert that every Lean formulation has been copied into the
printed statement. The unused functional-analytic route is described after
the table.

| Paper labels | Change |
|---|---|
| `eq:duhamel`, `lem:local-equation` | The manuscript states the localized identity and Duhamel formula distributionally with ∇p; its lemma does not explicitly select an integrable field in the conclusion. Lean supplies a measurable integrable weak pressure gradient where the sources require one and uses that same field in the pairings and estimates. `localized_duhamel_from_leibniz_of_sws` proves the direct causal representation. This additional explicit data is a formalization choice, not a claimed correction already printed in that lemma. |
| `lem:monotonicity`, `lem:interpolation-cylinder` | Require a compactly interior outer cylinder when using real-valued scale quantities under local energy assumptions. Infinite integrals must not be converted to zero before a radius comparison or interpolation estimate. The radius powers themselves are not corrected. |
| `ext:heat-kernel`, `eq:duhamel` | Unrestricted uniqueness for distributions supported in a lower time half-space is false: a Tychonoff heat solution is a counterexample. The corrected uniqueness statement restricts to tempered distributions. It is not required by the direct Duhamel proof, and is not claimed proved here. Half-space support alone also does not define a general convolution algebra. |
| `ext:sobolev-ball` (iv), `eq:interp-q103` | State the time-Sobolev estimate on a Euclidean ball with its radius factors, not an arbitrary bounded open domain. Disconnected domains with arbitrarily small components refute the unrestricted form. `ball_time_sobolev` supplies membership and the bound with the essential-supremum slice mass; a sharper actual-mass bound is not thereby asserted. |
| `ext:campanato`, `lem:campanato` | The comparison-only external Campanato characterization is not an input to the proof. The self-contained ball-average argument is used instead. This is a scope decision, not a proof of the excluded characterization. |
| `ext:aubin-lions` | The compactness theorem is not used in the chosen proof. Its general statement, including the time-continuity endpoint, is not claimed formalized by excluding it. |
| `eq:time-cutoff` | The literal cutoff is the decreasing piecewise-affine ramp: 1 before t−h, (t−s)/h on (t−h,t), and 0 afterwards. It is Lipschitz with derivative −1/h on the transition interval almost everywhere, not a smooth nondecreasing function. This corrects the description, not the printed formula. |
| `ext:heat-kernel`, `eq:duhamel` | The uniqueness clause has the tempered-distribution correction of the heat-kernel row above; delete unrestricted convolution-algebra and invertibility claims. Fundamental-solution identities and kernel bounds remain separate requirements. No new uniqueness theorem is claimed. |
| `ext:sobolev-ball` (ii) | Restrict the embedding to balls, with an absolute constant after the appropriate scaling, as explained in B52. |
| `eq:heat-kernel-bounds`, `ext:heat-kernel` | Assert kernel derivatives on t>0 and vanishing on t<0. Do not assert classical time differentiability across t=0 for general degree-one multipliers; see B53. |
| `prop:bootstrap`, `thm:endgame` | The original commutator and separated-remainder estimates are not inputs to the main proofs; the pressure-gradient source estimates supply their roles. This omission does not prove the unused estimates. |
| `lem:pressure-gradient-morrey`, `prop:bootstrap`, `cor:one-round`, `thm:endgame` | The current manuscript adopts the pressure-gradient proof and removes the former pointwise-potential and commutator route. Main theorem statements and their proved conclusions are unchanged; see B54. |

### B62 — General results, specializations, and unused exposition

A separately proved manuscript formulation can lie outside the main theorems'
import closure even when related estimates are used inside it. Rows B51,
B53, B54 and B56 describe examples; B61 lists the absolute-constant results.
An import-closure statement concerns available modules, not by itself the
exact dependency of an individual proof term.

Theorem A uses a quantitative Hölder-norm estimate on the closed
half-cylinder, corresponding to the one-sided route now stated in
`prop:past-bootstrap`; B58 and B60 describe its specialization. For
`thm:endgame`, Theorem B uses an arbitrary-centre qualitative
regularity argument: `regular_point_of_local_producers` in
`CKN/Core/Endgame/ProducerRegularity.lean` is applied by `TheoremBCloser.lean`
to a ball about the point under consideration. Its pressure-gradient input
is the general result described in B60. Neither use should be identified
with a proof of every quantitative bound at every centre and radius merely
because it yields a Hölder representative. General quantitative formulations
are supplied separately in the `QuantitativeEndgame` modules.

For `thm:C`, the Vitali selection, defect radii and radius sum are carried out
inside `CKN.singularSet_null_of_gradient_criterion_closed` and
`CKN.Foundation.Parabolic.parabolicHausdorffMeasure_one_le_integral_of_small_cylinders`.
Other modules under `CKN/Covering/` expose related steps and comparisons
separately. Theorem C's only imported module from that directory is
`TheoremCReductionClosed.lean`; that does not make the separately proved
covering results unavailable to users of `CKN.lean`.

### Exposition outside the formalized proof route

The manuscript's `eq:Z-space`, `lem:H2-embeddings`, `lem:dtu-dual`, and
`lem:weak-time-continuity` develop a weak-time-continuous representative
through the dual of H²₀. That chain, including the Z-space construction and
the domain H²₀ embeddings in their printed form, is not formalized here.
The associated `ext:pettis` and `ext:dubois-reymond` are unused external
inputs, not results supplied for this chain by Mathlib. The same scope
qualification applies to the unused `ext:aubin-lions` and the external
Campanato comparison; the proof uses its own `lem:campanato` construction.

The library separately proves `CKN.global_sobolev_embeddings`, which uses
whole-space H¹ functions with explicit
weak-gradient representatives to express global H²-type bounds. It is not
the H²₀/Z-space development above. The almost-every-time local energy route
used by the main theorems does not need that development.
