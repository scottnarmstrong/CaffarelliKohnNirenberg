# Mathematical and formalization design notes

These notes explain the conventions and proof choices behind the formalization
of the paper's `thm:A`, `thm:B`, and `thm:C`. They distinguish changes needed
for faithful mathematical statements from choices of proof. A theorem about
a special case or an alternative representation is not identified with a
more general paper statement merely because it suffices for the final result.

Paper labels refer to the included `paper/ckn.tex`. These notes distinguish
its printed statements from the explicit representations used in Lean, as
well as from supporting exposition outside the formalized proof route.

## Space, domains, derivatives, and tests

Space is represented by `Vec3 = Fin 3 → ℝ`, and spacetime by `Vec3 × ℝ`.
Spatial balls and the quantitative vector norms are Euclidean. The
solution predicate's energy-finiteness clauses use the ambient supremum
norms on `Vec3` and gradient arrays; in these fixed finite dimensions this
is equivalent to Euclidean finiteness. Quantitative estimates use explicit
norm comparisons rather than equating their numerical values.

A solution is defined on a product \(\Omega\times I\), where \(\Omega\)
is open and \(I\) is an open interval. This suffices for local regularity
on an arbitrary open spacetime set, since such a set can be covered by
relatively compact product neighbourhoods. It does not assert that a local
solution can be extended to a solution on all spacetime.

The weak spatial gradient is explicit data:
`Du : ParabolicPoint → Fin 3 → Vec3`. The solution predicate characterizes
it as the weak gradient of the velocity on almost every time slice.
Consequently quantities involving \(\nabla u\) are functions of specified
data, not of an unspecified choice of a derivative. Almost-everywhere
uniqueness identifies two fields that satisfy the same weak-gradient
characterization.

### Test functions on the product space

Smooth compactly supported test functions live on the ordinary product
space, with spatial and temporal derivatives taken in the corresponding
factors. Smooth means \(C^\infty\), not real analytic. Differentiation of
tests and distributions does not use the parabolic metric as a normed
vector-space structure.

## Integrability and finite-valued quantities

The solution class in `def:sws` explicitly requires local measurability and
finiteness of the energy quantities, pressure membership in \(L^{3/2}\),
and force membership in \(L^q\). The weak-equation and local-energy clauses
also require integrability of their integrands on the support of each test
in the internal class `IsSuitableWeakSolutionIntegrable`. The public class
`IsSuitableWeakSolution`, which the three theorems take, states the
manuscript's `def:sws` with no such side conditions; they are proved
redundant in `CKN/ClassEquivalence/` (see DEVIATIONS B57).
An identity of totalized Bochner integrals alone is not used to assert that
a distributional pairing is well defined.

Nonnegative masses and essential suprema are first handled in
\(\mathbb R_{\ge0}\cup\{\infty\}\). The scale quantities in `eq:ABCDE`
are real-valued, with finiteness established before interpreting the
conversion to real numbers. In particular, the library convention
`ENNReal.toReal ∞ = 0` must never make an infinite mass into a small datum
in a mathematical argument.

For `lem:monotonicity` and the cylinder interpolation bounds, the outer
cylinder has closure contained in the solution domain. This compact
interior condition supplies the finite masses and energy supremum needed
by their real-valued formulation. Mere containment of an open cylinder
would not control singular behaviour at its boundary. The interpolation
statement still assumes only the velocity and weak-gradient part of the
local energy class; the geometry correction does not add the momentum
equation, incompressibility, pressure, force, or local energy inequality.
The full radius range, including equal radii, and the outer time window
are retained. Change-of-variables identities in `lem:scaling-quantities`
have their own hypotheses; this condition is not imposed on them by analogy.
The corresponding interior conditions also occur in the pressure slice and
decomposition results, U-bounds, slice-norm identities, theta decay,
iteration, and the gamma-form Caccioppoli estimate. Depending on the result,
the condition is on a cylinder closure or a spatial ball closure; fixed-test
identities may instead require compact test support inside the domain.

The hypothesis of `thm:B` is the limsup of the extended nonnegative
normalized gradient mass,

\[
 \limsup_{r\downarrow0}\frac1r\iint_{Q_r(z_0)}|Du|^2<\varepsilon_1^2.
\]

It is not a limsup of a real conversion that could discard infinity.
On sufficiently small interior cylinders, finiteness justifies comparison
with the paper's real-valued \(\beta(z_0,r)^2\).

## Representatives and the scope of time statements

### The Hölder representative and the open-interior conclusion

Regularity conclusions concern an almost-everywhere equal continuous
representative. In `thm:A`, the Hölder representative and its norm are
controlled on the closed half-cylinder, but the regular-point conclusion
is only on its open interior. The upper time face is not an interior
neighbourhood and is not declared regular by that conclusion alone.

The local energy inequality `lem:lei-pointwise` is used at almost every
terminal time. Time cutoffs and Lebesgue differentiation give this form
directly from the distributional inequality. Subsequent energy estimates
use integrals or essential suprema, together with the upper-semicontinuity
estimate for the local energy. They do not require an every-time energy
inequality or the separate weak-time-continuity and time-derivative
statements `lem:weak-time-continuity` and `lem:dtu-dual`. Those statements,
the Z-space construction `eq:Z-space` and the printed H²₀-domain embeddings
`lem:H2-embeddings` are not formalized here. Pettis measurability and the
vector-valued du Bois-Reymond lemma (`ext:pettis`, `ext:dubois-reymond`) are
unused external inputs to that alternative route, not discharged Mathlib
inputs. Separate whole-space H²-type bounds are proved by
`CKN.global_sobolev_embeddings`; they do not constitute that H²₀/dual-space
construction.

A slice identity valid almost everywhere for each fixed test need not have
one exceptional set that works for every test. Where a common exceptional
set is required, it is obtained using countable dense families and
continuity of the pairings, including continuously parametrized test
families. The order of the almost-everywhere and universal quantifiers
remains part of the mathematical assertion.

The literal cutoff in `eq:time-cutoff` is the decreasing affine ramp

\[
 \chi(s)=
 \begin{cases}
  1,&s\le t-h,\\
  (t-s)/h,&t-h<s<t,\\
  0,&s\ge t,
 \end{cases}
 \qquad 0<h<t-t_-.
\]

It is Lipschitz, with derivative \(-h^{-1}\mathbf1_{(t-h,t)}\) almost
everywhere. A smooth approximation used to insert it into a weak equation
is a different function. Neither the approximation nor a separate
increasing cutoff changes the meaning of this displayed ramp.

## Pressure operators and the chosen regularity argument

The pressure estimates use a classical Calderón–Zygmund construction within
this repository. The construction proceeds through an \(L^2\) estimate,
a weak \((1,1)\) estimate, interpolation and completion. Its operators on
\(L^p\) are bounded extensions from a dense class. A singular Hessian
kernel is not treated as an absolutely convergent convolution everywhere;
literal kernel formulas require separation from the source support or an
appropriate singular-integral interpretation. No analytic estimate from
another formalization repository is assumed as a dependency.

The pressure equation and the identification of the resulting operator
with the chosen pressure term are separate obligations. The singly centred
tensor \(-u_i(u_j-c_j)\) and the doubly centred tensor
\(-(u_i-c_i)(u_j-c_j)\) serve different estimates. The latter is used in
the Lin pressure estimate, while the former occurs in the pressure-decay
and harmonic-remainder arguments. Incompressibility and Hessian symmetry
justify the appropriate changes of centering; the two formulas are not
interchanged without that identity.

Divergence freedom of the force is an additional hypothesis when used for
force-potential cancellation. It is not part of `def:sws`. Similarly,
weak harmonicity of a pressure remainder does not silently assert a
classical smooth representative on a larger region. Interior
representatives and their derivative estimates must be supplied on the
regions where they are used (`lem:harmonic-interior`). Component estimates
can be assembled into a corollary only after their identification and
integrability hypotheses have been proved.

The manuscript's regularity proof avoids the itemized commutator expansion by keeping
the weak pressure gradient in the undifferentiated source. For the
localized velocity \(v=\varphi u\), it uses

\[
 F=g-\varphi Dp,\qquad G_i=-2(\partial_i\varphi)u,
 \qquad (\partial_t-\Delta)v=F+\sum_i\partial_iG_i.
\]

Here \(g\) contains the cutoff, convection and force terms of
`eq:local-equation`. The manuscript's `lem:local-equation` states a
distributional identity and Duhamel formula with ∇p; it does not explicitly select an integrable field in
its conclusion. The formal proof supplies a measurable weak pressure-gradient
field, its required integrability and all-test identities, and uses the same
field in the source, the representation, and its estimates.
A bare pairing identity with no integrability guarantee is insufficient.

The general qualitative pressure-gradient result
`CKN.Core.Step4.routeAGradientProducerUniform` covers every admissible centre,
radius and τ∈[25/3,25], and is used by the proof of Theorem B. Theorem A's
explicit one-sided bounds use two prescribed exponent-radius triples. The
manuscript's `lem:pressure-gradient-past` and `prop:past-bootstrap` now
state the corresponding past-time route for general nested cylinder radii.
The lemma covers every τ∈[25/3,25]; the proposition improves the velocity
Morrey exponent to 25 before its final Hölder estimate. The quantitative
Lean instances used for Theorem A do not by themselves formalize these new
statements at every permitted radius.

The solution domain is open, including past and future neighbourhoods of its
interior points, but Theorem A's unit-cylinder data do not control a uniform
future neighbourhood. Its quantitative construction therefore uses backward
cylinders. The manuscript likewise uses the future collar only to obtain a
qualitative weak-gradient representative and to localize the equation;
causality makes the estimates depend on past data. Its past-bootstrap
conclusion gives a Hölder representative up to the top face, without
asserting open-neighbourhood regularity there. These quantitative
specializations are separate from the general qualitative result used by
Theorem B.

### Steps belonging only to the alternative proof

The original manuscript also estimated a pressure commutator, its Taylor
remainder and a separated-support remainder. Those steps are not inputs
to the proofs of the three main theorems. Their roles in the bootstrap and
Hölder estimates are supplied instead by the selected pressure gradient
and the two sources above, with the required exponents and constant
dependence. Omitting an unused proof route does not prove its individual
estimates.

### The manuscript follows the pressure-gradient proof

The proof of `prop:bootstrap` now follows the formal proof: first obtain
the localized weak-pressure-gradient Morrey bound
(`lem:pressure-gradient-morrey`), then apply the order-two potential estimate
to \(F\) and the order-one estimate to the \(G_i\). A fixed-scale harmonic
and force remainder is controlled by an \(L^{3/2}\)-in-time majorant;
no shrinking-scale growth assumption on unnormalized pressure is added.

The reciprocal-exponent gain is \(2/25\), giving \(25/3\to25\) in one
round (`eq:bootstrap-gain`, `cor:one-round`). The arbitrary-exponent
proposition is proved separately: when the incoming exponent is below
\(25/3\), the stronger Step 2 bound is used first and the resulting
exponent is lowered on bounded support. The final source exponents are
\(\min\{q,25/9\}\) and \(25/3\), yielding the unchanged Hölder exponent
\(\min\{2-5/q,1/5\}\).

The original manuscript's five-family pointwise-potential lemma and display,
pressure-commutator representation, and commutator/Taylor argument have
been removed from the current manuscript. The main theorem proofs did not
depend on them; the main theorems' statements and assumptions are unchanged.
This is a replacement of a proof, not a proof of the removed five-family
estimate. General homogeneous-multiplier heat estimates remain separate
results and are not inferred from the coordinate-derivative calculation.

Intermediate constructions that are superseded and unused by the final
Theorem A proof are not retained as mathematical assumptions. In particular,
the earlier one-sided origin pressure-gradient interface does not alter
any of the three main theorem statements.

## Heat representation and time-zero kernels

The causal representation `eq:duhamel` is proved by backward adjoint heat
tests and the localized equation. Equality against compact smooth tests,
together with local integrability, yields the almost-everywhere equality
of the localized velocity and its heat potential.

Causality alone does not imply uniqueness for arbitrary distributional
solutions of the homogeneous heat equation: smooth solutions with excessive
spatial growth can vanish for all past times and still be nonzero later.
A corrected uniqueness statement can be formulated for tempered
distributions with support bounded below in time, but this is not an input
to the direct adjoint proof. It is not claimed as a formalized theorem here.

Distributions supported in a time half-space do not form a universal
convolution algebra, even if they are tempered. Individual convolutions
need appropriate existence conditions; compact support of one factor is a
standard sufficient condition. Removing the unused uniqueness argument
does not remove the required fundamental-solution identity, kernel
integrability, derivative bounds, or adjoint identities of `ext:heat-kernel`.

The classical size and derivative estimates in `eq:heat-kernel-bounds`
are asserted for positive time. Causal kernels vanish for negative time,
and their values on the zero-time slice do not affect spacetime integrals.
For a general degree-one spatial multiplier, its heat kernel can have a
nonzero right trace away from the spatial origin; classical time
differentiability across time zero therefore cannot be assumed. In
particular, a mean-value argument crossing that slice requires a separate
estimate of the crossing region. Nullness of the slice alone does not
justify such an argument.

## Sobolev estimates and unused comparison results

The bounded-domain Sobolev estimates needed here concern Euclidean balls.
Their constants have the correct scaling: for one absolute \(C\),

\[
 \|g\|_{L^6(B_r)}\le C\bigl(\|\nabla g\|_{L^2(B_r)}
                    +r^{-1}\|g\|_{L^2(B_r)}\bigr).
\]

An absolute coefficient in front of the unscaled \(H^1(B_r)\) norm
would not express this estimate uniformly over all radii. The general
bounded-Lipschitz-domain extension theorem is not required by this
ball-only input (`ext:sobolev-ball`).

The time-integrated estimate also uses a ball \(U=B_r(x_0)\), with
\(r>0\), and a time interval \(J\), which need not be bounded. For
\(g\in L^\infty(J;L^2(U))\cap L^2(J;H^1(U))\), set
\(A=\|g\|_{L^\infty(J;L^2(U))}\). Then \(g\in L^{10/3}(U\times J)\)
and an absolute constant gives

\[
 \|g\|_{L^{10/3}(U\times J)}^{10/3}
 \le C\left(A^{4/3}\|\nabla g\|_{L^2(U\times J)}^2
                   +r^{-2}A^{10/3}|J|\right).
\]

Membership is a separate conclusion even when \(J\) is unbounded and
the displayed upper bound is infinite. An arbitrary bounded open set
cannot replace the ball without additional hypotheses: disconnected
components of arbitrarily small volume can defeat the proposed embedding.
This restriction of the local clauses does not identify them with the
separate whole-space Sobolev statements.

The proof uses the internally established parabolic Campanato result
`lem:campanato`. The one-sided cylinder characterization `ext:campanato`
is retained only for comparison with another proof route, and is not an
assumed theorem of the present route. The same distinction applies to
`ext:aubin-lions`: the main proof does not consume that compactness result.
If a different proof needs either statement, it must supply it with its
actual hypotheses and conclusions. Exclusion from a proof is neither a
proof nor a refutation of the excluded theorem.

## Metrics, potentials, and covering conventions

The parabolic distance is
\(d((x,t),(y,s))=\max\{|x-y|,|t-s|^{1/2}\}\). Some intermediate kernels
use \(\rho=|x-y|+|t-s|^{1/2}\). Since \(d\le\rho\le2d\), potentials
of order \(0<a<5\) satisfy

\[
 I_{\rho,a}(|g|)\le I_{d,a}(|g|)
           \le 2^{5-a}I_{\rho,a}(|g|).
\]

These are comparison inequalities, not equality of definitions
(`eq:riesz-potential`). The coefficient is carried through estimates or
absorbed into a constant with the same permitted dependencies.

### Mathlib's parabolic Hausdorff measure

Theorem C uses Mathlib's Hausdorff measure for the parabolic metric.
The paper's spherical radius gauge and the diameter gauge have comparable
measures and the same null sets (`def:parabolic-hausdorff` and
`eq:gauge-comparison`). Literal equality of the two measures is unnecessary.
`CKN.parabolic_spherical_hausdorff_comparison` in
`CKN/Covering/SphericalGaugeFull.lean` proves the two-sided factor 2^α
comparison for all α≥0; it is included by `CKN.lean` outside the main theorem
import closure. Ball and cylinder covers are at most countable and may be finite or empty.
Only selected radii must be positive; zero-radius padding is not used.
At dimension zero a nonempty covering ball has cost one, while the empty
cover has cost zero. These conventions preserve the empty-set and
zero-dimensional cases as well as `thm:C`.

## Faithful statements and theorem dependencies

Many declarations state a step of the manuscript in its printed form, with
the representation conventions described here. Such a result is proved in
the same library, but its proof may or may not lie on the dependency path of
the three main theorems. A statement is read together with its supporting
declarations, with their actual hypotheses, constants and conclusions.

Names containing `Faithful` or `Display` commonly identify modules or
declarations that present a manuscript statement or displayed estimate in
the form used in the manuscript. Such a result may assemble, specialize or reformulate
lemmas used by the main proof, or supply a separately proved result not used
there. These names are descriptive, not a mechanical guarantee of mathematical
faithfulness or a rule about dependency membership. In particular, a result
outside the main theorems' import closure is not thereby unproved; conversely,
membership in that closure does not show that its declaration is used by a
main theorem's proof term.

The main theorems' own proofs are checked by compilation, the axiom checks
and the comparator proof bridges, as described in
[Verification](VERIFICATION.md); comparison with the manuscript still
requires mathematical review.

## Constants, statement stability, and authorship

Constants are chosen in the order stated by each theorem. An absolute
constant is independent of the solution, the centre and scale, and all
other quantified data; a constant permitted to depend on \(q\) is chosen
after \(q\) and before the solution. Uniform estimates over a cutoff family
use common coefficient bounds fixed before choosing an individual cutoff.
The library also states the absolute choices explicitly:
`CKN.thmA_morrey_absolute`, `CKN.theoremA_initial_morrey_absolute`,
`CKN.thetaDecay_T_of_sws_absolute`, `CKN.iteration_of_sws_absolute`, and
`CKN.morreyDecay_of_sws_absolute` quantify the relevant constants before q.
These results are included by `CKN.lean` outside the main theorem import
closure; the main proofs use weaker constant-dependence statements sufficient
for their conclusions.

The iteration fixes its contraction and related parameters, including
\(\varepsilon=2/5\), as specified mathematical definitions
(`conv:kappa` and `conv:step-params`). A decay estimate proved at that
contraction is sufficient for the iteration; it does not automatically
establish a statement uniform over every contraction. The quantitative
final Hölder estimate preserves its explicit norm bound, not just existence of some
Hölder representative.

The stable statement boundary includes the main theorems and the
definitions that give their notation meaning: solution and regularity
predicates, scale quantities, metrics, averages, weak derivatives and
Morrey norms. Compilation and
the comparator checks verify their Lean statements and proofs. A change to a defining object must be reviewed as a
possible mathematical change; adding an unrelated theorem to the same
file is different from altering that object's definition. This
separation permits additive library development and documented revisions
without silently changing the meaning of a theorem.

Lean source files credit both authors with the first line
`-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.` and retain the
Apache 2.0 license notice. Updating a copyright comment changes source
bytes but not the elaborated theorem types. Authorship metadata and
mathematical statement identity are therefore checked separately.
