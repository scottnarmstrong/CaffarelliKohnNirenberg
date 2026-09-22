# Examples and satisfiability witnesses

The formalization includes explicit examples alongside its general theorems.
They show that the suitable weak-solution class and other mathematical
interfaces admit the data they are intended to describe. The main collection
is [CKN/Witnesses](../CKN/Witnesses); a nonzero suitable weak solution is
constructed in [CKN/Setting/Examples](../CKN/Setting/Examples).

A satisfiability theorem has a precise, limited purpose. A result of the form
`∃ data, P data` shows that the predicate `P` is inhabited. It does not prove
a general analytic estimate for every datum satisfying `P`, nor does it show
that every additional hypothesis of a later theorem can be satisfied
simultaneously. Those are separate assertions. The statement of each witness,
rather than its name, determines what it establishes.

## A nonzero suitable weak solution

In ordinary spatial coordinates, consider the decaying shear flow

\[
 u(x,t)=(e^{-t}\sin x_2,0,0),\qquad p(x,t)=0,\qquad f(x,t)=0.
\]

It is a suitable weak solution on \(\mathbb R^3\times(0,1)\) with force
exponent \(q=3\). The velocity is smooth, divergence free, and satisfies
\(u\cdot\nabla u=0\) and \(\partial_tu=\Delta u\). Its only nonzero
spatial-gradient component is \(\partial_2u_1=e^{-t}\cos x_2\).
The construction proves the local integrability, weak-gradient, weak
momentum, and local energy conditions of `IsSuitableWeakSolution`.
The local energy identity implies the required inequality.

The relevant declarations are:

- [`shearFlow` and `shearFlowGrad`](../CKN/Setting/Examples/ShearFlow.lean),
  the velocity and its explicit gradient. Lean indexes coordinates by
  `Fin 3`, so its indices `0` and `1` are the first and second coordinates
  in the displayed formula.
- [`isSuitableWeakSolutionIntegrable_shearFlow`](../CKN/Setting/Examples/ShearFlowSuitable.lean),
  which proves suitability on `Set.univ ×ˢ Ioo 0 1` at exponent `3`.
- [`shearFlow_ne_zero`](../CKN/Setting/Examples/ShearFlow.lean), which proves
  nonvanishing at a point strictly inside the time interval. The explicit
  point is \(((0,\pi/2,0),1/2)\), where the first component is \(e^{-1/2}\).
- [`shearFlow_energyIdentity`](../CKN/Setting/Examples/ShearFlowEnergy.lean),
  the identity against compact smooth scalar tests used in the suitability
  proof.

This example is nonzero on a nonempty spacetime domain. It need not have
finite energy on all of \(\mathbb R^3\): the solution class is local, with
finiteness required on compactly interior spatial and temporal regions.
The example demonstrates nontriviality of that class; it is not a separate
claim about every quantitative smallness hypothesis in the regularity
theorems.

## Zero solutions and basic interfaces

[`isSuitableWeakSolutionIntegrable_zero`](../CKN/Witnesses/TrivialSolution.lean)
proves that \(u=Du=p=f=0\) satisfies the solution definition on any open
spatial domain and open time interval, for every \(q>5/2\). In particular,
it applies on nonempty domains. All weak identities and the energy
inequality are proved with the required integrability, rather than obtained
from undefined integrals.

Other examples exercise particular definitions:

- [Campanato witnesses](../CKN/Witnesses/InterfaceWitnessesCampanato.lean)
  use zero functions to satisfy local and global oscillation bounds and
  local integrability conditions on parabolic balls or cylinders. These
  instantiate the displayed predicates; their chosen parameters are not
  automatically the full parameter hypotheses of a Hölder theorem.
- [Basic analytic witnesses](../CKN/Witnesses/InterfaceWitnessesFoundation.lean)
  instantiate slice divergence freedom, local Lebesgue integrability,
  gradient integrability, and a dyadic level-set condition.
- [A dyadic cube witness](../CKN/Witnesses/DyadicCubeWitness.lean)
  supplies an instance of the cube-membership predicate.

Some declarations with names ending in `_satisfiable` have stronger types
than an existential example. For instance,
[`routeA_gradient_producer_satisfiable`](../CKN/Witnesses/RouteAGradientProducer.lean)
proves the quantified pressure-gradient statement by applying a uniform
construction to arbitrary admissible data. It is not a zero-solution substitute
for that universal assertion.

## A nonzero multiplier example

[RepresentationWitnesses.lean](../CKN/Witnesses/RepresentationWitnesses.lean)
uses the concrete pressure multiplier

\[
 \sigma_{jlm}(\xi)=\mathrm{i}\,\frac{\xi_m\xi_j\xi_l}{|\xi|^2}.
\]

`IsDegreeOneHomogeneous_satisfiable` proves its degree-one homogeneity.
`pressureMultiplierSymbol_apply_one` gives its value \(\mathrm{i}/3\)
at \(\xi=(1,1,1)\), and `pressureMultiplierSymbol_ne_zero` proves that
it is not the zero symbol. The same module establishes a linear growth
bound and absolute integrability of its Gaussian-damped frequency
integrand for positive time.

The sign here is the sign of the implemented symbol. With the original
manuscript's convention \(T_{jl}=-\nabla\partial_j\partial_l\Delta^{-1}\), it is a
component of the symbol of \(-T_{jl}\). Nontriviality and homogeneity do
not depend on that sign, but operator identifications do. The current
manuscript no longer uses that pressure-commutator representation; this
symbol remains a nonzero example for the general multiplier definitions.

## Counterexamples and preservation

The collection also records negative facts that help delimit valid
hypotheses. For example,
[`not_integrable_time_singular`](../CKN/Witnesses/NonIntegrableBox.lean)
proves that \((t-a)^{-1}\) is not integrable on a positive-radius spatial
ball times \((a,b)\), when \(a<b\). Local integrability away from a
boundary does not imply integrability up to that boundary.

These examples are retained and checked even when the main proofs do not use
them. All 14 modules in `CKN/Witnesses` are imported by `CKN.lean`.
The exact statement of each declaration explains what the example proves;
compilation and axiom checks verify its proof.
