# Caffarelli–Kohn–Nirenberg partial regularity, formalized in Lean 4

[![Build and verify](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/actions/workflows/comparators.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/actions/workflows/comparators.yml)

A complete, machine-checked proof of the Caffarelli–Kohn–Nirenberg theorem:
for suitable weak solutions of the three-dimensional incompressible
Navier–Stokes equations, the set of singular space-time points has zero
one-dimensional parabolic Hausdorff measure. The formalization is written in
Lean 4 on top of Mathlib and covers the whole argument, from the definition
of a suitable weak solution to the final covering argument. The library uses
no axioms beyond Lean's standard three and contains no unfinished proofs.

The forcing term is allowed to lie in $L^q_{\mathrm{loc}}$ for any $q > 5/2$
and need not be divergence free. The proof keeps the direct scale iteration
of Caffarelli, Kohn and Nirenberg in the form organised by Kukavica, and
closes it with a Morrey-space bootstrap and potential estimates in the manner
of O'Leary and Lemarié-Rieusset; Lin's work supplies the pressure estimates.
It is written out in full in the accompanying [manuscript](paper/ckn.pdf).
The manuscript and the Lean development were produced together: the three
main theorems are stated in Lean with the manuscript's hypotheses and
conclusions.

## What is proved

Space is $\mathbb{R}^3$ and time is $\mathbb{R}$. A suitable weak solution
$(u,p)$ on an open product domain $\Omega\times I$ has locally finite energy, pressure locally in
$L^{3/2}$, satisfies the momentum equation and incompressibility weakly, and
satisfies the local energy inequality. $Q_r(x,t)$ is the past parabolic
cylinder $B_r(x)\times(t-r^2,t]$. A point is regular if $u$ agrees almost
everywhere with a parabolically Hölder-continuous function on a
neighbourhood. In every statement the constants are chosen after $q$ and
before the solution.

**Theorem A, small-data regularity** (Theorem 2.7 of the manuscript).
For each $q>5/2$ there are $\varepsilon_0>0$, an exponent
$0<\gamma_0\le 2/3$ and a constant $C_4$ such that every suitable weak
solution defined on a neighbourhood of the closed unit cylinder with

$$\iint_{Q_1}\bigl(|u|^3+|p|^{3/2}+|f|^q\bigr)\le\varepsilon_0$$

coincides almost everywhere on $Q_{1/2}$ with a function whose parabolic
Hölder norm of exponent $\gamma_0$ on the closed half-cylinder is at most
$C_4$, and every point of the open interior of $Q_{1/2}$ is regular.

**Theorem B, gradient regularity** (Theorem 2.9).
For each $q>5/2$ there is $\varepsilon_1>0$ such that an interior point
$z_0$ of a suitable weak solution is regular whenever

$$\limsup_{r\downarrow 0}\ \frac1r\iint_{Q_r(z_0)}|\nabla u|^2<\varepsilon_1^2 .$$

**Theorem C, partial regularity** (Theorem 2.10).
For every suitable weak solution with force in $L^q_{\mathrm{loc}}$,
$q>5/2$, the singular set has zero one-dimensional parabolic Hausdorff
measure.

Theorem C is a modern formulation of the Caffarelli–Kohn–Nirenberg theorem. The solution class uses the local pressure hypothesis $p\in L^{3/2}$ of
Lin and Ladyzhenskaya–Seregin. It is deduced from Theorem B by a covering argument. Theorems A and B are proved side by
side in the manuscript's $\varepsilon$-regularity section; B is not deduced
from A.

## The Lean statements

The three theorems are stated in [CKN/Statements](CKN/Statements) exactly as below.
`Vec3` is `Fin 3 → ℝ`, a `ParabolicPoint` is a pair of a point and a time,
and `IsSuitableWeakSolution Ω I q u Du p f` is the suitable-solution
predicate on the domain $\Omega\times I$, carrying an explicit weak
spatial gradient `Du` of `u`. It expresses the manuscript's definition, with the representation choices
described below:
the regularity conditions, the divergence-free and momentum identities and
the local energy inequality, with no integrability side condition on the
integrands they test. The library also carries a variant
`IsSuitableWeakSolutionIntegrable` that states those side conditions explicitly; the
two classes have the same inhabitants, and
`CKN.isSuitableWeakSolution_iff_integrable` proves it. The statements and their key definitions are in [CKN/Statements](CKN/Statements)
and [CKN/Foundation](CKN/Foundation). The
[design notes](docs/DESIGN_NOTES.md) explain the choices behind them.

Theorem A, [`CKN.epsilonRegularityL3`](CKN/Statements/TheoremA.lean):

```lean
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
            IsRegularPoint Ω I u z
```

Theorem B, [`CKN.epsilonRegularityGradient`](CKN/Statements/TheoremB.lean):

```lean
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
          IsRegularPoint Ω I u z₀
```

Theorem C, [`CKN.caffarelliKohnNirenberg`](CKN/Statements/TheoremC.lean):

```lean
theorem caffarelliKohnNirenberg (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolution Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0
```

The Hausdorff measure in Theorem C is defined with the parabolic diameter
gauge. The manuscript uses a radius gauge; the two have the same null sets,
which is all the theorem asserts.

Because a formal statement is only as good as the definitions inside it,
the repository also contains a standalone [Challenge](comparators/Challenge.lean)
that defines the objects using Mathlib alone and states all three theorems.
The separate [Solution](comparators/Solution.lean) proves the same named
declarations from the library. [Comparator](comparators/README.md) checks
their statement dependency closures and proofs, including an independent
NanoDa kernel replay. Reading the Challenge is the quickest way to inspect
the precise mathematical claims.

## How the formalization relates to the manuscript

The manuscript is the paper being formalized, not a description written
after the fact, and it was corrected as the formalization progressed. The three main theorems are proved as stated. Supporting results follow
the proof route described in the manuscript; unused alternative arguments
and auxiliary exposition without a Lean counterpart are identified in the documentation. Some auxiliary quantitative estimates are proved only in the special cases
used by the main proofs, including two fixed-centre parameter triples and
an affine rather than linear bound; entries
B58 to B62 of [docs/DEVIATIONS.md](docs/DEVIATIONS.md) list each one. Where the
formalization led us to change a statement or a proof, the
[deviations](docs/DEVIATIONS.md) document explains what changed and why, with the current scope stated explicitly.

The formalization includes a concrete nonzero suitable weak solution, the
viscous shear flow $u(x,t)=(e^{-t}\sin x_2,0,0)$ with zero pressure and
force, so that the solution class is known to be inhabited and the theorems
are not vacuous. The [witnesses](docs/WITNESSES.md) page lists what has been
checked in this direction.

## Building and checking it yourself

The project pins Lean 4 and Mathlib at v4.35.0-rc2. With `elan` and Python 3
installed:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
python3 scripts/build.py CKN
```

The library contains about 250,000 lines of Lean. Build time depends on the
machine and availability of the Mathlib cache. Keep the committed dependency
manifest; avoid `lake update` or `lake clean` when verifying this version.

To confirm the axioms used by the three main theorems, or to run the
source and comparator checks, follow the
[verification guide](docs/VERIFICATION.md). Each main theorem depends
exactly on `propext`, `Classical.choice` and `Quot.sound`.

## Repository layout

- [CKN/Statements](CKN/Statements): the main theorem statements and definitions of suitable weak solutions, regular and singular points, and scale-invariant quantities.
- [CKN/Foundation](CKN/Foundation): parabolic geometry, Sobolev spaces, weak derivatives, mollification, harmonic and heat-kernel estimates, Morrey and Campanato norms.
- [CKN/Setting](CKN/Setting): basic consequences of the suitable-solution definition (energy slices, cut-offs, interpolation on cylinders) and the shear-flow example.
- [CKN/Pressure](CKN/Pressure): the pressure theory: potentials, decompositions and the pressure-gradient estimates.
- [CKN/Core](CKN/Core): the proof itself, organised by the steps of the manuscript.
- [CKN/Covering](CKN/Covering): the parabolic Vitali covering and Hausdorff-measure argument of Theorem C.
- [CKN/Witnesses](CKN/Witnesses): explicit examples showing the definitions are inhabited.
- [CKN/ClassEquivalence](CKN/ClassEquivalence): the proof that the integrability conditions carried by the suitable-solution class follow from its energy conditions, so that the Lean class is the manuscript's.
- [CKN/Main](CKN/Main): the assembly of the three theorems from the core results.
- [comparators](comparators): the independent restatements described above.
- [paper](paper): the manuscript source and PDF.
- [docs](docs): design notes, deviations, witnesses, verification guide, and the [bibliography](docs/SOURCES.md).
- [scripts](scripts): the guarded build, checking, comparison, and release-verification tools.

## How this was made

The Lean development was written in roughly 48 hours using AI coding agents
under the authors' supervision. Claude Fable 5.1 coordinated agents using
GPT 5.6-Luna, GPT Astra, Deepseek 4.1 flash, Leanstral and Opus 5. The authors
reviewed the theorem statements before proof development and decided the
mathematics and the corrections to the manuscript. Separate reviews checked
the statements and the use of intermediate results in the main proofs.
Lean checks the proofs; the comparator files make their mathematical
statements available for independent inspection.

## Contributing, authors and license

See [Contributing](CONTRIBUTING.md) for the source rules and checks, and
[CITATION.cff](CITATION.cff) for how to cite this work.

The Lean development is by:

- **Scott Armstrong**, CNRS and Laboratoire Jacques-Louis Lions, Sorbonne
  Université; Courant Institute School of Mathematics, Computing, and Data Science, New York University.
  Supported by the European Research Council under the European Union's
  Horizon Europe programme, grant agreement No. 101200828.
- **Vlad Vicol**, Courant Institute School of Mathematics, Computing, and Data Science, New York University. Partially supported by Collaborative NSF
  grant DMS-2307681 and a Simons Investigator Award.

The Lean library, software, documentation and included manuscript are
copyright © 2026 Scott Armstrong and Vlad Vicol and distributed under the
[Apache License 2.0](LICENSE). Cited third-party works and dependencies retain
their own licenses.
