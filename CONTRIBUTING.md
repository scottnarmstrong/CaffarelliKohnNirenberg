# Contributing

This repository formalizes the Caffarelli–Kohn–Nirenberg partial regularity
theorem in Lean 4 and Mathlib. The main theorem statements are in
[CKN/Statements](CKN/Statements).

## Development environment

Install the pinned toolchain and obtain the Mathlib cache:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
```

Keep the committed `lake-manifest.json`. Avoid `lake update` and `lake clean`
when verifying this version: they can change dependencies or remove the cache.
The build scripts check the toolchain, dependency revision and package files.

## Lean source conventions

Every Lean file begins with:

```lean
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
```

Use `set_option autoImplicit false`. Library code must contain no `sorry`,
`admit`, `sorryAx`, or custom axiom declarations. The only exceptions are the
three deliberately unproved comparator Challenge statements, whose separate
Solution files provide the proofs.

Do not add heartbeat overrides or use bare `linarith` or `nlinarith`; use
explicit `only` arguments. Lean files must remain at most 1,500 lines.
The library builds with warnings treated as errors.

## Building and checking changes

From the repository root:

```sh
python3 scripts/build.py CKN
python3 scripts/build_all.py
python3 scripts/build.py Comparators
python3 scripts/check_comparators.py
python3 scripts/check_public.py
python3 scripts/check_axioms.py
```

The main build runs the source-rule and duplicate-declaration checks.
`build_all.py` additionally builds every tracked library module, including
auxiliary results and examples. Add new modules to Git before using that
command. The [verification guide](docs/VERIFICATION.md) explains each check.

For a focused check after building the file's imports:

```sh
scripts/lean_direct.sh CKN/Statements/TheoremA.lean \
  -DautoImplicit=false -DwarningAsError=true
```

Changes to the main statements or their definitions need mathematical review
against the manuscript. Update the [comparator definitions](comparators/README.md) together with any
changed library definitions and rerun both the local checks and upstream
Comparator.

## Submitting a change

Describe the mathematical or implementation change and include the relevant
build and checker results. For a new public theorem, include its `#print axioms`
output. Keep generated build files and temporary probes out of the commit.
