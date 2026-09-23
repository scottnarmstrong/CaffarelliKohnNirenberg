# Independent statements and proof comparison

[Challenge.lean](Challenge.lean) states Theorems A, B and C using only Mathlib
imports. It includes the definitions of suitable weak solutions, parabolic
geometry, Hölder regularity and the singular set, followed by three intentional
proof placeholders. A mathematical reader can compare it with the manuscript
without reading the proof library.

[Solution.lean](Solution.lean) defines the same objects and proves the same
named theorems from the library's results. The public statement layer uses
Mathlib's Euclidean spaces, continuous-linear-map weak derivatives and
ordinary product coordinates; the proof supplies the exact coordinate and
measure transports to the library's older componentwise presentation. It does
not import the Challenge. These are separate Lean environments: importing both
modules into one file would introduce duplicate declarations.

| Declaration in both environments | Library theorem |
|---|---|
| `CKNChallenge.epsilonRegularityL3` | `CKN.epsilonRegularityL3` |
| `CKNChallenge.epsilonRegularityGradient` | `CKN.epsilonRegularityGradient` |
| `CKNChallenge.caffarelliKohnNirenberg` | `CKN.caffarelliKohnNirenberg` |

The [configuration](../comparator.json) selects all three declarations for one
Palomar submission. The Challenge is below the 1,000-line and 100-KiB limits.

## Local checks

After building the library, run:

```sh
python3 scripts/check_comparators.py
```

This compares the full public definition source, theorem types and instance
choices shared by the Challenge and Solution. The Solution additionally
contains the coordinate-transport lemmas used by its proofs. The checker
requires three intentional Challenge warnings, a clean Solution elaboration
with warnings treated as errors, and exactly
`[propext, Classical.choice, Quot.sound]` as the axiom set of each solution.
Temporary compiled Solution files take precedence over existing build
artifacts when inspecting those axioms.

`--no-build` performs source checks only. `--lake` additionally builds the
`Comparators` target. The ordinary `lake build` target builds the CKN library.

## Upstream Comparator and NanoDa

```sh
lake exe cache get
scripts/verify_comparator.sh
```

The script builds pinned revisions of
[Comparator](https://github.com/leanprover/comparator),
[lean4export](https://github.com/leanprover/lean4export),
[NanoDa](https://github.com/robsimmons/nanoda_lib) and
[Landrun](https://github.com/zouuup/landrun), then runs `comparator.json`.
Their commit pins are recorded in the script. This requires Linux with
Landlock support, Go 1.24 or later, Rust/Cargo, Git, Python 3 and the project's
Lean toolchain. Tools are stored under `${XDG_CACHE_HOME:-$HOME/.cache}/ckn-comparator`;
set `CKN_COMPARATOR_CACHE` to use a different directory.

Comparator checks the exported statement dependency closures, allowed axioms
and proofs. NanoDa independently replays the exported Solution in a second
kernel. The local source checker complements this by checking that the cleaned
public layer is literally shared between Challenge and Solution. Neither check
establishes that the definitions express the intended mathematics; that
requires review against the manuscript.

A local run does not reproduce Palomar's entire hosted intake process, which
also checks the pinned public snapshot, dependency provenance, metadata,
licensing and editorial criteria. See the current
[submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
