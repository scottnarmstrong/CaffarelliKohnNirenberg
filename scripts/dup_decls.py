#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
# Released under Apache 2.0 license.
"""Find duplicate non-private Lean declaration names.

The source lexer is shared with ``check_axioms.py`` so one-line namespace
openings and masked comments/strings are handled consistently.  This checker
does not elaborate Lean: it is a cheap source-level guard against a duplicate
qualified name that can be hidden by a stale olean in a per-file build.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import subprocess
import sys


SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import check_axioms  # noqa: E402


@dataclass(frozen=True)
class DeclarationLocation:
    name: str
    path: str
    line: int


@dataclass(frozen=True)
class Duplicate:
    name: str
    first: DeclarationLocation
    second: DeclarationLocation


def tracked_lean_files(root: Path) -> list[Path]:
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--", "*.lean"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        values = result.stdout.splitlines()
    else:
        # git archive checkouts intentionally have no .git directory.  Every
        # Lean file in such a tree is part of the archived source universe.
        values = [
            path.relative_to(root).as_posix()
            for path in root.rglob("*.lean")
            if path.is_file() and ".git" not in path.parts and ".lake" not in path.parts
        ]
    return [
        (root / value).resolve()
        for value in values
        if value.endswith(".lean") and (root / value).is_file()
    ]


def relative_path(root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return str(path.resolve())


def top_level_declarations(root: Path, path: Path) -> list[DeclarationLocation]:
    """Return declarations whose command starts at the Lean top level.

    A tactic-local ``def`` or a local binder must never become a purported
    module declaration.  Lean's project files put namespace-level declarations
    at column zero, including declarations inside an already-open namespace,
    so require that shape here while using check_axioms' comment/string mask
    and namespace lexer.
    """
    masked = check_axioms.code_mask(path.read_text(encoding="utf-8"))
    namespaces: list[str] = []
    blocks: list[tuple[str, int]] = []
    result: list[DeclarationLocation] = []
    for line_number, line in enumerate(masked.splitlines(), start=1):
        events: list[tuple[int, str, object]] = []
        events.extend((match.start(), "namespace", match) for match in check_axioms.NAMESPACE.finditer(line))
        events.extend((match.start(), "section", match) for match in check_axioms.SECTION.finditer(line))
        if line == line.lstrip():
            end = check_axioms.END.match(line)
            if end is not None:
                events.append((end.start(), "end", end))
            declaration = check_axioms.DECL.match(line)
            if declaration is not None:
                events.append((declaration.start(), "declaration", declaration))
        for _position, kind, match in sorted(events, key=lambda item: item[0]):
            if kind == "namespace":
                parts = match.group(1).split(".")
                namespaces.extend(parts)
                blocks.append(("namespace", len(parts)))
            elif kind == "section":
                blocks.append(("section", 0))
            elif kind == "end":
                if blocks:
                    block, count = blocks.pop()
                    if block == "namespace" and count:
                        del namespaces[-count:]
            else:
                modifier, _declaration_kind, name = match.groups()
                if modifier not in {"private", "local"} and name is not None:
                    qualified = ".".join([*namespaces, *name.split(".")])
                    result.append(
                        DeclarationLocation(
                            qualified,
                            relative_path(root, path),
                            line_number,
                        )
                    )
    return result


def selected_files(root: Path, given: list[Path] | None = None) -> list[Path]:
    values = tracked_lean_files(root) if given is None else [*tracked_lean_files(root), *given]
    result: list[Path] = []
    seen: set[Path] = set()
    for value in values:
        path = value.resolve()
        if path.suffix != ".lean" or not path.is_file() or path in seen:
            continue
        seen.add(path)
        result.append(path)
    return sorted(result, key=lambda path: relative_path(root, path))


def find_duplicates(root: Path, given: list[Path] | None = None) -> list[Duplicate]:
    locations: dict[str, list[DeclarationLocation]] = {}
    for path in selected_files(root, given):
        for location in top_level_declarations(root, path):
            locations.setdefault(location.name, []).append(location)
    duplicates: list[Duplicate] = []
    for name, values in locations.items():
        for first, second in combinations(values, 2):
            # Comparator requires identical names in two separate environments.
            # This exact pair is never imported together; duplicates within
            # either file or involving any library file remain errors.
            if name.startswith("CKNChallenge.") and {first.path, second.path} == {
                "comparators/Challenge.lean", "comparators/Solution.lean"
            }:
                continue
            duplicates.append(Duplicate(name, first, second))
    return sorted(
        duplicates,
        key=lambda duplicate: (
            duplicate.name,
            duplicate.first.path,
            duplicate.first.line,
            duplicate.second.path,
            duplicate.second.line,
        ),
    )


def format_duplicate(duplicate: Duplicate) -> str:
    return (
        f"{duplicate.name}: {duplicate.first.path}:{duplicate.first.line} "
        f"<-> {duplicate.second.path}:{duplicate.second.line}"
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", type=Path, metavar="LEAN_FILE")
    parser.add_argument("--root", type=Path, default=SCRIPTS.parent)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    given: list[Path] | None = None
    if args.files:
        given = []
        for value in args.files:
            path = value if value.is_absolute() else root / value
            if path.suffix != ".lean" or not path.is_file():
                print(f"dup_decls: missing Lean file {value}", file=sys.stderr)
                return 2
            given.append(path)
    duplicates = find_duplicates(root, given)
    count = len(selected_files(root, given))
    if duplicates:
        print(f"DUP-DECLS FAIL: {len(duplicates)} duplicate declaration pair(s) in {count} file(s)")
        for duplicate in duplicates:
            print(f"- {format_duplicate(duplicate)}")
        return 1
    print(f"DUP-DECLS PASS: checked {count} Lean file(s), no duplicate non-private declarations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
