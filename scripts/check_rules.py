#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
# Released under Apache 2.0 license.
"""Check the repository's local Lean source rules."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import dup_decls  # noqa: E402
import prop_interfaces  # noqa: E402
import check_axioms  # noqa: E402


HEADER = (
    "-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.\n"
    "-- Released under Apache 2.0 license."
)


def source_files() -> list[Path]:
    """Lean sources subject to the rules: the root module and every tracked file
    under CKN/. Use --files to check an untracked file before adding it."""
    import subprocess
    files = [ROOT / "CKN.lean"]
    try:
        out = subprocess.run(["git", "ls-files", "CKN"], cwd=ROOT, capture_output=True,
                             text=True, check=True).stdout.split()
        files.extend(ROOT / p for p in sorted(out) if p.endswith(".lean"))
    except Exception:
        files.extend(sorted((ROOT / "CKN").rglob("*.lean")))
    return [path for path in files if path.is_file()]


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def add_match(
    errors: list[str], path: Path, text: str, label: str, match: re.Match[str]
) -> None:
    relative = path.relative_to(ROOT)
    errors.append(f"{relative}:{line_number(text, match.start())}: {label}")


# Files allowed to *mention* `EuclideanSpace`: transport lemmas that import one
# explicit Mathlib constant (the Euclidean ball volume) along `WithLp.toLp 2`.
# The ambient type stays `Fin 3 → ℝ`; nothing may be stated over EuclideanSpace.
EUCLIDEAN_TRANSPORT_ALLOWLIST = {
    "CKN/Foundation/Parabolic/BallDisplays.lean",
    "CKN/Foundation/Harmonic/Commutator/SphereTransport.lean",
}

# `ContDiff ℝ ⊤` / `ContDiff ℝ (⊤ : WithTop ℕ∞)` mean ANALYTIC (ω) in this Mathlib; with
# `HasCompactSupport` that forces the function to vanish, so such hypotheses make
# statements vacuous. Smooth is `ContDiff ℝ (⊤ : ℕ∞)`. The files below keep ω-order
# compatibility wrappers over their `_smooth` versions and may be removed later.
ANALYTIC_ORDER_PATTERN = re.compile(r"ContDiff\s+ℝ\s+(?:⊤(?!\s*:)|\(⊤\s*:\s*WithTop\s+ℕ∞\)|ω\b)")
ANALYTIC_ORDER_ALLOWLIST = {
    "CKN/Foundation/Harmonic/NewtonianRepresentation.lean",
    "CKN/Foundation/Heat/Convolution.lean",
    "CKN/Foundation/Harmonic/Newtonian.lean",
    "CKN/Pressure/LeibnizLaplacian.lean",
    "CKN/Core/Caccioppoli/Admissibility.lean",
}
PROP_INTERFACE_ALLOWLIST = ROOT / "scripts/prop_interface_allowlist.txt"
SET_AUTO_IMPLICIT = re.compile(
    r"\bset_option\s+autoImplicit\s+(?:=\s*)?true\b"
)
LEADING_UNDERSCORE_BINDER = re.compile(r"(?<![\w'])_[\w']+")
BINDER_DELIMITERS = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
NEW_CLAUSE_LIMIT = 10

CLAUSE_AUTO_IMPLICIT = "set_option autoImplicit true in CKN source"
CLAUSE_NO_PUBLIC = "CKN module has no public declaration"
CLAUSE_UNDERSCORE_BINDER = "leading-underscore theorem statement binder"


def _binder_group_header(group: str) -> str:
    stack: list[str] = []
    for index, char in enumerate(group):
        if char in BINDER_DELIMITERS:
            stack.append(BINDER_DELIMITERS[char])
        elif stack and char == stack[-1]:
            stack.pop()
        elif char == ":" and not stack:
            return group[:index]
    return group


def theorem_statement_binder_issues(
    root: Path, path: Path, text: str
) -> list[str]:
    """Find underscore-prefixed names in explicit theorem/lemma binders only."""
    masked = dup_decls.check_axioms.code_mask(text)
    declarations: list[tuple[int, int, str]] = []
    offset = 0
    for line_number, line in enumerate(masked.splitlines(keepends=True), start=1):
        match = dup_decls.check_axioms.DECL.match(line) if not line[:1].isspace() else None
        if match and match.group(2) in {"theorem", "lemma"} and match.group(3):
            declarations.append((offset + match.end(3), line_number, match.group(3)))
        offset += len(line)

    relative = path.resolve().relative_to(root.resolve()).as_posix()
    issues: list[str] = []
    for declaration_index, (start, start_line, declaration_name) in enumerate(declarations):
        limit = (
            declarations[declaration_index + 1][0]
            if declaration_index + 1 < len(declarations)
            else len(masked)
        )
        cursor = start
        while cursor < limit:
            char = masked[cursor]
            if char == ":" and (cursor + 1 >= limit or masked[cursor + 1] != "="):
                break
            if char not in BINDER_DELIMITERS:
                cursor += 1
                continue

            closing = BINDER_DELIMITERS[char]
            stack = [closing]
            group_start = cursor + 1
            end = group_start
            while end < limit and stack:
                nested = masked[end]
                if nested in BINDER_DELIMITERS:
                    stack.append(BINDER_DELIMITERS[nested])
                elif nested == stack[-1]:
                    stack.pop()
                end += 1
            if stack:
                break
            group = masked[group_start:end - 1]
            header = _binder_group_header(group)
            for binder in LEADING_UNDERSCORE_BINDER.finditer(header):
                line = masked.count("\n", 0, group_start + binder.start()) + 1
                issues.append(
                    f"{relative}:{line}: theorem {declaration_name} has "
                    f"leading-underscore binder {binder.group(0)}"
                )
            cursor = end
    return issues


def new_clause_issues(root: Path, files: list[Path]) -> dict[str, list[str]]:
    """Collect the three source rules, preserving every location."""
    found = {
        CLAUSE_AUTO_IMPLICIT: [],
        CLAUSE_NO_PUBLIC: [],
        CLAUSE_UNDERSCORE_BINDER: [],
    }
    for path in files:
        relative = path.resolve().relative_to(root.resolve()).as_posix()
        if relative != "CKN.lean" and not relative.startswith("CKN/"):
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        masked = dup_decls.check_axioms.code_mask(text)
        for match in SET_AUTO_IMPLICIT.finditer(masked):
            line = masked.count("\n", 0, match.start()) + 1
            found[CLAUSE_AUTO_IMPLICIT].append(
                f"{relative}:{line}: set_option autoImplicit true"
            )
        if relative.startswith("CKN/"):
            if not dup_decls.top_level_declarations(root, path):
                found[CLAUSE_NO_PUBLIC].append(
                    f"{relative}: no public top-level declaration"
                )
            found[CLAUSE_UNDERSCORE_BINDER].extend(
                theorem_statement_binder_issues(root, path, text)
            )
    return found


def prop_interface_errors(files: list[Path]) -> list[str]:
    errors: list[str] = []
    for issue in prop_interfaces.policy_issues_for_paths(
        ROOT, files, PROP_INTERFACE_ALLOWLIST
    ):
        declaration = issue.interface.declaration
        errors.append(
            f"{declaration.path}:{declaration.line}: {issue.reason}: "
            f"{declaration.name}; add an instantiated interface to "
            "scripts/prop_interface_allowlist.txt only after review"
        )
    return errors


def check_file(path: Path, errors: list[str]) -> None:
    relative = path.relative_to(ROOT).as_posix()
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        errors.append(f"{relative}: cannot read file: {exc}")
        return

    if not text.startswith(HEADER):
        errors.append(f"{relative}: missing copyright header")
    if len(text.splitlines()) > 1500:
        errors.append(f"{relative}: exceeds 1500 lines")

    match = re.compile(r"\bset_option\s+maxHeartbeats\b").search(text)
    if match:
        add_match(errors, path, text, "set_option maxHeartbeats", match)
    # Preserve source offsets while ignoring comments and string literals.
    code = check_axioms.strip_comments(text)
    match = re.search(r"(?<![\w'])(?:sorry|admit|sorryAx)(?![\w'])", code)
    if match:
        add_match(errors, path, text, "sorry/admit/sorryAx", match)
    for pattern, label in (
        (re.compile(r"\b(?:axiom|constant)\s+"), "axiom/constant declaration"),
        (re.compile(r"\bEuclideanSpace\b"), "EuclideanSpace"),
        (
            re.compile(r"\b(?:linarith|nlinarith)\b(?!\s+only\b)"),
            "bare linarith/nlinarith",
        ),
    ):
        if label == "EuclideanSpace" and relative in EUCLIDEAN_TRANSPORT_ALLOWLIST:
            continue
        match = pattern.search(code if label == "axiom/constant declaration" else text)
        if match:
            add_match(errors, path, text, label, match)
    if relative not in ANALYTIC_ORDER_ALLOWLIST:
        match = ANALYTIC_ORDER_PATTERN.search(text)
        if match:
            add_match(errors, path, text, "analytic-order ContDiff (use (⊤ : ℕ∞))", match)


def selected_files(values: list[str] | None) -> list[Path]:
    if values is None:
        return source_files()
    files: list[Path] = []
    for value in values:
        path = Path(value)
        path = path if path.is_absolute() else ROOT / path
        path = path.resolve()
        if path.suffix != ".lean" or not path.is_file():
            raise SystemExit(f"check_rules: missing Lean file {value}")
        try:
            path.relative_to(ROOT)
        except ValueError as exc:
            raise SystemExit(f"check_rules: file outside repository {value}") from exc
        files.append(path)
    return list(dict.fromkeys(files))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--files",
        nargs="+",
        metavar="LEAN_FILE",
        help="check only these in-repository Lean files; default checks the tracked tree",
    )
    args = parser.parse_args(argv)
    errors: list[str] = []
    files = selected_files(args.files)
    for path in files:
        check_file(path, errors)
    errors.extend(prop_interface_errors(files))
    baseline_findings = (
        new_clause_issues(ROOT, files)
        if args.files is None
        else new_clause_issues(ROOT, source_files())
    )
    selected_findings = (
        baseline_findings
        if args.files is None
        else new_clause_issues(ROOT, files)
    )
    warnings: list[tuple[str, str]] = []
    warning_modes: list[tuple[str, int]] = []
    for clause, findings in selected_findings.items():
        baseline_count = len(baseline_findings[clause])
        if baseline_count > NEW_CLAUSE_LIMIT:
            warning_modes.append((clause, baseline_count))
            warnings.extend((clause, finding) for finding in findings)
        else:
            errors.extend(f"{clause}: {finding}" for finding in findings)
    if args.files is None:
        for duplicate in dup_decls.find_duplicates(ROOT):
            errors.append(f"duplicate declaration: {dup_decls.format_duplicate(duplicate)}")
    for clause, count in warning_modes:
        print(
            f"check_rules: WARNING MODE [{clause}]: {count} existing tree "
            f"violation(s), above the {NEW_CLAUSE_LIMIT}-hit threshold"
        )
    for clause, finding in warnings:
        print(f"check_rules: WARNING [{clause}]: {finding}")
    if errors:
        print("check_rules: FAIL")
        for error in errors:
            print(f"- {error}")
        return 1
    warning_summary = f"; {len(warnings)} warning(s)" if warnings else ""
    print(f"check_rules: PASS ({len(files)} Lean files{warning_summary})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
