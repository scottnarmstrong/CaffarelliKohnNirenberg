#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
# Released under Apache 2.0 license.
"""Check the Challenge/Solution source agreement and Lean axiom dependencies.

For upstream Comparator and independent NanoDa replay, also run
scripts/verify_comparator.sh. This local check does not replace that replay.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from check_axioms import strip_comments

ROOT = Path(__file__).resolve().parents[1]
NAMES = ('epsilonRegularityL3', 'epsilonRegularityGradient', 'caffarelliKohnNirenberg')
AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def normalized(text: str) -> str:
    return ' '.join(strip_comments(text).split())


def statement(text: str, name: str) -> str:
    start = text.index(f'theorem {name} ')
    return text[start:text.index(':=', start)].strip()


def check_sources() -> None:
    config = json.loads((ROOT / 'comparator.json').read_text())
    require(config == {
        'challenge_module': 'comparators.Challenge',
        'solution_module': 'comparators.Solution',
        'theorem_names': ['CKNChallenge.' + name for name in NAMES],
        'definition_names': [], 'permitted_axioms': AXIOMS, 'enable_nanoda': True,
    }, 'Comparator configuration does not select the three main theorems')
    challenge = (ROOT / 'comparators/Challenge.lean').read_text()
    solution = (ROOT / 'comparators/Solution.lean').read_text()
    require(len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100 * 1024,
            'Challenge exceeds the 1000-line or 100-KiB limit')
    require(len(re.findall(r'\bsorry\b', strip_comments(challenge))) == 3,
            'Challenge must have exactly three intentional proof placeholders')
    require(not re.search(r'\b(?:sorry|admit|axiom|constant)\b', strip_comments(solution)),
            'Solution contains a placeholder or axiom declaration')
    for text, label in [(challenge, 'Challenge'), (solution, 'Solution')]:
        require(re.findall(r'^namespace (\S+)', text, re.M) == ['CKNChallenge'],
                f'{label} must use the common CKNChallenge namespace')
        require(not re.search(r'^\s*private\b', strip_comments(text), re.M),
                f'{label} has private declaration names')
        require(all(option == 'autoImplicit false' for option in
                    re.findall(r'^set_option (.+)$', text, re.M)),
                f'{label} sets an unexpected Lean option')
    imports = re.findall(r'^import (\S+)', challenge, re.M)
    require(imports and all(name.startswith('Mathlib.') for name in imports),
            'Challenge must import only Mathlib modules')
    extra_imports = re.findall(r'^import (\S+)', solution, re.M)
    require(extra_imports == [f'CKN.Statements.Theorem{x}' for x in 'ABC'] + imports,
            'Solution must import the library theorems and Mathlib, never the Challenge')
    # Check all definitions, instance choices and theorem types; the only code
    # differences allowed are the three library imports and three proof terms.
    expected = re.sub(r'^import .+\n', '', challenge, flags=re.M)
    for letter, name in zip('ABC', NAMES):
        library = (ROOT / f'CKN/Statements/Theorem{letter}.lean').read_text()
        require(statement(challenge, name) == statement(library, name),
                f'Theorem {letter} differs from the library statement')
        require(statement(solution, name) == statement(library, name),
                f'Solution {letter} differs from the library statement')
        expected = expected.replace('by sorry', f'CKN.{name} q hq', 1)
    require(normalized(expected) == normalized(re.sub(r'^import .+\n', '', solution, flags=re.M)),
            'Challenge/Solution definitions or proofs differ from the expected correspondence')
    print(f'Source comparison passed ({len(challenge.splitlines())} Challenge lines).')


def lean(path: Path, *args: str) -> str:
    proc = subprocess.run([str(ROOT / 'scripts/lean_direct.sh'), str(path),
                           '-DautoImplicit=false', *args], cwd=ROOT,
                          capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    require(proc.returncode == 0, output or f'Lean failed for {path}')
    return output


def check_proofs() -> None:
    with tempfile.TemporaryDirectory(prefix='ckn-comparator-') as tmp:
        staging = Path(tmp)
        module_dir = staging / 'comparators'
        module_dir.mkdir()
        challenge = ROOT / 'comparators/Challenge.lean'
        solution = ROOT / 'comparators/Solution.lean'
        diagnostics = lean(challenge).splitlines()
        require(len(diagnostics) == 3 and all(
            'warning: declaration uses `sorry`' in line for line in diagnostics),
            f'Unexpected Challenge diagnostics: {diagnostics}')
        diagnostics = lean(solution, '-DwarningAsError=true',
                           '-o', str(module_dir / 'Solution.olean'))
        require(not diagnostics.strip(), f'Unexpected Solution diagnostics: {diagnostics}')
        probe = staging / 'Axioms.lean'
        probe.write_text('import comparators.Solution\n' + ''.join(
            f'#print axioms CKNChallenge.{name}\n' for name in NAMES))
        old = os.environ.get('CKN_EXTRA_LEAN_PATH')
        os.environ['CKN_EXTRA_LEAN_PATH'] = str(staging)
        try:
            output = lean(probe, '-DwarningAsError=true').splitlines()
        finally:
            if old is None:
                del os.environ['CKN_EXTRA_LEAN_PATH']
            else:
                os.environ['CKN_EXTRA_LEAN_PATH'] = old
        expected = [f"'CKNChallenge.{name}' depends on axioms: "
                    '[propext, Classical.choice, Quot.sound]' for name in NAMES]
        require(output == expected, f'Unexpected solution axioms: {output}')
        print('All three Solution declarations have exactly the standard axioms.')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-build', action='store_true', help='source checks only')
    parser.add_argument('--lake', action='store_true', help='also build the Comparators target')
    args = parser.parse_args()
    try:
        check_sources()
        if not args.no_build:
            if args.lake:
                subprocess.run(['python3', 'scripts/build.py', 'Comparators'], cwd=ROOT, check=True)
            check_proofs()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f'Comparator check failed: {error}')
        return 1
    print('All local comparator checks passed.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
