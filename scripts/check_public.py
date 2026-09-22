#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
# Released under Apache 2.0 license.
"""Check the published file set, local documentation links and source references."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ROOT_FILES = {
    '.gitignore', 'CITATION.cff', 'CKN.lean', 'CONTRIBUTING.md', 'LICENSE',
    'README.md', 'formalization.yaml', 'lake-manifest.json', 'lakefile.toml',
    'lean-toolchain', 'comparator.json',
}
DIRECTORIES = {'CKN', 'comparators', 'docs', 'paper', 'scripts', '.github'}
TEXT_SUFFIXES = {'.lean', '.md', '.tex', '.bib', '.py', '.sh', '.toml', '.yaml', '.yml', '.json', '.cff', '.txt'}


def main() -> int:
    files = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')[:-1]
    errors = []
    required = ROOT_FILES | {'paper/ckn.pdf'}
    if not required <= set(files):
        errors.append(f'missing required files: {sorted(required - set(files))}')
    for name in files:
        path = Path(name)
        if name not in ROOT_FILES and (len(path.parts) == 1 or path.parts[0] not in DIRECTORIES):
            errors.append(f'unexpected release path: {name}')
        allowed = (
            path.parts[0] == 'CKN' and path.suffix == '.lean'
            or path.parts[0] == 'comparators' and path.suffix in {'.lean', '.md'}
            or path.parts[0] == 'docs' and path.suffix == '.md'
            or path.parts[0] == 'paper' and path.suffix in {'.md', '.tex', '.bib', '.pdf'}
            or path.parts[0] == 'scripts' and path.suffix in {'.py', '.sh', '.txt'}
            or path.parts[:2] == ('.github', 'workflows') and path.suffix == '.yml'
            or name in ROOT_FILES
        )
        if not allowed:
            errors.append(f'unexpected release file type: {name}')
        source = ROOT / path
        if source.is_symlink() or not source.is_file():
            errors.append(f'missing or symlinked source: {name}')
            continue
        if path.suffix not in TEXT_SUFFIXES:
            continue
        text = source.read_text()
        if path.suffix == '.md':
            for match in re.finditer(r'\]\(([^\s)]+)\)', text):
                target = match.group(1).split('#')[0]
                if not target or re.match(r'[a-z]+:', target):
                    continue
                destination = (source.parent / target).resolve()
                if not destination.is_relative_to(ROOT) or not destination.exists():
                    errors.append(f'{name}: missing local link {target}')
        if path.suffix == '.lean':
            for module in re.findall(r'^import (CKN(?:\.[\w]+)*)$', text, re.M):
                if module.replace('.', '/') + '.lean' not in files:
                    errors.append(f'{name}: missing import {module}')
    for error in errors:
        print(f'check_public: {error}', file=sys.stderr)
    print(f'check_public: {"FAIL" if errors else "PASS"} ({len(files)} tracked files)')
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
