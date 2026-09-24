#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
# Released under Apache 2.0 license.
"""Build local CKN modules with a fail-closed Mathlib package guard.

``--fresh TARGET`` is available only in a disposable non-main checkout.  It
records package-tree changes caused by a fresh cache/build setup instead of
failing, while the ordinary invocation and the main checkout remain strict.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = ROOT / ".lake/packages/mathlib"
MATHLIB_OLEAN_CACHE_COUNT = 8555
MATHLIB_OLEAN_THRESHOLD = (MATHLIB_OLEAN_CACHE_COUNT * 90 + 99) // 100
EXPECTED_LEAN_VERSION = "Lean version 4.35.0-rc2"
PACKAGE = "CKN"
ALLOWED_TARGETS = {PACKAGE, "CKNAll", "Comparators"}
# ``--fresh`` is deliberately restricted to disposable checkouts.  Keep the
# main checkout explicit so that the ordinary package-preservation guard can
# never be weakened by an environment variable or an invocation typo.
MAIN_CHECKOUT = Path(os.environ.get("CKN_MAIN_CHECKOUT", str(ROOT))).resolve()


def count_oleans(root: Path) -> int:
    return sum(1 for _ in root.rglob("*.olean")) if root.exists() else 0


def run_checked(command: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, check=True, text=True, **kwargs)


def git_output(repository: Path, *arguments: str) -> str:
    try:
        return run_checked(
            ["git", "-C", str(repository), *arguments], capture_output=True
        ).stdout.strip()
    except subprocess.CalledProcessError as exc:
        raise SystemExit(f"refusing build: Git check failed for {repository}: {exc}") from exc


def artifact_snapshot(
    root: Path, *, ignore_generated_build: bool = False
) -> dict[str, tuple[int, int, int, int, int]]:
    """Record package-tree entries without reading their contents.

    A source-only package check may reuse generated build artifacts. Those
    entries, including the containing ``.lake`` directory, are intentionally
    outside that check's source-package mutation guard.
    """
    snapshot: dict[str, tuple[int, int, int, int, int]] = {}
    if not root.exists():
        return snapshot
    for path in (root, *root.rglob("*")):
        relative = path.relative_to(root)
        if ignore_generated_build and (
            relative == Path(".git")
            or relative.parts[:1] == (".git",)
            or relative == Path(".lake")
            or any(
                relative.parts[index : index + 2] == (".lake", "build")
                for index in range(len(relative.parts) - 1)
            )
        ):
            continue
        metadata = path.lstat()
        snapshot[str(relative) or "."] = (
            metadata.st_mode,
            metadata.st_size,
            metadata.st_mtime_ns,
            metadata.st_ctime_ns,
            metadata.st_ino,
        )
    return snapshot


def stop_process(process: subprocess.Popen[str]) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        process.wait()
        return
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()


run_checked([sys.executable, str(ROOT / "scripts/check_rules.py")], cwd=ROOT)

build_arguments = list(sys.argv[1:])
fresh_mode = False
if "--fresh" in build_arguments:
    if build_arguments.count("--fresh") != 1:
        raise SystemExit("refusing build arguments: --fresh may be given at most once")
    build_arguments.remove("--fresh")
    fresh_mode = True
if build_arguments and (
    len(build_arguments) != 1 or build_arguments[0] not in ALLOWED_TARGETS
):
    raise SystemExit(
        f"refusing build arguments: expected no arguments or exactly one of "
        f"{sorted(ALLOWED_TARGETS)}, with optional --fresh"
    )
if fresh_mode and ROOT.resolve() == MAIN_CHECKOUT:
    raise SystemExit(
        "refusing --fresh in the main checkout; package-tree changes must fail closed"
    )

environment = os.environ.copy()
for variable in ("LEAN_PATH", "LAKE_PACKAGES_DIR", "ELAN_TOOLCHAIN"):
    environment.pop(variable, None)

try:
    lake_version = run_checked(
        ["lake", "--version"], cwd=ROOT, env=environment, capture_output=True
    ).stdout.strip()
except (FileNotFoundError, subprocess.CalledProcessError) as exc:
    raise SystemExit(f"refusing build: cannot resolve the pinned Lake executable: {exc}") from exc
if EXPECTED_LEAN_VERSION not in lake_version:
    raise SystemExit(f"refusing build: unexpected Lake/Lean version: {lake_version}")
print(lake_version, flush=True)

if not MATHLIB.is_dir():
    raise SystemExit(f"refusing build: Mathlib package is missing: {MATHLIB}")
mathlib_oleans = count_oleans(MATHLIB / ".lake/build/lib")
print(
    f"mathlib oleans: {mathlib_oleans} (minimum {MATHLIB_OLEAN_THRESHOLD})",
    flush=True,
)
if mathlib_oleans < MATHLIB_OLEAN_THRESHOLD:
    raise SystemExit(
        f"refusing build: Mathlib olean threshold {MATHLIB_OLEAN_THRESHOLD} failed"
    )

try:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
except (json.JSONDecodeError, OSError) as exc:
    raise SystemExit(f"refusing build: cannot read lake-manifest.json: {exc}") from exc
mathlib_entry = next(
    (entry for entry in manifest.get("packages", []) if entry.get("name") == "mathlib"),
    None,
)
if not isinstance(mathlib_entry, dict) or not isinstance(mathlib_entry.get("rev"), str):
    raise SystemExit("refusing build: lake-manifest.json has no pinned Mathlib revision")
actual_revision = git_output(MATHLIB, "rev-parse", "HEAD")
if actual_revision != mathlib_entry["rev"]:
    raise SystemExit(
        f"refusing build: mathlib is at {actual_revision}, expected {mathlib_entry['rev']}"
    )
package_status = git_output(MATHLIB, "status", "--short")
if package_status:
    print(package_status, file=sys.stderr)
    raise SystemExit("refusing build: Mathlib package is not clean")

# Set CKN_INVALIDATE=1 to rebuild the local library without clearing Mathlib.
removed: list[Path] = []
for base in (ROOT / ".lake/build/lib/lean", ROOT / ".lake/build/ir"):
    if os.environ.get("CKN_INVALIDATE") != "1" or not base.exists():
        continue
    resolved_base = base.resolve()
    if not resolved_base.is_relative_to(ROOT.resolve()):
        raise SystemExit(f"refusing unsafe artifact root: {resolved_base}")
    for target in base.glob(f"{PACKAGE}*"):
        resolved_target = target.resolve()
        if not resolved_target.is_relative_to(resolved_base):
            raise SystemExit(f"refusing unsafe artifact target: {resolved_target}")
        if target.is_dir():
            shutil.rmtree(target)
        else:
            target.unlink()
        removed.append(target)

print(
    f"removed {len(removed)} generated local artifacts; Lake will regenerate them",
    flush=True,
)

command = ["lake", "--old", "--no-ansi", "build", *(build_arguments or [PACKAGE])]
forbidden_output = re.compile(
    r"(?:^|\s)(?:Building|Built|Compiling)\s+Mathlib(?:[./:]|\b)|"
    r"\.lake/packages/mathlib(?:/|\b)"
)
diagnostic_output = re.compile(r"^\s*(?:warning|error|info|note|trace):")
ignore_generated_package_build = os.environ.get("CKN_IGNORE_PACKAGE_BUILD") == "1"
mathlib_snapshot_before = artifact_snapshot(
    MATHLIB, ignore_generated_build=ignore_generated_package_build
)

process: subprocess.Popen[str] | None = None
failure: str | None = None
caught: BaseException | None = None
package_tree_changed = False
try:
    process = subprocess.Popen(
        command,
        cwd=ROOT,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
        start_new_session=True,
    )
    assert process.stdout is not None
    for line in process.stdout:
        print(line, end="", flush=True)
        if forbidden_output.search(line) and not diagnostic_output.match(line):
            failure = f"terminated forbidden Mathlib activity after line: {line.strip()}"
            stop_process(process)
            break
    if failure is None:
        return_code = process.wait()
        if return_code != 0:
            failure = f"Lake build failed with exit code {return_code}"
except BaseException as exc:
    caught = exc
finally:
    if process is not None:
        stop_process(process)
    mathlib_snapshot_after = artifact_snapshot(
        MATHLIB, ignore_generated_build=ignore_generated_package_build
    )
    if mathlib_snapshot_after != mathlib_snapshot_before:
        package_tree_changed = True
        detail = "Mathlib package tree changed during guarded build"
        changed = sorted(
            set(mathlib_snapshot_before) ^ set(mathlib_snapshot_after)
            | {
                path
                for path in set(mathlib_snapshot_before) & set(mathlib_snapshot_after)
                if mathlib_snapshot_before[path] != mathlib_snapshot_after[path]
            }
        )
        if fresh_mode:
            print(
                f"fresh checkout: recorded {len(changed)} Mathlib package-tree "
                "change(s) during guarded build",
                file=sys.stderr,
            )
            for path in changed:
                print(f"  {path}", file=sys.stderr)
        else:
            failure = f"{failure}; {detail}" if failure else detail

if caught is not None:
    if failure:
        raise SystemExit(failure) from caught
    raise caught
if failure:
    raise SystemExit(failure)

if fresh_mode:
    if package_tree_changed:
        print(
            "guarded fresh-checkout build: PASS "
            "(Mathlib package-tree changes recorded, main guard unchanged)",
            flush=True,
        )
    else:
        print(
            "guarded fresh-checkout build: PASS "
            "(Mathlib package tree unchanged)",
            flush=True,
        )
else:
    print("guarded local build: PASS (Mathlib package tree unchanged)", flush=True)
