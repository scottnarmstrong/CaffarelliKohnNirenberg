#!/usr/bin/env bash
# Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
# Released under Apache 2.0 license.

set -Eeuo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/verify_fresh_clone.sh [--plan] [--expected-sha SHA] [--keep-on-failure]

Clone the configured repository into a temporary checkout and run the
publication verification sequence. --expected-sha requires HEAD and origin/main
in that clone to equal the full 40-digit SHA before any cache or build command.
CKN_EXPECTED_SHA supplies the default; the command-line option takes precedence.
The verified SHA is recorded in the temporary run directory's head.txt.
--keep-on-failure retains that directory on failure (default: remove on exit).
--plan lists the steps without cloning, downloading, or running any check.
EOF
}

plan=0
keep_on_failure=0
expected_sha="${CKN_EXPECTED_SHA:-}"
while (( $# )); do
  case "$1" in
    --plan) plan=1; shift ;;
    --keep-on-failure) keep_on_failure=1; shift ;;
    --expected-sha)
      if (( $# < 2 )) || [[ -z "$2" ]]; then
        echo "verify_fresh_clone: --expected-sha requires a full SHA" >&2
        exit 2
      fi
      expected_sha="$2"
      shift 2
      ;;
    -h|--help) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done
if [[ -n "$expected_sha" && ! "$expected_sha" =~ ^[[:xdigit:]]{40}$ ]]; then
  echo "verify_fresh_clone: expected SHA must have 40 hexadecimal digits" >&2
  exit 2
fi

repo_url="${CKN_REPO_URL:-}"
if [[ -z "$repo_url" ]]; then
  repo_url="$(git config --get remote.origin.url 2>/dev/null || true)"
fi
if [[ -z "$repo_url" ]]; then
  repo_url="<set CKN_REPO_URL>"
fi

if (( plan )); then
  printf '%s\n' "# verification plan (not executed)" \
    "CKN_REPO_URL=$(printf '%q' "$repo_url")" \
    "CKN_EXPECTED_SHA=$(printf '%q' "$expected_sha")" \
    "KEEP_ON_FAILURE=$keep_on_failure" \
    'TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/ckn-fresh-clone.XXXXXX")"' \
    'if [[ -d "$CKN_REPO_URL" ]]; then' \
    '  export CKN_MAIN_CHECKOUT="$(cd -- "$CKN_REPO_URL" && pwd -P)"' \
    'else' \
    '  export CKN_MAIN_CHECKOUT="$TMP_ROOT/protected-main-sentinel"' \
    'fi' \
    'git clone "$CKN_REPO_URL" "$TMP_ROOT/repo"' \
    'cd "$TMP_ROOT/repo"' \
    'HEAD_SHA="$(git rev-parse HEAD)"' \
    'if [[ -n "$CKN_EXPECTED_SHA" ]]; then' \
    '  ORIGIN_MAIN_SHA="$(git rev-parse --verify refs/remotes/origin/main 2>/dev/null || true)"' \
    '  if [[ "$HEAD_SHA" != "$CKN_EXPECTED_SHA" || "$ORIGIN_MAIN_SHA" != "$CKN_EXPECTED_SHA" ]]; then' \
    '    printf "FRESH-CLONE SHA MISMATCH expected=%s head=%s origin/main=%s\n" "$CKN_EXPECTED_SHA" "$HEAD_SHA" "$ORIGIN_MAIN_SHA" >&2' \
    '    exit 3' \
    '  fi' \
    '  printf "verify_fresh_clone: HEAD PASS: %s\n" "$HEAD_SHA"' \
    'fi' \
    'printf "%s\n" "$HEAD_SHA" > "$TMP_ROOT/head.txt"' \
    'PINNED_TOOLCHAIN="$(tr -d "[:space:]" < lean-toolchain)"' \
    'if ! command -v elan >/dev/null 2>&1; then' \
    '  curl --proto "=https" --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain "$PINNED_TOOLCHAIN"' \
    '  export PATH="$HOME/.elan/bin:$PATH"' \
    'fi' \
    'export PATH="$(dirname "$(command -v elan)"):$PATH"' \
    'elan toolchain list | awk '\''{print $1}'\'' | grep -Fqx "$PINNED_TOOLCHAIN" || elan toolchain install "$PINNED_TOOLCHAIN"' \
    'lake exe cache get' \
    'python3 scripts/build.py --fresh CKN' \
    'python3 scripts/build.py --fresh Comparators' \
    'python3 scripts/build_all.py' \
    'python3 scripts/check_comparators.py' \
    'python3 scripts/check_public.py' \
    'python3 scripts/check_axioms.py --root .' \
    'AXIOM_PROBE="$(mktemp "$PWD/.ckn-axioms.XXXXXX.lean")"' \
    'printf "%s\\n" "import CKN.Statements.TheoremA" "import CKN.Statements.TheoremB" "import CKN.Statements.TheoremC" "#print axioms CKN.epsilonRegularityL3" "#print axioms CKN.epsilonRegularityGradient" "#print axioms CKN.caffarelliKohnNirenberg" > "$AXIOM_PROBE"' \
    'scripts/lean_direct.sh "$AXIOM_PROBE" -DautoImplicit=false -DwarningAsError=true' \
    'rm -f -- "$AXIOM_PROBE"' \
    '# EXIT cleanup: remove TMP_ROOT unless exit status is nonzero and KEEP_ON_FAILURE=1'
  exit 0
fi

if [[ "$repo_url" == "<set CKN_REPO_URL>" ]]; then
  echo "verify_fresh_clone: no repository URL; set CKN_REPO_URL or configure origin" >&2
  exit 2
fi

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/ckn-fresh-clone.XXXXXX")"
clone_root="$tmp_root/repo"
axiom_probe=""

cleanup() {
  local exit_status=$?
  if [[ -n "$axiom_probe" ]]; then
    rm -f -- "$axiom_probe"
  fi
  if (( exit_status != 0 && keep_on_failure )); then
    printf 'verify_fresh_clone: kept failed run: %s\n' "$tmp_root" >&2
  else
    rm -rf -- "$tmp_root"
  fi
  return "$exit_status"
}
trap cleanup EXIT

# Identify the protected source before changing into the disposable checkout.
# Do not inherit a caller's value that could identify the new clone as main.
if [[ -d "$repo_url" ]]; then
  export CKN_MAIN_CHECKOUT="$(cd -- "$repo_url" && pwd -P)"
else
  export CKN_MAIN_CHECKOUT="$tmp_root/protected-main-sentinel"
fi

printf '+ git clone %q %q\n' "$repo_url" "$clone_root"
git clone "$repo_url" "$clone_root"
cd "$clone_root"

head_sha="$(git rev-parse HEAD)"
if [[ -n "$expected_sha" ]]; then
  origin_main_sha="$(git rev-parse --verify refs/remotes/origin/main 2>/dev/null || true)"
  if [[ "$head_sha" != "$expected_sha" || "$origin_main_sha" != "$expected_sha" ]]; then
    printf 'FRESH-CLONE SHA MISMATCH expected=%s head=%s origin/main=%s\n' \
      "$expected_sha" "$head_sha" "$origin_main_sha" >&2
    exit 3
  fi
  printf 'verify_fresh_clone: HEAD PASS: %s\n' "$head_sha"
fi
printf '%s\n' "$head_sha" > "$tmp_root/head.txt"

pinned_toolchain="$(tr -d '[:space:]' < lean-toolchain)"
if [[ -z "$pinned_toolchain" ]]; then
  echo "verify_fresh_clone: lean-toolchain is empty" >&2
  exit 1
fi

if ! command -v elan >/dev/null 2>&1; then
  printf '+ curl --proto =https --tlsv1.2 -sSf elan-init.sh | sh -s -- -y --default-toolchain %q\n' \
    "$pinned_toolchain"
  curl --proto "=https" --tlsv1.2 -sSf \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain "$pinned_toolchain"
  export PATH="$HOME/.elan/bin:$PATH"
fi
export PATH="$(dirname "$(command -v elan)"):$PATH"

if ! elan toolchain list | awk '{print $1}' | grep -Fqx "$pinned_toolchain"; then
  printf '+ elan toolchain install %q\n' "$pinned_toolchain"
  elan toolchain install "$pinned_toolchain"
fi

run_step() {
  printf '\n+'
  printf ' %q' "$@"
  printf '\n'
  "$@"
}

run_step lake exe cache get
run_step python3 scripts/build.py --fresh CKN
run_step python3 scripts/build.py --fresh Comparators
run_step python3 scripts/build_all.py
run_step python3 scripts/check_comparators.py
run_step python3 scripts/check_public.py
run_step python3 scripts/check_axioms.py --root .

axiom_probe="$(mktemp "$clone_root/.ckn-axioms.XXXXXX.lean")"
printf '%s\n' \
  'import CKN.Statements.TheoremA' \
  'import CKN.Statements.TheoremB' \
  'import CKN.Statements.TheoremC' \
  '#print axioms CKN.epsilonRegularityL3' \
  '#print axioms CKN.epsilonRegularityGradient' \
  '#print axioms CKN.caffarelliKohnNirenberg' > "$axiom_probe"
run_step scripts/lean_direct.sh "$axiom_probe" \
  -DautoImplicit=false -DwarningAsError=true

echo "verify_fresh_clone: PASS"
