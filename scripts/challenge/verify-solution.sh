#!/usr/bin/env bash
# Verify a claimed solution to a Lean Pool challenge with `leanprover/comparator`.
#
# Comparator is a trustworthy judge: it replays the solution environment through
# the Lean kernel and checks that the theorems it claims really do prove the
# statements in the challenge module, using no axiom outside the permitted set.
# A green run here is what turns "I solved it" into a verified claim.
#
#   scripts/challenge/verify-solution.sh <challenge-slug> [<solution-module>]
#
# The module defaults to the one the registry records for that challenge. It has
# to be importable from this workspace and must restate the challenge statement
# rather than import it — comparator exports the two environments separately and
# compares them. Everything comparator needs beyond that comes from
# `make comparator` (see CONTRIBUTING.md#challenge-mode).
#
# Options:
#   --comparator PATH    comparator binary (default: $COMPARATOR_BIN, then the
#                        `make comparator` cache directory)
#   --lean4export PATH   lean4export binary built at this project's toolchain
#   --landrun PATH       landrun sandbox binary
#   --nanoda             additionally replay through the nanoda kernel
#   --insecure-no-sandbox
#                        run without landrun. Compiling a solution executes its
#                        code; only pass this for a solution you already trust.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cache_dir="${XDG_CACHE_HOME:-$HOME/.cache}/lean-pool"
comparator_bin="${COMPARATOR_BIN:-$cache_dir/comparator/.lake/build/bin/comparator}"
lean4export_bin="${COMPARATOR_LEAN4EXPORT:-}"
landrun_bin="${COMPARATOR_LANDRUN:-}"
enable_nanoda=false
allow_no_sandbox=false

usage() {
  sed -n '3,25p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
  exit "${1:-1}"
}

positional=()
while [ $# -gt 0 ]; do
  case "$1" in
    --comparator) comparator_bin="$2"; shift 2 ;;
    --lean4export) lean4export_bin="$2"; shift 2 ;;
    --landrun) landrun_bin="$2"; shift 2 ;;
    --nanoda) enable_nanoda=true; shift ;;
    --insecure-no-sandbox) allow_no_sandbox=true; shift ;;
    -h|--help) usage 0 ;;
    -*) echo "Unknown option: $1" >&2; usage ;;
    *) positional+=("$1"); shift ;;
  esac
done

if [ "${#positional[@]}" -lt 1 ] || [ "${#positional[@]}" -gt 2 ]; then
  usage
fi
slug="${positional[0]}"
solution_module=""
if [ "${#positional[@]}" -eq 2 ]; then
  solution_module="${positional[1]}"
fi

if [ ! -x "$comparator_bin" ]; then
  cat >&2 <<EOF
error: comparator binary not found at $comparator_bin

Build it once with:

    make comparator

or point at an existing build with --comparator PATH (or COMPARATOR_BIN).
EOF
  exit 2
fi

if [ -z "$lean4export_bin" ] && command -v lean4export >/dev/null 2>&1; then
  lean4export_bin="$(command -v lean4export)"
fi
if [ -z "$lean4export_bin" ] || [ ! -x "$lean4export_bin" ]; then
  cat >&2 <<EOF
error: lean4export binary not found.

Comparator exports this workspace's environment with lean4export, so it has to
be built at the toolchain in lean-toolchain. \`make comparator\` builds one; or
pass --lean4export PATH (or COMPARATOR_LEAN4EXPORT).
EOF
  exit 2
fi

if [ -z "$landrun_bin" ] && command -v landrun >/dev/null 2>&1; then
  landrun_bin="$(command -v landrun)"
fi
if [ -z "$landrun_bin" ]; then
  if [ "$allow_no_sandbox" = false ]; then
    cat >&2 <<EOF
error: landrun not found.

Comparator compiles the solution, which runs its code. On Linux, install
landrun (https://github.com/Zouuup/landrun) and re-run. Elsewhere — or for a
solution you already trust — re-run with --insecure-no-sandbox, which
substitutes comparator's own scripts/fake-landrun.sh and provides no isolation.
EOF
    exit 2
  fi
  comparator_dir="$(cd "$(dirname "$comparator_bin")/../../.." && pwd)"
  landrun_bin="$comparator_dir/scripts/fake-landrun.sh"
  if [ ! -x "$landrun_bin" ]; then
    echo "error: fake-landrun.sh not found at $landrun_bin" >&2
    exit 2
  fi
  echo "warning: running without a sandbox; the solution's code will execute." >&2
fi

config="$(mktemp -t lean-pool-comparator)"
trap 'rm -f "$config"' EXIT

# Plain string, not an array: bash 3.2 (macOS) treats an empty array as
# unbound under `set -u`, and `${var:+...}` expands to nothing when unset.
nanoda_flag=""
if [ "$enable_nanoda" = true ]; then
  nanoda_flag="--enable-nanoda"
fi

cd "$repo_root"
(cd python && uv run python -m lean_pool.challenge --repo .. config "$slug" \
  ${solution_module:+--solution-module "$solution_module"} --out "$config" \
  ${nanoda_flag:+"$nanoda_flag"}) >/dev/null

echo "Comparator configuration:"
cat "$config"

# Build only the challenge side: comparator builds the solution itself, inside
# the sandbox, and pre-compiling an untrusted solution here would defeat that.
echo "Building the challenge library..."
lake build Challenge

echo "Running comparator..."
COMPARATOR_LANDRUN="$landrun_bin" COMPARATOR_LEAN4EXPORT="$lean4export_bin" \
  lake env "$comparator_bin" "$config"
echo "Verified: challenge '$slug' is proved by the solution comparator checked."
