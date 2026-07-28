#!/usr/bin/env bash
# Build the Challenge and Solution libraries and gate their warnings.
#
# Challenge statements are `sorry` by design, so Lean's "declaration uses
# `sorry`" notice is expected here — and only here. Every other warning fails
# the build exactly as it does for the pool, including anything from a
# solution, which is an ordinary sorry-free proof. Which declarations are
# allowed to be open is not decided here: `lean_pool.quality` checks each
# `sorry` against `Challenge/challenges.yml` and verifies via `#print axioms`
# that nothing else in either library rests on `sorryAx`.
set -euo pipefail

lake="${LAKE:-$HOME/.elan/bin/lake}"
log="${RUNNER_TEMP:-/tmp}/challenge-build.log"

"$lake" build Challenge Solution 2>&1 | tee "$log"

# `grep -v` exits 1 when everything was filtered out, which is the clean case.
unexpected="$(grep -nE '(^|: )warning:' "$log" | { grep -vE "declaration uses .sorry." || true; })"
if [ -n "$unexpected" ]; then
  printf '%s\n' "$unexpected"
  echo "::error::Challenge build emitted warnings beyond the expected sorry notices."
  exit 1
fi
echo "Challenge and Solution libraries built; only the expected sorry notices."
