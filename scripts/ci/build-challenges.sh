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

# Both greps exit 1 on no match, and both no-matches are the clean case: a
# build with no warnings at all (an empty board), or one whose only warnings
# are the expected sorry notices. Under `set -o pipefail` an unguarded first
# stage would kill the script on the quietest possible build.
unexpected="$(
  { grep -nE '(^|: )warning:' "$log" || true; } |
    { grep -vE "declaration uses .sorry." || true; }
)"
if [ -n "$unexpected" ]; then
  printf '%s\n' "$unexpected"
  echo "::error::Challenge build emitted warnings beyond the expected sorry notices."
  exit 1
fi
echo "Challenge and Solution libraries built; only the expected sorry notices."
