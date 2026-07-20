#!/usr/bin/env bash
# Usage: measure-heartbeats.sh <combined-log> <ref> <file>...
# Measures each file's source at <ref> in parallel (files are
# independent), then stitches the per-file sections together in
# input order so the combined log is deterministic. Parallelism
# trades some per-file wall-clock accuracy for hours of runtime
# on refactor-sized PRs; heartbeats are unaffected, and both
# sides of a comparison are measured the same way.
set -euo pipefail
out="$1"
ref="$2"
shift 2
outdir=$(mktemp -d)
jobs=$(nproc)
if [ "$jobs" -gt 1 ]; then jobs=$((jobs - 1)); fi
printf '%s\n' "$@" | xargs -P "$jobs" -I{} \
  bash "$RUNNER_TEMP/measure-one.sh" "$ref" {} "$outdir"
: > "$out"
for file in "$@"; do
  slug="$(printf '%s' "$file" | tr '/' '_')_$(printf '%s' "$file" | cksum | cut -d' ' -f1)"
  cat "$outdir/$slug.log" >> "$out"
done
rm -rf "$outdir"
