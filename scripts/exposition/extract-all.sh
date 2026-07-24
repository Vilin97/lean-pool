#!/usr/bin/env bash
# Per-project exposition extraction driver.
#
# Each project is extracted against its own environment (Mathlib + that
# project only). A whole-pool environment would superpose every project's
# parser extensions, and a foreign notation can turn an identifier used by
# another project (ε, s, …) into a keyword token — parse-error recovery
# then silently truncates re-parsed commands. Lean never builds against
# such a superposition, and neither do we.
#
# Usage: [LEAN_CMD=lean] [EXTRACT_JOBS=N] extract-all.sh <dump.jsonl> <commands.jsonl>
# Run from the repository root with LEAN_PATH set (e.g. via `lake env`).
set -euo pipefail

out_dump="${1:-exposition-dump.jsonl}"
out_cmds="${2:-exposition-commands.jsonl}"
jobs="${EXTRACT_JOBS:-2}"
lean_cmd="${LEAN_CMD:-lean}"
workdir="$(mktemp -d)"

# Project roots: the second component of every module the index imports.
projects="$(sed -n 's/^import LeanPool\.//p' LeanPool.lean | cut -d. -f1 | sort -u)"
count="$(printf '%s\n' "$projects" | wc -l | tr -d ' ')"
echo "exposition: extracting $count projects ($jobs at a time)"

extract_failed=0
printf '%s\n' "$projects" | xargs -P "$jobs" -I '{}' sh -c '
  "$1" --run scripts/exposition/Extract.lean \
    "$2/dump-$3.jsonl" "$2/cmds-$3.jsonl" "LeanPool.$3" \
    > "$2/log-$3.txt" 2>&1 || { echo "$3" >> "$2/FAILED"; }
' extract "$lean_cmd" "$workdir" '{}' || extract_failed=1

if [ -f "$workdir/FAILED" ] || [ "$extract_failed" -ne 0 ]; then
  echo "exposition: extraction FAILED for:" >&2
  cat "$workdir/FAILED" 2>/dev/null >&2 || true
  while read -r project; do
    echo "--- $project ---" >&2
    tail -15 "$workdir/log-$project.txt" >&2 || true
  done < "$workdir/FAILED"
  echo "exposition: work dir kept at $workdir" >&2
  exit 1
fi

: > "$out_dump"
: > "$out_cmds"
for project in $projects; do
  cat "$workdir/dump-$project.jsonl" >> "$out_dump"
  cat "$workdir/cmds-$project.jsonl" >> "$out_cmds"
done
rm -rf "$workdir"
echo "exposition: wrote $(wc -l < "$out_dump" | tr -d ' ') declarations to $out_dump"
echo "exposition: wrote $(wc -l < "$out_cmds" | tr -d ' ') module command tables to $out_cmds"
