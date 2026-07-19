#!/usr/bin/env bash
# Measure one file at one git revision with Mathlib's
# countHeartbeats linter (which reports in `set_option
# maxHeartbeats` units) plus wall time, into
# <outdir>/<slugified-path>.log. The source comes from `git show`
# and is compiled out-of-tree against whatever environment is
# currently built (imports resolve by module name, not path), so
# the working tree never has to sit at <ref>.
ref="$1"
file="$2"
outdir="$3"
# The checksum disambiguates paths that collide under `tr` (an
# underscore in a directory name vs a slash).
slug="$(printf '%s' "$file" | tr '/' '_')_$(printf '%s' "$file" | cksum | cut -d' ' -f1)"
src="$outdir/src-$slug.lean"
{
  echo "## $file"
  if git show "$ref:$file" > "$src"; then
    /usr/bin/time -p "$HOME/.elan/bin/lake" env lean \
      -Dlinter.countHeartbeats=true \
      "$src"
    status=$?
    if [ "$status" -ne 0 ]; then
      echo "error: count-heartbeats command exited with status $status"
    fi
  else
    echo "error: could not read $file at revision $ref"
  fi
  echo
} > "$outdir/$slug.log" 2>&1
rm -f "$src"
