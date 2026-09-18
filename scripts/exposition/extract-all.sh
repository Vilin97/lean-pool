#!/usr/bin/env bash
# Keep each project's parser environment isolated: combining projects would
# superpose their notation extensions and silently change command parsing.
# The Python driver caches each environment's output and assembles the JSONL.
# Usage: [LEAN_CMD=lean] [EXTRACT_JOBS=N] extract-all.sh [dump.jsonl] [commands.jsonl]
# Run from the repository root inside `lake env`.
set -euo pipefail
export PYTHONPATH="$PWD/python${PYTHONPATH:+:$PYTHONPATH}"
exec python3 -m lean_pool.exposition.extract "$@"
