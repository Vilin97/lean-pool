"""Decide how the CI build is parallelized, from the change set alone.

Emits a JSON plan on stdout for the `Lean Action CI` workflow:

    {"mode": "skip" | "single" | "sharded",
     "shard_count": <int>,
     "matrix": {"include": [{"shard": "00", "projects": "ProjA ProjB"}, ...]},
     "reason": "<human-readable explanation>"}

`skip` handles an exact README-only change. `single` keeps the
classic one-job pipeline — the fast path for a typical PR that adds or edits
one project. `sharded` splits the build across
parallel jobs for the cases that take hours serially: a cold cache, a
toolchain/manifest bump, or a refactor touching many projects.

Everything is computed at run time from the repository tree and the diff,
so there is no static shard assignment to maintain as the pool grows.
Projects are the shard unit because pool projects never import each
other; shards are balanced by per-project Lean file count using greedy
longest-processing-time assignment, deterministically (ties break on
name).

Environment:
    CHANGED_FILES   Newline-separated changed paths (empty when none).
    DIFF_AVAILABLE  "false" when no diff exists for this event
                    (workflow_dispatch, force-push); default "true".
    COLD            "true" when no warm Actions build cache matched.
    FORCE_FULL      "true" to shard-build the whole pool regardless.
"""

import json
import math
import os
from pathlib import Path

MAX_SHARDS = 10
FILES_PER_SHARD = 250
# Below either threshold a serial build is already fast; sharding would
# only add scheduling and artifact overhead to the common import PR.
SHARD_MIN_PROJECTS = 4
SHARD_MIN_FILES = 500
# Changes to any of these invalidate the whole pool's build.
GLOBAL_BUILD_INPUTS = {"lean-toolchain", "lake-manifest.json", "lakefile.toml"}


def project_weights() -> dict[str, int]:
    """Map each pool build unit to its Lean file count.

    A unit is a project directory (plus its umbrella module) or, for
    single-file projects like `LeanPool/CramerWold.lean`, the bare
    top-level module itself.
    """
    weights: dict[str, int] = {}
    for entry in Path("LeanPool").iterdir():
        if entry.is_dir():
            count = sum(1 for _ in entry.rglob("*.lean"))
            if Path(f"LeanPool/{entry.name}.lean").exists():
                count += 1
            weights[entry.name] = count
        elif entry.suffix == ".lean" and not entry.with_suffix("").is_dir():
            weights[entry.stem] = 1
    return weights


def dirty_projects(changed_files: list[str], known: set[str]) -> set[str]:
    """Projects whose directory or umbrella module appears in the diff."""
    dirty: set[str] = set()
    for path in changed_files:
        parts = path.split("/")
        if parts[0] != "LeanPool" or len(parts) < 2:
            continue
        name = parts[1].removesuffix(".lean") if len(parts) == 2 else parts[1]
        if name in known:
            dirty.add(name)
    return dirty


def assign_shards(targets: dict[str, int], shard_count: int) -> list[list[str]]:
    """Greedy LPT bin-packing of projects into `shard_count` balanced shards."""
    bins: list[tuple[int, list[str]]] = [(0, []) for _ in range(shard_count)]
    for name, weight in sorted(targets.items(), key=lambda kv: (-kv[1], kv[0])):
        load, members = min(bins, key=lambda b: b[0])
        index = bins.index((load, members))
        members.append(name)
        bins[index] = (load + weight, members)
    return [members for _, members in bins if members]


def main() -> None:
    """Read the change set from the environment and print the build plan."""
    changed_files = os.environ.get("CHANGED_FILES", "").split()
    diff_available = os.environ.get("DIFF_AVAILABLE", "true") != "false"
    cold = os.environ.get("COLD", "") == "true"
    force_full = os.environ.get("FORCE_FULL", "") == "true"

    if diff_available and changed_files == ["README.md"] and not force_full:
        plan = {
            "mode": "skip",
            "shard_count": 0,
            # Keep the matrix expression valid even though its jobs are skipped.
            "matrix": {"include": [{"shard": "00", "projects": ""}]},
            "reason": "README-only change",
        }
        print(json.dumps(plan))
        return

    weights = project_weights()
    global_change = bool(GLOBAL_BUILD_INPUTS.intersection(changed_files))
    full = cold or force_full or global_change or not diff_available

    if full:
        targets = weights
        if force_full:
            reason = "full rebuild requested"
        elif cold:
            reason = "no warm build cache"
        elif global_change:
            reason = "toolchain/manifest/lakefile changed"
        else:
            reason = "no diff available for this event"
    else:
        dirty = dirty_projects(changed_files, set(weights))
        targets = {name: weights[name] for name in dirty}
        reason = f"{len(dirty)} dirty project(s), {sum(targets.values())} files"

    total = sum(targets.values())
    if not full and (len(targets) < SHARD_MIN_PROJECTS or total < SHARD_MIN_FILES):
        plan = {
            "mode": "single",
            "shard_count": 1,
            # Placeholder so the matrix expression always parses; the
            # shard jobs are skipped by their `if:` in single mode.
            "matrix": {"include": [{"shard": "00", "projects": ""}]},
            "reason": f"single: {reason}",
        }
    else:
        shard_count = min(MAX_SHARDS, max(2, math.ceil(total / FILES_PER_SHARD)))
        shards = assign_shards(targets, shard_count)
        plan = {
            "mode": "sharded",
            "shard_count": len(shards),
            "matrix": {
                "include": [
                    {"shard": f"{index:02d}", "projects": " ".join(sorted(members))}
                    for index, members in enumerate(shards)
                ]
            },
            "reason": f"sharded ({len(shards)}): {reason}",
        }
    print(json.dumps(plan))


if __name__ == "__main__":
    main()
