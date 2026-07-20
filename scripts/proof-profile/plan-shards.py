"""Emit the proof-profile `measure` job's shard matrix as JSON on stdout.

Shards are computed from the PR's own modified-file count at run time, so
there is no static shard list to maintain and nothing to redistribute as
the pool grows. Each side (base/head) is split into the same number of
round-robin shards; the measure jobs re-derive their slice from the shard
index and count, so the matrix itself stays small no matter how large the
PR is.

Environment:
    COMPARE     "true" when a base→head comparison will run.
    MODIFIED    Space-separated modified .lean files.
    MERGE_BASE  Revision the base side measures against.
    HEAD_SHA    Revision the head side measures against.

When no comparison will run, the matrix carries a single placeholder
entry: the measure job is skipped by its `if:` in that case, but the
strategy expression must still parse.
"""

import json
import math
import os

MAX_SHARDS = 8
FILES_PER_SHARD = 75

modified = os.environ.get("MODIFIED", "").split()
compare = os.environ.get("COMPARE", "") == "true"

sides = [
    ("base", os.environ.get("MERGE_BASE", ""), "proof-profile-base-heartbeats"),
    ("head", os.environ.get("HEAD_SHA", ""), "proof-profile-modified-heartbeats"),
]

entries = []
if compare and modified:
    shard_count = min(MAX_SHARDS, math.ceil(len(modified) / FILES_PER_SHARD))
    for side, ref, log_stem in sides:
        for index in range(shard_count):
            shard = f"{index:02d}"
            entries.append(
                {
                    "side": side,
                    "shard": shard,
                    "shard_count": shard_count,
                    "ref": ref,
                    "log": f"{log_stem}-{shard}.log",
                }
            )
else:
    entries.append(
        {"side": "base", "shard": "00", "shard_count": 1, "ref": "", "log": ""}
    )

print(json.dumps({"include": entries}))
