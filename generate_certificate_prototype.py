#!/usr/bin/env python3
"""Generate the disposable six-branch certificate-checker benchmark data."""

from __future__ import annotations

import importlib.util
import json
import pathlib
import re
from dataclasses import dataclass


ROOT = pathlib.Path(__file__).parent
LEAN = ROOT / "LeanPool/Erdos97ConvexOctagon"
PIVOTS = ((5, 31), (5, 32), (5, 34), (2, 32), (6, 31), (1, 30))
ORDER = (3, 4, 7, 6, 5)

spec = importlib.util.spec_from_file_location("order_bench", "/tmp/pr287_order_bench.py")
assert spec is not None and spec.loader is not None
bench = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bench)

CHOICE_RE = re.compile(
    r"private def patternSummaryChoice\d+_\d+ : SummaryRowChoice :=\s*"
    r"\n\s*⟨(\d+), (\d+),"
)


def source_choices() -> tuple[tuple[tuple[int, int], ...], ...]:
    """Read the exact row order used by the generated Lean choice arrays."""
    choices = []
    for centre in range(8):
        text = (LEAN / f"CoveragePatternChoices{centre}.lean").read_text()
        values = tuple((int(row), int(pairs)) for row, pairs in CHOICE_RE.findall(text))
        assert len(values) == 35
        choices.append(values)
    return tuple(choices)


SOURCE_CHOICES = source_choices()


@dataclass(frozen=True)
class Leaf:
    origin: int


@dataclass(frozen=True)
class Node:
    depth: int
    code: int
    pair_once: int
    pair_twice: int
    column_counts: int
    pattern_rows: int
    pattern_origins: tuple[int, ...]
    children: tuple[Leaf | Node, ...]


def summary_maps() -> tuple[dict[int, int], dict[int, int]]:
    """Load the deterministic code-to-origin witnesses."""
    pattern_entries = json.loads(
        pathlib.Path("/tmp/pr287-pattern-hit-map.json").read_text()
    )["entries"]
    patterns = {entry["code"]: entry["origin"] for entry in pattern_entries}
    hards: dict[int, int] = {}
    pair = re.compile(r"⟨(\d+),\s*(\d+)⟩")
    for shard in range(32):
        text = (LEAN / f"CoverageSummaryData{shard:02}.lean").read_text()
        hard_text = text.split(
            "/-- Lightweight exact-table summaries", maxsplit=1
        )[1].split("/-- Every pattern summary", maxsplit=1)[0]
        for match in pair.finditer(hard_text):
            origin, code = map(int, match.groups())
            hards[code] = origin
    assert len(patterns) == 33_533
    assert len(hards) == 1_088
    return patterns, hards


def dense_summaries() -> tuple[list[tuple[int, int]], list[tuple[int, int]]]:
    """Read each unique generated summary in ascending source-origin order."""
    pair = re.compile(r"⟨(\d+),\s*(\d+)⟩")
    patterns: dict[int, int] = {}
    hards: dict[int, int] = {}
    for shard in range(32):
        text = (LEAN / f"CoverageSummaryData{shard:02}.lean").read_text()
        pattern_text, remainder = text.split(
            "/-- Lightweight exact-table summaries", maxsplit=1
        )
        hard_text = remainder.split("/-- Every pattern summary", maxsplit=1)[0]
        for match in pair.finditer(pattern_text):
            origin, mask = map(int, match.groups())
            patterns[origin] = mask
        for match in pair.finditer(hard_text):
            origin, code = map(int, match.groups())
            hards[origin] = code
    assert len(patterns) == 1_361
    assert len(hards) == 1_088
    return sorted(patterns.items()), sorted(hards.items())


def render_summary_groups(
    summaries: list[tuple[int, int]], prefix: str, summary_type: str
) -> tuple[list[str], list[str]]:
    """Render shallow 64-entry groups and return their definitions and names."""
    definitions = []
    names = []
    for start in range(0, len(summaries), 64):
        name = f"{prefix}{start // 64:02}"
        names.append(name)
        entries = [f"⟨{origin}, {value}⟩" for origin, value in summaries[start:start + 64]]
        lines = [", ".join(entries[offset:offset + 4])
                 for offset in range(0, len(entries), 4)]
        definitions.append(
            f"private def {name} : Array {summary_type} := #[\n  "
            + ",\n  ".join(lines) + "\n]"
        )
    return definitions, names


def generate_dense_summaries() -> tuple[dict[int, int], dict[int, int]]:
    """Generate constant-time dense identifiers for both audited summary tables."""
    patterns, hards = dense_summaries()
    pattern_definitions, pattern_names = render_summary_groups(
        patterns, "densePatternSummaries", "PatternSummary"
    )
    hard_definitions, hard_names = render_summary_groups(
        hards, "denseHardSummaries", "HardSummary"
    )
    source = """/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryTypes

/-! # Dense identifiers for audited coverage summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

""" + "\n\n".join(pattern_definitions + hard_definitions) + f"""

/-- Pattern summaries indexed by compact certificate identifier. -/
def densePatternSummaryGroups : Array (Array PatternSummary) :=
  #[{', '.join(pattern_names)}]

/-- Exact summaries indexed by compact certificate identifier. -/
def denseHardSummaryGroups : Array (Array HardSummary) :=
  #[{', '.join(hard_names)}]

/-- Number of compact pattern-summary identifiers. -/
def densePatternSummaryCount : Nat := {len(patterns)}

/-- Number of compact exact-summary identifiers. -/
def denseHardSummaryCount : Nat := {len(hards)}

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
"""
    (LEAN / "CoverageCertificateDenseSummaries.lean").write_text(source)
    return (
        {origin: identifier for identifier, (origin, _mask) in enumerate(patterns)},
        {origin: identifier for identifier, (origin, _code) in enumerate(hards)},
    )


def build_branch(
    orbit: int, row_two: int, patterns: dict[int, int], hards: dict[int, int]
) -> tuple[Node, dict[str, int]]:
    """Build one deterministic preorder tree after its three fixed rows."""
    fixed = (30, bench.CANONICAL_ROWS[orbit], bench.ROW_TWO[row_two])
    code = fixed[0] | fixed[1] << 8
    assert code not in patterns
    pair_state = (0, 0)
    columns = (0,) * 8
    for row in fixed[:2]:
        pair_state = bench.add_pair(pair_state, bench.pair_mask(row))
        columns = bench.add_columns(columns, row)
    row_pairs = bench.pair_mask(fixed[2])
    assert pair_state[1] & row_pairs == 0
    pair_state = bench.add_pair(pair_state, row_pairs)
    columns = bench.add_columns(columns, fixed[2])
    code |= fixed[2] << 16
    assert bench.column_feasible(columns, ORDER, "exact")
    assert code not in patterns
    counts = {"nodes": 0, "patterns": 0, "hards": 0,
              "pair_compatible": 0, "column_surviving": 0}

    def visit(
        depth: int,
        current_code: int,
        state: tuple[int, int],
        current_columns: tuple[int, ...],
    ) -> Leaf | Node:
        if depth == len(ORDER):
            counts["hards"] += 1
            return Leaf(hards[current_code])
        counts["nodes"] += 1
        centre = ORDER[depth]
        remaining = ORDER[depth + 1 :]
        pattern_rows = 0
        pattern_origins: list[int] = []
        children: list[Leaf | Node] = []
        for index, (row, row_pairs) in enumerate(SOURCE_CHOICES[centre]):
            if state[1] & row_pairs:
                continue
            counts["pair_compatible"] += 1
            next_columns = bench.add_columns(current_columns, row)
            if not bench.column_feasible(next_columns, remaining, "exact"):
                continue
            counts["column_surviving"] += 1
            next_code = current_code | row << (8 * centre)
            if next_code in patterns:
                pattern_rows |= 1 << index
                pattern_origins.append(patterns[next_code])
                counts["patterns"] += 1
            else:
                children.append(
                    visit(
                        depth + 1,
                        next_code,
                        bench.add_pair(state, row_pairs),
                        next_columns,
                    )
                )
        return Node(
            depth, current_code, state[0], state[1],
            sum(count << (8 * target) for target, count in enumerate(current_columns)),
            pattern_rows,
            tuple(pattern_origins), tuple(children)
        )

    witness = visit(0, code, pair_state, columns)
    assert isinstance(witness, Node)
    return witness, counts


def render_witness_definitions(
    witness: Node, branch_name: str
) -> tuple[list[str], str]:
    """Render bottom-up node constants so no generated term contains a full tree."""
    definitions: list[str] = []
    next_index = 0

    def emit(node: Node) -> str:
        nonlocal next_index
        children = []
        for child in node.children:
            if isinstance(child, Leaf):
                children.append(f".leaf {child.origin}")
            else:
                children.append(emit(child))
        name = f"{branch_name}_node_{next_index:04}"
        next_index += 1
        origins = ", ".join(map(str, node.pattern_origins))
        child_source = ", ".join(children)
        definitions.append(
            f"private def {name} : SearchWitness :=\n"
            f"  .node {node.pattern_rows} [{origins}] [{child_source}]"
        )
        return name

    root_name = emit(witness)
    return definitions, root_name


def generate_light_choices() -> None:
    """Generate the pure row/pair table without any pattern payloads."""
    arrays = []
    for centre in range(8):
        values = SOURCE_CHOICES[centre]
        rows = []
        for start in range(0, 35, 4):
            group = ", ".join(f"⟨{row}, {pairs}⟩" for row, pairs in values[start:start + 4])
            rows.append("  " + group)
        arrays.append(
            f"private def searchRowChoices{centre} : Array SearchRowChoice := #[\n"
            + ",\n".join(rows)
            + "\n]"
        )
    source = """/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryTypes

/-! # Lightweight legal-row search data -/

namespace Erdos97Octagon.RawIncidence

/-- A legal row and its packed unordered-pair mask. -/
structure SearchRowChoice where
  rowMask : UInt64
  pairMask : UInt64

""" + "\n\n".join(arrays) + """

/-- All lightweight choices, in the same order as the generated pattern choices. -/
def searchRowChoices : Array (Array SearchRowChoice) := #[
  searchRowChoices0, searchRowChoices1, searchRowChoices2, searchRowChoices3,
  searchRowChoices4, searchRowChoices5, searchRowChoices6, searchRowChoices7
]

/-- Retrieve one lightweight choice by its row mask. -/
def searchChoiceForRow (centre : Vertex) (row : UInt64) : SearchRowChoice :=
  ((searchRowChoices.getD centre.val #[]).find?
    (fun choice => choice.rowMask == row)).getD ⟨0, 0⟩

end Erdos97Octagon.RawIncidence
"""
    (LEAN / "CoverageSearchRowChoices.lean").write_text(source)


def generate_certificates() -> None:
    """Generate the six certificate constants and a compact stats manifest."""
    patterns, hards = summary_maps()
    definitions = []
    manifest = {}
    for orbit, row_two in PIVOTS:
        witness, counts = build_branch(orbit, row_two, patterns, hards)
        name = f"certificate_{orbit}_{row_two}"
        node_definitions, root_name = render_witness_definitions(witness, name)
        definitions.extend(node_definitions)
        definitions.append(
            f"/-- Deterministic certificate for branch ({orbit}, {row_two}). -/\n"
            f"def {name} : BranchWitness := .search {root_name}"
        )
        manifest[f"{orbit}-{row_two}"] = counts
    source = """/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificatePrototype

/-! # Six deterministic prototype coverage certificates -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

""" + "\n\n".join(definitions) + """

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
"""
    (LEAN / "CoverageCertificatePrototypeData.lean").write_text(source)
    (ROOT / "certificate-prototype-stats.json").write_text(
        json.dumps(manifest, indent=2) + "\n"
    )


GroupedOrigins = tuple[tuple[int, ...], ...]


def flatten_claims(
    root: Node, pattern_ids: dict[int, int], hard_ids: dict[int, int]
) -> tuple[list[tuple[int, int, int, int, int, int, int, GroupedOrigins,
                                                      GroupedOrigins, GroupedOrigins,
                                                      GroupedOrigins]], int]:
    """Flatten one witness tree postorder, returning child identifiers."""
    claims = []

    def emit(node: Node) -> int:
        pattern_groups = [[] for _ in range(7)]
        child_groups = [[] for _ in range(7)]
        hard_groups = [[] for _ in range(7)]
        rejection_target_groups = [[] for _ in range(7)]
        pattern_origins = iter(node.pattern_origins)
        children = iter(node.children)
        centre = ORDER[node.depth]
        remaining = ORDER[node.depth + 1 :]
        active_rows = 0
        rejected_rows = 0
        columns = tuple((node.column_counts >> (8 * target)) & 255
                        for target in range(8))
        for index, (row, row_pairs) in enumerate(SOURCE_CHOICES[centre]):
            if node.pair_twice & row_pairs:
                continue
            next_columns = bench.add_columns(columns, row)
            if not bench.column_feasible(next_columns, remaining, "exact"):
                rejected_rows |= 1 << index
                conflicts = [target for target, count in enumerate(next_columns)
                             if count > 4 or count + sum(
                                 centre != target for centre in remaining) < 4]
                assert conflicts
                rejection_target_groups[index // 5].append(conflicts[0])
                continue
            active_rows |= 1 << index
            group = index // 5
            if node.pattern_rows & (1 << index):
                pattern_groups[group].append(pattern_ids[next(pattern_origins)])
            else:
                child = next(children)
                if isinstance(child, Leaf):
                    hard_groups[group].append(hard_ids[child.origin])
                else:
                    child_groups[group].append(emit(child))
        assert next(pattern_origins, None) is None
        assert next(children, None) is None
        identifier = len(claims)
        claims.append((
            node.depth, node.code, node.pair_once, node.pair_twice,
            active_rows, rejected_rows, node.pattern_rows,
            tuple(tuple(group) for group in rejection_target_groups),
            tuple(tuple(group) for group in pattern_groups),
            tuple(tuple(group) for group in child_groups),
            tuple(tuple(group) for group in hard_groups)
        ))
        return identifier

    root_id = emit(root)
    return claims, root_id


def lean_list(values: tuple[int, ...] | list[int]) -> str:
    """Render a compact list of decimal naturals."""
    return "[" + ", ".join(map(str, values)) + "]"


def lean_groups(groups: GroupedOrigins) -> str:
    """Render seven compact word-local lists."""
    return "#[" + ", ".join(lean_list(group) for group in groups) + "]"


def generate_local_claims() -> None:
    """Generate flat postorder claims and six independent chunk-audit modules."""
    patterns, hards = summary_maps()
    pattern_ids, hard_ids = generate_dense_summaries()
    definitions = []
    probes = {}
    for orbit, row_two in PIVOTS:
        witness, _counts = build_branch(orbit, row_two, patterns, hards)
        claims, root_id = flatten_claims(witness, pattern_ids, hard_ids)
        prefix = f"branchClaims_{orbit}_{row_two}"
        names = []
        for identifier, claim in enumerate(claims):
            (depth, code, pair_once, pair_twice, active_rows, rejected_rows,
             pattern_rows, rejection_targets, origins, child_ids, hard_origins) = claim
            name = f"{prefix}_node_{identifier:04}"
            names.append(name)
            definitions.append(
                f"private def {name} : NodeClaim :=\n"
                f"  ⟨{depth}, {code}, {pair_once}, {pair_twice}, {active_rows}, "
                f"{rejected_rows}, {pattern_rows}, {lean_groups(rejection_targets)}, "
                f"{lean_groups(origins)}, "
                f"{lean_groups(child_ids)}, {lean_groups(hard_origins)}⟩"
            )
        group_names = []
        for start in range(0, len(names), 64):
            group_name = f"{prefix}_group_{start // 64:02}"
            group_names.append(group_name)
            definitions.append(
                f"private def {group_name} : Array NodeClaim :=\n"
                f"  #[{', '.join(names[start:start + 64])}]"
            )
        definitions.append(
            f"/-- Flat postorder claims for branch ({orbit}, {row_two}). -/\n"
            f"def {prefix} : BranchClaims :=\n"
            f"  ⟨#[{', '.join(group_names)}], {len(names)}, {root_id}⟩"
        )
        probe_lines = [
            "import LeanPool.Erdos97ConvexOctagon.CoverageCertificateLocalPrototypeData",
            "open Erdos97Octagon.RawIncidence.StaticDirectCoverage",
            "",
            f"example : branchClaimRootValidB {orbit} {row_two} {prefix} = true := by rfl",
        ]
        chunk_size = 1
        for start in range(0, len(claims), chunk_size):
            count = min(chunk_size, len(claims) - start)
            probe_lines.append(
                f"example : nodeClaimChunkValidB {prefix} {start} {count} = true := by rfl"
            )
        probes[f"LocalCertificateProbe{orbit}{row_two}.lean"] = "\n".join(probe_lines) + "\n"

    source = """/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateLocalPrototype

/-! # Six flat prototype coverage certificates -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

""" + "\n\n".join(definitions) + """

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
"""
    (LEAN / "CoverageCertificateLocalPrototypeData.lean").write_text(source)
    for name, probe in probes.items():
        (ROOT / name).write_text(probe)


if __name__ == "__main__":
    generate_light_choices()
    generate_certificates()
    generate_local_claims()
