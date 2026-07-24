"""Orchestrate generation of the static exposition site.

Reads the extractor JSONL dump, the project registry
(``LeanPool/projects.yml``) and the Lean sources under the repository root,
computes per-project layered layouts and statistics, and writes the site
described in ``SCHEMA.md``: ``data/projects/<Project>.json`` shards,
``data/index.json``, ``data/decls.json``, static assets copied verbatim from
``static/``, and one instantiated ``p/<Project>/index.html`` per project.
"""

from __future__ import annotations

import html
import json
import logging
import shutil
import string
from collections import Counter
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path

import yaml

from lean_pool.exposition.layout import compute_layout
from lean_pool.exposition.source_text import (
    ModuleSkeleton,
    SourceFile,
    module_skeleton,
    statement_slice,
)

logger = logging.getLogger(__name__)

PACKAGE_DIRECTORY = Path(__file__).resolve().parent
DEFAULT_STATIC_DIRECTORY = PACKAGE_DIRECTORY / "static"
DEFAULT_TEMPLATES_DIRECTORY = PACKAGE_DIRECTORY / "templates"


CARD_SOURCE_FIELDS = ("title", "authors", "doi", "arxiv", "url", "github_repo")


@dataclass
class ProjectCard:
    """Registry metadata for one project (from ``LeanPool/projects.yml``)."""

    title: str | None
    provenance: str | None
    card: dict | None = None
    main_declarations: list[str] | None = None
    main_results: list[dict] | None = None


@dataclass
class SiteSummary:
    """Totals reported after a site generation run."""

    projects: int
    decls: int
    edges: int


class SourceCache:
    """Read and cache Lean source files by module name (one read per file)."""

    def __init__(self, repo_root: Path) -> None:
        """Remember the repository root that module paths resolve against."""
        self._repo_root = repo_root
        self._files: dict[str, SourceFile | None] = {}

    def get(self, module: str) -> SourceFile | None:
        """Return the parsed source for ``module``, or ``None`` if missing."""
        if module not in self._files:
            path = self._repo_root.joinpath(*module.split(".")).with_suffix(".lean")
            if path.is_file():
                text = path.read_text(encoding="utf-8")
                self._files[module] = SourceFile.from_text(text)
            else:
                logger.warning("source file missing for module %s: %s", module, path)
                self._files[module] = None
        return self._files[module]


def read_dump(dump_path: Path) -> list[dict]:
    """Parse the extractor JSONL dump into a list of record dicts.

    Records are deduplicated by ``id`` (first occurrence wins): a constant
    declared textually in two modules would otherwise become two nodes.
    """
    records: list[dict] = []
    seen_ids: set[str] = set()
    with Path(dump_path).open(encoding="utf-8") as dump_file:
        for line in dump_file:
            stripped = line.strip()
            if not stripped:
                continue
            record = json.loads(stripped)
            if record["id"] in seen_ids:
                logger.warning("duplicate dump record dropped: %s", record["id"])
                continue
            seen_ids.add(record["id"])
            records.append(record)
    return records


def project_for_module(module: str) -> str:
    """Return the project slug a module belongs to (second name component)."""
    parts = module.split(".")
    return parts[1] if len(parts) > 1 else parts[0]


def group_records_by_project(records: list[dict]) -> dict[str, list[dict]]:
    """Group dump records into per-project lists keyed by slug."""
    grouped: dict[str, list[dict]] = {}
    for record in records:
        grouped.setdefault(project_for_module(record["m"]), []).append(record)
    return grouped


def _card_payload(entry: dict) -> dict:
    """Build the shard ``card`` object (schema 1.1) from a registry entry."""
    card: dict = {}
    for field in ("authors", "license", "branch", "summary", "tags", "msc", "status"):
        value = entry.get(field)
        if value:
            card[field] = value
    source = entry.get("source") or {}
    source_payload = {
        field: source[field] for field in CARD_SOURCE_FIELDS if source.get(field)
    }
    if source_payload:
        card["source"] = source_payload
    return card


def load_project_cards(projects_yml_path: Path) -> dict[str, ProjectCard]:
    """Load registry metadata per project, keyed by entry-module last component."""
    if not projects_yml_path.is_file():
        logger.warning("project registry not found: %s", projects_yml_path)
        return {}
    data = yaml.safe_load(projects_yml_path.read_text(encoding="utf-8")) or {}
    cards: dict[str, ProjectCard] = {}
    for entry in data.get("projects", []):
        entry_module = entry.get("entry_module") or ""
        if not entry_module:
            continue
        slug = entry_module.split(".")[-1]
        main_results = [
            {
                "declaration": result.get("declaration"),
                "informal": result.get("informal"),
            }
            for result in entry.get("main_results") or []
            if result.get("declaration")
        ]
        cards[slug] = ProjectCard(
            title=entry.get("title"),
            provenance=entry.get("provenance"),
            card=_card_payload(entry),
            main_declarations=list(entry.get("main_declarations") or []),
            main_results=main_results,
        )
    return cards


def _resolve_main_results(card: ProjectCard | None, nodes: list[dict]) -> list[dict]:
    """Resolve card main declarations/results to node ids (schema 1.1).

    Returns one entry per declaration in the union of ``main_declarations``
    and ``main_results``, keeping the informal statement when the card has
    one. Resolved ids also flag their node with ``main: true``.
    """
    if card is None:
        return []
    informal_by_name = {
        result["declaration"]: result.get("informal")
        for result in card.main_results or []
    }
    names: list[str] = list(informal_by_name)
    for name in card.main_declarations or []:
        if name not in informal_by_name:
            names.append(name)
    id_by_name: dict[str, int] = {}
    for node_id, node in enumerate(nodes):
        id_by_name.setdefault(node.get("full", node["name"]), node_id)
        id_by_name.setdefault(node["name"], node_id)
    resolved = []
    for name in names:
        node_id = id_by_name.get(name)
        if node_id is None:
            logger.warning("main declaration not found in shard: %s", name)
        else:
            nodes[node_id]["main"] = True
        entry: dict = {"id": node_id, "name": name}
        informal = informal_by_name.get(name)
        if informal:
            entry["informal"] = informal
        resolved.append(entry)
    return resolved


def _sorted_records(records: list[dict]) -> list[dict]:
    """Order records by (module, start line, name) — the shard id order."""
    return sorted(
        records, key=lambda record: (record["m"], record["r"][0], record["n"])
    )


def _remap_dependencies(records: list[dict], key: str = "deps") -> list[list[int]]:
    """Map dependency ids under ``key`` to shard-local indices.

    Dangling and self references are dropped. Records without the key yield
    an empty list.
    """
    index_of = {record["id"]: index for index, record in enumerate(records)}
    dependency_lists: list[list[int]] = []
    for index, record in enumerate(records):
        indices = {
            index_of[dependency]
            for dependency in record.get(key, [])
            if dependency in index_of
        }
        indices.discard(index)
        dependency_lists.append(sorted(indices))
    return dependency_lists


def _refined_kind_and_statement(
    record: dict, source: SourceFile | None
) -> tuple[str, str, tuple[int, int] | None]:
    """Refine the extractor kind and slice the statement from the source."""
    if source is None:
        return record["k"], "", None
    return statement_slice(source, record["r"], record["s"], record["k"])


# Declarations whose proofs the minimal Lean file replaces with `sorry`.
PROOF_KINDS = frozenset({"theorem", "lemma"})


def _attach_minimal_file_fields(
    nodes: list[dict],
    skeletons: dict[int, ModuleSkeleton | None],
) -> None:
    """Add per-node minimal-file fields: ``span`` and ``host`` (schema 1.2).

    ``span`` widens a node's verbatim slice to its enclosing top-level
    ``mutual`` block. ``host`` points a generated declaration (mid-line
    range, blanked statement) at the human-written declaration whose source
    contains it, so the builder can emit the host instead.
    """
    by_module: dict[int, list[int]] = {}
    for node_id, node in enumerate(nodes):
        by_module.setdefault(node["module"], []).append(node_id)
    for module_index, node_ids in by_module.items():
        skeleton = skeletons.get(module_index)
        if skeleton is not None:
            for start_line, end_line in skeleton.mutual_spans:
                for node_id in node_ids:
                    node = nodes[node_id]
                    if start_line <= node["line"] and node["endLine"] <= end_line:
                        node["span"] = [start_line, end_line]
        if skeleton is not None and skeleton.prefix_blocks:
            # Lean's declaration range excludes a bare `open/set_option/
            # attribute … in` prefix on the preceding lines; reattach it.
            # The prefix's following command may start inside the node's
            # range at a later line than node["line"] when a doc comment
            # sits between them, hence the range check. Chains supported.
            prefix_by_next_line = {
                next_line: (line, text)
                for line, next_line, text in skeleton.prefix_blocks
            }
            for node_id in node_ids:
                node = nodes[node_id]
                chain_end = None
                for line, next_line, text in skeleton.prefix_blocks:
                    if node["line"] <= next_line <= node["endLine"]:
                        chain_end = (line, text)
                        break
                if chain_end is None:
                    continue
                parts = [chain_end[1]]
                cursor = chain_end[0]
                while cursor in prefix_by_next_line:
                    line, text = prefix_by_next_line[cursor]
                    parts.append(text)
                    cursor = line
                node["prefix"] = "\n".join(reversed(parts))
        for node_id in node_ids:
            node = nodes[node_id]
            generated = node["statement"] == "" and "stmtEnd" not in node
            if not generated:
                continue
            host = None
            for other_id in node_ids:
                other = nodes[other_id]
                if other_id == node_id or other["statement"] == "":
                    continue
                if other["line"] <= node["line"] <= other["endLine"]:
                    if host is None or other["line"] >= nodes[host]["line"]:
                        host = other_id
            if host is not None:
                node["host"] = host


def _build_node(
    record: dict,
    kind: str,
    statement: str,
    statement_end: tuple[int, int] | None,
    module_index: int,
    dependencies: list[int],
    type_dependencies: list[int] | None,
    layer: int,
    order: int,
) -> dict:
    """Build one shard ``decls`` entry with the schema's key order."""
    node: dict = {"name": record["n"]}
    if record["id"] != record["n"]:
        node["full"] = record["id"]
    node["kind"] = kind
    node["module"] = module_index
    node["line"] = record["r"][0]
    node["endLine"] = record["r"][2]
    if "d" in record:
        node["doc"] = record["d"]
    node["statement"] = statement
    if statement_end is not None and kind in PROOF_KINDS:
        node["stmtEnd"] = list(statement_end)
    if record.get("p"):
        node["private"] = True
    node["deps"] = dependencies
    if type_dependencies is not None and kind in PROOF_KINDS:
        node["tdeps"] = type_dependencies
    node["ext"] = record.get("ext", 0)
    node["layer"] = layer
    node["order"] = order
    return node


def _kind_counts(kinds: list[str]) -> dict[str, int]:
    """Count kinds, ordered by descending count then name for determinism."""
    counts = Counter(kinds)
    return dict(sorted(counts.items(), key=lambda item: (-item[1], item[0])))


def _closed_module_list(
    slug: str, project_modules: list[str], source_cache: SourceCache
) -> tuple[list[str], dict[int, ModuleSkeleton | None]]:
    """Close the module list under same-project imports; return skeletons.

    Modules without exposed declarations (notation- or attribute-only files)
    still contribute context commands, so the minimal-file builder needs
    their skeletons too; they are appended after the declaration-bearing
    modules.
    """
    modules = list(project_modules)
    known = set(modules)
    project_prefix = f"LeanPool.{slug}."
    skeletons: dict[int, ModuleSkeleton | None] = {}
    index = 0
    while index < len(modules):
        source = source_cache.get(modules[index])
        skeleton = module_skeleton(source) if source else None
        skeletons[index] = skeleton
        if skeleton is not None:
            for imported in skeleton.local_imports:
                if imported.startswith(project_prefix) and imported not in known:
                    known.add(imported)
                    modules.append(imported)
        index += 1
    return modules, skeletons


def build_project_shard(
    slug: str,
    records: list[dict],
    card: ProjectCard | None,
    source_cache: SourceCache,
    commit: str = "main",
) -> dict:
    """Build one ``data/projects/<Project>.json`` payload per SCHEMA.md."""
    ordered = _sorted_records(records)
    declaration_modules = sorted({record["m"] for record in ordered})
    modules, skeletons = _closed_module_list(slug, declaration_modules, source_cache)
    module_indices = {module: index for index, module in enumerate(modules)}
    dependency_lists = _remap_dependencies(ordered)
    type_dependency_lists = _remap_dependencies(ordered, key="tdeps")
    layout = compute_layout(dependency_lists)
    nodes = []
    for index, record in enumerate(ordered):
        source = source_cache.get(record["m"])
        kind, statement, statement_end = _refined_kind_and_statement(record, source)
        nodes.append(
            _build_node(
                record,
                kind,
                statement,
                statement_end,
                module_indices[record["m"]],
                dependency_lists[index],
                type_dependency_lists[index] if "tdeps" in record else None,
                layout.node_layers[index],
                layout.node_orders[index],
            )
        )
    _attach_minimal_file_fields(nodes, skeletons)
    node_count = len(nodes)
    average = sum(layout.node_layers) / node_count if node_count else 0.0
    stats = {
        "nodes": node_count,
        "edges": sum(len(dependencies) for dependencies in dependency_lists),
        "maxDepth": max(layout.node_layers, default=0),
        "avgDepth": round(average, 2),
        "kinds": _kind_counts([node["kind"] for node in nodes]),
    }
    main_results = _resolve_main_results(card, nodes)
    module_data = []
    for index in range(len(modules)):
        skeleton = skeletons[index]
        uses = sorted(
            module_indices[imported]
            for imported in (skeleton.local_imports if skeleton else [])
            if imported in module_indices
        )
        module_data.append(
            {
                "imports": skeleton.external_imports if skeleton else [],
                "uses": uses,
                "contexts": [list(entry) for entry in skeleton.contexts]
                if skeleton
                else [],
            }
        )
    return {
        "schema": 1,
        "project": slug,
        "commit": commit,
        "title": card.title if card else None,
        "provenance": card.provenance if card else None,
        "card": card.card if card and card.card else None,
        "mainResults": main_results,
        "stats": stats,
        "modules": modules,
        "moduleData": module_data,
        "layers": layout.layer_sizes,
        "decls": nodes,
    }


def build_index(shards: dict[str, dict], commit: str) -> dict:
    """Build the ``data/index.json`` payload (projects sorted by slug)."""
    project_rows = []
    total_kinds: Counter[str] = Counter()
    for slug in sorted(shards):
        shard = shards[slug]
        stats = shard["stats"]
        total_kinds.update(stats["kinds"])
        card = shard.get("card") or {}
        project_rows.append(
            {
                "slug": slug,
                "title": shard["title"],
                "provenance": shard["provenance"],
                "nodes": stats["nodes"],
                "edges": stats["edges"],
                "maxDepth": stats["maxDepth"],
                "avgDepth": stats["avgDepth"],
                "authors": card.get("authors"),
                "license": card.get("license"),
                "branch": card.get("branch"),
                "mainResults": len(shard.get("mainResults") or []),
            }
        )
    totals = {
        "projects": len(project_rows),
        "decls": sum(row["nodes"] for row in project_rows),
        "edges": sum(row["edges"] for row in project_rows),
        "maxDepth": max((row["maxDepth"] for row in project_rows), default=0),
        "kinds": dict(
            sorted(total_kinds.items(), key=lambda item: (-item[1], item[0]))
        ),
    }
    generated = datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")
    return {
        "schema": 1,
        "commit": commit,
        "generated": generated,
        "totals": totals,
        "projects": project_rows,
    }


def build_declaration_index(shards: dict[str, dict], index: dict) -> dict:
    """Build the compact ``data/decls.json`` payload for the viewer."""
    kinds = list(index["totals"]["kinds"])
    kind_indices = {kind: position for position, kind in enumerate(kinds)}
    slugs = [row["slug"] for row in index["projects"]]
    rows = []
    for project_position, slug in enumerate(slugs):
        for declaration_id, node in enumerate(shards[slug]["decls"]):
            rows.append(
                [
                    node["name"],
                    kind_indices[node["kind"]],
                    project_position,
                    declaration_id,
                ]
            )
    return {"schema": 1, "kinds": kinds, "projects": slugs, "decls": rows}


def _write_json(path: Path, payload: dict) -> None:
    """Write compact JSON (preserving insertion key order) to ``path``."""
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
    path.write_text(text, encoding="utf-8")


def _write_project_pages(
    out_dir: Path, shards: dict[str, dict], template_path: Path
) -> None:
    """Instantiate ``templates/project.html`` once per project."""
    template = string.Template(template_path.read_text(encoding="utf-8"))
    for slug, shard in shards.items():
        title = shard["title"] or slug
        page = template.safe_substitute(SLUG=slug, TITLE=html.escape(title))
        page_directory = out_dir / "p" / slug
        page_directory.mkdir(parents=True, exist_ok=True)
        (page_directory / "index.html").write_text(page, encoding="utf-8")


def generate_site(
    dump_path: Path,
    repo_root: Path,
    out_dir: Path,
    commit: str = "main",
    static_dir: Path | None = None,
    templates_dir: Path | None = None,
) -> SiteSummary:
    """Generate the whole static site; return the run's totals.

    ``static_dir`` and ``templates_dir`` default to the package's ``static/``
    and ``templates/`` directories; tests inject fakes through them.
    """
    static_directory = Path(static_dir) if static_dir else DEFAULT_STATIC_DIRECTORY
    templates_directory = (
        Path(templates_dir) if templates_dir else DEFAULT_TEMPLATES_DIRECTORY
    )
    template_path = templates_directory / "project.html"
    if not static_directory.is_dir():
        raise FileNotFoundError(f"static asset directory not found: {static_directory}")
    if not template_path.is_file():
        raise FileNotFoundError(f"project page template not found: {template_path}")
    grouped = group_records_by_project(read_dump(dump_path))
    cards = load_project_cards(Path(repo_root) / "LeanPool" / "projects.yml")
    source_cache = SourceCache(Path(repo_root))
    shards = {
        slug: build_project_shard(slug, records, cards.get(slug), source_cache, commit)
        for slug, records in grouped.items()
    }
    index = build_index(shards, commit)
    out_directory = Path(out_dir)
    out_directory.mkdir(parents=True, exist_ok=True)
    shutil.copytree(static_directory, out_directory, dirs_exist_ok=True)
    for slug, shard in shards.items():
        _write_json(out_directory / "data" / "projects" / f"{slug}.json", shard)
    _write_json(out_directory / "data" / "index.json", index)
    _write_json(
        out_directory / "data" / "decls.json",
        build_declaration_index(shards, index),
    )
    _write_project_pages(out_directory, shards, template_path)
    return SiteSummary(
        projects=index["totals"]["projects"],
        decls=index["totals"]["decls"],
        edges=index["totals"]["edges"],
    )
