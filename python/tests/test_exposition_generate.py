"""End-to-end tests for the exposition site generator."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from lean_pool.exposition.generate import SiteSummary, generate_site

ALPHA_ONE = """lemma a1 : True := trivial

theorem a2 : True := a1

/-- Third. -/
def a3 : Nat :=
  2
"""

ALPHA_TWO = """theorem a4 : True := by
  exact a2
"""

BETA = """def b1 : Nat := 1

lemma b2 : b1 = 1 := rfl

private theorem b3 : True := trivial
"""

PROJECTS_YML = """projects:
  - slug: alpha-project
    title: Alpha & Co
    entry_module: LeanPool.Alpha
    provenance: AI
    authors:
      - Ada Lovelace
    license: Apache-2.0
    branch: order theory
    summary: Toy project.
    tags:
      - toy
    msc:
      - 06B35
    status: verified
    source:
      title: A Paper
      doi: 10.1000/xyz
      github_repo: ada/alpha
    main_declarations:
      - a2
      - a3
    main_results:
      - declaration: a2
        informal: Truth holds, twice.
      - declaration: NotInShard.thm
        informal: An unresolved headline.
"""

TEMPLATE = (
    "<title>${TITLE}</title>"
    '<div data-slug="${SLUG}">${TITLE}</div>'
    "<script>const label = `${d.name}`;</script>"
)

# Deliberately out of source order; ids are assigned after sorting by
# (module, line, name). a4 carries a dangling and a self dependency.
RECORDS = [
    {
        "id": "a4",
        "n": "a4",
        "m": "LeanPool.Alpha.Two",
        "k": "theorem",
        "r": [1, 0, 2, 10],
        "s": [1, 8],
        "deps": ["a2", "a4", "Missing.dep"],
        "ext": 3,
    },
    {
        "id": "a2",
        "n": "a2",
        "m": "LeanPool.Alpha.One",
        "k": "theorem",
        "r": [3, 0, 3, 23],
        "s": [3, 8],
        "deps": ["a1"],
        "ext": 2,
    },
    {
        "id": "a1",
        "n": "a1",
        "m": "LeanPool.Alpha.One",
        "k": "theorem",
        "r": [1, 0, 1, 26],
        "s": [1, 6],
        "deps": [],
        "tdeps": [],
        "ext": 1,
    },
    {
        "id": "a3",
        "n": "a3",
        "m": "LeanPool.Alpha.One",
        "k": "def",
        "r": [5, 0, 7, 3],
        "s": [6, 4],
        "d": "Third.",
        "deps": [],
        "ext": 0,
    },
    {
        "id": "b1",
        "n": "b1",
        "m": "LeanPool.Beta",
        "k": "def",
        "r": [1, 0, 1, 17],
        "s": [1, 4],
        "deps": [],
        "ext": 0,
    },
    {
        "id": "b2",
        "n": "b2",
        "m": "LeanPool.Beta",
        "k": "theorem",
        "r": [3, 0, 3, 24],
        "s": [3, 6],
        "deps": ["b1"],
        "ext": 1,
    },
    {
        "id": "_private.LeanPool.Beta.0.b3",
        "n": "b3",
        "m": "LeanPool.Beta",
        "k": "theorem",
        "r": [5, 0, 5, 36],
        "s": [5, 16],
        "p": True,
        "deps": [],
        "ext": 1,
    },
]


def _write_inputs(tmp_path: Path) -> tuple[Path, Path, Path, Path]:
    """Create the fake repo, static, templates, and dump under tmp_path."""
    repo = tmp_path / "repo"
    (repo / "LeanPool" / "Alpha").mkdir(parents=True)
    (repo / "LeanPool" / "Alpha" / "One.lean").write_text(ALPHA_ONE)
    (repo / "LeanPool" / "Alpha" / "Two.lean").write_text(ALPHA_TWO)
    (repo / "LeanPool" / "Beta.lean").write_text(BETA)
    (repo / "LeanPool" / "projects.yml").write_text(PROJECTS_YML)
    static = tmp_path / "static"
    (static / "decls").mkdir(parents=True)
    (static / "assets").mkdir()
    (static / "index.html").write_text("LANDING")
    (static / "decls" / "index.html").write_text("DECLS")
    (static / "assets" / "style.css").write_text("/*css*/")
    templates = tmp_path / "templates"
    templates.mkdir()
    (templates / "project.html").write_text(TEMPLATE)
    dump = tmp_path / "dump.jsonl"
    dump.write_text("\n".join(json.dumps(record) for record in RECORDS) + "\n")
    return repo, static, templates, dump


@pytest.fixture
def site(tmp_path: Path) -> tuple[Path, SiteSummary]:
    """Generate the site from the synthetic dump; return (out_dir, summary)."""
    repo, static, templates, dump = _write_inputs(tmp_path)
    out = tmp_path / "out"
    summary = generate_site(
        dump,
        repo,
        out,
        commit="deadbeef",
        static_dir=static,
        templates_dir=templates,
    )
    return out, summary


def _load(out: Path, relative: str) -> dict:
    """Load one generated JSON file."""
    return json.loads((out / relative).read_text())


def test_summary_totals(site: tuple[Path, SiteSummary]) -> None:
    """The returned summary reports pool-wide totals."""
    _, summary = site
    assert summary == SiteSummary(projects=2, decls=7, edges=3)


def test_project_shard_schema_and_stats(site: tuple[Path, SiteSummary]) -> None:
    """The Alpha shard has schema key order, stats, layout, and remapped deps."""
    out, _ = site
    shard = _load(out, "data/projects/Alpha.json")
    assert list(shard) == [
        "schema",
        "project",
        "commit",
        "title",
        "provenance",
        "card",
        "mainResults",
        "stats",
        "modules",
        "moduleData",
        "layers",
        "decls",
    ]
    assert shard["commit"] == "deadbeef"
    assert len(shard["moduleData"]) == len(shard["modules"])
    assert shard["schema"] == 1
    assert shard["project"] == "Alpha"
    assert shard["title"] == "Alpha & Co"
    assert shard["provenance"] == "AI"
    assert shard["stats"] == {
        "nodes": 4,
        "edges": 2,
        "maxDepth": 2,
        "avgDepth": 0.75,
        "kinds": {"theorem": 2, "def": 1, "lemma": 1},
    }
    assert shard["modules"] == ["LeanPool.Alpha.One", "LeanPool.Alpha.Two"]
    assert shard["layers"] == [2, 1, 1]
    names = [node["name"] for node in shard["decls"]]
    assert names == ["a1", "a2", "a3", "a4"]
    a4 = shard["decls"][3]
    assert a4["deps"] == [1]  # dangling and self deps dropped, id remapped
    assert a4["layer"] == 2
    assert a4["module"] == 1
    assert shard["decls"][1]["deps"] == [0]


def test_card_and_main_results(site: tuple[Path, SiteSummary]) -> None:
    """Shards carry the registry card and resolved main results (schema 1.1)."""
    out, _ = site
    shard = _load(out, "data/projects/Alpha.json")
    assert shard["card"] == {
        "authors": ["Ada Lovelace"],
        "license": "Apache-2.0",
        "branch": "order theory",
        "summary": "Toy project.",
        "tags": ["toy"],
        "msc": ["06B35"],
        "status": "verified",
        "source": {
            "title": "A Paper",
            "doi": "10.1000/xyz",
            "github_repo": "ada/alpha",
        },
    }
    # a2 (id 1) keeps its informal text; a3 (id 2) comes from
    # main_declarations only; the unknown name stays unresolved with id null.
    assert shard["mainResults"] == [
        {"id": 1, "name": "a2", "informal": "Truth holds, twice."},
        {"id": None, "name": "NotInShard.thm", "informal": "An unresolved headline."},
        {"id": 2, "name": "a3"},
    ]
    decls = shard["decls"]
    assert decls[1].get("main") is True
    assert decls[2].get("main") is True
    assert "main" not in decls[0]
    beta = _load(out, "data/projects/Beta.json")
    assert beta["card"] is None
    assert beta["mainResults"] == []


def test_declaration_nodes(site: tuple[Path, SiteSummary]) -> None:
    """Node rows carry refined kinds, statements, docs, and privacy flags."""
    out, _ = site
    alpha = _load(out, "data/projects/Alpha.json")["decls"]
    assert alpha[0]["kind"] == "lemma"
    assert alpha[0]["statement"] == "lemma a1 : True"
    assert alpha[2]["doc"] == "Third."
    assert alpha[2]["statement"] == "def a3 : Nat"
    assert alpha[2]["line"] == 5
    assert alpha[2]["endLine"] == 7
    assert list(alpha[2]) == [
        "name",
        "kind",
        "module",
        "line",
        "endLine",
        "doc",
        "statement",
        "deps",
        "ext",
        "layer",
        "order",
        "main",  # a3 is one of the card's main declarations
    ]
    # a1 is a lemma: it carries the statement boundary and type-only deps.
    assert alpha[0]["stmtEnd"] == [1, 16]  # the `:=` in `lemma a1 : True := …`
    assert alpha[0]["tdeps"] == []
    assert "stmtEnd" not in alpha[2]  # defs keep their bodies — no boundary field
    beta = _load(out, "data/projects/Beta.json")["decls"]
    b3 = beta[2]
    assert b3["full"] == "_private.LeanPool.Beta.0.b3"
    assert b3["private"] is True
    assert b3["statement"] == "theorem b3 : True"
    assert list(b3) == [
        "name",
        "full",
        "kind",
        "module",
        "line",
        "endLine",
        "statement",
        "stmtEnd",
        "private",
        "deps",
        "ext",
        "layer",
        "order",
    ]


def test_index_json(site: tuple[Path, SiteSummary]) -> None:
    """index.json carries the commit, totals, and per-project rows by slug."""
    out, _ = site
    index = _load(out, "data/index.json")
    assert index["schema"] == 1
    assert index["commit"] == "deadbeef"
    assert index["generated"].endswith("Z")
    assert index["totals"] == {
        "projects": 2,
        "decls": 7,
        "edges": 3,
        "maxDepth": 2,
        "kinds": {"theorem": 3, "def": 2, "lemma": 2},
    }
    assert [row["slug"] for row in index["projects"]] == ["Alpha", "Beta"]
    assert index["projects"][0] == {
        "slug": "Alpha",
        "title": "Alpha & Co",
        "provenance": "AI",
        "nodes": 4,
        "edges": 2,
        "maxDepth": 2,
        "avgDepth": 0.75,
        "authors": ["Ada Lovelace"],
        "license": "Apache-2.0",
        "branch": "order theory",
        "mainResults": 3,
    }
    beta_row = index["projects"][1]
    assert beta_row["title"] is None  # pseudo-project: no registry card
    assert beta_row["provenance"] is None
    assert beta_row["avgDepth"] == 0.33
    assert beta_row["authors"] is None
    assert beta_row["license"] is None
    assert beta_row["mainResults"] == 0


def test_decls_json(site: tuple[Path, SiteSummary]) -> None:
    """decls.json rows are [name, kindIdx, projectIdx, declId]."""
    out, _ = site
    declarations = _load(out, "data/decls.json")
    assert declarations["schema"] == 1
    assert declarations["kinds"] == ["theorem", "def", "lemma"]
    assert declarations["projects"] == ["Alpha", "Beta"]
    assert declarations["decls"] == [
        ["a1", 2, 0, 0],
        ["a2", 0, 0, 1],
        ["a3", 1, 0, 2],
        ["a4", 0, 0, 3],
        ["b1", 1, 1, 0],
        ["b2", 2, 1, 1],
        ["b3", 0, 1, 2],
    ]


def test_static_copy_and_project_pages(site: tuple[Path, SiteSummary]) -> None:
    """Static files are copied verbatim; project pages are instantiated."""
    out, _ = site
    assert (out / "index.html").read_text() == "LANDING"
    assert (out / "decls" / "index.html").read_text() == "DECLS"
    assert (out / "assets" / "style.css").read_text() == "/*css*/"
    alpha_page = (out / "p" / "Alpha" / "index.html").read_text()
    assert "<title>Alpha &amp; Co</title>" in alpha_page
    assert 'data-slug="Alpha"' in alpha_page
    assert "`${d.name}`" in alpha_page  # JS template literals survive
    beta_page = (out / "p" / "Beta" / "index.html").read_text()
    assert "<title>Beta</title>" in beta_page  # title falls back to the slug
    assert 'data-slug="Beta"' in beta_page


def test_missing_static_directory_raises(tmp_path: Path) -> None:
    """A missing static directory fails loudly instead of emitting a site."""
    repo, _, templates, dump = _write_inputs(tmp_path)
    with pytest.raises(FileNotFoundError, match="static asset directory"):
        generate_site(
            dump,
            repo,
            tmp_path / "out2",
            static_dir=tmp_path / "no-such-static",
            templates_dir=templates,
        )
