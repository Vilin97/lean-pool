"""Tests for the candidates README renderer."""

from __future__ import annotations

from pathlib import Path

import pytest

from lean_pool.aggregator.render import (
    BEGIN_MARKER,
    END_MARKER,
    canonical_key,
    count_lean_loc,
    load_decisions,
    load_pool_repos,
    package_key,
    read_toolchain,
    render_table,
    update_readme,
)

_UNSET = object()


def _package(
    *,
    full_name: str = "acme/demo",
    stars: int = 0,
    description: str | None = "A demo package.",
    license_name: str | None = "MIT",
    repo_url: str | None = _UNSET,  # type: ignore[assignment]
    versions: list[dict] | None = None,
    builds: list[dict] | None = None,
) -> dict:
    """Build a minimal package fixture.

    By default ``repo_url`` is derived from ``full_name`` so each
    fixture corresponds to a distinct GitHub repo (and therefore a
    distinct canonical key). Pass ``repo_url=None`` to omit sources, or
    a string to override.
    """
    owner, name = full_name.split("/")
    if repo_url is _UNSET:
        repo_url = f"https://github.com/{full_name}"
    sources = []
    if repo_url is not None:
        sources.append(
            {
                "type": "git",
                "host": "github",
                "id": "R_1",
                "fullName": full_name,
                "repoUrl": repo_url,
                "gitUrl": repo_url,
                "defaultBranch": "main",
            }
        )
    return {
        "name": name,
        "owner": owner,
        "fullName": full_name,
        "description": description,
        "keywords": [],
        "homepage": None,
        "license": license_name,
        "createdAt": "2026-01-01T00:00:00Z",
        "updatedAt": "2026-05-01T00:00:00Z",
        "stars": stars,
        "sources": sources,
        "versions": [] if versions is None else versions,
        "builds": [] if builds is None else builds,
        "dependents": [],
    }


def _manifest(packages: list[dict]) -> dict:
    return {
        "bundledAt": "2026-05-09T00:00:00Z",
        "toolchains": [],
        "packageAliases": {},
        "packages": packages,
    }


def test_render_table_sorts_by_stars_descending_then_name() -> None:
    """Highest-starred packages come first; ties break alphabetically."""
    manifest = _manifest(
        [
            _package(full_name="acme/low", stars=2),
            _package(full_name="zeta/high", stars=10),
            _package(full_name="alpha/high", stars=10),
        ]
    )

    table = render_table(manifest)

    body_lines = [line for line in table.splitlines() if line.startswith("|")][2:]
    package_order = [line.split("|")[2].strip() for line in body_lines]
    # Expect markdown-link cells; verify the package names appear in order.
    assert "alpha/high" in package_order[0]
    assert "zeta/high" in package_order[1]
    assert "acme/low" in package_order[2]


def test_render_table_renders_updated_date_and_build_glyph() -> None:
    """The table shows the updatedAt date and the latest build glyph."""
    manifest = _manifest(
        [
            _package(
                stars=1,
                builds=[{"toolchain": "v4.30.0", "built": True, "runAt": "2026-05-02"}],
            )
        ]
    )
    # The fixture's updatedAt is fixed at 2026-05-01T00:00:00Z.
    table = render_table(manifest)

    assert "2026-05-01" in table
    assert " ✓ " in table


def test_render_table_handles_missing_optional_fields() -> None:
    """Packages without versions, builds, or license render blanks/dashes."""
    manifest = _manifest(
        [_package(license_name=None, versions=[], builds=[], description=None)]
    )

    table = render_table(manifest)

    package_row = next(line for line in table.splitlines() if "acme/demo" in line)
    cells = [cell.strip() for cell in package_row.split("|")]
    # Build glyph sits in the Build column (index 8); the trailing In
    # Pool cell is blank when no pool_repos is provided.
    assert cells[8] == "–"
    assert cells[9] == ""


def test_render_table_escapes_pipes_and_newlines_in_description() -> None:
    """Pipes are escaped and newlines collapsed so cells stay on one row."""
    manifest = _manifest([_package(description="line one|with pipe\nline two")])

    table = render_table(manifest)

    package_row = next(line for line in table.splitlines() if "acme/demo" in line)
    # Original pipe must be escaped, and the row must remain a single line.
    assert "line one\\|with pipe line two" in package_row


def test_render_table_truncates_long_descriptions() -> None:
    """Descriptions longer than the limit get an ellipsis."""
    long_description = "x" * 500
    manifest = _manifest([_package(description=long_description)])

    table = render_table(manifest)

    assert "…" in table
    assert "x" * 500 not in table


def test_update_readme_replaces_only_marker_block(tmp_path: Path) -> None:
    """Content outside the markers is preserved exactly."""
    readme_path = tmp_path / "README.md"
    readme_path.write_text(
        "# Candidates\n\n"
        "Intro text that must survive.\n\n"
        f"{BEGIN_MARKER}\nold table content\n{END_MARKER}\n\n"
        "Footer text that must survive.\n"
    )

    update_readme(readme_path, "new table content\n")

    updated = readme_path.read_text()
    assert "Intro text that must survive." in updated
    assert "Footer text that must survive." in updated
    assert "old table content" not in updated
    assert "new table content" in updated


def test_update_readme_is_idempotent(tmp_path: Path) -> None:
    """Running the renderer twice with the same input produces no diff."""
    readme_path = tmp_path / "README.md"
    readme_path.write_text(f"{BEGIN_MARKER}\nfiller\n{END_MARKER}\n")

    update_readme(readme_path, "table v1\n")
    after_first = readme_path.read_text()
    update_readme(readme_path, "table v1\n")
    after_second = readme_path.read_text()

    assert after_first == after_second


def test_canonical_key_lowercases_and_strips_suffixes() -> None:
    """Owner/name comparison must ignore case and Lake/git URL suffixes."""
    assert canonical_key("Acme", "Demo") == "acme/demo"
    assert canonical_key("acme", "Demo.lean") == "acme/demo"
    assert canonical_key("acme", "demo.git") == "acme/demo"
    assert canonical_key("acme", "Demo.LEAN") == "acme/demo"
    assert canonical_key("acme", "no-suffix") == "acme/no-suffix"


def test_package_key_prefers_source_url_over_full_name() -> None:
    """The source URL beats fullName, which uses the lakefile name."""
    package = _package(
        full_name="argumentcomputer/Straume",
        repo_url="https://github.com/argumentcomputer/straume",
    )
    assert package_key(package) == "argumentcomputer/straume"


def test_package_key_falls_back_to_full_name_when_no_sources() -> None:
    """Manual entries with no sources still produce a usable key."""
    package = _package(full_name="acme/demo", repo_url=None)
    assert package_key(package) == "acme/demo"


def test_render_table_dedupes_keeping_first_occurrence() -> None:
    """Two packages pointing at the same GitHub repo collapse to one row."""
    reservoir_entry = _package(
        full_name="argumentcomputer/Straume",
        stars=99,
        repo_url="https://github.com/argumentcomputer/straume",
    )
    manual_entry = _package(
        full_name="argumentcomputer/straume",
        stars=6,
        repo_url="https://github.com/argumentcomputer/straume",
    )
    manifest = _manifest([reservoir_entry, manual_entry])

    table = render_table(manifest)

    rows = [line for line in table.splitlines() if "argumentcomputer" in line]
    assert len(rows) == 1, f"expected one row, got {rows}"
    # The first occurrence (reservoir) should win, so stars=99 not stars=6.
    assert "| 99 |" in rows[0]


def test_render_table_dedupes_lean_suffix_collisions() -> None:
    """A repo named ``Foo.lean`` and one named ``Foo`` are the same repo."""
    reservoir_entry = _package(
        full_name="argumentcomputer/Blake3",
        stars=50,
        repo_url="https://github.com/argumentcomputer/Blake3.lean",
    )
    manual_entry = _package(
        full_name="argumentcomputer/Blake3.lean",
        stars=2,
        repo_url="https://github.com/argumentcomputer/Blake3.lean",
    )
    manifest = _manifest([reservoir_entry, manual_entry])

    table = render_table(manifest)

    rows = [line for line in table.splitlines() if "Blake3" in line]
    assert len(rows) == 1
    assert "| 50 |" in rows[0]


def test_load_decisions_parses_jsonl_and_lowercases_repo(tmp_path: Path) -> None:
    """Each line becomes a dict; later lines for the same repo override earlier."""
    path = tmp_path / "decisions.jsonl"
    path.write_text(
        '{"repo":"Acme/Demo","include":true,"category":"mathlib"}\n'
        "\n"
        '{"repo":"acme/demo","include":false,"category":"tool"}\n'
        '{"repo":"other/repo","include":true,"category":"cslib"}\n'
    )

    decisions = load_decisions(path)

    assert set(decisions) == {"acme/demo", "other/repo"}
    assert decisions["acme/demo"]["include"] is False
    assert decisions["acme/demo"]["category"] == "tool"


def test_load_decisions_missing_file_returns_empty(tmp_path: Path) -> None:
    """A missing decisions file is the same as no decisions provided."""
    assert load_decisions(tmp_path / "absent.jsonl") == {}


def test_load_decisions_skips_invalid_lines(tmp_path: Path) -> None:
    """Bad JSON or missing-repo lines are skipped, not fatal."""
    path = tmp_path / "decisions.jsonl"
    path.write_text(
        '{"repo":"acme/demo","include":true}\n'
        "this is not json\n"
        '{"include":true}\n'
        '{"repo":"other/repo","include":false}\n'
    )

    decisions = load_decisions(path)

    assert set(decisions) == {"acme/demo", "other/repo"}


def test_render_table_drops_excluded_repos() -> None:
    """``decisions`` filters rows where include=false; unknown repos stay."""
    keep_decided = _package(full_name="alpha/keep", stars=5)
    drop = _package(full_name="beta/drop", stars=5)
    no_decision = _package(full_name="gamma/unknown", stars=5)

    decisions = {
        "alpha/keep": {"repo": "alpha/keep", "include": True, "category": "mathlib"},
        "beta/drop": {"repo": "beta/drop", "include": False, "category": "tool"},
    }

    table = render_table(
        _manifest([keep_decided, drop, no_decision]),
        decisions=decisions,
    )

    assert "alpha/keep" in table
    assert "beta/drop" not in table
    # Unknown repos are kept, since absence of a verdict is not exclusion.
    assert "gamma/unknown" in table


def test_render_table_no_decisions_keeps_all_rows() -> None:
    """Passing ``decisions=None`` (or empty dict) is a no-op."""
    keep = _package(full_name="alpha/keep", stars=5)
    other = _package(full_name="beta/other", stars=5)

    table = render_table(_manifest([keep, other]), decisions={})

    assert "alpha/keep" in table
    assert "beta/other" in table


def test_update_readme_raises_when_markers_missing(tmp_path: Path) -> None:
    """Refuse to clobber a README that does not have the markers."""
    readme_path = tmp_path / "README.md"
    readme_path.write_text("no markers here\n")

    with pytest.raises(ValueError, match="autogenerated markers"):
        update_readme(readme_path, "table\n")


def _write_toolchain(clones_dir: Path, key: str, contents: str) -> None:
    """Create a fake clone tree with a ``lean-toolchain`` file."""
    owner, _, name = key.partition("/")
    repo_dir = clones_dir / owner / name
    repo_dir.mkdir(parents=True, exist_ok=True)
    (repo_dir / "lean-toolchain").write_text(contents)


def test_read_toolchain_strips_channel_prefix(tmp_path: Path) -> None:
    """The ``leanprover/lean4:`` prefix is dropped so cells stay short."""
    _write_toolchain(tmp_path, "acme/demo", "leanprover/lean4:v4.30.0\n")

    assert read_toolchain(tmp_path, "acme/demo") == "v4.30.0"


def test_read_toolchain_returns_none_when_missing(tmp_path: Path) -> None:
    """A missing or empty file returns None, not an empty string."""
    _write_toolchain(tmp_path, "acme/empty", "   \n")

    assert read_toolchain(tmp_path, "acme/missing") is None
    assert read_toolchain(tmp_path, "acme/empty") is None


def test_read_toolchain_handles_unprefixed_pin(tmp_path: Path) -> None:
    """Some repos pin a bare version with no channel prefix."""
    _write_toolchain(tmp_path, "acme/bare", "nightly-2024-01-01\n")

    assert read_toolchain(tmp_path, "acme/bare") == "nightly-2024-01-01"


def test_render_table_includes_lean_column_header() -> None:
    """The Lean column lives between License and Updated."""
    table = render_table(_manifest([_package(stars=1)]))

    header_line = table.splitlines()[0]
    assert "| Lean |" in header_line
    assert header_line.index("| License") < header_line.index("| Lean ")
    assert header_line.index("| Lean ") < header_line.index("| Updated ")


def test_render_table_fills_lean_column_from_clones_dir(tmp_path: Path) -> None:
    """When a clone is present, its toolchain shows up in the Lean cell."""
    package = _package(
        full_name="acme/demo",
        repo_url="https://github.com/acme/demo",
        stars=1,
    )
    _write_toolchain(tmp_path, "acme/demo", "leanprover/lean4:v4.30.0")

    table = render_table(_manifest([package]), clones_dir=tmp_path)

    package_row = next(line for line in table.splitlines() if "acme/demo" in line)
    assert " v4.30.0 " in package_row


def _write_lean_files(repo_dir: Path, files: dict[str, int]) -> None:
    """Write fake ``.lean`` files with ``files[path] = line count``."""
    for relative_path, lines in files.items():
        path = repo_dir / relative_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(["theorem x : True := trivial"] * lines) + "\n")


def test_count_lean_loc_sums_all_lean_files(tmp_path: Path) -> None:
    """LOC = total lines across every ``.lean`` file under the repo dir."""
    repo = tmp_path / "acme" / "demo"
    _write_lean_files(repo, {"Main.lean": 5, "Demo/Sub.lean": 7})

    assert count_lean_loc(tmp_path, "acme/demo") == 12


def test_count_lean_loc_excludes_lake_and_build_dirs(tmp_path: Path) -> None:
    """``.lake``, ``lake-packages``, ``build``, and ``.git`` are skipped."""
    repo = tmp_path / "acme" / "demo"
    _write_lean_files(
        repo,
        {
            "Main.lean": 3,
            ".lake/packages/mathlib/Mathlib.lean": 1000,
            "lake-packages/std/Std.lean": 1000,
            "build/Output.lean": 100,
            ".git/hooks/Hook.lean": 1,
        },
    )

    assert count_lean_loc(tmp_path, "acme/demo") == 3


def test_count_lean_loc_returns_none_without_clone(tmp_path: Path) -> None:
    """A missing clone dir returns None so the renderer can skip filtering."""
    assert count_lean_loc(tmp_path, "missing/repo") is None


def test_count_lean_loc_returns_zero_for_empty_clone(tmp_path: Path) -> None:
    """An existing clone with no ``.lean`` files counts as zero, not None."""
    (tmp_path / "acme" / "empty").mkdir(parents=True)

    assert count_lean_loc(tmp_path, "acme/empty") == 0


def test_render_table_includes_loc_column_header() -> None:
    """The LOC column header lives between Lean and Updated, right-aligned."""
    table = render_table(_manifest([_package(stars=1)]))

    header_line = table.splitlines()[0]
    separator_line = table.splitlines()[1]
    assert "| LOC |" in header_line
    assert header_line.index("| Lean ") < header_line.index("| LOC ")
    assert header_line.index("| LOC ") < header_line.index("| Updated ")
    # LOC column right-aligned via ``---:`` in the separator row.
    columns = [cell.strip() for cell in separator_line.split("|")]
    assert columns[6] == "---:"


def test_render_table_fills_loc_column_from_clones_dir(tmp_path: Path) -> None:
    """LOC cells render the per-repo line count formatted with commas."""
    repo = tmp_path / "acme" / "demo"
    _write_lean_files(repo, {"Main.lean": 1234})
    package = _package(
        full_name="acme/demo",
        repo_url="https://github.com/acme/demo",
        stars=1,
    )

    table = render_table(_manifest([package]), clones_dir=tmp_path)

    package_row = next(line for line in table.splitlines() if "acme/demo" in line)
    assert " 1,234 " in package_row


def test_render_table_filters_below_min_loc(tmp_path: Path) -> None:
    """``min_loc`` drops rows whose clone has fewer .lean lines than the floor."""
    big = _package(full_name="alpha/big", stars=5)
    small = _package(full_name="beta/small", stars=5)
    no_clone = _package(full_name="gamma/missing", stars=5)
    _write_lean_files(tmp_path / "alpha" / "big", {"Main.lean": 300})
    _write_lean_files(tmp_path / "beta" / "small", {"Main.lean": 50})
    # gamma/missing intentionally has no clone dir.

    table = render_table(
        _manifest([big, small, no_clone]),
        clones_dir=tmp_path,
        min_loc=250,
    )

    assert "alpha/big" in table
    assert "beta/small" not in table
    # Repos without a clone (LOC unknown) are kept; only known-too-small drops.
    assert "gamma/missing" in table


def test_render_table_min_loc_no_op_without_clones_dir(tmp_path: Path) -> None:
    """Without ``clones_dir`` we cannot count LOC, so the filter is a no-op."""
    package = _package(full_name="acme/demo", stars=5)

    table = render_table(_manifest([package]), clones_dir=None, min_loc=10000)

    assert "acme/demo" in table


def test_render_table_filters_below_min_stars() -> None:
    """``min_stars`` excludes low-star rows so GitHub still renders the table."""
    manifest = _manifest(
        [
            _package(full_name="alpha/big", stars=42),
            _package(full_name="beta/edge", stars=2),
            _package(full_name="gamma/one", stars=1),
            _package(full_name="delta/zero", stars=0),
        ]
    )

    table = render_table(manifest, min_stars=2)

    body_lines = [line for line in table.splitlines() if line.startswith("| ")][2:]
    package_cells = [line.split("|")[2] for line in body_lines]
    rendered = " ".join(package_cells)
    assert "alpha/big" in rendered
    assert "beta/edge" in rendered
    assert "gamma/one" not in rendered
    assert "delta/zero" not in rendered


def test_render_table_min_stars_zero_keeps_everything() -> None:
    """``min_stars=0`` is a no-op so existing callers keep current behaviour."""
    manifest = _manifest(
        [
            _package(full_name="alpha/some", stars=3),
            _package(full_name="beta/zero", stars=0),
        ]
    )

    table = render_table(manifest, min_stars=0)

    assert "alpha/some" in table
    assert "beta/zero" in table


def test_render_table_lean_column_blank_without_clone(tmp_path: Path) -> None:
    """Repos without a local clone show an empty Lean cell, not an error."""
    package = _package(stars=1)

    table = render_table(_manifest([package]), clones_dir=tmp_path)

    package_row = next(line for line in table.splitlines() if "acme/demo" in line)
    cells = [cell.strip() for cell in package_row.split("|")]
    # Cells: ['', stars, name, description, license, lean, loc, updated,
    # build, in_pool, '']
    assert cells[5] == ""


def test_load_pool_repos_collects_github_repo_keys(tmp_path: Path) -> None:
    """Each ``source.github_repo`` becomes a canonical key in the result."""
    path = tmp_path / "projects.yml"
    path.write_text(
        "projects:\n"
        "  - slug: alpha\n"
        "    source:\n"
        "      github_repo: Acme/Demo\n"
        "  - slug: beta\n"
        "    source:\n"
        "      github_repo: other/repo.lean\n"
    )

    assert load_pool_repos(path) == {"acme/demo", "other/repo"}


def test_load_pool_repos_ignores_projects_without_github_repo(tmp_path: Path) -> None:
    """Projects with only arxiv/doi/url sources contribute no keys."""
    path = tmp_path / "projects.yml"
    path.write_text(
        "projects:\n"
        "  - slug: alpha\n"
        "    source:\n"
        "      arxiv: '2602.03716'\n"
        "  - slug: beta\n"
        "    source:\n"
        "      github_repo: kept/here\n"
    )

    assert load_pool_repos(path) == {"kept/here"}


def test_load_pool_repos_missing_file_returns_empty(tmp_path: Path) -> None:
    """A missing projects.yml is the same as no merged candidates."""
    assert load_pool_repos(tmp_path / "absent.yml") == set()


def test_load_pool_repos_invalid_yaml_returns_empty(tmp_path: Path) -> None:
    """A malformed file logs and returns empty rather than crashing render."""
    path = tmp_path / "projects.yml"
    path.write_text("projects:\n  - : : :\n  bad indent\n")

    assert load_pool_repos(path) == set()


def test_load_pool_repos_skips_malformed_entries(tmp_path: Path) -> None:
    """Non-mapping projects, missing slashes, and non-string repos are skipped."""
    path = tmp_path / "projects.yml"
    path.write_text(
        "projects:\n"
        "  - slug: ok\n"
        "    source:\n"
        "      github_repo: kept/here\n"
        "  - slug: bare-source-string\n"
        "    source: arxiv:1234.5678\n"
        "  - slug: missing-slash\n"
        "    source:\n"
        "      github_repo: noslash\n"
        "  - slug: non-string\n"
        "    source:\n"
        "      github_repo: 42\n"
    )

    assert load_pool_repos(path) == {"kept/here"}


def test_render_table_includes_in_pool_column_header() -> None:
    """The In Pool column header sits at the right edge of the table."""
    table = render_table(_manifest([_package(stars=1)]))

    header_line = table.splitlines()[0]
    separator_line = table.splitlines()[1]
    assert "| In Pool |" in header_line
    assert header_line.index("| Build ") < header_line.index("| In Pool ")
    columns = [cell.strip() for cell in separator_line.split("|")]
    # Last data column should be center-aligned via ``:---:``.
    assert columns[9] == ":---:"


def test_render_table_marks_pool_repos_with_check() -> None:
    """Rows whose canonical key is in pool_repos render ✓ in the last cell."""
    merged = _package(
        full_name="acme/merged",
        repo_url="https://github.com/acme/merged",
        stars=1,
    )
    other = _package(
        full_name="acme/other",
        repo_url="https://github.com/acme/other",
        stars=1,
    )

    table = render_table(
        _manifest([merged, other]),
        pool_repos={"acme/merged"},
    )

    merged_row = next(line for line in table.splitlines() if "acme/merged" in line)
    other_row = next(line for line in table.splitlines() if "acme/other" in line)
    assert merged_row.rstrip().endswith("| ✓ |")
    assert other_row.rstrip().endswith("|  |")


def test_render_table_in_pool_column_blank_when_pool_repos_omitted() -> None:
    """Without ``pool_repos`` every row's In Pool cell is blank."""
    package = _package(stars=1)

    table = render_table(_manifest([package]))

    package_row = next(line for line in table.splitlines() if "acme/demo" in line)
    assert package_row.rstrip().endswith("|  |")
