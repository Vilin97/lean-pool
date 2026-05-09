"""Tests for the candidates README renderer."""

from __future__ import annotations

from pathlib import Path

import pytest

from lean_pool.aggregator.render import (
    BEGIN_MARKER,
    END_MARKER,
    render_table,
    update_readme,
)


def _package(
    *,
    full_name: str = "acme/demo",
    stars: int = 0,
    description: str | None = "A demo package.",
    license_name: str | None = "MIT",
    repo_url: str | None = "https://github.com/acme/demo",
    versions: list[dict] | None = None,
    builds: list[dict] | None = None,
) -> dict:
    """Build a minimal package fixture."""
    owner, name = full_name.split("/")
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

    # Build column is the last cell on the row; expect the missing-glyph.
    package_row = next(line for line in table.splitlines() if "acme/demo" in line)
    assert package_row.rstrip().endswith("| – |")


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


def test_update_readme_raises_when_markers_missing(tmp_path: Path) -> None:
    """Refuse to clobber a README that does not have the markers."""
    readme_path = tmp_path / "README.md"
    readme_path.write_text("no markers here\n")

    with pytest.raises(ValueError, match="autogenerated markers"):
        update_readme(readme_path, "table\n")
