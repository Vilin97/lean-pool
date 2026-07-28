"""Tests for NOTICE generation from the project registry."""

from __future__ import annotations

from pathlib import Path

import pytest

from lean_pool.notice import (
    URL_COLUMN,
    build,
    main,
    project_directory,
    render_entry,
    repository_url,
    unregistered_notes,
)

PROJECTS_YML = """projects:
  - slug: alpha
    entry_module: LeanPool.Alpha
    license: Apache-2.0
    source:
      github_repo: someone/alpha
  - slug: beta
    entry_module: LeanPool.Beta
    license: MIT
    source:
      github_repo: someone/beta
"""


def _write_repo(root: Path, extra: str = "") -> None:
    """Create a minimal repository with two projects, one Apache and one MIT."""
    pool = root / "LeanPool"
    pool.mkdir()
    (pool / "projects.yml").write_text(PROJECTS_YML)
    if extra:
        (root / "NOTICE.extra.yml").write_text(extra)


def test_every_project_appears(tmp_path: Path) -> None:
    """Both projects are listed, each under its own license section."""
    _write_repo(tmp_path)
    text = build(tmp_path)
    assert "  LeanPool/Alpha" in text
    assert "  LeanPool/Beta" in text
    assert "https://github.com/someone/alpha" in text
    assert text.index("Apache License, Version 2.0\n---") < text.index("LeanPool/Alpha")
    assert text.index("MIT License\n---") < text.index("LeanPool/Beta")


def test_mit_permission_notice_present(tmp_path: Path) -> None:
    """The MIT section carries the permission notice the license requires."""
    _write_repo(tmp_path)
    assert "Permission is hereby granted, free of charge" in build(tmp_path)


def test_note_is_rendered_under_its_entry(tmp_path: Path) -> None:
    """A project's ``note`` appears indented directly beneath its entry."""
    _write_repo(tmp_path, "Beta:\n  note: Copyright (c) 2026 Someone\n")
    lines = build(tmp_path).splitlines()
    index = next(i for i, line in enumerate(lines) if "LeanPool/Beta" in line)
    assert lines[index + 1] == "      Copyright (c) 2026 Someone"


def test_relicensed_moves_out_of_license_section(tmp_path: Path) -> None:
    """A relicensed project is listed only in the relicensing section."""
    _write_repo(tmp_path, "Alpha:\n  relicensed: Relicensed by its author.\n")
    text = build(tmp_path)
    assert text.count("LeanPool/Alpha") == 1
    assert "Projects relicensed by their original author" in text
    assert text.index("relicensed by their original author") < text.index(
        "LeanPool/Alpha"
    )


def test_attribution_adds_a_second_listing(tmp_path: Path) -> None:
    """An attributed project stays in its license section and is repeated."""
    _write_repo(tmp_path, "Alpha:\n  attribution: Upstream asks for a citation.\n")
    text = build(tmp_path)
    assert text.count("LeanPool/Alpha") == 2
    assert "Upstream asks for a citation." in text


def test_empty_relicensed_note_lists_without_prose(tmp_path: Path) -> None:
    """An empty ``relicensed`` value lists the project with no note of its own."""
    _write_repo(tmp_path, 'Alpha:\n  relicensed: ""\n')
    text = build(tmp_path)
    assert "Projects relicensed by their original author" in text
    assert text.count("LeanPool/Alpha") == 1


def test_long_directory_wraps_the_url(tmp_path: Path) -> None:
    """A name that reaches the URL column pushes the URL to its own line."""
    short = render_entry("Alpha", "https://example.com")
    assert len(short) == 1
    assert short[0].index("https://") == URL_COLUMN

    long = render_entry("A" * 40, "https://example.com")
    assert len(long) == 2
    assert long[1].index("https://") == URL_COLUMN


def test_stale_extra_key_is_rejected(tmp_path: Path) -> None:
    """A note for a project that no longer exists fails loudly."""
    _write_repo(tmp_path, "Gamma:\n  note: Copyright (c) 2026 Ghost\n")
    with pytest.raises(SystemExit, match="Gamma"):
        build(tmp_path)


def test_unregistered_notes_lists_orphans() -> None:
    """Orphan detection compares note keys against project directories."""
    projects = [{"entry_module": "LeanPool.Alpha"}]
    assert unregistered_notes(projects, {"Alpha": {}, "Ghost": {}}) == ["Ghost"]


def test_project_directory_and_url_helpers() -> None:
    """Directory and URL are derived from the card, not typed by hand."""
    card = {"entry_module": "LeanPool.Alpha", "source": {"github_repo": "who/what"}}
    assert project_directory(card) == "Alpha"
    assert repository_url(card) == "https://github.com/who/what"
    assert repository_url({"entry_module": "LeanPool.Alpha"}) == ""


def test_check_mode_detects_drift(tmp_path: Path) -> None:
    """``--check`` passes on a generated file and fails once it drifts."""
    _write_repo(tmp_path)
    assert main(["--repo", str(tmp_path)]) == 0
    assert main(["--repo", str(tmp_path), "--check"]) == 0

    (tmp_path / "NOTICE").write_text("hand-edited\n")
    assert main(["--repo", str(tmp_path), "--check"]) == 1
    # Check mode must not repair the file it is checking.
    assert (tmp_path / "NOTICE").read_text() == "hand-edited\n"


def test_generation_is_idempotent(tmp_path: Path) -> None:
    """Regenerating an up-to-date NOTICE leaves it byte-identical."""
    _write_repo(tmp_path)
    main(["--repo", str(tmp_path)])
    first = (tmp_path / "NOTICE").read_text()
    main(["--repo", str(tmp_path)])
    assert (tmp_path / "NOTICE").read_text() == first


def test_repository_notice_is_current() -> None:
    """The committed NOTICE matches what the generator produces."""
    root = Path(__file__).resolve().parents[2]
    assert (root / "NOTICE").read_text(encoding="utf-8") == build(root)
