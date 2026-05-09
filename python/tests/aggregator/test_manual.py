"""Tests for the manual candidate fetcher."""

from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from lean_pool.aggregator.manual import (
    _to_package,
    fetch_manual_packages,
    load_manual_packages,
    parse_manual_list,
    save_manual_packages,
)


def _gh_repo_response(
    *,
    full_name: str = "acme/demo",
    description: str | None = "demo",
    stars: int = 5,
    license_id: str | None = "MIT",
) -> dict:
    """Build a GitHub REST repo response payload for tests."""
    owner, name = full_name.split("/")
    return {
        "name": name,
        "full_name": full_name,
        "owner": {"login": owner},
        "description": description,
        "topics": ["lean4"],
        "homepage": "",
        "license": {"spdx_id": license_id} if license_id is not None else None,
        "created_at": "2026-01-01T00:00:00Z",
        "updated_at": "2026-05-01T00:00:00Z",
        "pushed_at": "2026-05-01T00:00:00Z",
        "stargazers_count": stars,
        "html_url": f"https://github.com/{full_name}",
        "node_id": "R_1",
        "default_branch": "main",
    }


def test_parse_manual_list_handles_comments_and_blanks(tmp_path: Path) -> None:
    """Comments, blank lines, trailing slashes, and .git suffixes all work."""
    list_path = tmp_path / "manual.txt"
    list_path.write_text(
        "# Header comment\n"
        "\n"
        "https://github.com/acme/demo\n"
        "https://github.com/acme/with-slash/   # inline comment\n"
        "https://github.com/acme/with-suffix.git\n"
        "  https://github.com/acme/leading-space  \n"
    )

    entries = parse_manual_list(list_path)

    assert entries == [
        ("acme", "demo"),
        ("acme", "with-slash"),
        ("acme", "with-suffix"),
        ("acme", "leading-space"),
    ]


def test_parse_manual_list_rejects_non_github_urls(tmp_path: Path) -> None:
    """Anything that isn't a github.com repo URL must be flagged."""
    list_path = tmp_path / "manual.txt"
    list_path.write_text("https://gitlab.com/acme/demo\n")

    with pytest.raises(ValueError, match="not a GitHub repo URL"):
        parse_manual_list(list_path)


def test_to_package_maps_github_fields_to_reservoir_shape() -> None:
    """The Package dict should have the keys the renderer reads."""
    package = _to_package(_gh_repo_response(full_name="acme/demo", stars=42))

    assert package["fullName"] == "acme/demo"
    assert package["stars"] == 42
    assert package["license"] == "MIT"
    assert package["updatedAt"] == "2026-05-01T00:00:00Z"
    assert package["sources"][0]["repoUrl"] == "https://github.com/acme/demo"
    assert package["versions"] == []
    assert package["builds"] == []


def test_to_package_normalises_unrecognised_license_to_none() -> None:
    """GitHub's NOASSERTION is treated the same as a missing license."""
    package = _to_package(_gh_repo_response(license_id="NOASSERTION"))

    assert package["license"] is None


def test_fetch_manual_packages_calls_gh_for_each_entry() -> None:
    """Each (owner, name) entry triggers one ``gh api repos/...`` call."""
    entries = [("acme", "first"), ("acme", "second")]
    responses = {
        "repos/acme/first": _gh_repo_response(full_name="acme/first", stars=1),
        "repos/acme/second": _gh_repo_response(full_name="acme/second", stars=2),
    }

    def fake_run(cmd, **_):
        endpoint = cmd[2]
        body = responses[endpoint]

        class _R:
            returncode = 0
            stdout = json.dumps(body)
            stderr = ""

        return _R()

    with patch("lean_pool.aggregator.manual.subprocess.run", side_effect=fake_run):
        packages = fetch_manual_packages(entries)

    assert [p["fullName"] for p in packages] == ["acme/first", "acme/second"]
    assert [p["stars"] for p in packages] == [1, 2]


def test_save_and_load_manual_packages_round_trip(tmp_path: Path) -> None:
    """Saving then loading produces the same packages."""
    packages = [_to_package(_gh_repo_response(full_name="acme/demo"))]
    output_path = tmp_path / "nested" / "manual_packages.json"

    save_manual_packages(packages, output_path)
    loaded = load_manual_packages(output_path)

    assert loaded == packages


def test_load_manual_packages_returns_empty_when_missing(tmp_path: Path) -> None:
    """``render`` works even when ``fetch`` has never run for manual entries."""
    assert load_manual_packages(tmp_path / "absent.json") == []
