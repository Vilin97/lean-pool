"""Tests for the Reservoir manifest fetcher and writer."""

from __future__ import annotations

import io
import json
from pathlib import Path
from unittest.mock import patch

from lean_pool.aggregator.reservoir import (
    MANIFEST_URL,
    fetch_manifest,
    save_manifest,
    trim_manifest,
    trim_package,
)


def _make_package(
    *,
    name: str = "demo",
    versions: list[dict] | None = None,
    builds: list[dict] | None = None,
    dependents: list[dict] | None = None,
) -> dict:
    """Build a minimal package fixture mirroring the Reservoir shape."""
    return {
        "name": name,
        "owner": "acme",
        "fullName": f"acme/{name}",
        "description": "demo package",
        "keywords": ["lean"],
        "homepage": "https://example.com",
        "license": "MIT",
        "createdAt": "2026-01-01T00:00:00Z",
        "updatedAt": "2026-05-01T00:00:00Z",
        "stars": 7,
        "sources": [
            {
                "type": "git",
                "host": "github",
                "id": "R_1",
                "fullName": f"acme/{name}",
                "repoUrl": f"https://github.com/acme/{name}",
                "gitUrl": f"https://github.com/acme/{name}",
                "defaultBranch": "main",
            }
        ],
        "versions": [] if versions is None else versions,
        "builds": [] if builds is None else builds,
        "dependents": [] if dependents is None else dependents,
    }


def test_save_manifest_round_trip(tmp_path: Path) -> None:
    """save_manifest writes JSON that can be read back identically."""
    manifest = {"bundledAt": "2026-05-09T00:00:00Z", "packages": [{"stars": 3}]}
    output_path = tmp_path / "nested" / "manifest.json"

    save_manifest(manifest, output_path)

    assert output_path.exists()
    assert json.loads(output_path.read_text()) == manifest


def test_fetch_manifest_parses_response() -> None:
    """fetch_manifest decodes JSON returned by urlopen."""
    payload = {"bundledAt": "now", "packages": []}
    response = io.BytesIO(json.dumps(payload).encode())
    response.__enter__ = lambda self: self  # type: ignore[method-assign]
    response.__exit__ = lambda self, *exc: None  # type: ignore[method-assign]

    with patch(
        "lean_pool.aggregator.reservoir.urlopen", return_value=response
    ) as mock_urlopen:
        result = fetch_manifest(timeout=5)

    assert result == payload
    mock_urlopen.assert_called_once_with(MANIFEST_URL, timeout=5)


def test_trim_package_keeps_latest_version_and_build() -> None:
    """trim_package keeps only the first (newest) version and build."""
    versions = [
        {"version": "0.2.0", "revision": "abc", "date": "2026-05-01"},
        {"version": "0.1.0", "revision": "def", "date": "2026-04-01"},
    ]
    builds = [
        {"toolchain": "v4.30.0", "built": True, "runAt": "2026-05-02"},
        {"toolchain": "v4.29.0", "built": True, "runAt": "2026-04-02"},
        {"toolchain": "v4.28.0", "built": False, "runAt": "2026-03-02"},
    ]
    package = _make_package(versions=versions, builds=builds)

    trimmed = trim_package(package)

    assert trimmed["latestVersion"] == versions[0]
    assert trimmed["latestBuild"] == builds[0]
    # The historical entries must not leak into the trimmed package.
    assert "versions" not in trimmed
    assert "builds" not in trimmed
    assert "dependents" not in trimmed


def test_trim_package_handles_empty_history() -> None:
    """trim_package returns None when there are no versions or builds."""
    package = _make_package(versions=[], builds=[])

    trimmed = trim_package(package)

    assert trimmed["latestVersion"] is None
    assert trimmed["latestBuild"] is None


def test_trim_manifest_preserves_top_level_and_drops_per_package_history() -> None:
    """trim_manifest keeps toolchains and aliases, trims every package."""
    manifest = {
        "bundledAt": "2026-05-09T00:00:00Z",
        "toolchains": [{"name": "v4.30.0", "tag": "v4.30.0", "date": "2026-05-01"}],
        "packageAliases": {"old-name": "acme/demo"},
        "packages": [
            _make_package(
                name="demo",
                versions=[
                    {"version": "0.2.0", "revision": "abc", "date": "2026-05-01"}
                ],
                builds=[{"toolchain": "v4.30.0", "built": True, "runAt": "2026-05-02"}],
                dependents=[{"name": "consumer", "fullName": "acme/consumer"}],
            ),
            _make_package(name="empty", versions=[], builds=[]),
        ],
    }

    trimmed = trim_manifest(manifest)

    assert trimmed["bundledAt"] == manifest["bundledAt"]
    assert trimmed["toolchains"] == manifest["toolchains"]
    assert trimmed["packageAliases"] == manifest["packageAliases"]
    assert len(trimmed["packages"]) == 2
    assert trimmed["packages"][0]["latestVersion"]["version"] == "0.2.0"
    assert trimmed["packages"][1]["latestVersion"] is None


def test_save_manifest_round_trips_a_trimmed_manifest(tmp_path: Path) -> None:
    """save_manifest also accepts a TrimmedManifest payload."""
    manifest = {
        "bundledAt": "2026-05-09T00:00:00Z",
        "toolchains": [],
        "packageAliases": {},
        "packages": [_make_package(name="demo", versions=[], builds=[])],
    }
    trimmed = trim_manifest(manifest)
    output_path = tmp_path / "manifest_trimmed.json"

    save_manifest(trimmed, output_path)

    assert json.loads(output_path.read_text()) == trimmed
