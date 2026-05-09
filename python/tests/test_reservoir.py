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
)


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
