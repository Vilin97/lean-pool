"""Fetch the Reservoir package manifest.

The Reservoir website bundles every indexed Lean package into a single
JSON file at ``https://reservoir.lean-lang.org/index/manifest.json``.
That file is the canonical input for aggregation: it contains every
package's metadata, recent versions, and per-toolchain build results.
"""

from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Any, TypedDict
from urllib.request import urlopen

logger = logging.getLogger(__name__)

MANIFEST_URL = "https://reservoir.lean-lang.org/index/manifest.json"
DEFAULT_TIMEOUT_SECONDS = 60


class ReservoirManifest(TypedDict):
    """Top-level shape of the Reservoir manifest JSON."""

    bundledAt: str
    toolchains: list[dict[str, Any]]
    packages: list[dict[str, Any]]
    packageAliases: dict[str, str]


def fetch_manifest(
    url: str = MANIFEST_URL, timeout: float = DEFAULT_TIMEOUT_SECONDS
) -> ReservoirManifest:
    """Download and parse the Reservoir manifest JSON.

    Args:
        url: The URL to fetch the manifest from.
        timeout: Socket timeout in seconds for the HTTP request.

    Returns:
        The parsed manifest with ``bundledAt``, ``toolchains``,
        ``packages``, and ``packageAliases`` fields.
    """
    logger.info("Fetching %s", url)
    with urlopen(url, timeout=timeout) as response:
        return json.load(response)


def save_manifest(manifest: ReservoirManifest, path: Path) -> None:
    """Write the manifest to disk as pretty-printed JSON.

    Args:
        manifest: The parsed manifest.
        path: The output file path; parent directories are created.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as output_file:
        json.dump(manifest, output_file, indent=2)
