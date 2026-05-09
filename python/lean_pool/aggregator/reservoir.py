"""Fetch and decode the Reservoir package manifest.

The Reservoir website bundles every indexed Lean package into a single
JSON file at ``https://reservoir.lean-lang.org/index/manifest.json``.
That file is the canonical input for aggregation: it contains every
package's metadata, recent versions, and per-toolchain build results.

The TypedDicts below mirror Reservoir's own type definitions in
``reservoir/scripts/utils/`` (``package.py``, ``manifest.py``,
``toolchain.py``) so the decoded manifest is statically typed end to
end, not just ``dict[str, Any]``.
"""

from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import TypedDict
from urllib.request import urlopen

logger = logging.getLogger(__name__)

MANIFEST_URL = "https://reservoir.lean-lang.org/index/manifest.json"
DEFAULT_TIMEOUT_SECONDS = 60


class PackageSource(TypedDict, total=False):
    """A source location for a package. Most entries are GitHub repos."""

    type: str
    host: str
    id: str
    fullName: str
    repoUrl: str
    gitUrl: str
    defaultBranch: str


class BuildResult(TypedDict):
    """Outcome of building a package against a single toolchain."""

    built: bool | None
    tested: bool | None
    toolchain: str
    requiredUpdate: bool | None
    archiveSize: int | None
    archiveHash: str | None
    runAt: str
    url: str | None


class Build(BuildResult):
    """A build result tagged with the source revision it ran against."""

    revision: str


class DependencyBase(TypedDict):
    """Fields shared by outgoing dependencies and incoming dependents."""

    type: str
    name: str
    scope: str | None
    version: str
    transitive: bool | None
    rev: str | None
    inputRev: str | None
    url: str | None


class Dependency(DependencyBase, total=False):
    """An outgoing dependency. ``fullName`` is set when resolvable."""

    fullName: str


class Dependent(DependencyBase):
    """A package that depends on this one. ``fullName`` is always set."""

    fullName: str


class PackageVersion(TypedDict):
    """A released version of a package, as serialized in the manifest."""

    version: str
    revision: str
    date: str
    tag: str | None
    toolchain: str | None
    platformIndependent: bool | None
    license: str | None
    licenseFiles: list[str]
    readmeFile: str | None
    dependencies: list[Dependency]


class Package(TypedDict):
    """A package as published in the Reservoir manifest."""

    name: str
    owner: str
    fullName: str
    description: str | None
    keywords: list[str] | None
    homepage: str | None
    license: str | None
    createdAt: str
    updatedAt: str
    stars: int
    sources: list[PackageSource]
    versions: list[PackageVersion]
    dependents: list[Dependent]
    builds: list[Build]


class Toolchain(TypedDict):
    """An indexed Lean toolchain release."""

    name: str
    version: int | None
    tag: str
    date: str
    releaseUrl: str
    prerelease: bool


class ReservoirManifest(TypedDict):
    """The decoded ``manifest.json`` produced by Reservoir's bundler."""

    bundledAt: str
    toolchains: list[Toolchain]
    packages: list[Package]
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
