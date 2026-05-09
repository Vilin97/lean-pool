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


class TrimmedPackage(TypedDict):
    """A package reduced to the fields needed for candidate selection.

    The Reservoir manifest stores the full per-toolchain build history
    and every released version of every package, which together account
    for ~97% of the bundle's size. Most of that is irrelevant to picking
    candidates: we only need to know the latest build attempt and the
    most recent version. ``dependents`` is dropped entirely because the
    forward-dependency graph in each version's ``dependencies`` is
    enough to rebuild it if we ever need to.
    """

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
    latestVersion: PackageVersion | None
    latestBuild: Build | None


class TrimmedManifest(TypedDict):
    """A trimmed Reservoir manifest suitable for committing to the repo.

    Has the same top-level shape as :class:`ReservoirManifest` but with
    :class:`TrimmedPackage` entries in ``packages``. Toolchains and
    package aliases are kept verbatim because they are tiny.
    """

    bundledAt: str
    toolchains: list[Toolchain]
    packages: list[TrimmedPackage]
    packageAliases: dict[str, str]


def trim_package(package: Package) -> TrimmedPackage:
    """Reduce a package to the fields needed for candidate selection.

    Reservoir orders ``versions`` and ``builds`` newest first, so the
    most recent entry is always at index ``0``.

    Args:
        package: A package as published in the full Reservoir manifest.

    Returns:
        The same package with historical builds, historical versions,
        and the incoming-dependent list dropped.
    """
    versions = package.get("versions") or []
    builds = package.get("builds") or []
    return {
        "name": package["name"],
        "owner": package["owner"],
        "fullName": package["fullName"],
        "description": package.get("description"),
        "keywords": package.get("keywords"),
        "homepage": package.get("homepage"),
        "license": package.get("license"),
        "createdAt": package["createdAt"],
        "updatedAt": package["updatedAt"],
        "stars": package["stars"],
        "sources": package["sources"],
        "latestVersion": versions[0] if versions else None,
        "latestBuild": builds[0] if builds else None,
    }


def trim_manifest(manifest: ReservoirManifest) -> TrimmedManifest:
    """Produce a trimmed manifest suitable for committing to the repo.

    Args:
        manifest: The full manifest as fetched from Reservoir.

    Returns:
        A manifest of the same shape with each package reduced via
        :func:`trim_package`. The full bundle is roughly 50 MB; the
        trimmed form is around 3 MB.
    """
    return {
        "bundledAt": manifest["bundledAt"],
        "toolchains": manifest["toolchains"],
        "packageAliases": manifest["packageAliases"],
        "packages": [trim_package(p) for p in manifest["packages"]],
    }


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


def save_manifest(manifest: ReservoirManifest | TrimmedManifest, path: Path) -> None:
    """Write the manifest to disk as pretty-printed JSON.

    Args:
        manifest: The parsed manifest, full or trimmed.
        path: The output file path; parent directories are created.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as output_file:
        json.dump(manifest, output_file, indent=2)
