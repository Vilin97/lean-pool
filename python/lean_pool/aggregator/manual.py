"""Manual candidate list maintained alongside Reservoir's index.

Reservoir excludes packages that lack a root ``lake-manifest.json``,
have a non-OSI license, are forks, or have fewer than two stars (see
https://reservoir.lean-lang.org/inclusion-criteria). Several real,
completed Lean formalisation projects fail one of those rules but are
still worth tracking. We keep a hand-edited URL list and fetch their
metadata from the GitHub REST API at the same time we fetch the
Reservoir manifest.

The list lives at ``candidates/manual.txt`` — one GitHub URL per line,
``#`` comments and blank lines allowed.
"""

from __future__ import annotations

import json
import logging
import re
import subprocess
from pathlib import Path

from lean_pool.aggregator.reservoir import Package

logger = logging.getLogger(__name__)

_GITHUB_URL = re.compile(
    r"https?://github\.com/(?P<owner>[^/\s]+)/(?P<name>[^/\s#?]+?)(?:\.git)?/?$"
)


def parse_manual_list(path: Path) -> list[tuple[str, str]]:
    """Parse a manual URL list into ``(owner, name)`` pairs.

    Strips ``#``-prefixed comments and blank lines. Each remaining line
    must be a GitHub repository URL.

    Args:
        path: Path to the manual list file.

    Returns:
        A list of ``(owner, name)`` tuples in file order.

    Raises:
        ValueError: If a non-empty, non-comment line is not a GitHub
            repo URL.
    """
    entries: list[tuple[str, str]] = []
    for line_number, raw in enumerate(path.read_text().splitlines(), start=1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        match = _GITHUB_URL.match(line)
        if not match:
            raise ValueError(f"{path}:{line_number}: not a GitHub repo URL: {raw!r}")
        entries.append((match["owner"], match["name"]))
    return entries


def _gh_api(endpoint: str) -> dict:
    """Call ``gh api <endpoint>`` and parse the JSON response.

    Args:
        endpoint: The REST endpoint, e.g. ``repos/owner/name``.

    Returns:
        The decoded JSON body.

    Raises:
        RuntimeError: If ``gh`` exits non-zero.
    """
    result = subprocess.run(
        ["gh", "api", endpoint],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(f"gh api {endpoint} failed: {result.stderr.strip()}")
    return json.loads(result.stdout)


def _to_package(repo: dict) -> Package:
    """Convert a GitHub REST repo response into a Reservoir-shaped package.

    The renderer only reads a small subset of fields, so unsupported
    fields (versions, builds, dependents) are filled with empty defaults.
    The build column will render as ``–`` for manual entries because we
    have no toolchain build data for them.

    Args:
        repo: The body of a ``repos/{owner}/{name}`` GitHub REST call.

    Returns:
        A package dict with the same keys the renderer expects from
        Reservoir.
    """
    license_block = repo.get("license") or {}
    license_id = license_block.get("spdx_id")
    if license_id in (None, "", "NOASSERTION"):
        license_id = None
    repo_url = repo["html_url"]
    return {
        "name": repo["name"],
        "owner": repo["owner"]["login"],
        "fullName": repo["full_name"],
        "description": repo.get("description"),
        "keywords": repo.get("topics") or [],
        "homepage": repo.get("homepage") or None,
        "license": license_id,
        "createdAt": repo.get("created_at", ""),
        "updatedAt": repo.get("updated_at") or repo.get("pushed_at", ""),
        "stars": repo.get("stargazers_count", 0),
        "sources": [
            {
                "type": "git",
                "host": "github",
                "id": repo.get("node_id", ""),
                "fullName": repo["full_name"],
                "repoUrl": repo_url,
                "gitUrl": repo_url,
                "defaultBranch": repo.get("default_branch", "main"),
            }
        ],
        "versions": [],
        "builds": [],
        "dependents": [],
    }


def _cache_path(cache_dir: Path, owner: str, name: str) -> Path:
    """Return the per-entry cache file path."""
    return cache_dir / f"{owner}__{name}.json"


def fetch_manual_packages(
    entries: list[tuple[str, str]], cache_dir: Path
) -> list[Package]:
    """Fetch GitHub metadata for each manual entry, caching per-entry.

    Each successful response is written to
    ``cache_dir/<owner>__<name>.json`` immediately so partial progress
    survives a rate-limit pause or process interruption. On re-run,
    cached entries are loaded from disk instead of re-fetched. To force
    a refresh of one entry, delete its cache file; for a full refresh,
    delete the cache directory.

    Entries that fail (renamed, deleted, made private, rate-limited)
    are logged and skipped so the bulk fetch can finish without
    aborting.

    Args:
        entries: ``(owner, name)`` pairs from :func:`parse_manual_list`.
        cache_dir: Directory holding per-entry JSON files. Created if
            missing.

    Returns:
        A list of Reservoir-shaped package dicts in input order, with
        skipped entries omitted.
    """
    cache_dir.mkdir(parents=True, exist_ok=True)
    packages: list[Package] = []
    for owner, name in entries:
        cached = _cache_path(cache_dir, owner, name)
        if cached.exists():
            with cached.open() as cache_file:
                packages.append(json.load(cache_file))
            continue
        logger.info("Fetching manual entry %s/%s", owner, name)
        try:
            repo = _gh_api(f"repos/{owner}/{name}")
        except RuntimeError as exc:
            logger.warning("Skipping %s/%s: %s", owner, name, exc)
            continue
        package = _to_package(repo)
        with cached.open("w") as cache_file:
            json.dump(package, cache_file, indent=2)
        packages.append(package)
    return packages


def save_manual_packages(packages: list[Package], path: Path) -> None:
    """Write the manual package list to disk as pretty-printed JSON.

    Args:
        packages: Package dicts produced by :func:`fetch_manual_packages`.
        path: The output file path; parent directories are created.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as output_file:
        json.dump(packages, output_file, indent=2)


def load_manual_packages(path: Path) -> list[Package]:
    """Read a previously-saved manual package list.

    Returns an empty list if ``path`` does not exist so that ``render``
    works even when nobody has run ``fetch`` for the manual entries.
    """
    if not path.exists():
        return []
    with path.open() as input_file:
        return json.load(input_file)
