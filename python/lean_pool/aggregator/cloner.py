"""Shallow-clone every candidate repo into a local cache directory.

Each repo is cloned with ``git clone --depth=1 --filter=blob:none``,
which fetches the latest tree without history or blob contents. Files
are downloaded on demand the first time they are read, so an idle
clone is typically a few hundred KB.

The cache lives at
``candidates/raw_data/clones/<owner>/<name>/``, keyed by the
package's canonical GitHub key (lowercased, ``.lean``/``.git`` suffix
stripped) so two manifest entries pointing at the same repo (e.g.
Reservoir's ``leanprover-community/mathlib`` and a manual entry's
``mathlib4``) clone once.
"""

from __future__ import annotations

import logging
import shutil
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from lean_pool.aggregator.render import package_key
from lean_pool.aggregator.reservoir import Package

logger = logging.getLogger(__name__)

DEFAULT_PARALLELISM = 8
DEFAULT_CLONE_TIMEOUT_SECONDS = 120.0


def _repo_url(package: Package) -> str | None:
    """Return the package's primary repository URL, if available."""
    sources = package.get("sources") or []
    if not sources:
        return None
    return sources[0].get("repoUrl") or sources[0].get("gitUrl")


def _git_clone(
    url: str, dest: Path, timeout: float = DEFAULT_CLONE_TIMEOUT_SECONDS
) -> None:
    """Run a shallow blobless clone with a timeout."""
    subprocess.run(
        [
            "git",
            "clone",
            "--depth=1",
            "--filter=blob:none",
            "--quiet",
            url,
            str(dest),
        ],
        check=True,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def _target_for_key(clones_dir: Path, key: str) -> Path:
    """Map an ``owner/name`` canonical key to a directory under ``clones_dir``."""
    owner, _, name = key.partition("/")
    return clones_dir / owner / name


def clone_package(
    package: Package,
    clones_dir: Path,
    *,
    timeout: float = DEFAULT_CLONE_TIMEOUT_SECONDS,
) -> Path | None:
    """Clone one package's repo into ``clones_dir`` if not already cloned.

    Args:
        package: A package dict from the Reservoir manifest or the
            manual list.
        clones_dir: Root directory holding all clones.
        timeout: Per-clone timeout in seconds.

    Returns:
        The clone path on success or already-present, or ``None`` if
        the package has no usable URL or the clone failed.
    """
    key = package_key(package)
    url = _repo_url(package)
    if not key or not url:
        logger.debug("Skipping %s: no canonical key or URL", package.get("fullName"))
        return None
    target = _target_for_key(clones_dir, key)
    if target.exists():
        return target
    target.parent.mkdir(parents=True, exist_ok=True)
    try:
        _git_clone(url, target, timeout=timeout)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        stderr = (getattr(exc, "stderr", "") or "").strip()
        logger.warning("Clone failed for %s: %s", key, stderr[:200] or exc)
        if target.exists():
            shutil.rmtree(target, ignore_errors=True)
        return None
    return target


def _dedupe_by_key(packages: list[Package]) -> list[Package]:
    """First-seen-wins dedup by canonical GitHub key."""
    seen: set[str] = set()
    deduped: list[Package] = []
    for package in packages:
        key = package_key(package)
        if key is None or key in seen:
            continue
        seen.add(key)
        deduped.append(package)
    return deduped


def clone_all(
    packages: list[Package],
    clones_dir: Path,
    *,
    parallelism: int = DEFAULT_PARALLELISM,
    timeout: float = DEFAULT_CLONE_TIMEOUT_SECONDS,
) -> tuple[int, int, int]:
    """Shallow-clone every package in parallel.

    Packages are deduplicated by canonical GitHub key before cloning so
    Reservoir + manual overlaps don't clone twice.

    Args:
        packages: Combined list of packages to clone.
        clones_dir: Root directory for the clones; created if missing.
        parallelism: Maximum concurrent ``git clone`` processes.
        timeout: Per-clone timeout in seconds.

    Returns:
        ``(cloned_now, already_present, failed)``. ``cloned_now`` counts
        repos a fresh clone produced this run; ``already_present`` counts
        repos that were cached on disk and skipped; ``failed`` counts
        repos that errored or had no usable URL.
    """
    clones_dir.mkdir(parents=True, exist_ok=True)
    queue = _dedupe_by_key(packages)

    cloned_now = 0
    already_present = 0
    failed = 0

    def _process(package: Package) -> tuple[Path | None, bool]:
        key = package_key(package)
        url = _repo_url(package)
        if not key or not url:
            return None, False
        existed = _target_for_key(clones_dir, key).exists()
        result = clone_package(package, clones_dir, timeout=timeout)
        return result, existed

    with ThreadPoolExecutor(max_workers=parallelism) as pool:
        futures = [pool.submit(_process, p) for p in queue]
        for future in as_completed(futures):
            result, existed = future.result()
            if result is None:
                failed += 1
            elif existed:
                already_present += 1
            else:
                cloned_now += 1
    return cloned_now, already_present, failed
