"""Cache isolated, per-project Lean extraction and assemble deterministic JSONL.

Run after ``lake build LeanPool``, inside ``lake env``. Lake's setup files
provide the transitive import inventory; missing inventories conservatively
invalidate against the whole pool instead of risking stale dependency data.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import shutil
import subprocess
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass
from pathlib import Path

from lean_pool.exposition.source_text import SourceFile, module_skeleton

LOGGER = logging.getLogger(__name__)
OUTPUTS = ("declarations.jsonl", "commands.jsonl")
GLOBAL_INPUTS = (
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "scripts/exposition/Extract.lean",
    "scripts/exposition/extract-all.sh",
    "python/lean_pool/exposition/extract.py",
    "python/lean_pool/exposition/source_text.py",
)


def file_digest(path: Path) -> str:
    """Hash a file without loading large extraction outputs into memory."""
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def projects(root: Path) -> list[str]:
    """Read the generated index, including module-system import modifiers."""
    source = SourceFile.from_text((root / "LeanPool.lean").read_text())
    names = sorted(
        {name.split(".")[1] for name in module_skeleton(source).local_imports}
    )
    if not names or any(
        not (root / f"LeanPool/{name}.lean").is_file() for name in names
    ):
        raise ValueError("LeanPool.lean must import existing project entry modules")
    return names


def project_sources(root: Path, project: str) -> set[Path]:
    """Include project sources and all local transitive imports recorded by Lake."""
    sources = {root / f"LeanPool/{project}.lean"}
    sources.update((root / "LeanPool" / project).rglob("*.lean"))
    setup = root / f".lake/build/ir/LeanPool/{project}.setup.json"
    try:
        inventory = json.loads(setup.read_text())
        if inventory["name"] != f"LeanPool.{project}":
            raise ValueError("wrong module in setup file")
        imports = inventory["importArts"]
        if not isinstance(imports, dict):
            raise ValueError("invalid import inventory")
        for module in imports:
            path = root / (module.replace(".", "/") + ".lean")
            if path.is_file():
                sources.add(path)
            elif module.startswith("LeanPool."):
                raise ValueError(f"missing imported source: {module}")
    except (OSError, ValueError, KeyError, TypeError):
        LOGGER.warning(
            "%s: no usable Lake import inventory; hashing the whole pool", project
        )
        sources.update((root / "LeanPool").rglob("*.lean"))
        sources.add(root / "LeanPool.lean")
    return sources


def fingerprint(root: Path, project: str, digests: dict[Path, str]) -> str:
    """Hash source contents, dependencies, build configuration, and extractor code."""
    paths = project_sources(root, project) | {root / name for name in GLOBAL_INPUTS}
    inputs = {}
    for path in sorted(paths):
        if path not in digests:
            digests[path] = file_digest(path)
        inputs[path.relative_to(root).as_posix()] = digests[path]
    return hashlib.sha256(json.dumps(inputs, sort_keys=True).encode()).hexdigest()


def cache_valid(directory: Path, expected: str) -> bool:
    """Reject partial, corrupt, and incompatible cached output pairs."""
    try:
        manifest = json.loads((directory / "manifest.json").read_text())
        return manifest["fingerprint"] == expected and all(
            file_digest(directory / name) == manifest["outputs"][name]
            for name in OUTPUTS
        )
    except (OSError, ValueError, KeyError, TypeError):
        return False


def validate_output(path: Path, required: set[str]) -> None:
    """Require complete JSONL records before publishing an extraction to the cache."""
    with path.open() as stream:
        for line in stream:
            record = json.loads(line)
            if not isinstance(record, dict) or not required <= record.keys():
                raise ValueError(f"Invalid extraction record in {path}")
            if not line.endswith("\n"):
                raise ValueError(f"Unterminated extraction record in {path}")


@dataclass
class Extraction:
    """Result and timing of one isolated project extraction."""

    project: str
    directory: Path
    cached: bool
    seconds: float


def extract_project(
    root: Path, cache: Path, project: str, digest: str, lean: str, refresh: bool
) -> Extraction:
    """Reuse a verified output pair or run Lean in this project's own environment."""
    started = time.monotonic()
    directory = cache / project / digest
    if not refresh and cache_valid(directory, digest):
        return Extraction(project, directory, True, time.monotonic() - started)
    directory.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="extract-", dir=directory.parent
    ) as temporary:
        staging = Path(temporary)
        command = [lean, "--run", "scripts/exposition/Extract.lean"]
        command += [str(staging / name) for name in OUTPUTS] + [f"LeanPool.{project}"]
        try:
            with (staging / "extract.log").open("w") as log:
                subprocess.run(command, cwd=root, stdout=log, stderr=log, check=True)
            validate_output(staging / OUTPUTS[0], {"id", "m"})
            validate_output(staging / OUTPUTS[1], {"m", "c"})
        except (subprocess.CalledProcessError, OSError, ValueError):
            shutil.copyfile(staging / "extract.log", directory.parent / "failed.log")
            LOGGER.exception(
                "%s failed; log: %s", project, directory.parent / "failed.log"
            )
            raise
        manifest = {"fingerprint": digest, "outputs": {}}
        manifest["outputs"] = {name: file_digest(staging / name) for name in OUTPUTS}
        (staging / "manifest.json").write_text(json.dumps(manifest) + "\n")
        if directory.exists():
            shutil.rmtree(directory)
        staging.replace(directory)
    elapsed = time.monotonic() - started
    LOGGER.info("%s: extracted in %.1fs", project, elapsed)
    return Extraction(project, directory, False, elapsed)


def combine(results: list[Extraction], destinations: tuple[Path, Path]) -> None:
    """Concatenate in project order, publishing only after every extraction succeeds."""
    for name, destination in zip(OUTPUTS, destinations, strict=True):
        destination.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(
            dir=destination.parent, delete=False
        ) as output:
            temporary = Path(output.name)
            try:
                for result in results:
                    with (result.directory / name).open("rb") as source:
                        shutil.copyfileobj(source, output)
                output.close()
                temporary.replace(destination)
            finally:
                temporary.unlink(missing_ok=True)


def prune_cache(cache: Path, results: list[Extraction]) -> None:
    """Save only current projects and their current generation in the CI cache."""
    retained = {result.directory for result in results}
    for path in cache.iterdir():
        if path.is_dir():
            for generation in path.iterdir():
                if generation.is_dir() and generation not in retained:
                    shutil.rmtree(generation)
            if path.name not in {result.project for result in results}:
                shutil.rmtree(path)


def run_extraction(
    root: Path,
    cache: Path,
    destinations: tuple[Path, Path],
    jobs: int = 2,
    lean: str = "lean",
    refresh: bool = False,
) -> list[Extraction]:
    """Extract every indexed project, reusing only matching content-addressed data."""
    if jobs < 1:
        raise ValueError("jobs must be positive")
    names = projects(root)
    digests: dict[Path, str] = {}
    fingerprints = {name: fingerprint(root, name, digests) for name in names}
    LOGGER.info("Extracting %d projects (%d at a time)", len(names), jobs)
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = [
            executor.submit(
                extract_project, root, cache, name, fingerprints[name], lean, refresh
            )
            for name in names
        ]
        results = [future.result() for future in futures]
    combine(results, destinations)
    prune_cache(cache, results)
    return results


def main() -> None:
    """Run extraction from the repository root with Lean's environment available."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "declarations", nargs="?", type=Path, default=Path("exposition-dump.jsonl")
    )
    parser.add_argument(
        "commands", nargs="?", type=Path, default=Path("exposition-commands.jsonl")
    )
    parser.add_argument("--cache", type=Path, default=Path(".lake/exposition-cache/v1"))
    parser.add_argument(
        "--jobs", type=int, default=int(os.environ.get("EXTRACT_JOBS", "2"))
    )
    parser.add_argument("--lean", default=os.environ.get("LEAN_CMD", "lean"))
    parser.add_argument(
        "--refresh", action="store_true", help="Re-extract even valid cache hits"
    )
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="exposition: %(message)s")
    started = time.monotonic()
    results = run_extraction(
        Path.cwd(),
        arguments.cache.resolve(),
        (arguments.declarations, arguments.commands),
        arguments.jobs,
        arguments.lean,
        arguments.refresh,
    )
    report = {
        "seconds": time.monotonic() - started,
        "projects": [asdict(item) for item in results],
    }
    Path(".lake/exposition-timings.json").write_text(
        json.dumps(report, default=str, indent=2) + "\n"
    )
    LOGGER.info(
        "Finished in %.1fs; %d/%d cache hits",
        report["seconds"],
        sum(item.cached for item in results),
        len(results),
    )


if __name__ == "__main__":
    main()
