"""Reuse successful project validation after compiling the current checkout.

CI restores receipts from main or earlier runs of the same PR. Every receipt
covers module inventories, transitive local imports, dependency pins, and code.
Static repository invariants and text style lint still run on every checkout.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import subprocess
from collections.abc import Callable
from pathlib import Path
from typing import Any

LOGGER = logging.getLogger(__name__)
GLOBAL_INPUTS = (
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "lakefile.lean",
    "scripts/nolints.json",
    "scripts/nolints-style.txt",
    "scripts/ci/lint-project.lean",
    "python/lean_pool/quality.py",
    "python/lean_pool/challenge.py",
    "python/lean_pool/validation_cache.py",
    "python/pyproject.toml",
    "python/uv.lock",
    ".github/workflows/lean_action_ci.yml",
)


def pool_units(root: Path) -> list[list[str]]:
    """Partition every pool source, including the root and unregistered modules."""
    units: dict[str, list[str]] = {}
    for path in sorted((root / "LeanPool").rglob("*.lean")):
        relative = path.relative_to(root).with_suffix("")
        unit = relative.parts[1]
        units.setdefault(unit, []).append(".".join(relative.parts))
    if (root / "LeanPool.lean").exists():
        units["__root__"] = ["LeanPool"]
    return [sorted(modules) for _, modules in sorted(units.items())]


def source_inventory(root: Path, modules: list[str]) -> set[Path]:
    """Use every module's compiler inventory; fall back to all local Lean sources."""
    paths = {root / (module.replace(".", "/") + ".lean") for module in modules}
    try:
        for module in modules:
            setup = root / (
                ".lake/build/ir/" + module.replace(".", "/") + ".setup.json"
            )
            inventory = json.loads(setup.read_text())
            if inventory["name"] != module or not isinstance(
                inventory["importArts"], dict
            ):
                raise ValueError("invalid compiler inventory")
            for imported in inventory["importArts"]:
                path = root / (imported.replace(".", "/") + ".lean")
                if path.is_file():
                    paths.add(path)
                elif imported.split(".")[0] in {"LeanPool", "Challenge", "Solution"}:
                    raise ValueError(f"missing imported source: {imported}")
    except (OSError, ValueError, KeyError, TypeError):
        LOGGER.warning(
            "%s: missing import inventory; hashing all local sources", modules[0]
        )
        for library in ("LeanPool", "Challenge", "Solution"):
            paths.update((root / library).rglob("*.lean"))
            index = root / f"{library}.lean"
            if index.exists():
                paths.add(index)
    return paths


class ValidationCache:
    """Store pass receipts only, with content fingerprints and atomic publication."""

    def __init__(self, root: Path, directory: Path, *, refresh: bool = False) -> None:
        """Load optional receipts; a missing or corrupt cache is a cold run."""
        self.root = root
        self.directory = directory
        self.refresh = refresh
        self.digests: dict[Path, str] = {}
        self.receipts: dict[str, dict[str, Any]] = {}
        self.used: dict[str, dict[str, Any]] = {}
        self.hits = 0
        self.misses = 0
        try:
            data = json.loads((directory / "passes.json").read_text())
            if data["version"] == 1 and isinstance(data["receipts"], dict):
                self.receipts = data["receipts"]
        except (OSError, ValueError, KeyError, TypeError):
            pass

    def fingerprint(self, modules: list[str], metadata: Any = None) -> str:
        """Hash all checked inputs, retaining missing optional files in the key."""
        paths = source_inventory(self.root, modules)
        paths.update(self.root / name for name in GLOBAL_INPUTS)
        inputs = {}
        for path in sorted(paths):
            if path not in self.digests:
                self.digests[path] = (
                    hashlib.sha256(path.read_bytes()).hexdigest()
                    if path.is_file()
                    else "missing"
                )
            inputs[path.relative_to(self.root).as_posix()] = self.digests[path]
        payload = {"inputs": inputs, "modules": modules, "metadata": metadata}
        return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()

    def check[T](
        self,
        kind: str,
        modules: list[str],
        validate: Callable[[], list[T]],
        metadata: Any = None,
    ) -> list[T]:
        """Run on a miss and retain only passes; failures never create receipts."""
        digest = self.fingerprint(modules, metadata)
        key = f"{kind}:{modules[0]}"
        expected = {"fingerprint": digest, "modules": modules, "passed": True}
        if not self.refresh and self.receipts.get(key) == expected:
            self.hits += 1
            self.used[key] = expected
            LOGGER.info("%s: cache hit", key)
            return []
        self.misses += 1
        LOGGER.info("%s: validating", key)
        errors = validate()
        if not errors:
            self.used[key] = expected
        return errors

    def save(self) -> None:
        """Publish only receipts used in this run, pruning deleted/changed projects."""
        self.directory.mkdir(parents=True, exist_ok=True)
        temporary = self.directory / "passes.tmp"
        temporary.write_text(json.dumps({"version": 1, "receipts": self.used}) + "\n")
        temporary.replace(self.directory / "passes.json")
        LOGGER.info(
            "Validation: %d cached checks, %d fresh checks", self.hits, self.misses
        )


def lint_pool(root: Path, cache: ValidationCache) -> None:
    """Lint owned declarations once per unit, importing every owned module."""
    for modules in pool_units(root):

        def validate() -> list[str]:
            subprocess.run(
                [
                    "lake",
                    "env",
                    "lean",
                    "--run",
                    "scripts/ci/lint-project.lean",
                    *modules,
                ],
                cwd=root,
                check=True,
            )
            return []

        cache.check("lint", modules, validate)


def main() -> int:
    """Run the cached declaration linter or repository quality checker."""
    from lean_pool.quality import run_checks

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=("lint", "quality"))
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--cache", type=Path, default=Path(".lake/validation-cache/v1"))
    parser.add_argument("--refresh", action="store_true")
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="validation: %(message)s")
    root = arguments.repo.resolve()
    cache = ValidationCache(root, root / arguments.cache, refresh=arguments.refresh)
    if arguments.check == "lint":
        lint_pool(root, cache)
        # Keep quality receipts for the subsequent step.
        cache.used = {
            key: receipt
            for key, receipt in cache.receipts.items()
            if not key.startswith("lint:")
        } | cache.used
        errors = []
    else:
        errors = run_checks(root, validation_cache=cache)
        cache.used |= {
            key: receipt
            for key, receipt in cache.receipts.items()
            if key.startswith("lint:")
        }
    for error in errors:
        print(error.format(root))
    if errors:
        return 1
    cache.save()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
