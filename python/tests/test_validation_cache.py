"""Check validation coverage, dependency invalidation, and pass-only cache reuse."""

from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from lean_pool.quality import _cached_pool_audits
from lean_pool.validation_cache import GLOBAL_INPUTS, ValidationCache, pool_units


def _inventory(root: Path, module: str, imports: tuple[str, ...] = ()) -> None:
    path = root / (".lake/build/ir/" + module.replace(".", "/") + ".setup.json")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"name": module, "importArts": dict.fromkeys(imports)}))


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    """Create independent units, a nested module, and compiler import inventories."""
    for module in ("LeanPool", "LeanPool.A", "LeanPool.A.Detail", "LeanPool.B"):
        path = tmp_path / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"-- {module}\n")
        _inventory(tmp_path, module)
    _inventory(tmp_path, "LeanPool", ("LeanPool.A", "LeanPool.A.Detail", "LeanPool.B"))
    for name in GLOBAL_INPUTS:
        if name in {"lakefile.lean", "scripts/nolints.json"}:
            continue
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("configuration\n")
    return tmp_path


def _run(root: Path, *, refresh: bool = False) -> tuple[ValidationCache, list[str]]:
    cache = ValidationCache(root, root / ".lake/validation-cache/v1", refresh=refresh)
    calls: list[str] = []
    for modules in pool_units(root):
        cache.check("lint", modules, lambda: calls.append(modules[0]) or [])
    cache.save()
    return cache, calls


def test_coverage_and_warm_reuse(repository: Path) -> None:
    """Every file belongs to a unit, even without a registry or umbrella import."""
    units = pool_units(repository)
    covered = [module for modules in units for module in modules]
    assert sorted(covered) == [
        "LeanPool",
        "LeanPool.A",
        "LeanPool.A.Detail",
        "LeanPool.B",
    ]
    assert len(_run(repository)[1]) == 3
    assert _run(repository)[1] == []
    assert len(_run(repository, refresh=True)[1]) == 3


def test_project_edit_leaves_sibling_cached(repository: Path) -> None:
    """A rebase reuses identical sources regardless of commit SHA or registry order."""
    _run(repository)
    (repository / "LeanPool/projects.yml").write_text("projects: []\n")
    assert _run(repository)[1] == []
    (repository / "LeanPool/A/Detail.lean").write_text("-- edited nested source\n")
    assert _run(repository)[1] == ["LeanPool.A", "LeanPool"]


def test_transitive_import_of_nested_module_invalidates_consumer(
    repository: Path,
) -> None:
    """Dependencies of each nested module count, not just umbrella dependencies."""
    _inventory(repository, "LeanPool.A.Detail", ("LeanPool.B",))
    _run(repository)
    (repository / "LeanPool/B.lean").write_text("-- dependency edit\n")
    assert len(_run(repository)[1]) == 3


@pytest.mark.parametrize("name", GLOBAL_INPUTS)
def test_checker_and_dependency_changes_invalidate_all(
    repository: Path, name: str
) -> None:
    """Toolchain, dependencies, lint options, and checker implementations are inputs."""
    _run(repository)
    (repository / name).write_text("changed\n")
    assert len(_run(repository)[1]) == 3


@pytest.mark.parametrize("contents", [None, "{", "{}", '{"name": "wrong"}'])
def test_missing_inventory_falls_back_conservatively(
    repository: Path, contents
) -> None:
    """A missing/broken nested inventory must not produce a false cache hit."""
    path = repository / ".lake/build/ir/LeanPool/A/Detail.setup.json"
    if contents is None:
        path.unlink()
    else:
        path.write_text(contents)
    _run(repository)
    (repository / "LeanPool/B.lean").write_text("-- changed\n")
    assert len(_run(repository)[1]) == 3


def test_metadata_is_scoped_to_one_project(repository: Path) -> None:
    """Changing one card's declaration list invalidates that check only."""
    modules = ["LeanPool.A"]
    cache = ValidationCache(repository, repository / ".lake/validation-cache/v1")
    cache.check("declarations", modules, lambda: [], {"main_declarations": ["a"]})
    cache.save()
    cache = ValidationCache(repository, cache.directory)
    assert cache.check(
        "declarations", modules, lambda: ["error"], {"main_declarations": ["b"]}
    ) == ["error"]


def test_failures_and_corrupt_receipts_are_rechecked(repository: Path) -> None:
    """Failed validators and malformed saved data cannot create successful hits."""
    cache = ValidationCache(repository, repository / ".lake/validation-cache/v1")
    assert cache.check("lint", ["LeanPool.A"], lambda: ["bad proof"]) == ["bad proof"]
    cache.save()
    assert _run(repository)[0].misses == 3
    (cache.directory / "passes.json").write_text("broken")
    assert _run(repository)[0].misses == 3


def test_added_deleted_sources_change_coverage(repository: Path) -> None:
    """New files are checked and deleted units are removed from the cache."""
    _run(repository)
    (repository / "LeanPool/B.lean").unlink()
    (repository / "LeanPool/C.lean").write_text("-- new project\n")
    _inventory(repository, "LeanPool.C")
    _inventory(repository, "LeanPool", ("LeanPool.A", "LeanPool.C"))
    cache, calls = _run(repository)
    assert calls == ["LeanPool.C", "LeanPool"]
    assert "lint:LeanPool.B" not in cache.used


def test_quality_audits_cover_every_owned_module(repository: Path) -> None:
    """Cold and warm checks preserve complete axiom/backdoor coverage."""
    cache = ValidationCache(repository, repository / ".lake/validation-cache/v1")
    with (
        patch("lean_pool.quality._audit_axioms", return_value=[]) as axioms,
        patch("lean_pool.quality._run_option_audit", return_value=[]) as backdoors,
    ):
        assert _cached_pool_audits(repository, cache) == []
        assert [call.args[2] for call in axioms.call_args_list] == pool_units(
            repository
        )
        assert [
            call.kwargs["only_modules"] for call in backdoors.call_args_list
        ] == pool_units(repository)
        cache.save()
        cache = ValidationCache(repository, cache.directory)
        assert _cached_pool_audits(repository, cache) == []
        assert axioms.call_count == backdoors.call_count == 3
