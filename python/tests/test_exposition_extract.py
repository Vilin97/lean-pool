"""Exercise incremental extraction, invalidation, and failure publication rules."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from lean_pool.exposition.extract import GLOBAL_INPUTS, OUTPUTS, run_extraction


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    """Create two projects and a fake Lean process producing valid extractor JSONL."""
    for name in GLOBAL_INPUTS:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("configuration\n")
    (tmp_path / "LeanPool").mkdir()
    (tmp_path / "LeanPool.lean").write_text(
        "public import LeanPool.B\nimport LeanPool.A\n"
    )
    for project in ("A", "B"):
        (tmp_path / f"LeanPool/{project}.lean").write_text(f"-- {project}\n")
        _inventory(tmp_path, project, {})
    executable = tmp_path / "lean"
    executable.write_text(
        f"#!{sys.executable}\n"
        "import json, pathlib, sys\n"
        "_, _, _, declarations, commands, module = sys.argv\n"
        "with open('calls', 'a') as log: log.write(module + '\\n')\n"
        "if pathlib.Path('fail').exists(): raise SystemExit(1)\n"
        "source = pathlib.Path(module.replace('.', '/') + '.lean').read_text()\n"
        "data = {'id': module + '.theorem', 'm': module, 'source': source}\n"
        "pathlib.Path(declarations).write_text(json.dumps(data) + '\\n')\n"
        "commands_data = json.dumps({'m': module, 'c': []})\n"
        "pathlib.Path(commands).write_text(commands_data + '\\n')\n"
    )
    executable.chmod(0o755)
    return tmp_path


def _inventory(root: Path, project: str, imports: dict) -> None:
    path = root / f".lake/build/ir/LeanPool/{project}.setup.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"name": f"LeanPool.{project}", "importArts": imports}))


def _run(root: Path, refresh: bool = False):
    return run_extraction(
        root,
        root / ".lake/exposition-cache/v1",
        tuple(root / name for name in OUTPUTS),
        lean=str(root / "lean"),
        refresh=refresh,
    )


def _outputs(root: Path) -> tuple[bytes, ...]:
    return tuple((root / name).read_bytes() for name in OUTPUTS)


def test_warm_cache_and_refresh_match_cold_outputs(repository: Path) -> None:
    """Warm builds skip Lean completely; forced extraction produces identical data."""
    assert not any(item.cached for item in _run(repository))
    expected = _outputs(repository)
    assert [json.loads(line)["m"] for line in expected[0].splitlines()] == [
        "LeanPool.A",
        "LeanPool.B",
    ]
    assert all(item.cached for item in _run(repository))
    assert len((repository / "calls").read_text().splitlines()) == 2
    assert _outputs(repository) == expected
    assert not any(item.cached for item in _run(repository, refresh=True))
    assert _outputs(repository) == expected


def test_edit_only_reextracts_affected_project(repository: Path) -> None:
    """A project source edit invalidates that project without repeating its siblings."""
    _run(repository)
    (repository / "LeanPool/A.lean").write_text("-- changed\n")
    assert [item.cached for item in _run(repository)] == [False, True]
    expected = _outputs(repository)
    _run(repository, refresh=True)
    assert _outputs(repository) == expected


def test_transitive_import_invalidates_consumer(repository: Path) -> None:
    """Cross-project dependencies come from the compiler's transitive inventory."""
    _inventory(repository, "B", {"LeanPool.A": {"olean": "irrelevant"}})
    _run(repository)
    (repository / "LeanPool/A.lean").write_text("-- changed dependency\n")
    assert not any(item.cached for item in _run(repository))


@pytest.mark.parametrize("name", GLOBAL_INPUTS)
def test_global_input_invalidates_every_project(repository: Path, name: str) -> None:
    """Toolchain, configuration, dependency pins, and extractor edits invalidate all."""
    _run(repository)
    (repository / name).write_text("changed configuration\n")
    assert not any(item.cached for item in _run(repository))


@pytest.mark.parametrize("contents", [None, "broken", "{}", '{"name": "wrong"}'])
def test_missing_inventory_conservatively_hashes_pool(
    repository: Path, contents
) -> None:
    """Older cache formats never silently miss a cross-project dependency."""
    path = repository / ".lake/build/ir/LeanPool/B.setup.json"
    if contents is None:
        path.unlink()
    else:
        path.write_text(contents)
    _run(repository)
    (repository / "LeanPool/A.lean").write_text("-- changed\n")
    assert not any(item.cached for item in _run(repository))


def test_deleted_project_disappears_from_outputs_and_cache(repository: Path) -> None:
    """Assembly uses the current index, never stale cached project names."""
    _run(repository)
    (repository / "LeanPool.lean").write_text("import LeanPool.B\n")
    (repository / "LeanPool/A.lean").unlink()
    assert [item.project for item in _run(repository)] == ["B"]
    assert b"LeanPool.A" not in _outputs(repository)[0]
    assert not (repository / ".lake/exposition-cache/v1/A").exists()


@pytest.mark.parametrize("name", [*OUTPUTS, "manifest.json"])
def test_corrupt_cache_reextracts_project(repository: Path, name: str) -> None:
    """Both outputs and their manifest must be intact to reuse a project."""
    results = _run(repository)
    expected = _outputs(repository)
    (results[0].directory / name).write_text("corrupt")
    assert [item.cached for item in _run(repository)] == [False, True]
    assert _outputs(repository) == expected


def test_failed_extraction_keeps_published_output_and_diagnostics(
    repository: Path,
) -> None:
    """A failed process cannot publish a truncated aggregate or a successful cache."""
    _run(repository)
    expected = _outputs(repository)
    (repository / "fail").touch()
    (repository / "LeanPool/A.lean").write_text("-- changed\n")
    with pytest.raises(subprocess.CalledProcessError):
        _run(repository)
    assert _outputs(repository) == expected
    assert (repository / ".lake/exposition-cache/v1/A/failed.log").exists()
    (repository / "fail").unlink()
    assert [item.cached for item in _run(repository)] == [False, True]


def test_invalid_jsonl_is_not_cached(repository: Path) -> None:
    """A zero exit code with malformed extraction output is still a failed run."""
    executable = repository / "lean"
    executable.write_text(
        executable.read_text().replace("json.dumps(data)", "'broken'")
    )
    with pytest.raises(ValueError):
        _run(repository)
    assert not (repository / OUTPUTS[0]).exists()
    assert not list(
        (repository / ".lake/exposition-cache/v1").glob("*/*/manifest.json")
    )


def test_empty_extraction_is_not_cached(repository: Path) -> None:
    """A successful exit with no records is a failed extraction, never a cache entry."""
    executable = repository / "lean"
    executable.write_text(
        executable.read_text().replace(
            "pathlib.Path(declarations).write_text(json.dumps(data) + '\\n')",
            "pathlib.Path(declarations).write_text('')",
        )
    )
    with pytest.raises(ValueError, match="Empty extraction output"):
        _run(repository)
    assert not (repository / OUTPUTS[0]).exists()
    assert not list(
        (repository / ".lake/exposition-cache/v1").glob("*/*/manifest.json")
    )


def test_additional_source_invalidates_project(repository: Path) -> None:
    """Adding a module changes the project key even before the inventory mentions it."""
    _run(repository)
    directory = repository / "LeanPool/A"
    directory.mkdir()
    (directory / "New.lean").write_text("-- new module\n")
    assert [item.cached for item in _run(repository)] == [False, True]
