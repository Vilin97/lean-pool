"""Keep shared cache producers and consumers compatible across CI workflows."""

from __future__ import annotations

from pathlib import Path

import yaml

WORKFLOWS = Path(__file__).resolve().parents[2] / ".github/workflows"


def test_shared_cache_paths_and_keys_match() -> None:
    """Cache versions include paths, so consumers must match the producer's contract."""
    contracts = {}
    producers = {}
    for path in WORKFLOWS.glob("*.yml"):
        workflow = yaml.safe_load(path.read_text())
        for job in workflow.get("jobs", {}).values():
            for step in job.get("steps", []):
                if not step.get("uses", "").startswith("actions/cache/"):
                    continue
                settings = step.get("with", {})
                key = settings.get("key", "")
                if key.startswith("LeanDependencies-v1-"):
                    category = "dependencies"
                    identity = key
                elif key.startswith("LeanPoolBuild-v1-"):
                    category = "build"
                    identity = key.rsplit("-${{", 1)[0] + "-"
                    if "restore-keys" in settings:
                        assert settings["restore-keys"].strip() == identity
                else:
                    continue
                paths = tuple(settings["path"].strip().splitlines())
                contract = (identity, paths)
                assert contracts.setdefault(category, contract) == contract, path
                if step["uses"].startswith("actions/cache/save@"):
                    producers[category] = True
    assert set(producers) == set(contracts) == {"dependencies", "build"}
    assert contracts["dependencies"][1] == ("~/.elan", ".lake/packages")
    assert contracts["build"][1] == (".lake/build",)
