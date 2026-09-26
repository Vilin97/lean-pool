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


def _docs_condition(condition: str, event: str, ref: str, preview: bool, readme: bool):
    """Evaluate the small event predicate used by docs job allocation."""
    expression = condition
    values = {
        "needs.preflight.outputs.readme_only": repr(str(readme).lower()),
        "github.event_name": repr(event),
        "github.ref": repr(ref),
        "inputs.preview": repr(preview),
    }
    for name, value in values.items():
        expression = expression.replace(name, value)
    return eval(
        expression.replace("&&", " and ").replace("||", " or "),
        {"__builtins__": {}},
        {},
    )


def test_docs_generate_on_main_and_explicit_preview_only() -> None:
    """A PR runs its protected preflight without allocating heavy docs runners."""
    jobs = yaml.safe_load((WORKFLOWS / "docs.yml").read_text())["jobs"]
    assert jobs["preflight"]["name"] == "Documentation preflight"
    assert "if" not in jobs["preflight"]
    scenarios = [
        ("pull_request", "refs/pull/123/merge", False, False, False),
        ("push", "refs/heads/main", False, False, True),
        ("workflow_dispatch", "refs/heads/main", False, False, True),
        ("workflow_dispatch", "refs/heads/topic", False, False, False),
        ("workflow_dispatch", "refs/heads/topic", True, False, True),
        ("pull_request", "refs/pull/123/merge", True, False, False),
        ("push", "refs/heads/main", False, True, False),
    ]
    for name in ("exposition", "mathlib_doc_info", "build"):
        for event, ref, preview, readme, expected in scenarios:
            assert (
                _docs_condition(jobs[name]["if"], event, ref, preview, readme)
                == expected
            )
    # Branch previews produce artifacts but cannot replace production Pages.
    assert not _docs_condition(
        jobs["deployment_freshness"]["if"],
        "workflow_dispatch",
        "refs/heads/topic",
        True,
        False,
    )


def test_single_and_sharded_builds_use_validation_cache() -> None:
    """Both execution paths validate before saving receipts and keep the same gate."""
    jobs = yaml.safe_load((WORKFLOWS / "lean_action_ci.yml").read_text())["jobs"]
    assert jobs["gate"]["name"] == "Build project"
    contracts = []
    for job in ("build", "finalize"):
        steps = jobs[job]["steps"]
        names = [step.get("name") for step in steps]
        assert names.index("Restore project validation") < names.index("Lint")
        assert names.index("Repository quality checks") < names.index(
            "Save project validation"
        )
        restore = steps[names.index("Restore project validation")]
        save = steps[names.index("Save project validation")]
        assert restore["with"]["key"] == save["with"]["key"]
        assert (
            restore["with"]["path"]
            == save["with"]["path"]
            == ".lake/validation-cache/v1"
        )
        assert "if" not in save  # normal success guard, including PR updates
        contracts.append(restore["with"])
        assert "validation_cache lint" in steps[names.index("Lint")]["run"]
        assert "runLinter Challenge" in steps[names.index("Lint")]["run"]
        assert "runLinter Solution" in steps[names.index("Lint")]["run"]
        assert "lint-style LeanPool" in steps[names.index("Text style lint")]["run"]
    assert contracts[0] == contracts[1]
