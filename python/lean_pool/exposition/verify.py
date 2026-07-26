"""Verify that minimal Lean files really compile.

Assembles a minimal file for every target (default: each project card's
``main_declarations``) with the same builder module the browser uses
(``scripts/exposition/build-minimal.mjs``), then compiles each with
``lean`` against the built pool/Mathlib. A file passes when ``lean`` exits
zero and reports nothing beyond ``declaration uses 'sorry'`` warnings.

Run from ``python/`` with a generated site and LEAN_PATH set (or via
``lake env``)::

    uv run python -m lean_pool.exposition.verify \
        --site <site-dir> --repo-root .. --out <work-dir> [--jobs 3]
"""

from __future__ import annotations

import json
import logging
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

import click
import yaml

logger = logging.getLogger(__name__)

COMPILE_TIMEOUT_SECONDS = 600


@dataclass
class Target:
    """One declaration to verify."""

    project: str
    name: str


@dataclass
class Outcome:
    """Build + compile result for one target."""

    target: Target
    stage: str  # "pass" | "resolve" | "build" | "compile" | "timeout"
    detail: str = ""


def main_declaration_targets(repo_root: Path, site_dir: Path) -> list[Target]:
    """Every project card ``main_declarations`` entry with a generated shard."""
    registry = yaml.safe_load(
        (repo_root / "LeanPool" / "projects.yml").read_text(encoding="utf-8")
    )
    targets: list[Target] = []
    for entry in registry.get("projects", []):
        entry_module = entry.get("entry_module") or ""
        if not entry_module:
            continue
        slug = entry_module.split(".")[-1]
        if not (site_dir / "data" / "projects" / f"{slug}.json").is_file():
            logger.warning("no shard for project %s; skipping its targets", slug)
            continue
        for name in entry.get("main_declarations") or []:
            targets.append(Target(project=slug, name=name))
    return targets


def _build_one(
    repo_root: Path, site_dir: Path, out_dir: Path, index: int, target: Target
) -> tuple[Path | None, Outcome | None]:
    """Assemble one minimal file; return (path, failure-outcome)."""
    out_file = (
        out_dir / f"{index:03d}-{target.project}-{target.name.replace('.', '_')}.lean"
    )
    result = subprocess.run(
        [
            "node",
            str(repo_root / "scripts" / "exposition" / "build-minimal.mjs"),
            str(site_dir),
            str(repo_root),
            target.project,
            target.name,
            str(out_file),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 2:
        return None, Outcome(target, "resolve", result.stderr.strip()[:200])
    if result.returncode != 0:
        return None, Outcome(target, "build", result.stderr.strip()[:200])
    return out_file, None


def _compile_one(lean_command: str, target: Target, path: Path) -> Outcome:
    """Compile one assembled file; only sorry warnings may remain."""
    try:
        result = subprocess.run(
            [lean_command, str(path)],
            capture_output=True,
            text=True,
            timeout=COMPILE_TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return Outcome(target, "timeout")
    output = (result.stdout + result.stderr).strip()
    real_lines = [
        line
        for line in output.splitlines()
        if line.strip()
        and "declaration uses `sorry`" not in line
        and "declaration uses 'sorry'" not in line
    ]
    if result.returncode == 0 and not real_lines:
        return Outcome(target, "pass")
    return Outcome(target, "compile", "\n".join(real_lines[:6])[:500])


def preflight(lean_command: str, out_dir: Path) -> str | None:
    """Check that ``lean`` can see Mathlib; return an error message if it cannot.

    Without this, a missing LEAN_PATH makes every single target fail at
    ``import Mathlib`` and the report reads as a pipeline regression rather
    than a broken environment.
    """
    probe = out_dir / "_preflight.lean"
    probe.write_text("import Mathlib\n")
    try:
        result = subprocess.run(
            [lean_command, str(probe)],
            capture_output=True,
            text=True,
            timeout=COMPILE_TIMEOUT_SECONDS,
            check=False,
        )
    except (subprocess.TimeoutExpired, OSError) as error:
        return f"could not run `{lean_command}`: {error}"
    finally:
        probe.unlink(missing_ok=True)
    if result.returncode != 0:
        return (
            "`lean` cannot import Mathlib — LEAN_PATH is unset or wrong.\n"
            "Run under `lake env` from the repository root, e.g.\n"
            '  export LEAN_PATH="$(lake env printenv LEAN_PATH)"\n'
            f"lean said: {(result.stdout + result.stderr).strip()[:300]}"
        )
    return None


@click.command()
@click.option(
    "--site",
    "site_dir",
    type=click.Path(exists=True, file_okay=False, path_type=Path),
    required=True,
    help="Generated exposition site directory (with data/projects/).",
)
@click.option(
    "--repo-root",
    "repo_root",
    type=click.Path(exists=True, file_okay=False, path_type=Path),
    required=True,
    help="Repository root (sources + scripts/exposition/).",
)
@click.option(
    "--out",
    "out_dir",
    type=click.Path(file_okay=False, path_type=Path),
    required=True,
    help="Work directory for assembled files and the report.",
)
@click.option("--jobs", default=3, show_default=True, help="Concurrent lean compiles.")
@click.option(
    "--lean", "lean_command", default="lean", show_default=True, help="lean binary."
)
@click.option(
    "--limit", default=0, show_default=True, help="Verify only the first N targets."
)
@click.option(
    "--baseline",
    default=0,
    show_default=True,
    help="Minimum passing count to accept; 0 requires every target to pass.",
)
def cli(
    site_dir: Path,
    repo_root: Path,
    out_dir: Path,
    jobs: int,
    lean_command: str,
    limit: int,
    baseline: int,
) -> None:
    """Assemble and compile minimal files for every main declaration."""
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    out_dir.mkdir(parents=True, exist_ok=True)
    environment_error = preflight(lean_command, out_dir)
    if environment_error:
        raise click.ClickException(environment_error)
    targets = main_declaration_targets(repo_root, site_dir)
    if limit:
        targets = targets[:limit]
    click.echo(f"verifying {len(targets)} minimal files")

    outcomes: list[Outcome] = []
    compile_queue: list[tuple[Target, Path]] = []
    for index, target in enumerate(targets):
        path, failure = _build_one(repo_root, site_dir, out_dir, index, target)
        if failure:
            outcomes.append(failure)
        elif path:
            compile_queue.append((target, path))

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        outcomes.extend(
            pool.map(lambda item: _compile_one(lean_command, *item), compile_queue)
        )

    passed = sum(1 for outcome in outcomes if outcome.stage == "pass")
    report = {
        "total": len(targets),
        "passed": passed,
        "failures": [
            {
                "project": outcome.target.project,
                "name": outcome.target.name,
                "stage": outcome.stage,
                "detail": outcome.detail,
            }
            for outcome in outcomes
            if outcome.stage != "pass"
        ],
    }
    (out_dir / "report.json").write_text(json.dumps(report, indent=2))
    for failure in report["failures"]:
        click.echo(f"FAIL [{failure['stage']}] {failure['project']}/{failure['name']}")
    click.echo(f"passed {passed}/{len(targets)} (report: {out_dir / 'report.json'})")
    if passed == len(targets):
        return
    if baseline and passed >= baseline:
        click.echo(
            f"at or above the {baseline} baseline; {len(targets) - passed} still "
            "fail — see report.json"
        )
        if passed > baseline:
            click.echo(f"raise --baseline to {passed} to lock in the gain")
        return
    if baseline:
        click.echo(f"REGRESSION: {passed} passing is below the {baseline} baseline")
    sys.exit(1)


if __name__ == "__main__":
    cli()
