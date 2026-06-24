"""CLI entry point for the aggregator.

Run with ``uv run python -m lean_pool.aggregator <subcommand>`` from
``python/``. Subcommands:

- ``fetch``: download the Reservoir manifest and the manual package
  list into ``raw_data/``.
- ``clone``: shallow-clone every candidate repo into
  ``raw_data/clones/`` so downstream classification can read source
  files locally.
- ``render``: regenerate the candidates README table from those files.
- ``discover``: query GitHub and arXiv for recent untracked Lean
  projects and add them to ``candidates/discovered.yml``.
"""

import json
from pathlib import Path

import click

from lean_pool.aggregator.cloner import (
    DEFAULT_PARALLELISM,
    clone_all,
)
from lean_pool.aggregator.discovery import (
    DEFAULT_LOOKBACK_DAYS,
    github_token_from_environment,
    load_known_repository_keys,
    render_discovery_report,
    save_discovery_report,
    update_discovered_file,
)
from lean_pool.aggregator.discovery import (
    discover as run_discovery,
)
from lean_pool.aggregator.manual import (
    fetch_manual_packages,
    load_manual_packages,
    parse_manual_list,
    save_manual_packages,
)
from lean_pool.aggregator.render import (
    load_decisions,
    load_pool_repos,
    render_table,
    update_readme,
)
from lean_pool.aggregator.reservoir import (
    MANIFEST_URL,
    fetch_manifest,
    save_manifest,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
CANDIDATES_DIR = REPO_ROOT / "candidates"
DEFAULT_MANIFEST = CANDIDATES_DIR / "raw_data" / "manifest.json"
DEFAULT_MANUAL_LIST = CANDIDATES_DIR / "manual.txt"
DEFAULT_MANUAL_DATA = CANDIDATES_DIR / "raw_data" / "manual_packages.json"
DEFAULT_MANUAL_CACHE = CANDIDATES_DIR / "raw_data" / "manual_cache"
DEFAULT_CLONES_DIR = CANDIDATES_DIR / "raw_data" / "clones"
DEFAULT_DECISIONS = CANDIDATES_DIR / "decisions.jsonl"
DEFAULT_README = CANDIDATES_DIR / "README.md"
DEFAULT_PROJECTS_YML = REPO_ROOT / "LeanPool" / "projects.yml"
DEFAULT_DISCOVERED = CANDIDATES_DIR / "discovered.yml"


@click.group()
def cli() -> None:
    """Aggregate Lean packages from Reservoir."""


@cli.command()
@click.option(
    "--url",
    default=MANIFEST_URL,
    show_default=True,
    help="Reservoir manifest URL.",
)
@click.option(
    "--output",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_MANIFEST,
    show_default=True,
    help="Where to save the downloaded manifest.",
)
@click.option(
    "--manual-list",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_MANUAL_LIST,
    show_default=True,
    help="Manual GitHub URL list to fetch alongside the manifest.",
)
@click.option(
    "--manual-output",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_MANUAL_DATA,
    show_default=True,
    help="Where to save the manual package metadata.",
)
@click.option(
    "--manual-cache",
    type=click.Path(file_okay=False, path_type=Path),
    default=DEFAULT_MANUAL_CACHE,
    show_default=True,
    help="Per-entry cache directory; cached entries skip the API call.",
)
def fetch(
    url: str,
    output: Path,
    manual_list: Path,
    manual_output: Path,
    manual_cache: Path,
) -> None:
    """Download the Reservoir manifest and manual package metadata."""
    manifest = fetch_manifest(url)
    save_manifest(manifest, output)
    click.echo(f"Saved {len(manifest['packages'])} packages to {output}")

    if manual_list.exists():
        entries = parse_manual_list(manual_list)
        manual_packages = fetch_manual_packages(entries, manual_cache)
        save_manual_packages(manual_packages, manual_output)
        click.echo(f"Saved {len(manual_packages)} manual packages to {manual_output}")
    else:
        click.echo(f"No manual list at {manual_list}; skipping manual fetch.")


@cli.command()
@click.option(
    "--manifest",
    "manifest_path",
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
    default=DEFAULT_MANIFEST,
    show_default=True,
    help="Manifest JSON produced by `fetch`.",
)
@click.option(
    "--manual-data",
    "manual_data_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_MANUAL_DATA,
    show_default=True,
    help="Manual package metadata produced by `fetch`.",
)
@click.option(
    "--clones-dir",
    type=click.Path(file_okay=False, path_type=Path),
    default=DEFAULT_CLONES_DIR,
    show_default=True,
    help="Where to write shallow blobless clones.",
)
@click.option(
    "--parallelism",
    type=int,
    default=DEFAULT_PARALLELISM,
    show_default=True,
    help="Maximum concurrent `git clone` processes.",
)
def clone(
    manifest_path: Path,
    manual_data_path: Path,
    clones_dir: Path,
    parallelism: int,
) -> None:
    """Shallow-clone every candidate repo into the local cache."""
    with manifest_path.open() as manifest_file:
        manifest = json.load(manifest_file)
    manual_packages = load_manual_packages(manual_data_path)
    packages = list(manifest["packages"]) + manual_packages
    cloned_now, already_present, failed = clone_all(
        packages, clones_dir, parallelism=parallelism
    )
    click.echo(
        f"Clones at {clones_dir}: "
        f"{cloned_now} new, {already_present} cached, {failed} failed."
    )


@cli.command()
@click.option(
    "--manifest",
    "manifest_path",
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
    default=DEFAULT_MANIFEST,
    show_default=True,
    help="Manifest JSON to render from.",
)
@click.option(
    "--manual-data",
    "manual_data_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_MANUAL_DATA,
    show_default=True,
    help="Manual package metadata produced by `fetch`.",
)
@click.option(
    "--clones-dir",
    type=click.Path(file_okay=False, path_type=Path),
    default=DEFAULT_CLONES_DIR,
    show_default=True,
    help=(
        "Local clone cache (produced by `clone`). Used to read each "
        "repo's `lean-toolchain` for the Lean column; pass a missing "
        "directory to leave that column blank."
    ),
)
@click.option(
    "--min-stars",
    type=int,
    default=2,
    show_default=True,
    help=(
        "Drop rows with fewer stars than this from the rendered table. "
        "Underlying data files keep every package; this only affects "
        "the markdown table size so GitHub keeps rendering it."
    ),
)
@click.option(
    "--min-loc",
    type=int,
    default=250,
    show_default=True,
    help=(
        "Drop rows whose local clone has fewer .lean lines than this. "
        "Counts every .lean file outside .lake/.git/build dirs. Repos "
        "with no local clone (LOC unknown) are kept; this is purely a "
        "preliminary filter to remove empty/MWE/scratch projects. "
        "Pass 0 to disable; effective only when --clones-dir exists."
    ),
)
@click.option(
    "--decisions",
    "decisions_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_DECISIONS,
    show_default=True,
    help=(
        "Classifier verdicts (JSONL). When the file exists, rows whose "
        "canonical key has include=false are dropped. Repos with no "
        "verdict are kept regardless. Pass a missing path to disable."
    ),
)
@click.option(
    "--readme",
    "readme_path",
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
    default=DEFAULT_README,
    show_default=True,
    help="Candidates README to update in place.",
)
@click.option(
    "--projects-yml",
    "projects_yml_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_PROJECTS_YML,
    show_default=True,
    help=(
        "Path to LeanPool/projects.yml. Each project's optional "
        "`source.github_repo` field marks the upstream candidate as "
        "merged, putting a ✓ in the In Pool column. Pass a missing "
        "path to leave the column blank for every row."
    ),
)
def render(
    manifest_path: Path,
    manual_data_path: Path,
    clones_dir: Path,
    min_stars: int,
    min_loc: int,
    decisions_path: Path,
    readme_path: Path,
    projects_yml_path: Path,
) -> None:
    """Render the candidates README table from a manifest."""
    with manifest_path.open() as manifest_file:
        manifest = json.load(manifest_file)
    manual_packages = load_manual_packages(manual_data_path)
    combined = {**manifest, "packages": list(manifest["packages"]) + manual_packages}
    effective_clones_dir = clones_dir if clones_dir.exists() else None
    decisions = load_decisions(decisions_path)
    pool_repos = load_pool_repos(projects_yml_path)
    table = render_table(
        combined,
        clones_dir=effective_clones_dir,
        min_stars=min_stars,
        min_loc=min_loc,
        decisions=decisions,
        pool_repos=pool_repos,
    )
    update_readme(readme_path, table)
    rendered_rows = sum(1 for line in table.splitlines() if line.startswith("| "))
    # Subtract the two header lines from the count.
    rendered_rows = max(0, rendered_rows - 2)
    click.echo(
        f"Rendered {rendered_rows} of {len(combined['packages'])} packages "
        f"({len(manifest['packages'])} reservoir + {len(manual_packages)} manual; "
        f"min-stars={min_stars}, min-loc={min_loc}, "
        f"decisions={len(decisions)}, pool={len(pool_repos)}) into {readme_path}"
    )


@cli.command("discover")
@click.option(
    "--lookback-days",
    type=int,
    default=DEFAULT_LOOKBACK_DAYS,
    show_default=True,
    help="How many days of GitHub and arXiv activity to scan.",
)
@click.option(
    "--manifest",
    "manifest_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_MANIFEST,
    show_default=True,
    help="Reservoir manifest JSON used to suppress already-tracked repos.",
)
@click.option(
    "--manual-list",
    "manual_list_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_MANUAL_LIST,
    show_default=True,
    help="Manual GitHub URL list used to suppress already-tracked repos.",
)
@click.option(
    "--manual-data",
    "manual_data_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_MANUAL_DATA,
    show_default=True,
    help="Manual package metadata used to suppress already-tracked repos.",
)
@click.option(
    "--projects-yml",
    "projects_yml_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_PROJECTS_YML,
    show_default=True,
    help="Lean Pool project registry used to suppress already-merged repos.",
)
@click.option(
    "--include-known/--skip-known",
    default=False,
    show_default=True,
    help="Include repositories that are already tracked locally.",
)
@click.option(
    "--max-github-results-per-query",
    type=int,
    default=100,
    show_default=True,
    help="Maximum GitHub search results fetched for each query.",
)
@click.option(
    "--output",
    "output_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=None,
    help="Optional local markdown report path.",
)
@click.option(
    "--discovered",
    "discovered_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=DEFAULT_DISCOVERED,
    show_default=True,
    help="YAML file to update with newly discovered GitHub/arXiv entries.",
)
def discover(
    lookback_days: int,
    manifest_path: Path,
    manual_list_path: Path,
    manual_data_path: Path,
    projects_yml_path: Path,
    include_known: bool,
    max_github_results_per_query: int,
    output_path: Path | None,
    discovered_path: Path,
) -> None:
    """Query GitHub/arXiv for recent untracked Lean projects."""
    known = load_known_repository_keys(
        manifest_path=manifest_path,
        manual_list_path=manual_list_path,
        manual_data_path=manual_data_path,
        projects_yml_path=projects_yml_path,
    )
    result = run_discovery(
        lookback_days=lookback_days,
        known_repositories=set(known),
        github_token=github_token_from_environment(),
        include_known=include_known,
        max_github_results_per_query=max_github_results_per_query,
    )
    report = render_discovery_report(result)
    if output_path is not None:
        save_discovery_report(report, output_path)
    update = update_discovered_file(result, discovered_path)

    candidate_count = sum(
        1 for repository in result.github_repositories if repository.signal != "low"
    )
    click.echo(
        f"Discovery found {candidate_count} candidate repos, "
        f"{len(result.github_repositories)} untracked repos total, "
        f"{len(result.arxiv_papers)} arXiv matches, and skipped "
        f"{result.known_repositories_skipped} known repos."
    )
    click.echo(
        f"Updated {discovered_path}: {update.added_github} new GitHub repos, "
        f"{update.added_arxiv} new arXiv papers."
    )


if __name__ == "__main__":
    cli()
