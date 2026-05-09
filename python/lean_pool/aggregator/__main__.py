"""CLI entry point for the aggregator.

Run with ``uv run python -m lean_pool.aggregator <subcommand>`` from
``python/``. Subcommands:

- ``fetch``: download the Reservoir manifest and the manual package
  list into ``raw_data/``.
- ``render``: regenerate the candidates README table from those files.
"""

import json
from pathlib import Path

import click

from lean_pool.aggregator.manual import (
    fetch_manual_packages,
    load_manual_packages,
    parse_manual_list,
    save_manual_packages,
)
from lean_pool.aggregator.render import render_table, update_readme
from lean_pool.aggregator.reservoir import (
    MANIFEST_URL,
    fetch_manifest,
    save_manifest,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
CANDIDATES_DIR = REPO_ROOT / "aggregator" / "candidates"
DEFAULT_MANIFEST = CANDIDATES_DIR / "raw_data" / "manifest.json"
DEFAULT_MANUAL_LIST = CANDIDATES_DIR / "manual.txt"
DEFAULT_MANUAL_DATA = CANDIDATES_DIR / "raw_data" / "manual_packages.json"
DEFAULT_MANUAL_CACHE = CANDIDATES_DIR / "raw_data" / "manual_cache"
DEFAULT_README = CANDIDATES_DIR / "README.md"


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
    "--readme",
    "readme_path",
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
    default=DEFAULT_README,
    show_default=True,
    help="Candidates README to update in place.",
)
def render(manifest_path: Path, manual_data_path: Path, readme_path: Path) -> None:
    """Render the candidates README table from a manifest."""
    with manifest_path.open() as manifest_file:
        manifest = json.load(manifest_file)
    manual_packages = load_manual_packages(manual_data_path)
    combined = {**manifest, "packages": list(manifest["packages"]) + manual_packages}
    table = render_table(combined)
    update_readme(readme_path, table)
    click.echo(
        f"Rendered {len(combined['packages'])} packages "
        f"({len(manifest['packages'])} reservoir + {len(manual_packages)} manual) "
        f"into {readme_path}"
    )


if __name__ == "__main__":
    cli()
