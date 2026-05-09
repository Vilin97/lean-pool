"""CLI entry point for the aggregator.

Run with ``uv run python -m lean_pool.aggregator <subcommand>`` from
``python/``. Subcommands:

- ``fetch``: download the Reservoir manifest into ``raw_data/``.
- ``render``: regenerate the candidates README table from the manifest.
"""

import json
from pathlib import Path

import click

from lean_pool.aggregator.render import render_table, update_readme
from lean_pool.aggregator.reservoir import (
    MANIFEST_URL,
    fetch_manifest,
    save_manifest,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
CANDIDATES_DIR = REPO_ROOT / "aggregator" / "candidates"
DEFAULT_MANIFEST = CANDIDATES_DIR / "raw_data" / "manifest.json"
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
def fetch(url: str, output: Path) -> None:
    """Download the Reservoir manifest and save it to disk."""
    manifest = fetch_manifest(url)
    save_manifest(manifest, output)
    click.echo(f"Saved {len(manifest['packages'])} packages to {output}")


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
    "--readme",
    "readme_path",
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
    default=DEFAULT_README,
    show_default=True,
    help="Candidates README to update in place.",
)
def render(manifest_path: Path, readme_path: Path) -> None:
    """Render the candidates README table from a manifest."""
    with manifest_path.open() as manifest_file:
        manifest = json.load(manifest_file)
    table = render_table(manifest)
    update_readme(readme_path, table)
    click.echo(f"Rendered {len(manifest['packages'])} packages into {readme_path}")


if __name__ == "__main__":
    cli()
