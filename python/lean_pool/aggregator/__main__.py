"""CLI entry point for the aggregator.

Run with ``uv run python -m lean_pool.aggregator`` from ``python/``.
"""

from pathlib import Path

import click

from lean_pool.aggregator.reservoir import (
    MANIFEST_URL,
    fetch_manifest,
    save_manifest,
)


@click.command()
@click.option(
    "--url",
    default=MANIFEST_URL,
    show_default=True,
    help="Reservoir manifest URL.",
)
@click.option(
    "--output",
    type=click.Path(dir_okay=False, path_type=Path),
    default=Path("cache/manifest.json"),
    show_default=True,
    help="Where to save the downloaded manifest.",
)
def main(url: str, output: Path) -> None:
    """Download the Reservoir manifest and save it to disk."""
    manifest = fetch_manifest(url)
    save_manifest(manifest, output)
    click.echo(f"Saved {len(manifest['packages'])} packages to {output}")


if __name__ == "__main__":
    main()
