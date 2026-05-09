"""CLI entry point for the aggregator.

Run with ``uv run python -m lean_pool.aggregator`` from ``python/``.
"""

from pathlib import Path

import click

from lean_pool.aggregator.reservoir import (
    MANIFEST_URL,
    fetch_manifest,
    save_manifest,
    trim_manifest,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_TRIMMED_OUTPUT = (
    REPO_ROOT / "aggregator" / "candidates" / "raw_data" / "manifest_trimmed.json"
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
    default=DEFAULT_TRIMMED_OUTPUT,
    show_default=True,
    help="Where to save the trimmed manifest (committed to the repo).",
)
@click.option(
    "--raw-output",
    type=click.Path(dir_okay=False, path_type=Path),
    default=None,
    help="Optional path to also save the full untrimmed manifest (gitignored).",
)
def main(url: str, output: Path, raw_output: Path | None) -> None:
    """Download the Reservoir manifest, trim it, and save."""
    manifest = fetch_manifest(url)
    if raw_output is not None:
        save_manifest(manifest, raw_output)
        click.echo(f"Saved full manifest to {raw_output}")
    trimmed = trim_manifest(manifest)
    save_manifest(trimmed, output)
    click.echo(f"Saved {len(trimmed['packages'])} packages to {output}")


if __name__ == "__main__":
    main()
