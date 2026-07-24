"""CLI entry point for the exposition site generator.

Run with ``uv run python -m lean_pool.exposition --dump <jsonl>
--repo-root <path> --out <dir> [--commit <sha>]`` from ``python/``.
"""

import logging
from pathlib import Path

import click

from lean_pool.exposition.generate import generate_site


@click.command()
@click.option(
    "--dump",
    "dump_path",
    type=click.Path(exists=True, dir_okay=False, path_type=Path),
    required=True,
    help="Extractor JSONL dump (one JSON object per declaration).",
)
@click.option(
    "--repo-root",
    "repo_root",
    type=click.Path(exists=True, file_okay=False, path_type=Path),
    required=True,
    help="Repository root containing LeanPool/ sources and projects.yml.",
)
@click.option(
    "--out",
    "out_dir",
    type=click.Path(file_okay=False, path_type=Path),
    required=True,
    help="Output directory for the generated static site.",
)
@click.option(
    "--commit",
    default="main",
    show_default=True,
    help="Commit SHA recorded in index.json and used for GitHub link metadata.",
)
def cli(dump_path: Path, repo_root: Path, out_dir: Path, commit: str) -> None:
    """Generate the static exposition site from an extractor dump."""
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    summary = generate_site(
        dump_path=dump_path, repo_root=repo_root, out_dir=out_dir, commit=commit
    )
    click.echo(
        f"Wrote {summary.projects} projects ({summary.decls} declarations, "
        f"{summary.edges} edges) to {out_dir}"
    )


if __name__ == "__main__":
    cli()
