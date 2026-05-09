"""CLI entry point for the aggregator.

Run with ``uv run python -m lean_pool.aggregator`` from ``python/``.
"""

import argparse
import logging
import sys
from pathlib import Path

from lean_pool.aggregator.reservoir import (
    MANIFEST_URL,
    fetch_manifest,
    save_manifest,
)

logger = logging.getLogger(__name__)


def main() -> int:
    """Download the Reservoir manifest and log a summary.

    Returns:
        Process exit code (0 on success).
    """
    parser = argparse.ArgumentParser(
        description="Fetch the Reservoir manifest and summarize it."
    )
    parser.add_argument(
        "--url",
        default=MANIFEST_URL,
        help=f"Manifest URL (default: {MANIFEST_URL})",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("cache/manifest.json"),
        help="Where to save the downloaded manifest (default: ./cache/manifest.json)",
    )
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(message)s")

    manifest = fetch_manifest(args.url)
    save_manifest(manifest, args.output)

    packages = manifest.get("packages", [])
    logger.info("Bundled at: %s", manifest.get("bundledAt"))
    logger.info("Toolchains: %d", len(manifest.get("toolchains", [])))
    logger.info("Packages:   %d", len(packages))
    logger.info("Aliases:    %d", len(manifest.get("packageAliases", {})))
    logger.info("Saved to:   %s", args.output)

    if packages:
        logger.info("")
        logger.info("Top 10 by stars:")
        top = sorted(
            packages, key=lambda package: package.get("stars", 0), reverse=True
        )[:10]
        for package in top:
            logger.info("  %5d  %s", package.get("stars", 0), package["fullName"])

    return 0


if __name__ == "__main__":
    sys.exit(main())
