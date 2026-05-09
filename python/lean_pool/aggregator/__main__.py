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


def main() -> int:
    """Download the Reservoir manifest and print a summary.

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
        default=Path("manifest.json"),
        help="Where to save the downloaded manifest (default: ./manifest.json)",
    )
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(message)s")

    manifest = fetch_manifest(args.url)
    save_manifest(manifest, args.output)

    packages = manifest.get("packages", [])
    print(f"Bundled at: {manifest.get('bundledAt')}")
    print(f"Toolchains: {len(manifest.get('toolchains', []))}")
    print(f"Packages:   {len(packages)}")
    print(f"Aliases:    {len(manifest.get('packageAliases', {}))}")
    print(f"Saved to:   {args.output}")

    if packages:
        print("\nTop 10 by stars:")
        top = sorted(packages, key=lambda p: p.get("stars", 0), reverse=True)[:10]
        for pkg in top:
            print(f"  {pkg.get('stars', 0):>5}  {pkg['fullName']}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
