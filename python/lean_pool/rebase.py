"""Deterministic conflict resolution for import pull requests.

Backs ``.github/workflows/auto-rebase.yml``. When a pull request merges,
every other open import PR conflicts in exactly two files, and in both the
resolution is mechanical rather than editorial:

``LeanPool.lean``
    The ``mk_all`` index is a sorted list of ``import LeanPool.X`` lines, one
    per Lean file in the tree, so it is regenerated rather than merged --
    and, because it is derived purely from the file tree, without needing a
    Lean toolchain.

``LeanPool/projects.yml``
    Take the merged base's registry and re-append the cards this branch
    added. Cards are moved as verbatim text blocks, never re-serialised:
    round-tripping 141 cards through a YAML dumper would reformat every one
    of them and bury the real change.

Anything else in conflict is a genuine content overlap and is left alone for
a human. This module only computes file contents; the workflow decides what
to do with them.
"""

from __future__ import annotations

import argparse
import logging
import sys
from pathlib import Path

logger = logging.getLogger(__name__)

REGISTRY = "LeanPool/projects.yml"
INDEX = "LeanPool.lean"
CARD_PREFIX = "  - slug: "
# The only conflicts this module claims to resolve.
RESOLVABLE = frozenset({INDEX, REGISTRY})


def render_index(root: Path) -> str:
    """Regenerate the ``mk_all`` index from the Lean files on disk."""
    pool = root / "LeanPool"
    modules = sorted(
        "LeanPool."
        + str(path.relative_to(pool)).removesuffix(".lean").replace("/", ".")
        for path in pool.rglob("*.lean")
    )
    return "".join(f"import {module}\n" for module in modules)


def split_cards(text: str) -> tuple[str, list[tuple[str, str]]]:
    """Split a registry into its header and its cards, as verbatim text.

    Returns ``(header, [(slug, block)])`` where concatenating the header and
    every block reproduces ``text`` exactly.
    """
    lines = text.splitlines(keepends=True)
    starts = [i for i, line in enumerate(lines) if line.startswith(CARD_PREFIX)]
    if not starts:
        return text, []
    header = "".join(lines[: starts[0]])
    cards: list[tuple[str, str]] = []
    for index, start in enumerate(starts):
        end = starts[index + 1] if index + 1 < len(starts) else len(lines)
        slug = lines[start][len(CARD_PREFIX) :].strip()
        cards.append((slug, "".join(lines[start:end])))
    return header, cards


def merge_registry(base: str, ours: str, theirs: str) -> str:
    """Three-way merge the registry by card.

    ``ours`` is the updated base branch, ``theirs`` the pull request. The
    result is ``ours`` plus every card the pull request added, appended in
    the order the pull request had them. Cards are never reordered or
    reformatted, so the diff shows only the additions.
    """
    base_slugs = {slug for slug, _ in split_cards(base)[1]}
    header, our_cards = split_cards(ours)
    our_slugs = {slug for slug, _ in our_cards}

    added = [
        (slug, block)
        for slug, block in split_cards(theirs)[1]
        if slug not in base_slugs and slug not in our_slugs
    ]
    if not added:
        return ours

    merged = header + "".join(block for _, block in our_cards)
    # A registry whose last card lacks a trailing newline would otherwise
    # run into the first appended card.
    if merged and not merged.endswith("\n"):
        merged += "\n"
    return merged + "".join(block for _, block in added)


def resolvable(conflicts: list[str]) -> bool:
    """Whether every conflicted path is one this module can resolve."""
    return bool(conflicts) and set(conflicts) <= RESOLVABLE


def _command_index(args: argparse.Namespace) -> int:
    """Rewrite the index from the working tree."""
    root = args.repo.resolve()
    (root / INDEX).write_text(render_index(root), encoding="utf-8")
    logger.info("regenerated %s", INDEX)
    return 0


def _command_registry(args: argparse.Namespace) -> int:
    """Three-way merge the registry from three revisions on disk."""
    merged = merge_registry(
        args.base.read_text(encoding="utf-8"),
        args.ours.read_text(encoding="utf-8"),
        args.theirs.read_text(encoding="utf-8"),
    )
    (args.repo.resolve() / REGISTRY).write_text(merged, encoding="utf-8")
    logger.info("merged %s", REGISTRY)
    return 0


def _command_resolvable(args: argparse.Namespace) -> int:
    """Exit 0 when every conflicted path is mechanically resolvable."""
    conflicts = [line.strip() for line in args.conflicts.read_text().splitlines()]
    conflicts = [path for path in conflicts if path]
    if resolvable(conflicts):
        logger.info("all conflicts are mechanically resolvable")
        return 0
    unresolvable = sorted(set(conflicts) - RESOLVABLE)
    logger.error("conflicts need a human: %s", ", ".join(unresolvable) or "none")
    return 1


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    subparsers = parser.add_subparsers(dest="command", required=True)

    index = subparsers.add_parser("index", help="regenerate LeanPool.lean")
    index.add_argument("--repo", type=Path, default=Path("."))
    index.set_defaults(func=_command_index)

    registry = subparsers.add_parser("registry", help="three-way merge projects.yml")
    registry.add_argument("--repo", type=Path, default=Path("."))
    registry.add_argument("--base", type=Path, required=True)
    registry.add_argument("--ours", type=Path, required=True)
    registry.add_argument("--theirs", type=Path, required=True)
    registry.set_defaults(func=_command_registry)

    check = subparsers.add_parser("resolvable", help="are these conflicts mechanical?")
    check.add_argument("--conflicts", type=Path, required=True)
    check.set_defaults(func=_command_resolvable)

    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Dispatch a subcommand; return a process exit code."""
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    args = _parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    sys.exit(main())
