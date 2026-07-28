"""Challenge mode: the registry, cards, and comparator configuration.

Lean Pool's ``Challenge/`` library holds *open* statements — theorems (and
occasionally definitions) written in Mathlib vocabulary and left as
``sorry``. It is the only place in the repository where ``sorry`` is
allowed, and only as the whole proof body of a declaration registered in
``Challenge/challenges.yml``. Everything else about a challenge file is
held to the same standard as pooled content: file header, narrow imports,
no ``set_option``, no axioms, size limits.

This module owns the challenge *domain*:

- the registry schema and its validation (:func:`registry_errors`),
- the generated challenge card shown on the docs site
  (:func:`challenge_card`),
- the JSON configuration consumed by `leanprover/comparator
  <https://github.com/leanprover/comparator>`_, the third-party judge that
  decides whether a claimed solution really proves the challenge statement
  (:func:`comparator_config`).

The deterministic gates that *enforce* all of this live in
``lean_pool.quality``, which imports this module; nothing here imports
``lean_pool.quality``.

Run:
    uv run python -m lean_pool.challenge list
    uv run python -m lean_pool.challenge config twin-primes --solution-module M
"""

from __future__ import annotations

import argparse
import json
import sys
import textwrap
from pathlib import Path
from typing import Any

import yaml

# The library (and directory) holding open statements.
LIBRARY_NAME = "Challenge"
# The library holding answers. A solution restates its challenge's statement
# under the same name and proves it, and deliberately does NOT import the
# challenge module: comparator exports the two environments separately and
# compares them, which is what makes the verdict independent of the
# statement file.
SOLUTION_LIBRARY_NAME = "Solution"
REGISTRY_RELATIVE_PATH = f"{LIBRARY_NAME}/challenges.yml"
# Axioms a challenge solution may depend on. Passed verbatim to comparator
# as `permitted_axioms`; `lean_pool.quality.ALLOWED_AXIOMS` is derived from
# this tuple so the pool gate and the external judge cannot drift apart.
PERMITTED_AXIOMS: tuple[str, ...] = ("propext", "Quot.sound", "Classical.choice")
# `open` — nobody has proved it yet. `solved` — a solution exists and the
# `solution` block records where; the statement itself keeps its `sorry`,
# because it is the trusted text every solution is compared against.
STATUS_VALUES = ("open", "solved")
REQUIRED_FIELDS = (
    "slug",
    "title",
    "summary",
    "branch",
    "entry_module",
    "proposers",
    "source",
    "license",
    "provenance",
    "status",
    "statements",
    "tags",
    "msc",
)
LICENSE_VALUES = ("Apache-2.0", "MIT")
# Who wrote the Lean statement, mirroring `projects.yml`.
PROVENANCE_VALUES = ("human", "AI", "mix")
SOURCE_KEY_ORDER = ("arxiv", "doi", "url")
# Mathlib's style linter caps lines at 100 columns and the card is checked
# byte-for-byte, so wrapping has to be deterministic.
CARD_WIDTH = 100


def registry_path(root: Path) -> Path:
    """Return the path of the challenge registry inside ``root``."""
    return root / REGISTRY_RELATIVE_PATH


def challenge_files(root: Path) -> list[Path]:
    """Return every Lean file of the challenge library, index file first."""
    files = [root / f"{LIBRARY_NAME}.lean"]
    files.extend(sorted((root / LIBRARY_NAME).rglob("*.lean")))
    return [path for path in files if path.exists()]


def statement_files(root: Path) -> list[Path]:
    """Return the challenge statement files (every file but the index)."""
    index = root / f"{LIBRARY_NAME}.lean"
    return [path for path in challenge_files(root) if path != index]


def solution_files(root: Path) -> list[Path]:
    """Return every Lean file of the solution library, index file first."""
    files = [root / f"{SOLUTION_LIBRARY_NAME}.lean"]
    files.extend(sorted((root / SOLUTION_LIBRARY_NAME).rglob("*.lean")))
    return [path for path in files if path.exists()]


def solution_proof_files(root: Path) -> list[Path]:
    """Return the solution files (every file but the generated index)."""
    index = root / f"{SOLUTION_LIBRARY_NAME}.lean"
    return [path for path in solution_files(root) if path != index]


def solution_module(challenge: dict[str, Any]) -> str | None:
    """Return the in-repo module proving a challenge, if it has one."""
    solution = challenge.get("solution")
    if not isinstance(solution, dict):
        return None
    module = solution.get("module")
    return module if isinstance(module, str) and module.strip() else None


def is_solved(challenge: dict[str, Any]) -> bool:
    """Whether the registry records this challenge as solved."""
    return challenge.get("status") == "solved"


def load_challenges(root: Path) -> tuple[list[Any], list[tuple[Path, str]]]:
    """Load the challenge registry.

    Args:
        root: Repository root.

    Returns:
        ``(challenges, errors)``. ``challenges`` is the raw ``challenges``
        list — entries are validated separately by :func:`registry_errors`
        — and is empty whenever ``errors`` is non-empty.
    """
    path = registry_path(root)
    if not path.exists():
        return [], [(path, f"missing {REGISTRY_RELATIVE_PATH}")]
    try:
        data = yaml.safe_load(path.read_text()) or {}
    except yaml.YAMLError as error:
        return [], [(path, f"invalid YAML: {error}")]
    if not isinstance(data, dict):
        return [], [(path, f"{REGISTRY_RELATIVE_PATH} must contain a mapping")]
    challenges = data.get("challenges", [])
    if not isinstance(challenges, list):
        return [], [(path, "`challenges` must be a list")]
    return challenges, []


def find_challenge(root: Path, slug: str) -> dict[str, Any] | None:
    """Return the registered challenge with ``slug``, or ``None``."""
    challenges, _ = load_challenges(root)
    for challenge in challenges:
        if isinstance(challenge, dict) and challenge.get("slug") == slug:
            return challenge
    return None


def open_declarations(challenge: dict[str, Any]) -> list[dict[str, Any]]:
    """Return the declarations a challenge leaves open, statements first.

    These are exactly the declarations allowed to be ``sorry`` — the
    theorems under ``statements`` plus any definition holes under
    ``definitions``.
    """
    entries = []
    for key in ("statements", "definitions"):
        value = challenge.get(key)
        if isinstance(value, list):
            entries.extend(item for item in value if isinstance(item, dict))
    return entries


def open_declaration_names(challenge: dict[str, Any]) -> list[str]:
    """Return the names of every declaration a challenge leaves open."""
    return [
        entry["declaration"]
        for entry in open_declarations(challenge)
        if isinstance(entry.get("declaration"), str)
    ]


def statement_names(challenge: dict[str, Any]) -> list[str]:
    """Return the theorem names a solution has to prove."""
    statements = challenge.get("statements")
    if not isinstance(statements, list):
        return []
    return [
        item["declaration"]
        for item in statements
        if isinstance(item, dict) and isinstance(item.get("declaration"), str)
    ]


def definition_names(challenge: dict[str, Any]) -> list[str]:
    """Return the definition holes a solution has to fill in."""
    definitions = challenge.get("definitions")
    if not isinstance(definitions, list):
        return []
    return [
        item["declaration"]
        for item in definitions
        if isinstance(item, dict) and isinstance(item.get("declaration"), str)
    ]


def comparator_config(
    challenge: dict[str, Any],
    solution_module: str,
    *,
    enable_nanoda: bool = False,
) -> dict[str, Any]:
    """Build the JSON configuration `comparator`_ consumes.

    Comparator replays the solution environment through the Lean kernel and
    checks that each listed theorem proves *the same statement* as the
    challenge module, using no axiom outside ``permitted_axioms``. Passing
    it is what turns "someone says they solved it" into a verified claim.

    Args:
        challenge: A registry entry.
        solution_module: Module name of the claimed solution, resolvable in
            the Lake workspace comparator runs in.
        enable_nanoda: Also replay through the external ``nanoda`` kernel.
            Requires the ``nanoda_bin`` binary; off by default.

    Returns:
        The configuration mapping, ready to be serialized to JSON.

    .. _comparator: https://github.com/leanprover/comparator
    """
    config: dict[str, Any] = {
        "challenge_module": challenge["entry_module"],
        "solution_module": solution_module,
        "theorem_names": statement_names(challenge),
        "permitted_axioms": list(PERMITTED_AXIOMS),
        "enable_nanoda": enable_nanoda,
    }
    holes = definition_names(challenge)
    if holes:
        # Definition holes are gameable by construction — comparator only
        # checks that name, type, universes and safety level match — so a
        # challenge that declares them needs human review of the solution
        # too. See the "Definition Holes" section of comparator's README.
        config["definition_names"] = holes
    return config


def _format_source(source: Any) -> str:
    """Render the source anchor the way project cards render theirs."""
    if isinstance(source, str):
        return source
    if not isinstance(source, dict):
        return ""
    return ", ".join(
        f"{key}:{source[key]}" for key in SOURCE_KEY_ORDER if key in source
    )


def _format_solution(solution: Any) -> str:
    """Render the `solution` block as one line of card text."""
    if not isinstance(solution, dict):
        return str(solution)
    parts = []
    if isinstance(solution.get("module"), str):
        parts.append(f"`{solution['module']}`")
    if isinstance(solution.get("project"), str):
        parts.append(f"pool project `{solution['project']}`")
    if isinstance(solution.get("url"), str):
        parts.append(solution["url"])
    if isinstance(solution.get("authors"), list):
        parts.append(f"by {', '.join(str(a) for a in solution['authors'])}")
    if isinstance(solution.get("verified"), str):
        parts.append(f"verified {solution['verified']}")
    return ", ".join(parts)


def _wrap(text: str, *, indent: str = "  ") -> list[str]:
    """Wrap one card line to the style linter's column limit.

    Field lines indent their continuations two spaces so the label stays
    readable; prose paragraphs pass ``indent=""``. Long unbreakable tokens
    (URLs, qualified declaration names) are left intact rather than split,
    matching how the style linter exempts bare URLs.
    """
    wrapped = textwrap.wrap(
        text,
        width=CARD_WIDTH,
        subsequent_indent=indent,
        break_long_words=False,
        break_on_hyphens=False,
    )
    return wrapped or [text]


def _join(values: Any) -> str:
    """Join a list field for display, tolerating a bare string."""
    if isinstance(values, list):
        return ", ".join(str(value) for value in values)
    return str(values)


def challenge_card(challenge: dict[str, Any]) -> str:
    """Render the module docstring shown at the top of a challenge file.

    The card is the human-readable half of a challenge: it carries the
    informal statement that the Lean is supposed to say, so a reader (and
    the LLM reviewer) can judge faithfulness without leaving the file.
    ``lean_pool.quality`` regenerates and gates it, so the format has to be
    deterministic.
    """
    lines = [f"# {challenge['title']}", ""]
    fields = [
        ("Source", _format_source(challenge["source"])),
        ("Proposed by", _join(challenge["proposers"])),
        ("Status", str(challenge["status"])),
        ("Open declarations", _join_declarations(challenge)),
        ("Tags", _join(challenge["tags"])),
        ("MSC", _join(challenge["msc"])),
    ]
    if challenge.get("estimated_lines") is not None:
        estimated = challenge["estimated_lines"]
        unit = "line" if estimated == 1 else "lines"
        fields.append(("Estimated size", f"~{estimated} {unit} of Lean"))
    if challenge.get("solution") is not None:
        fields.append(("Solution", _format_solution(challenge["solution"])))
    for label, value in fields:
        lines.extend(_wrap(f"{label}: {value}"))
    lines.extend(["", "Informal statement:"])
    for entry in open_declarations(challenge):
        lines.extend(_wrap(f"* `{entry['declaration']}` — {entry['informal']}"))
    return "/-!\n" + "\n".join(lines) + "\n-/"


def _join_declarations(challenge: dict[str, Any]) -> str:
    """Render the open declaration names as backticked card text."""
    return ", ".join(f"`{name}`" for name in open_declaration_names(challenge))


def solution_card(challenge: dict[str, Any]) -> str:
    """Render the module docstring for a challenge's solution file.

    The card exists to say what the file is for a reader who lands on it:
    a restatement of somebody else's trusted text, proved. It also records
    the verification date, so a stale claim is visible in the source.
    """
    solution = challenge.get("solution") or {}
    lines = [f"# Solution: {challenge['title']}", ""]
    fields = [
        ("Challenge", f"`{challenge['slug']}` (`{challenge['entry_module']}`)"),
        ("Proves", _join_declarations(challenge)),
    ]
    if isinstance(solution.get("authors"), list):
        fields.append(("Solved by", _join(solution["authors"])))
    if isinstance(solution.get("project"), str):
        fields.append(("Pool project", f"`{solution['project']}`"))
    if isinstance(solution.get("verified"), str):
        fields.append(("Verified with comparator", solution["verified"]))
    for label, value in fields:
        lines.extend(_wrap(f"{label}: {value}"))
    lines.extend(
        [
            "",
            *_wrap(
                "This module restates the challenge statement under its own name and "
                "proves it. It must not import the challenge module: comparator "
                "exports both environments separately and checks that the statements "
                "agree, which is what makes the verdict independent of the statement "
                "file.",
                indent="",
            ),
        ]
    )
    return "/-!\n" + "\n".join(lines) + "\n-/"


def registry_errors(root: Path) -> list[tuple[Path, str]]:
    """Validate the challenge registry against the schema.

    Returns:
        ``(path, message)`` pairs, empty when the registry is valid. The
        caller turns these into whatever error type it reports.
    """
    challenges, errors = load_challenges(root)
    if errors:
        return errors
    path = registry_path(root)
    errors = _uniqueness_errors(path, challenges)
    errors.extend(_registration_errors(root, path, challenges))
    if errors:
        return errors
    for index, challenge in enumerate(challenges, start=1):
        errors.extend(_challenge_errors(root, path, index, challenge))
    return errors


def _uniqueness_errors(path: Path, challenges: list[Any]) -> list[tuple[Path, str]]:
    """Reject duplicate slugs, entry modules, or open declarations."""
    errors: list[tuple[Path, str]] = []
    for field in ("slug", "entry_module"):
        seen: dict[str, int] = {}
        for index, challenge in enumerate(challenges, start=1):
            if not isinstance(challenge, dict):
                continue
            value = challenge.get(field)
            if not isinstance(value, str):
                continue
            if value in seen:
                errors.append(
                    (
                        path,
                        f"duplicate `{field}` {value!r} in challenges "
                        f"#{seen[value]} and #{index}",
                    )
                )
            else:
                seen[value] = index
    declarations: dict[str, int] = {}
    for index, challenge in enumerate(challenges, start=1):
        if not isinstance(challenge, dict):
            continue
        for name in open_declaration_names(challenge):
            if name in declarations:
                errors.append(
                    (
                        path,
                        f"duplicate open declaration {name!r} in challenges "
                        f"#{declarations[name]} and #{index}",
                    )
                )
            else:
                declarations[name] = index
    return errors


def _registration_errors(
    root: Path, path: Path, challenges: list[Any]
) -> list[tuple[Path, str]]:
    """Require every statement and solution file to be registered."""
    registered = {
        challenge["entry_module"]
        for challenge in challenges
        if isinstance(challenge, dict)
        and isinstance(challenge.get("entry_module"), str)
    }
    solutions = {
        module
        for challenge in challenges
        if isinstance(challenge, dict)
        and (module := solution_module(challenge)) is not None
    }
    errors: list[tuple[Path, str]] = []
    for file in solution_proof_files(root):
        module = ".".join(file.relative_to(root).with_suffix("").parts)
        if module not in solutions:
            errors.append(
                (
                    path,
                    f"solution module {module} is not the recorded solution of any "
                    f"challenge in {REGISTRY_RELATIVE_PATH}",
                )
            )
    for file in statement_files(root):
        module = ".".join(file.relative_to(root).with_suffix("").parts)
        if module not in registered:
            errors.append(
                (
                    path,
                    f"challenge module {module} missing from {REGISTRY_RELATIVE_PATH}",
                )
            )
    return errors


def _challenge_errors(
    root: Path, path: Path, index: int, challenge: Any
) -> list[tuple[Path, str]]:
    """Validate one registry entry."""
    if not isinstance(challenge, dict):
        return [(path, f"challenge #{index} must be a mapping")]
    missing = sorted(set(REQUIRED_FIELDS) - set(challenge))
    if missing:
        return [(path, f"challenge #{index} missing fields: {', '.join(missing)}")]
    errors = _value_errors(path, index, challenge)
    module_path = _module_path(root, str(challenge["entry_module"]))
    if not module_path.exists():
        errors.append((path, f"challenge #{index} entry_module does not exist"))
    errors.extend(_declaration_errors(path, index, challenge))
    errors.extend(_solution_errors(path, index, challenge))
    return errors


def _value_errors(
    path: Path, index: int, challenge: dict[str, Any]
) -> list[tuple[Path, str]]:
    """Check the scalar and list-valued fields of one entry."""
    errors: list[tuple[Path, str]] = []
    if challenge["status"] not in STATUS_VALUES:
        errors.append(
            (
                path,
                f"challenge #{index} has invalid status "
                f"(expected one of {', '.join(STATUS_VALUES)})",
            )
        )
    if challenge["license"] not in LICENSE_VALUES:
        errors.append(
            (
                path,
                f"challenge #{index} has invalid license "
                f"(expected one of {', '.join(LICENSE_VALUES)})",
            )
        )
    if challenge["provenance"] not in PROVENANCE_VALUES:
        errors.append(
            (
                path,
                f"challenge #{index} has invalid provenance "
                f"(expected one of {', '.join(PROVENANCE_VALUES)})",
            )
        )
    if not _source_is_valid(challenge["source"]):
        errors.append(
            (
                path,
                f"challenge #{index} source needs at least one of "
                f"{', '.join(SOURCE_KEY_ORDER)}",
            )
        )
    for field in ("slug", "title", "summary", "branch", "entry_module"):
        if not _nonempty_string(challenge[field]):
            errors.append(
                (path, f"challenge #{index} {field} must be a nonempty string")
            )
    for field in ("proposers", "tags", "msc"):
        if not _string_list(challenge[field]):
            errors.append(
                (path, f"challenge #{index} {field} must be nonempty strings")
            )
    estimated = challenge.get("estimated_lines")
    if estimated is not None and not (isinstance(estimated, int) and estimated > 0):
        errors.append(
            (path, f"challenge #{index} estimated_lines must be a positive integer")
        )
    return errors


def _declaration_errors(
    path: Path, index: int, challenge: dict[str, Any]
) -> list[tuple[Path, str]]:
    """Check `statements` / `definitions` shape and namespacing."""
    errors: list[tuple[Path, str]] = []
    statements = challenge["statements"]
    if not isinstance(statements, list) or not statements:
        errors.append((path, f"challenge #{index} statements must be a nonempty list"))
        return errors
    definitions = challenge.get("definitions", [])
    if not isinstance(definitions, list):
        errors.append((path, f"challenge #{index} definitions must be a list"))
        return errors
    module = str(challenge["entry_module"])
    for entry in [*statements, *definitions]:
        if not isinstance(entry, dict):
            errors.append(
                (path, f"challenge #{index} declaration entries must be mappings")
            )
            continue
        if not _nonempty_string(entry.get("declaration")):
            errors.append(
                (path, f"challenge #{index} declaration names must be nonempty strings")
            )
            continue
        if not _nonempty_string(entry.get("informal")):
            errors.append(
                (
                    path,
                    f"challenge #{index} declaration {entry['declaration']} needs a "
                    "nonempty `informal` statement — it is what the Lean is judged "
                    "against",
                )
            )
        if not entry["declaration"].startswith(f"{module}."):
            errors.append(
                (
                    path,
                    f"challenge #{index} declaration {entry['declaration']} must live "
                    f"in the {module} namespace",
                )
            )
    return errors


def _solution_errors(
    path: Path, index: int, challenge: dict[str, Any]
) -> list[tuple[Path, str]]:
    """Keep `status` and the `solution` block consistent."""
    solution = challenge.get("solution")
    if challenge["status"] == "solved":
        if not isinstance(solution, dict):
            return [
                (
                    path,
                    f"challenge #{index} is solved but has no `solution` mapping "
                    "recording where the proof lives",
                )
            ]
        if not any(
            _nonempty_string(solution.get(key)) for key in ("module", "project", "url")
        ):
            return [
                (
                    path,
                    f"challenge #{index} solution needs a `module` (in this "
                    "repository), a `project` slug, or a `url`",
                )
            ]
        module = solution.get("module")
        if module is not None and not str(module).startswith(
            f"{SOLUTION_LIBRARY_NAME}."
        ):
            return [
                (
                    path,
                    f"challenge #{index} solution module {module} must live in the "
                    f"{SOLUTION_LIBRARY_NAME} library",
                )
            ]
        return []
    if solution is not None:
        return [
            (
                path,
                f"challenge #{index} is open but carries a `solution` block; set "
                "status to solved",
            )
        ]
    return []


def _module_path(root: Path, module: str) -> Path:
    """Return the file backing a Lean module name."""
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def _source_is_valid(source: Any) -> bool:
    """Whether the source anchor names a paper, DOI, or URL."""
    if isinstance(source, str):
        return any(source.startswith(f"{key}:") for key in SOURCE_KEY_ORDER)
    if isinstance(source, dict):
        return bool(set(SOURCE_KEY_ORDER) & set(source))
    return False


def _nonempty_string(value: Any) -> bool:
    """Whether ``value`` is a string with non-whitespace content."""
    return isinstance(value, str) and bool(value.strip())


def _string_list(value: Any) -> bool:
    """Whether ``value`` is a nonempty list of nonempty strings."""
    return (
        isinstance(value, list)
        and bool(value)
        and all(isinstance(item, str) and item for item in value)
    )


def _render_listing(challenges: list[Any]) -> str:
    """Render the `list` subcommand's human-readable output."""
    if not challenges:
        return "No challenges registered."
    rows = []
    for challenge in challenges:
        if not isinstance(challenge, dict):
            continue
        names = ", ".join(open_declaration_names(challenge))
        row = (
            f"{challenge.get('slug', '?')}  [{challenge.get('status', '?')}]  "
            f"{challenge.get('title', '?')}\n    {challenge.get('entry_module', '?')}"
            f" — {names}"
        )
        module = solution_module(challenge)
        if module is not None:
            row += f"\n    solved by {module}"
        rows.append(row)
    return "\n".join(rows)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    """Parse the challenge CLI arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="Repository root. Defaults to the checkout containing this package.",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("list", help="List registered challenges.")
    subparsers.add_parser(
        "solved",
        help="Print the slug of every challenge with an in-repo solution, one "
        "per line — the set CI hands to comparator.",
    )
    config = subparsers.add_parser(
        "config", help="Emit a comparator JSON configuration for one challenge."
    )
    config.add_argument("slug", help="Challenge slug from Challenge/challenges.yml.")
    config.add_argument(
        "--solution-module",
        help="Module name of the claimed solution, as comparator will import it. "
        "Defaults to the module recorded in the registry.",
    )
    config.add_argument(
        "--out", type=Path, help="Write the configuration here instead of stdout."
    )
    config.add_argument(
        "--enable-nanoda",
        action="store_true",
        help="Also replay the solution through the nanoda kernel.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Run the challenge CLI."""
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo.resolve()
    if args.command in ("list", "solved"):
        if not registry_path(root).exists():
            # An installed but empty board: nothing to list, nothing to
            # verify. Only the quality gate treats a missing registry as an
            # error, and only once a statement file exists.
            if args.command == "list":
                print("No challenges registered.")
            return 0
        challenges, errors = load_challenges(root)
        for path, message in errors:
            print(f"{path}: {message}", file=sys.stderr)
        if errors:
            return 1
        if args.command == "solved":
            for entry in challenges:
                if isinstance(entry, dict) and solution_module(entry) is not None:
                    print(entry.get("slug", ""))
            return 0
        print(_render_listing(challenges))
        return 0

    challenge = find_challenge(root, args.slug)
    if challenge is None:
        print(f"Unknown challenge {args.slug!r}.", file=sys.stderr)
        return 1
    module = args.solution_module or solution_module(challenge)
    if module is None:
        print(
            f"Challenge {args.slug!r} records no solution module; pass "
            "--solution-module.",
            file=sys.stderr,
        )
        return 1
    config = comparator_config(challenge, module, enable_nanoda=args.enable_nanoda)
    rendered = json.dumps(config, indent=4) + "\n"
    if args.out is not None:
        args.out.write_text(rendered)
        print(f"Wrote {args.out}")
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
