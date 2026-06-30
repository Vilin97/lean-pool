"""Deterministic repository quality checks for Lean Pool."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml

ALLOWED_AXIOMS = {"Classical.choice", "propext", "Quot.sound"}
CODE_QUALITY_URL = (
    "https://github.com/Vilin97/lean-pool/blob/main/.github/CODE_QUALITY.md"
)
FILE_HEADERS_DOC = f"{CODE_QUALITY_URL}#7-file-headers"
STATUS_VALUES = {"verified"}
SOURCE_KEYS = {"arxiv", "doi", "url"}
SOURCE_KEY_ORDER = ("arxiv", "doi", "url")
# Permissive SPDX licenses accepted for Lean Pool projects (Apache-2.0 or MIT,
# per CONTRIBUTING.md). Every project entry must declare one; enforced below.
LICENSE_VALUES = {"Apache-2.0", "MIT"}
# Kept identical to partial_port_audit.GITHUB_REPO_RE on purpose: a project is
# auditable for partial imports only when source.github_repo matches this
# `owner/name` shape, so the quality gate must reject exactly what the audit
# would otherwise silently skip.
GITHUB_REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
DECLARATION_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "class",
    "structure",
    "inductive",
)
DECLARATION_PREFIX = (
    r"(?:@\[[^\n\]]+\]\s+)*"
    r"(?:(?:private|protected|noncomputable|scoped)\s+)*"
)
# A (possibly dotted) Lean identifier: a leading letter or `_`, then letters /
# digits / `_` / `'` / `.`. `\w` and `\W` are Unicode-aware in Python 3, so
# this matches names with subscripts or Greek letters (`c₀`, `α`) that an
# ASCII-only `[A-Za-z0-9_'.]` pattern would truncate.
LEAN_IDENT = r"[^\W\d][\w'.]*"

FORBIDDEN_DIAGNOSTICS = re.compile(
    r"^\s*#(?:check|print|eval!?|reduce|guard_msgs|lint)\b"
)
FORBIDDEN_SOUNDNESS = re.compile(
    r"\b(?:axiom|constant|unsafe|partial|opaque)\b|@\[\s*extern\b"
)
# Strict four-line header. Anchored at the start of the file, no extra lines
# allowed inside the block: this forbids ad-hoc Source/MSC/Tags/Status fields
# (those belong in projects.yml per CODE_QUALITY.md §7) and enforces the
# documented field order.
HEADER_PATTERN = re.compile(
    r"\A/-\n"
    r"Copyright \(c\) \d{4} [^\n]+\. All rights reserved\.\n"
    r"Released under Apache 2\.0 license as described in the file LICENSE\.\n"
    r"Authors: [^\n]+\n"
    r"-/\n"
)


@dataclass(frozen=True)
class _QualityError:
    path: Path
    line: int
    message: str

    def format(self, root: Path) -> str:
        """Format the error using a repository-relative path."""
        relative = self.path.relative_to(root)
        return f"{relative}:{self.line}: {self.message}"


@dataclass(frozen=True)
class _Declaration:
    name: str
    path: Path
    line: int
    kind: str


def _strip_lean_comments(text: str) -> str:
    result: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(text):
        char = text[index]
        pair = text[index : index + 2]

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                result.append("\n")
            else:
                result.append(" ")
            index += 1
            continue

        if block_depth > 0:
            if pair == "/-":
                block_depth += 1
                result.append("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                result.append("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if in_string:
            result.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue

        if pair == "--":
            in_line_comment = True
            result.append("  ")
            index += 2
        elif pair == "/-":
            block_depth = 1
            result.append("  ")
            index += 2
        elif char == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(char)
            index += 1

    return "".join(result)


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _lean_content_files(root: Path) -> list[Path]:
    files = [root / "LeanPool.lean"]
    files.extend(sorted((root / "LeanPool").rglob("*.lean")))
    return [path for path in files if path.exists()]


def _module_to_path(root: Path, module: str) -> Path:
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def _parse_imports(text: str) -> list[str]:
    stripped = _strip_lean_comments(text)
    imports: list[str] = []
    for line in stripped.splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_'.]+)\s*$", line)
        if match:
            imports.append(match.group(1))
    return imports


def _reachable_leanpool_files(root: Path, entry_module: str = "LeanPool") -> set[Path]:
    reachable: set[Path] = set()
    pending = [entry_module]

    while pending:
        module = pending.pop()
        path = _module_to_path(root, module)
        if path in reachable or not path.exists():
            continue
        reachable.add(path)
        text = path.read_text()
        pending.extend(
            imported
            for imported in _parse_imports(text)
            if imported.startswith("LeanPool")
        )

    return reachable


def _check_reachability(root: Path) -> list[_QualityError]:
    expected = set(_lean_content_files(root))
    reachable = _reachable_leanpool_files(root)
    missing = sorted(expected - reachable)
    return [
        _QualityError(path, 1, "Lean file is not reachable from LeanPool.lean")
        for path in missing
    ]


def _check_headers(root: Path) -> list[_QualityError]:
    errors: list[_QualityError] = []
    for path in _lean_content_files(root):
        if path == root / "LeanPool.lean":
            continue
        text = path.read_text()
        if not HEADER_PATTERN.match(text):
            errors.append(
                _QualityError(
                    path,
                    1,
                    "malformed file header: expected exactly the four-line "
                    "Copyright/License/Authors block in order, with no extra "
                    "Source/MSC/Tags/Status fields (those live in "
                    f"projects.yml); see {FILE_HEADERS_DOC}",
                )
            )
    return errors


def _check_forbidden_lean_text(root: Path) -> list[_QualityError]:
    errors: list[_QualityError] = []
    for path in _lean_content_files(root):
        stripped = _strip_lean_comments(path.read_text())
        for line_number, line in enumerate(stripped.splitlines(), start=1):
            if re.search(r"\bset_option\b", line):
                errors.append(
                    _QualityError(path, line_number, "set_option is forbidden")
                )
            if re.search(r"\bnolint\b", line):
                errors.append(
                    _QualityError(path, line_number, "nolint waiver is forbidden")
                )
            if re.match(r"^\s*(?:public\s+)?import\s+Mathlib\s*$", line):
                errors.append(
                    _QualityError(
                        path, line_number, "broad import Mathlib is forbidden"
                    )
                )
            if re.search(r"\b(?:sorry|admit)\b", line):
                errors.append(
                    _QualityError(path, line_number, "sorry/admit is forbidden")
                )
            if FORBIDDEN_SOUNDNESS.search(line):
                errors.append(
                    _QualityError(
                        path, line_number, "unchecked declaration is forbidden"
                    )
                )
            if FORBIDDEN_DIAGNOSTICS.search(line):
                errors.append(
                    _QualityError(path, line_number, "diagnostic command is forbidden")
                )
    return errors


def _check_lake_options(root: Path) -> list[_QualityError]:
    errors: list[_QualityError] = []
    forbidden_patterns = {
        "moreLeanArgs": re.compile(r"\bmoreLeanArgs\b"),
        "heartbeat override": re.compile(
            r"\b(?:maxHeartbeats|synthInstance\.maxHeartbeats)\b"
        ),
        "trace option": re.compile(r"\btrace\."),
        "autoImplicit enabled": re.compile(
            r"\b(?:relaxedAutoImplicit|autoImplicit)\s*=\s*true"
        ),
        "disabled linter": re.compile(r"\blinter\.[A-Za-z0-9_.-]+\s*=\s*false"),
        "set_option": re.compile(r"\bset_option\b"),
    }
    for path in [root / "lakefile.toml", root / "lakefile.lean"]:
        if not path.exists():
            continue
        text = path.read_text()
        for label, pattern in forbidden_patterns.items():
            for match in pattern.finditer(text):
                errors.append(
                    _QualityError(
                        path, _line_number(text, match.start()), f"{label} is forbidden"
                    )
                )
    return errors


def _check_style_nolints(root: Path) -> list[_QualityError]:
    """Reject style-linter allowlist entries."""
    path = root / "scripts" / "nolints-style.txt"
    if not path.exists():
        return []
    errors: list[_QualityError] = []
    for line_number, line in enumerate(path.read_text().splitlines(), start=1):
        stripped = line.strip()
        if stripped and not stripped.startswith(("--", "#")):
            errors.append(
                _QualityError(path, line_number, "style linter waiver is forbidden")
            )
    return errors


def _non_comment_code_lines(text: str) -> int:
    stripped = _strip_lean_comments(text)
    return sum(1 for line in stripped.splitlines() if line.strip())


def _check_file_sizes(root: Path) -> list[_QualityError]:
    errors: list[_QualityError] = []
    for path in _lean_content_files(root):
        code_lines = _non_comment_code_lines(path.read_text())
        if code_lines > 10000:
            errors.append(
                _QualityError(
                    path, 1, f"file has {code_lines} code lines; limit is 10000"
                )
            )
    return errors


def _declaration_starts(stripped: str) -> list[tuple[int, str]]:
    starts: list[tuple[int, str]] = []
    pattern = re.compile(rf"^\s*{DECLARATION_PREFIX}(?:theorem|lemma)\b")
    for index, line in enumerate(stripped.splitlines(), start=1):
        if pattern.match(line):
            starts.append((index, line))
    return starts


def _check_proof_sizes(root: Path) -> list[_QualityError]:
    errors: list[_QualityError] = []
    for path in _lean_content_files(root):
        original_lines = path.read_text().splitlines()
        stripped = _strip_lean_comments("\n".join(original_lines))
        starts = _declaration_starts(stripped)
        for index, (start_line, _) in enumerate(starts):
            end_line = (
                starts[index + 1][0]
                if index + 1 < len(starts)
                else len(original_lines) + 1
            )
            block = original_lines[start_line - 1 : end_line - 1]
            try:
                body_start = next(
                    offset for offset, line in enumerate(block) if ":=" in line
                )
            except StopIteration:
                continue
            body = "\n".join(block[body_start:])
            proof_lines = _non_comment_code_lines(body)
            if proof_lines > 200:
                errors.append(
                    _QualityError(
                        path,
                        start_line,
                        f"proof has {proof_lines} code lines; limit is 200",
                    )
                )
    return errors


def _parse_declarations(root: Path) -> list[_Declaration]:
    declarations: list[_Declaration] = []
    keyword_pattern = "|".join(DECLARATION_KEYWORDS)
    # Use a negative lookahead instead of `\b`: `\b` does not treat `'` as a
    # word character, so a name like `foo'` would be parsed as `foo` and the
    # subsequent `#print axioms` audit would fail with `unknown constant`.
    decl_pattern = re.compile(
        rf"^\s*{DECLARATION_PREFIX}({keyword_pattern})\s+"
        rf"({LEAN_IDENT})(?![\w'.])"
    )
    for path in _lean_content_files(root):
        # Track `namespace` and `section` opens together so that an
        # `end <section>` pops the section rather than the enclosing namespace.
        # Each entry is (is_namespace, name); only namespace entries qualify a
        # declaration's name. Without this, a `section X .. end X` nested inside
        # a `namespace N` would pop `N` at `end X`, leaving every following
        # declaration mis-qualified (its `#print axioms _root_.<name>` then
        # fails with `unknown constant`).
        scope_stack: list[tuple[bool, str | None]] = []
        stripped = _strip_lean_comments(path.read_text())
        for line_number, line in enumerate(stripped.splitlines(), start=1):
            namespace_match = re.match(rf"^\s*namespace\s+({LEAN_IDENT})\s*$", line)
            if namespace_match:
                scope_stack.append((True, namespace_match.group(1)))
                continue
            section_match = re.match(rf"^\s*section(?:\s+({LEAN_IDENT}))?\s*$", line)
            if section_match:
                scope_stack.append((False, section_match.group(1)))
                continue
            if re.match(rf"^\s*end(?:\s+{LEAN_IDENT})?\s*$", line):
                if scope_stack:
                    scope_stack.pop()
                continue
            match = decl_pattern.match(line)
            if match and _is_private_declaration_line(line):
                continue
            if match and not match.group(2).startswith(":"):
                namespace_stack = [
                    name for is_namespace, name in scope_stack if is_namespace
                ]
                name = _qualify_name(namespace_stack, match.group(2))
                declarations.append(
                    _Declaration(name, path, line_number, match.group(1))
                )
    return declarations


def _is_private_declaration_line(line: str) -> bool:
    line = re.sub(r"^\s*(?:@\[[^\n\]]+\]\s+)*", "", line)
    return "private" in line.split()


def _qualify_name(namespace_stack: list[str], name: str) -> str:
    if name.startswith("_root_."):
        # `_root_.Foo.bar` declares `Foo.bar` at the top level regardless of
        # the enclosing namespace; strip the escape so the audit emits
        # `#print axioms _root_.Foo.bar`, not `_root_._root_.Foo.bar`.
        return name.removeprefix("_root_.")
    if not namespace_stack:
        return name
    # Prepend the enclosing namespaces even when the written name is itself
    # dotted: `theorem Foo.bar` inside `namespace N` declares `N.Foo.bar`, so
    # the audit must look it up under the fully-qualified name, not `Foo.bar`.
    return ".".join([*namespace_stack, name])


def _check_axioms(root: Path) -> list[_QualityError]:
    declarations = _parse_declarations(root)
    if not declarations:
        return []

    commands = "import LeanPool\n" + "\n".join(
        f"#print axioms _root_.{declaration.name}" for declaration in declarations
    )
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as temp_file:
        temp_path = Path(temp_file.name)
        temp_file.write(commands)
        temp_file.flush()

    try:
        try:
            process = subprocess.run(
                ["lake", "env", "lean", str(temp_path)],
                cwd=root,
                check=False,
                capture_output=True,
                text=True,
            )
        except FileNotFoundError:
            # `lake` not on PATH; surface a single advisory error rather
            # than crashing the whole quality run.
            return [
                _QualityError(
                    root / "LeanPool.lean",
                    1,
                    "axiom audit skipped: `lake` not found",
                )
            ]
    finally:
        temp_path.unlink(missing_ok=True)

    errors = _parse_axiom_output(root, declarations, process.stdout)
    resolved = _axiom_audit_resolved(process.stdout)
    missing = [
        declaration for declaration in declarations if declaration.name not in resolved
    ]
    # Distinguish "Lean ran but couldn't resolve some declarations" (per-decl
    # localization is useful) from "Lean failed before any #print axioms ran"
    # (a single root-cause error is more useful than N copies).
    if missing and not resolved and process.returncode != 0:
        return errors + [
            _QualityError(
                root / "LeanPool.lean",
                1,
                f"axiom audit failed before any declaration was checked: "
                f"{process.stderr.strip() or '(no stderr)'}",
            )
        ]
    errors.extend(_axiom_audit_missing(missing, process.stderr))
    return errors


def _parse_axiom_output(
    root: Path,
    declarations: list[_Declaration],
    output: str,
) -> list[_QualityError]:
    errors: list[_QualityError] = []
    by_name = {declaration.name: declaration for declaration in declarations}
    by_name.update(
        {f"_root_.{declaration.name}": declaration for declaration in declarations}
    )
    # Names may contain `'` (e.g. `foo'`); see _axiom_audit_resolved comment.
    pattern = re.compile(r"^'(.+?)' depends on axioms: \[(.*)\]$", re.MULTILINE)
    for match in pattern.finditer(output):
        name = match.group(1)
        axioms = {item.strip() for item in match.group(2).split(",") if item.strip()}
        extra_axioms = sorted(axioms - ALLOWED_AXIOMS)
        if extra_axioms and name in by_name:
            declaration = by_name[name]
            errors.append(
                _QualityError(
                    declaration.path,
                    declaration.line,
                    f"{name} depends on unallowlisted axioms: "
                    f"{', '.join(extra_axioms)}",
                )
            )
    return errors


def _axiom_audit_resolved(stdout: str) -> set[str]:
    """Return the set of declaration names that `#print axioms` resolved."""
    # `#print axioms NAME` produces one of two messages on stdout:
    #   'NAME' depends on axioms: [a, b, c]
    #   'NAME' does not depend on any axioms
    # Both indicate the lookup resolved; only the first list is interesting
    # for the trusted-axiom check, but both must count as "seen" so we don't
    # emit a spurious "produced no result" for axiom-free declarations.
    #
    # Names may contain `'` (e.g. `foo'`), so we cannot use `[^']+` for the
    # name. Use a non-greedy match anchored on `' ` (closing quote followed
    # by space) — Lean always emits one space between the echoed name and
    # the verb, and a name cannot end with whitespace.
    pattern = re.compile(
        r"^'(.+?)' (?:depends on axioms: \[|does not depend on any axioms)",
        re.MULTILINE,
    )
    resolved: set[str] = set()
    for match in pattern.finditer(stdout):
        name = match.group(1)
        # Lean echoes back the qualified name we passed in; strip _root_. so it
        # matches the unqualified names we collected via _parse_declarations.
        if name.startswith("_root_."):
            name = name[len("_root_.") :]
        resolved.add(name)
    return resolved


def _axiom_audit_missing(
    missing: list[_Declaration],
    stderr: str,
) -> list[_QualityError]:
    """Emit one error per declaration that `#print axioms` could not resolve."""
    errors: list[_QualityError] = []
    for declaration in missing:
        snippet = _stderr_snippet_for(stderr, declaration.name)
        message = (
            f"axiom audit failed for {declaration.name}: {snippet}"
            if snippet
            else f"axiom audit produced no result for {declaration.name}"
        )
        errors.append(_QualityError(declaration.path, declaration.line, message))
    return errors


def _stderr_snippet_for(stderr: str, name: str) -> str:
    """Find the most relevant stderr line mentioning `name`, or ''."""
    error_lines = [line for line in stderr.splitlines() if name in line]
    for line in error_lines:
        if "error" in line.lower():
            return line.strip()
    return error_lines[0].strip() if error_lines else ""


def _load_projects_yaml(
    root: Path,
) -> tuple[dict[str, Any] | None, list[_QualityError]]:
    path = root / "LeanPool" / "projects.yml"
    if not path.exists():
        return None, [_QualityError(path, 1, "missing LeanPool/projects.yml")]
    try:
        data = yaml.safe_load(path.read_text()) or {}
    except yaml.YAMLError as error:
        return None, [_QualityError(path, 1, f"invalid YAML: {error}")]
    if not isinstance(data, dict):
        return None, [_QualityError(path, 1, "projects.yml must contain a mapping")]
    return data, []


def _check_projects(root: Path) -> list[_QualityError]:
    data, errors = _load_projects_yaml(root)
    if data is None:
        return errors

    path = root / "LeanPool" / "projects.yml"
    projects = data.get("projects", [])
    errors.extend(_check_project_container(path, projects))
    if errors:
        return errors

    errors.extend(_check_project_uniqueness(path, projects))
    if errors:
        return errors
    errors.extend(_check_top_level_project_modules(root, path, projects))
    if errors:
        return errors

    for index, project in enumerate(projects, start=1):
        errors.extend(_check_project(root, path, index, project))
    return errors


def _check_project_container(path: Path, projects: Any) -> list[_QualityError]:
    errors: list[_QualityError] = []
    if not isinstance(projects, list):
        errors.append(_QualityError(path, 1, "`projects` must be a list"))
    return errors


def _check_project_uniqueness(path: Path, projects: list[Any]) -> list[_QualityError]:
    """Reject duplicate `slug` or `entry_module` across projects."""
    errors: list[_QualityError] = []
    for field in ("slug", "entry_module"):
        seen: dict[str, int] = {}
        for index, project in enumerate(projects, start=1):
            if not isinstance(project, dict):
                continue
            value = project.get(field)
            if not isinstance(value, str):
                continue
            if value in seen:
                errors.append(
                    _QualityError(
                        path,
                        1,
                        f"duplicate `{field}` {value!r} in projects "
                        f"#{seen[value]} and #{index}",
                    )
                )
            else:
                seen[value] = index
    return errors


def _check_top_level_project_modules(
    root: Path, path: Path, projects: list[Any]
) -> list[_QualityError]:
    """Require every top-level LeanPool project module in `projects.yml`."""
    entry_modules = {
        project["entry_module"]
        for project in projects
        if isinstance(project, dict) and isinstance(project.get("entry_module"), str)
    }
    missing = sorted(_top_level_project_modules(root) - entry_modules)
    return [
        _QualityError(
            path, 1, f"top-level project module {module} missing from projects.yml"
        )
        for module in missing
    ]


def _top_level_project_modules(root: Path) -> set[str]:
    """Return direct `LeanPool.Foo` modules that represent project entry points."""
    lean_pool = root / "LeanPool"
    if not lean_pool.is_dir():
        return set()
    excluded = {"Basic.lean"}
    return {
        f"LeanPool.{path.stem}"
        for path in lean_pool.glob("*.lean")
        if path.name not in excluded
    }


def _check_project(
    root: Path,
    path: Path,
    index: int,
    project: Any,
) -> list[_QualityError]:
    if not isinstance(project, dict):
        return [_QualityError(path, 1, f"project #{index} must be a mapping")]

    errors = _check_required_project_fields(path, index, project)
    errors.extend(_check_project_values(root, path, index, project))
    if errors:
        return errors

    entry_path = _module_to_path(root, project["entry_module"])
    errors.extend(_check_project_declarations(root, path, project))
    errors.extend(_check_project_card(entry_path, path, project))
    return errors


def _check_required_project_fields(
    path: Path, index: int, project: dict[str, Any]
) -> list[_QualityError]:
    required = {
        "slug",
        "title",
        "summary",
        "branch",
        "entry_module",
        "authors",
        "source",
        "license",
        "status",
        "main_declarations",
        "main_results",
        "tags",
        "msc",
    }
    missing = sorted(required - set(project))
    if missing:
        return [
            _QualityError(
                path, 1, f"project #{index} missing fields: {', '.join(missing)}"
            )
        ]
    return []


def _check_project_values(
    root: Path,
    path: Path,
    index: int,
    project: dict[str, Any],
) -> list[_QualityError]:
    errors: list[_QualityError] = []
    if project["status"] not in STATUS_VALUES:
        errors.append(_QualityError(path, 1, f"project #{index} has invalid status"))
    if "license" in project and project["license"] not in LICENSE_VALUES:
        errors.append(
            _QualityError(
                path,
                1,
                f"project #{index} has invalid license "
                f"(expected one of {', '.join(sorted(LICENSE_VALUES))})",
            )
        )
    if not _source_is_valid(project["source"]):
        errors.append(_QualityError(path, 1, f"project #{index} has invalid source"))
    elif not _has_github_repo(project["source"]):
        errors.append(
            _QualityError(
                path,
                1,
                f"project #{index} source is missing a valid `github_repo` "
                f"(`owner/name`); the partial-port audit needs it to run",
            )
        )
    if not _nonempty_string(project["summary"]):
        errors.append(
            _QualityError(path, 1, f"project #{index} summary must be nonempty")
        )
    if not _nonempty_string(project["branch"]):
        errors.append(
            _QualityError(path, 1, f"project #{index} branch must be nonempty")
        )
    if not _string_list(project["authors"]):
        errors.append(
            _QualityError(path, 1, f"project #{index} authors must be nonempty strings")
        )
    main_declarations_valid = _string_list(project["main_declarations"])
    if not main_declarations_valid:
        errors.append(
            _QualityError(
                path, 1, f"project #{index} main_declarations must be nonempty strings"
            )
        )
    main_results_valid = _main_results(project["main_results"])
    if not main_results_valid:
        errors.append(
            _QualityError(
                path,
                1,
                f"project #{index} main_results must list declaration/informal strings",
            )
        )
    if main_declarations_valid and main_results_valid:
        result_declarations = {
            result["declaration"] for result in project["main_results"]
        }
        missing_results = [
            declaration
            for declaration in project["main_declarations"]
            if declaration not in result_declarations
        ]
        if missing_results:
            errors.append(
                _QualityError(
                    path,
                    1,
                    f"project #{index} main_results missing main declarations: "
                    f"{', '.join(missing_results)}",
                )
            )
    if not _string_list(project["tags"]):
        errors.append(
            _QualityError(path, 1, f"project #{index} tags must be nonempty strings")
        )
    if not _string_list(project["msc"]):
        errors.append(
            _QualityError(path, 1, f"project #{index} msc must be nonempty strings")
        )
    entry_path = _module_to_path(root, str(project["entry_module"]))
    if not entry_path.exists():
        errors.append(
            _QualityError(path, 1, f"project #{index} entry_module does not exist")
        )
    return errors


def _source_is_valid(source: Any) -> bool:
    if isinstance(source, str):
        return any(source.startswith(f"{key}:") for key in SOURCE_KEYS)
    if isinstance(source, dict):
        # At least one recognized source key; multiple (e.g. arxiv + doi) are fine.
        return len(SOURCE_KEYS & set(source)) >= 1
    return False


def _has_github_repo(source: Any) -> bool:
    """Return true when `source` carries a well-formed `github_repo` slug."""
    if not isinstance(source, dict):
        return False
    repo = source.get("github_repo")
    return isinstance(repo, str) and GITHUB_REPO_RE.fullmatch(repo) is not None


def _nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _string_list(value: Any) -> bool:
    return (
        isinstance(value, list)
        and bool(value)
        and all(isinstance(item, str) and item for item in value)
    )


def _main_results(value: Any) -> bool:
    if not isinstance(value, list) or not value:
        return False
    for item in value:
        if not isinstance(item, dict):
            return False
        if not _nonempty_string(item.get("declaration")):
            return False
        if not _nonempty_string(item.get("informal")):
            return False
        for optional_key in ("source_ref", "import"):
            if optional_key in item and not _nonempty_string(item[optional_key]):
                return False
    return True


def _check_project_declarations(
    root: Path,
    path: Path,
    project: dict[str, Any],
) -> list[_QualityError]:
    commands = f"import {project['entry_module']}\n"
    commands += "\n".join(f"#check {name}" for name in project["main_declarations"])
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as temp_file:
        temp_path = Path(temp_file.name)
        temp_file.write(commands)
        temp_file.flush()

    try:
        try:
            process = subprocess.run(
                ["lake", "env", "lean", str(temp_path)],
                cwd=root,
                check=False,
                capture_output=True,
                text=True,
            )
        except FileNotFoundError:
            # `lake` not on PATH (sandboxed CI, contributor without Lean).
            # Treat the same as `--skip-lean-axioms`: emit a single advisory
            # error so callers know the check was skipped, rather than crash.
            return [
                _QualityError(
                    path, 1, "project declarations check skipped: `lake` not found"
                )
            ]
    finally:
        temp_path.unlink(missing_ok=True)

    if process.returncode == 0:
        return []
    return [
        _QualityError(
            path, 1, f"project declarations do not check: {process.stderr.strip()}"
        )
    ]


def _check_project_card(
    entry_path: Path,
    metadata_path: Path,
    project: dict[str, Any],
) -> list[_QualityError]:
    if not entry_path.exists():
        return []
    text = entry_path.read_text()
    expected = _project_card(project)
    # The project card is the first module docstring (`/-!`) after the file
    # header. Mathlib convention places imports between the header and the
    # module docstring, so we skip past those.
    body = text[_initial_header_end(text) :]
    idx = body.find("/-!")
    if idx >= 0 and body[idx:].startswith(expected):
        return []
    return [
        _QualityError(
            metadata_path, 1, f"project card for {project['slug']} is out of date"
        )
    ]


def _initial_header_end(text: str) -> int:
    if not text.startswith("/-"):
        return 0
    end = text.find("-/")
    return 0 if end == -1 else end + 2


def _project_card(project: dict[str, Any]) -> str:
    authors = ", ".join(project["authors"])
    declarations = ", ".join(f"`{name}`" for name in project["main_declarations"])
    tags = ", ".join(project["tags"])
    lines = [
        "/-!",
        f"# {project['title']}",
        "",
        f"Source: {_format_source(project['source'])}",
        f"Authors: {authors}",
        f"Status: {project['status']}",
        f"Main declarations: {declarations}",
        f"Tags: {tags}",
    ]
    if project.get("msc"):
        lines.append(f"MSC: {_format_msc(project['msc'])}")
    return "\n".join(lines) + "\n-/"


def _format_source(source: Any) -> str:
    if isinstance(source, str):
        return source
    # List every recognized identifier, in arxiv/doi/url priority order.
    return ", ".join(
        f"{key}:{source[key]}" for key in SOURCE_KEY_ORDER if key in source
    )


def _format_msc(msc: Any) -> str:
    if isinstance(msc, list):
        return ", ".join(str(item) for item in msc)
    return str(msc)


def _write_project_cards(root: Path) -> None:
    data, errors = _load_projects_yaml(root)
    if errors or data is None:
        raise SystemExit("\n".join(error.format(root) for error in errors))
    for project in data.get("projects", []):
        if not isinstance(project, dict) or "entry_module" not in project:
            continue
        entry_path = _module_to_path(root, project["entry_module"])
        if entry_path.exists():
            _write_project_card(entry_path, _project_card(project))


_PROJECT_CARD_RE = re.compile(
    # A project card is a `/-! ... -/` block whose first content line is an
    # h1 heading and which contains a `Source:` line. Matching on `Source:`
    # distinguishes it from sibling docstrings like `/-! ## Mathematical
    # overview ... -/`. Non-greedy + DOTALL so we capture exactly one block.
    r"/-!\s*\n#\s+[^\n]+\n(?:[^\n]*\n)*?Source:[^\n]+\n(?:[^\n]*\n)*?-/\n*",
    re.MULTILINE,
)
_IMPORT_LINE_RE = re.compile(r"^\s*(?:public\s+)?import\s+\S+\s*$")


def _write_project_card(path: Path, card: str) -> None:
    text = path.read_text()
    # Strip any existing project card(s) wherever they currently live in the
    # file — the previous implementation only stripped a card immediately
    # after the copyright header, leaving a second card behind whenever the
    # canonical card layout (after imports) was already in use. `count=0`
    # means "every match", so a malformed file with two cards collapses to
    # zero cards before we insert the fresh one.
    stripped = _PROJECT_CARD_RE.sub("", text)

    header_end = _initial_header_end(stripped)
    header = stripped[:header_end].rstrip()
    rest = stripped[header_end:]

    # Find the trailing edge of the import block at the top of `rest`. Imports
    # have to live directly under the copyright header (mathlib / Lean
    # convention); allow blank lines between them. Anything after the last
    # import line is the body.
    rest_lines = rest.splitlines(keepends=True)
    cursor = 0
    last_import_line = -1
    while cursor < len(rest_lines):
        line = rest_lines[cursor]
        if _IMPORT_LINE_RE.match(line):
            last_import_line = cursor
            cursor += 1
        elif line.strip() == "":
            cursor += 1
        else:
            break
    if last_import_line >= 0:
        import_lines = rest_lines[: last_import_line + 1]
        while import_lines and import_lines[0].strip() == "":
            import_lines.pop(0)
        imports = "".join(import_lines).rstrip() + "\n"
        body = "".join(rest_lines[last_import_line + 1 :]).lstrip("\n")
    else:
        imports = ""
        body = rest.lstrip("\n")

    pieces: list[str] = []
    if header:
        pieces.append(header + "\n")
    if imports:
        pieces.append("\n" + imports)
    pieces.append("\n" + card + "\n")
    if body.strip():
        pieces.append("\n" + body)

    new_text = "".join(pieces).rstrip() + "\n"
    path.write_text(new_text)


def run_checks(root: Path, *, skip_lean_axioms: bool = False) -> list[_QualityError]:
    """Run all deterministic quality checks."""
    checks = [
        _check_reachability,
        _check_headers,
        _check_forbidden_lean_text,
        _check_lake_options,
        _check_style_nolints,
        _check_file_sizes,
        _check_proof_sizes,
        _check_projects,
    ]
    errors = [error for check in checks for error in check(root)]
    if not skip_lean_axioms:
        errors.extend(_check_axioms(root))
    return sorted(
        errors, key=lambda error: (str(error.path), error.line, error.message)
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="Repository root. Defaults to the checkout containing this package.",
    )
    parser.add_argument(
        "--skip-lean-axioms",
        action="store_true",
        help="Skip the Lean subprocess used for #print axioms.",
    )
    parser.add_argument(
        "--write-project-cards",
        action="store_true",
        help="Rewrite project-card module docstrings from LeanPool/projects.yml.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Run the quality checker CLI."""
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo.resolve()
    if args.write_project_cards:
        _write_project_cards(root)

    errors = run_checks(root, skip_lean_axioms=args.skip_lean_axioms)
    if errors:
        for error in errors:
            print(error.format(root), file=sys.stderr)
        return 1
    print("Quality checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
