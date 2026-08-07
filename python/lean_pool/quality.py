"""Deterministic repository quality checks for Lean Pool.

Two Lean libraries are checked, under almost the same rules:

- ``LeanPool`` — completed formalizations. No ``sorry``, ever.
- ``Challenge`` — open statements awaiting a proof (see
  :mod:`lean_pool.challenge`). ``sorry`` is allowed here and nowhere else,
  and only as the whole proof body of a declaration registered in
  ``Challenge/challenges.yml``. Every other rule (headers, narrow imports,
  no ``set_option``, no axioms, size caps, the environment backdoor audit)
  applies unchanged, and the Lean-backed audits additionally verify that
  the registered open declarations are the *only* ones resting on
  ``sorryAx``.
"""

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

from lean_pool import challenge

# Derived from the challenge module so the pool gate and the axiom list
# handed to the external comparator judge cannot drift apart.
ALLOWED_AXIOMS = set(challenge.PERMITTED_AXIOMS)
# The `sorry` tactic/term compiles to this axiom. Permitted only for the
# declarations a challenge registers as open.
SORRY_AXIOM = "sorryAx"
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
# Provenance of a project's Lean proofs: written by a human (`human`), by an AI
# system (`AI`), or by a mix of both (`mix`). Every project entry must declare
# one; enforced below. See candidates/provenance.md for the rubric.
PROVENANCE_VALUES = {"human", "AI", "mix"}
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
# Programmatic option manipulation is semantically `set_option` (banned below)
# but invisible to that textual gate: PR #278 raised `maxRecDepth` from a
# custom elaborator via `withOptions (fun options => options.set `maxRecDepth
# (100000 : Nat))`. Two complementary layers close the gap: these patterns
# reject option-API tokens and gated option names in comment-stripped source,
# and the `_check_option_backdoors` environment audit rejects compiled
# declarations whose terms reference option-manipulating constants or embed
# gated option-name literals (catching spellings the text scan cannot see,
# e.g. names assembled from string literals).
FORBIDDEN_OPTION_APIS = re.compile(
    r"\b(?:withOptions|modifyOptions|MonadWithOptions|withRecDepth"
    r"|withCurrHeartbeats|elabSetOption|setOptionFromString|modifyScope"
    r"|KVMap\.(?:set|insert|erase)\w*|Options\.set\w*|Option\.set(?:IfNotSet)?)\b"
)
FORBIDDEN_OPTION_NAMES = re.compile(
    r"\b(?:maxRecDepth|maxHeartbeats|maxSynthPendingDepth)\b|\blinter\.[\w'.]+"
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
# A `sorry` in a challenge file may only be the entire proof body — either
# `:= sorry` closing the declaration line, or a lone `sorry` on its own
# line after a `:=`. This rules out partially open proofs like
# `⟨sorry, trivial⟩` or `by simp [sorry]`, which would leave a challenge
# quietly easier than its statement suggests.
WHOLE_BODY_SORRY = re.compile(r"(?::=\s*sorry|^\s*sorry)\s*$")
# Challenge statements are read by every would-be solver and by the LLM
# reviewer judging faithfulness, so they stay small; a challenge needing
# more setup than this belongs in the pool as a project first.
CHALLENGE_CODE_LINE_LIMIT = 500
POOL_CODE_LINE_LIMIT = 10000


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


def _challenge_files(root: Path) -> list[Path]:
    """Return every Lean file of the challenge library, index included."""
    return challenge.challenge_files(root)


def _solution_files(root: Path) -> list[Path]:
    """Return every Lean file of the solution library, index included."""
    return challenge.solution_files(root)


def _all_lean_files(root: Path) -> list[Path]:
    """Return the Lean files of all three libraries."""
    return [*_lean_content_files(root), *_challenge_files(root), *_solution_files(root)]


def _generated_index_files(root: Path) -> set[Path]:
    """Return the `mk_all`-generated library index files."""
    return {
        root / "LeanPool.lean",
        root / f"{challenge.LIBRARY_NAME}.lean",
        root / f"{challenge.SOLUTION_LIBRARY_NAME}.lean",
    }


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
    root_module = entry_module.split(".")[0]

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
            if imported.startswith(root_module)
        )

    return reachable


def _check_reachability(root: Path) -> list[_QualityError]:
    errors = _unreachable_errors(root, "LeanPool", _lean_content_files(root))
    errors.extend(
        _unreachable_errors(root, challenge.LIBRARY_NAME, _challenge_files(root))
    )
    errors.extend(
        _unreachable_errors(
            root, challenge.SOLUTION_LIBRARY_NAME, _solution_files(root)
        )
    )
    return errors


def _unreachable_errors(
    root: Path, entry_module: str, expected: list[Path]
) -> list[_QualityError]:
    """Report library files the generated index does not import."""
    reachable = _reachable_leanpool_files(root, entry_module)
    return [
        _QualityError(path, 1, f"Lean file is not reachable from {entry_module}.lean")
        for path in sorted(set(expected) - reachable)
    ]


def _check_headers(root: Path) -> list[_QualityError]:
    errors: list[_QualityError] = []
    generated = _generated_index_files(root)
    for path in _all_lean_files(root):
        if path in generated:
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
    """Scan both libraries for forbidden tokens.

    Identical rules either side of the split, except that a challenge file
    may use `sorry` — and only as a whole proof body, checked by
    :func:`_sorry_errors`.
    """
    errors: list[_QualityError] = []
    for path in _lean_content_files(root):
        errors.extend(_forbidden_text_errors(path, allow_sorry=False))
    for path in _challenge_files(root):
        errors.extend(_forbidden_text_errors(path, allow_sorry=True))
    # A solution is a proof, so it is held to the pool's rules exactly.
    for path in _solution_files(root):
        errors.extend(_forbidden_text_errors(path, allow_sorry=False))
    return errors


def _forbidden_text_errors(path: Path, *, allow_sorry: bool) -> list[_QualityError]:
    errors: list[_QualityError] = []
    stripped = _strip_lean_comments(path.read_text())
    for line_number, line in enumerate(stripped.splitlines(), start=1):
        if re.search(r"\bset_option\b", line):
            errors.append(_QualityError(path, line_number, "set_option is forbidden"))
        if re.search(r"\bnolint\b", line):
            errors.append(
                _QualityError(path, line_number, "nolint waiver is forbidden")
            )
        if FORBIDDEN_OPTION_APIS.search(line):
            errors.append(
                _QualityError(
                    path,
                    line_number,
                    "programmatic option manipulation is forbidden",
                )
            )
        if FORBIDDEN_OPTION_NAMES.search(line):
            errors.append(
                _QualityError(
                    path,
                    line_number,
                    "gated option name in code is forbidden",
                )
            )
        if re.match(r"^\s*(?:public\s+)?import\s+Mathlib\s*$", line):
            errors.append(
                _QualityError(path, line_number, "broad import Mathlib is forbidden")
            )
        errors.extend(_sorry_errors(path, line_number, line, allow_sorry=allow_sorry))
        if FORBIDDEN_SOUNDNESS.search(line):
            errors.append(
                _QualityError(path, line_number, "unchecked declaration is forbidden")
            )
        if FORBIDDEN_DIAGNOSTICS.search(line):
            errors.append(
                _QualityError(path, line_number, "diagnostic command is forbidden")
            )
    return errors


def _sorry_errors(
    path: Path, line_number: int, line: str, *, allow_sorry: bool
) -> list[_QualityError]:
    """Apply the `sorry` rule for one comment-stripped line.

    `admit` is forbidden everywhere: challenge statements use one spelling
    so the open declarations stay easy to eyeball.
    """
    if re.search(r"\badmit\b", line):
        return [_QualityError(path, line_number, "admit is forbidden")]
    if not re.search(r"\bsorry\b", line):
        return []
    if not allow_sorry:
        return [
            _QualityError(
                path,
                line_number,
                "sorry is forbidden outside "
                f"{challenge.LIBRARY_NAME}/ (see CONTRIBUTING.md#challenge-mode)",
            )
        ]
    if not WHOLE_BODY_SORRY.search(line):
        return [
            _QualityError(
                path,
                line_number,
                "sorry must be the whole proof body of an open declaration "
                "(`:= sorry`), not part of a larger term",
            )
        ]
    return []


def _check_lake_options(root: Path) -> list[_QualityError]:
    errors: list[_QualityError] = []
    forbidden_patterns = {
        "moreLeanArgs": re.compile(r"\bmoreLeanArgs\b"),
        "heartbeat override": re.compile(
            r"\b(?:maxHeartbeats|synthInstance\.maxHeartbeats)\b"
        ),
        "recursion-depth override": re.compile(r"\bmaxRecDepth\b"),
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
    errors = _file_size_errors(_lean_content_files(root), POOL_CODE_LINE_LIMIT)
    errors.extend(_file_size_errors(_challenge_files(root), CHALLENGE_CODE_LINE_LIMIT))
    # A solution that needs more than this is really a pooled project; it
    # should live in `LeanPool/` with a thin bridge module here.
    errors.extend(_file_size_errors(_solution_files(root), CHALLENGE_CODE_LINE_LIMIT))
    return errors


def _file_size_errors(paths: list[Path], limit: int) -> list[_QualityError]:
    errors: list[_QualityError] = []
    for path in paths:
        code_lines = _non_comment_code_lines(path.read_text())
        if code_lines > limit:
            errors.append(
                _QualityError(
                    path, 1, f"file has {code_lines} code lines; limit is {limit}"
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
    for path in _all_lean_files(root):
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
    return _declarations_in(_lean_content_files(root))


def _declarations_in(
    paths: list[Path], *, include_private: bool = False
) -> list[_Declaration]:
    declarations: list[_Declaration] = []
    keyword_pattern = "|".join(DECLARATION_KEYWORDS)
    # Use a negative lookahead instead of `\b`: `\b` does not treat `'` as a
    # word character, so a name like `foo'` would be parsed as `foo` and the
    # subsequent `#print axioms` audit would fail with `unknown constant`.
    decl_pattern = re.compile(
        rf"^\s*{DECLARATION_PREFIX}({keyword_pattern})\s+"
        rf"({LEAN_IDENT})(?![\w'.])"
    )
    for path in paths:
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
            if match and not include_private and _is_private_declaration_line(line):
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


# Environment-level companion to FORBIDDEN_OPTION_APIS/FORBIDDEN_OPTION_NAMES:
# a standalone Lean script (same `lake env lean --run` pattern as
# scripts/exposition/Extract.lean). It imports the pool WITHOUT activating
# extensions, so project-defined notation cannot interfere with the audit,
# then walks every declaration compiled into a `LeanPool.*` module (including
# elaborator auxiliaries and generated declarations the textual declaration
# parser cannot see) and reports any that
#   - references an option-manipulating constant,
#   - embeds a gated option-name string literal (Lean `Name` literals compile
#     to string pieces, so `` `maxRecDepth `` and `Name.mkStr1 "maxRecDepth"`
#     both surface here),
#   - directly references an axiom-injecting constant (`sorryAx`,
#     `ofReduceBool`, ...), or
#   - IS an axiom declared inside a pool module — this extends the
#     `#print axioms` audit to declarations it cannot enumerate textually (on
#     this toolchain `native_decide` compiles to a generated per-theorem
#     axiom in the module, which is exactly what the kind check rejects; an
#     elaborator calling `addDecl (Declaration.axiomDecl ...)` is the same
#     hole).
# Candidate constants absent from the current toolchain are skipped, so core
# renames degrade coverage rather than break the audit; the completion marker
# lets the Python side fail closed if the audit itself stops compiling.
_OPTION_AUDIT_FINDING_RE = re.compile(
    r"LEANPOOL_OPTION_AUDIT\|([^|\s]+)\|([^|\s]+)\|([^\n]*)"
)
_OPTION_AUDIT_COMPLETE_MARKER = "LEANPOOL_OPTION_AUDIT_COMPLETE"
_OPTION_AUDIT_LEAN = """
import Lean

namespace LeanPoolQuality.OptionAudit

open Lean

def gatedFragments : List String :=
  ["maxRecDepth", "maxHeartbeats", "maxSynthPendingDepth", "linter."]

def isGatedLiteral (s : String) : Bool :=
  s == "linter"
    || gatedFragments.any fun fragment => (s.splitOn fragment).length > 1

def manipulatorCandidates : List Name :=
  [`Lean.MonadWithOptions.withOptions, `Lean.withOptions, `Lean.modifyOptions,
   `Lean.MonadRecDepth.withRecDepth,
   `Lean.withCurrHeartbeats, `Lean.Core.withCurrHeartbeats,
   `Lean.KVMap.set, `Lean.KVMap.setBool, `Lean.KVMap.setNat, `Lean.KVMap.setInt,
   `Lean.KVMap.setString, `Lean.KVMap.setName, `Lean.KVMap.setSyntax,
   `Lean.KVMap.insert, `Lean.KVMap.insertCore, `Lean.KVMap.setEntry,
   `Lean.KVMap.erase,
   `Lean.Option.set, `Lean.Option.setIfNotSet,
   `Lean.Options.set, `Lean.Options.setBool, `Lean.Options.setNat,
   `Lean.Core.Context.mk, `Lean.Elab.Command.Scope.mk,
   `Lean.Elab.Command.modifyScope,
   `Lean.Elab.elabSetOption, `Lean.Elab.Command.elabSetOption,
   `Lean.setOptionFromString,
   `Lean.maxRecDepth, `Lean.maxHeartbeats, `maxRecDepth, `maxHeartbeats]

def axiomInjectorCandidates : List Name :=
  [`sorryAx, `Lean.sorryAx, `Lean.ofReduceBool, `Lean.ofReduceNat,
   `Lean.trustCompiler]

/- Only the axiom kind is rejected: `opaque` and `partial`/`unsafe`
definitions carry kernel-checked values (and unsafe constants cannot appear
in proofs at all), and the compiler legitimately generates such companions
(`._unsafe_rec`, hygienic `ext._@...` opaques, `deriving` helpers) for
ordinary safe code. An axiom declared inside a pool module, by contrast, is
always a soundness hole — whether written via an elaborator calling `addDecl`
or generated by `native_decide`. -/
def kindViolation? (info : ConstantInfo) : Option String :=
  match info with
  | .axiomInfo _ => some "declares an axiom"
  | _ => none

def gatedLiteral? (e : Expr) : Option String :=
  match e.find? fun sub =>
    match sub with
    | .lit (.strVal s) => isGatedLiteral s
    | _ => false
  with
  | some (.lit (.strVal s)) => some s
  | _ => none

def auditEnv (env : Environment) (roots : List Name) : IO Unit := do
  let manipulators := manipulatorCandidates.filter env.contains
  let injectors := axiomInjectorCandidates.filter env.contains
  let mut visited : NameSet := NameSet.empty
  for (moduleName, data) in env.header.moduleNames.zip env.header.moduleData do
    unless roots.contains moduleName.getRoot do continue
    for declName in data.constNames do
      unless visited.contains declName do
        visited := visited.insert declName
        if let some info := env.find? declName then
          let exprs := info.type :: info.value?.toList
          let used := exprs.foldl (fun acc e => acc ++ e.getUsedConstants) #[]
          let mut details : List String := []
          let hits := manipulators.filter used.contains
          unless hits.isEmpty do
            let joined := ", ".intercalate (hits.map (·.toString))
            details := details.concat
              s!"references forbidden option-manipulating constants: {joined}"
          if let some s := exprs.findSome? gatedLiteral? then
            details := details.concat
              s!"embeds forbidden gated option name {repr s}"
          let injectorHits := injectors.filter used.contains
          unless injectorHits.isEmpty do
            let joined := ", ".intercalate (injectorHits.map (·.toString))
            details := details.concat
              s!"references forbidden axiom-injecting constants: {joined}"
          if let some kindDetail := kindViolation? info then
            details := details.concat kindDetail
          unless details.isEmpty do
            let joined := "; ".intercalate details
            IO.println s!"LEANPOOL_OPTION_AUDIT|{moduleName}|{declName}|{joined}"
  IO.println "LEANPOOL_OPTION_AUDIT_COMPLETE"

end LeanPoolQuality.OptionAudit

def main (args : List String) : IO UInt32 := do
  let modules := if args.isEmpty then [`LeanPool] else args.map (·.toName)
  Lean.initSearchPath (<- Lean.findSysroot)
  let imports := modules.toArray.map fun module => ({ module } : Lean.Import)
  let env <- Lean.importModules imports {} (trustLevel := 1024)
  LeanPoolQuality.OptionAudit.auditEnv env (modules.map (·.getRoot))
  return 0
"""
# Detail emitted by the audit when a declaration is a `sorry`. Tolerated
# for — and only for — the declarations a challenge registers as open.
_SORRY_INJECTOR_DETAIL = (
    f"references forbidden axiom-injecting constants: {SORRY_AXIOM}"
)


def _check_option_backdoors(root: Path) -> list[_QualityError]:
    """Audit every declaration compiled into the libraries for backdoors.

    Two passes, because a solution declares the same names as the challenge
    it answers: importing `Challenge` and `Solution` into one environment is
    a name clash by construction.
    """
    pool_modules = ["LeanPool"]
    if (root / f"{challenge.LIBRARY_NAME}.lean").exists():
        pool_modules.append(challenge.LIBRARY_NAME)
    errors = _run_option_audit(root, pool_modules)
    if (root / f"{challenge.SOLUTION_LIBRARY_NAME}.lean").exists():
        errors.extend(_run_option_audit(root, [challenge.SOLUTION_LIBRARY_NAME]))
    return errors


def _run_option_audit(root: Path, modules: list[str]) -> list[_QualityError]:
    """Run the environment audit over one set of importable modules."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as temp_file:
        temp_path = Path(temp_file.name)
        temp_file.write(_OPTION_AUDIT_LEAN)
        temp_file.flush()

    index_path = root / f"{modules[0]}.lean"
    try:
        try:
            process = subprocess.run(
                ["lake", "env", "lean", "--run", str(temp_path), *modules],
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
                    index_path,
                    1,
                    "option-manipulation audit skipped: `lake` not found",
                )
            ]
    finally:
        temp_path.unlink(missing_ok=True)

    return _parse_option_audit_output(
        root,
        process.stdout,
        process.stderr,
        open_declarations=_open_declarations(root),
        index_path=index_path,
    )


def _open_declarations(root: Path) -> set[str]:
    """Return every declaration the challenge registry leaves open."""
    challenges, errors = challenge.load_challenges(root)
    if errors:
        return set()
    return {
        name
        for entry in challenges
        if isinstance(entry, dict)
        for name in challenge.open_declaration_names(entry)
    }


def _is_open_declaration(name: str, open_declarations: set[str]) -> bool:
    """Whether ``name`` is a registered open declaration or its companion.

    Lean generates companions for a sorried declaration (`foo.eq_def`,
    equation lemmas, hygienic auxiliaries); they carry the same `sorryAx`
    reference and live under the same name prefix.
    """
    return any(
        name == declaration or name.startswith(f"{declaration}.")
        for declaration in open_declarations
    )


def _parse_option_audit_output(
    root: Path,
    stdout: str,
    stderr: str,
    open_declarations: set[str] | None = None,
    index_path: Path | None = None,
) -> list[_QualityError]:
    """Turn environment-audit findings (and non-completion) into errors.

    A finding that says nothing but "this declaration is a `sorry`" is
    dropped for declarations the challenge registry lists as open — that is
    the whole point of a challenge. Findings that combine `sorryAx` with
    anything else still surface.
    """
    permitted = open_declarations or set()
    errors: list[_QualityError] = []
    for match in _OPTION_AUDIT_FINDING_RE.finditer(stdout):
        module, declaration, detail = match.groups()
        detail = detail.strip()
        if detail == _SORRY_INJECTOR_DETAIL and _is_open_declaration(
            declaration, permitted
        ):
            continue
        errors.append(
            _QualityError(
                _module_to_path(root, module),
                1,
                f"{declaration} {detail}",
            )
        )
    if _OPTION_AUDIT_COMPLETE_MARKER not in stdout:
        snippet = stderr.strip().splitlines()
        errors.append(
            _QualityError(
                index_path or root / "LeanPool.lean",
                1,
                "option-manipulation audit did not complete: "
                f"{snippet[0] if snippet else '(no stderr)'}",
            )
        )
    return errors


def _check_axioms(root: Path) -> list[_QualityError]:
    """Audit pooled declarations: allowlisted axioms only, never `sorry`."""
    return _audit_axioms(root, _parse_declarations(root), "LeanPool", set())


def _check_challenge_axioms(root: Path) -> list[_QualityError]:
    """Audit the challenge library's declarations.

    A registered open declaration must actually rest on `sorryAx` — the
    statement file is the trusted text every solution is compared against,
    so it stays open and stable, and a solution lives elsewhere. Every
    other declaration in the library (the definitions a statement is
    phrased in terms of) must be closed, or the challenge would be resting
    on unproved scaffolding nobody declared.
    """
    files = challenge.statement_files(root)
    if not files:
        return []
    return _audit_axioms(
        root,
        _declarations_in(files),
        challenge.LIBRARY_NAME,
        _open_declarations(root),
    )


def _check_solution_axioms(root: Path) -> list[_QualityError]:
    """Audit the solution library: real proofs, allowed axioms, no `sorry`.

    Run in its own Lean process, never alongside `Challenge`: a solution
    declares the same names as the challenge it answers, so importing both
    environments at once is a name clash by construction.
    """
    files = challenge.solution_proof_files(root)
    if not files:
        return []
    return _audit_axioms(
        root,
        _declarations_in(files),
        challenge.SOLUTION_LIBRARY_NAME,
        set(),
    )


def _audit_axioms(
    root: Path,
    declarations: list[_Declaration],
    import_module: str,
    open_declarations: set[str],
) -> list[_QualityError]:
    """Run `#print axioms` over ``declarations`` and grade the results."""
    if not declarations:
        return []

    index_path = root / f"{import_module}.lean"
    commands = f"import {import_module}\n" + "\n".join(
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
                    index_path,
                    1,
                    "axiom audit skipped: `lake` not found",
                )
            ]
    finally:
        temp_path.unlink(missing_ok=True)

    errors = _parse_axiom_output(root, declarations, process.stdout, open_declarations)
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
                index_path,
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
    open_declarations: set[str] | None = None,
) -> list[_QualityError]:
    permitted = open_declarations or set()
    errors: list[_QualityError] = []
    by_name = {declaration.name: declaration for declaration in declarations}
    by_name.update(
        {f"_root_.{declaration.name}": declaration for declaration in declarations}
    )
    # Names may contain `'` (e.g. `foo'`); see _axiom_audit_resolved comment.
    pattern = re.compile(r"^'(.+?)' depends on axioms: \[(.*)\]$", re.MULTILINE)
    seen: set[str] = set()
    for match in pattern.finditer(output):
        name = match.group(1)
        if name not in by_name:
            continue
        declaration = by_name[name]
        seen.add(declaration.name)
        axioms = {item.strip() for item in match.group(2).split(",") if item.strip()}
        errors.extend(
            _axiom_errors(
                declaration, name, axioms, is_open=declaration.name in permitted
            )
        )
    # Only for declarations Lean actually resolved: an unresolved name is
    # already reported once by `_axiom_audit_missing`.
    resolved = _axiom_audit_resolved(output)
    errors.extend(
        _not_open_error(declaration)
        for declaration in declarations
        if declaration.name in permitted
        and declaration.name not in seen
        and declaration.name in resolved
    )
    return errors


def _not_open_error(declaration: _Declaration) -> _QualityError:
    """Report a registered challenge statement that is no longer open."""
    return _QualityError(
        declaration.path,
        declaration.line,
        f"{declaration.name} is registered as an open challenge declaration "
        f"but does not depend on `{SORRY_AXIOM}`; challenge statements keep "
        "their `sorry` and solutions live outside the statement file",
    )


def _axiom_errors(
    declaration: _Declaration, name: str, axioms: set[str], *, is_open: bool
) -> list[_QualityError]:
    """Grade one declaration's axiom set."""
    allowed = ALLOWED_AXIOMS | ({SORRY_AXIOM} if is_open else set())
    extra_axioms = sorted(axioms - allowed)
    errors: list[_QualityError] = []
    if is_open and SORRY_AXIOM not in axioms:
        # Proved in place, using nothing worse than the allowed axioms — so
        # the checks below are all happy, and the challenge has silently
        # stopped being one.
        errors.append(_not_open_error(declaration))
    if SORRY_AXIOM in extra_axioms:
        extra_axioms.remove(SORRY_AXIOM)
        errors.append(
            _QualityError(
                declaration.path,
                declaration.line,
                f"{name} depends on `{SORRY_AXIOM}` but is not registered as an "
                "open declaration in Challenge/challenges.yml",
            )
        )
    if extra_axioms:
        errors.append(
            _QualityError(
                declaration.path,
                declaration.line,
                f"{name} depends on unallowlisted axioms: {', '.join(extra_axioms)}",
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
    errors.extend(_check_project_entry_imports(root, projects))
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


def _check_project_entry_imports(
    root: Path, projects: list[Any]
) -> list[_QualityError]:
    """Require LeanPool.lean to import every registered project entry module."""
    index_path = root / "LeanPool.lean"
    if not index_path.exists():
        return []
    imports = set(_parse_imports(index_path.read_text()))
    entry_modules = {
        project["entry_module"]
        for project in projects
        if isinstance(project, dict) and isinstance(project.get("entry_module"), str)
    }
    return [
        _QualityError(
            index_path,
            1,
            f"project entry module {module} is not imported by LeanPool.lean; "
            "run `lake exe mk_all`",
        )
        for module in sorted(entry_modules - imports)
    ]


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
        "provenance",
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
    if "provenance" in project and project["provenance"] not in PROVENANCE_VALUES:
        errors.append(
            _QualityError(
                path,
                1,
                f"project #{index} has invalid provenance "
                f"(expected one of {', '.join(sorted(PROVENANCE_VALUES))})",
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
    if _card_is_current(entry_path.read_text(), _project_card(project)):
        return []
    return [
        _QualityError(
            metadata_path, 1, f"project card for {project['slug']} is out of date"
        )
    ]


def _card_is_current(text: str, expected: str) -> bool:
    """Whether a file's generated card matches ``expected``.

    The card is the first module docstring (`/-!`) after the file header.
    Mathlib convention places imports between the header and the module
    docstring, so we skip past those.
    """
    body = text[_initial_header_end(text) :]
    index = body.find("/-!")
    return index >= 0 and body[index:].startswith(expected)


def _check_challenges(root: Path) -> list[_QualityError]:
    """Validate the challenge registry, its cards, and its imports.

    These are the checks that need no Lean subprocess; the axiom side of
    challenge mode lives in :func:`_check_challenge_axioms`.
    """
    registry = challenge.registry_path(root)
    if not challenge.statement_files(root) and not registry.exists():
        # An empty board is fine: the libraries can exist with nothing on
        # them, which is how challenge mode ships before its first entry.
        return []
    errors = [
        _QualityError(path, 1, message)
        for path, message in challenge.registry_errors(root)
    ]
    if errors:
        return errors
    errors.extend(_check_challenge_imports(root))
    errors.extend(_check_challenge_open_declarations(root))
    errors.extend(_check_solution_imports(root))
    challenges, _ = challenge.load_challenges(root)
    for entry in challenges:
        if not isinstance(entry, dict):
            continue
        entry_path = _module_to_path(root, str(entry["entry_module"]))
        errors.extend(_check_challenge_statements(entry_path, registry, entry))
        errors.extend(_check_challenge_card(entry_path, registry, entry))
        errors.extend(_check_solution(root, registry, entry))
    return errors


def _check_solution_imports(root: Path) -> list[_QualityError]:
    """Forbid a solution from importing the challenge it answers.

    Comparator exports the challenge and solution environments separately
    and compares the statements. A solution that imports the challenge
    module would inherit the statement (and its `sorry`) instead of
    restating it, which is precisely the check being skipped.
    """
    errors: list[_QualityError] = []
    prefix = f"{challenge.LIBRARY_NAME}."
    for path in challenge.solution_proof_files(root):
        stripped = _strip_lean_comments(path.read_text())
        for line_number, line in enumerate(stripped.splitlines(), start=1):
            match = re.match(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_'.]+)\s*$", line)
            if match and match.group(1).startswith(prefix):
                errors.append(
                    _QualityError(
                        path,
                        line_number,
                        f"a solution may not import the challenge module "
                        f"({match.group(1)}); restate the statement and prove it",
                    )
                )
    return errors


def _check_solution(
    root: Path,
    registry: Path,
    entry: dict[str, Any],
) -> list[_QualityError]:
    """Check the in-repo solution module of a solved challenge."""
    module = challenge.solution_module(entry)
    if module is None:
        return []
    path = _module_to_path(root, module)
    if not path.exists():
        return [_QualityError(registry, 1, f"solution module {module} does not exist")]
    errors: list[_QualityError] = []
    declared = {declaration.name for declaration in _declarations_in([path])}
    errors.extend(
        _QualityError(
            registry,
            1,
            f"solution {module} does not declare {name}; comparator compares the "
            "challenge and solution environments by declaration name",
        )
        for name in challenge.open_declaration_names(entry)
        if name not in declared
    )
    if not _card_is_current(path.read_text(), challenge.solution_card(entry)):
        errors.append(
            _QualityError(
                registry,
                1,
                f"solution card for {entry['slug']} is out of date; regenerate with "
                "`python -m lean_pool.quality --write-challenge-cards`",
            )
        )
    return errors


def _check_challenge_imports(root: Path) -> list[_QualityError]:
    """Require challenge statements to be phrased in Mathlib vocabulary.

    A challenge is a contract: whoever attempts it, and whoever reviews the
    attempt, has to be able to read the statement without auditing pool
    code. Restricting imports to Mathlib keeps that boundary small and
    keeps a statement from resting on a pooled project that may later be
    refactored underneath it.
    """
    errors: list[_QualityError] = []
    for path in challenge.statement_files(root):
        text = path.read_text()
        stripped = _strip_lean_comments(text)
        for line_number, line in enumerate(stripped.splitlines(), start=1):
            match = re.match(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_'.]+)\s*$", line)
            if match and not match.group(1).startswith("Mathlib."):
                errors.append(
                    _QualityError(
                        path,
                        line_number,
                        f"challenge statements may import only Mathlib modules; "
                        f"found {match.group(1)}",
                    )
                )
    return errors


def _check_challenge_open_declarations(root: Path) -> list[_QualityError]:
    """Require every `sorry` to belong to a declaration the registry lists.

    The Lean-backed audits establish this from the compiled environment,
    which is the authoritative check. Doing it textually as well points at
    the offending line for a contributor running without Lean, and covers
    `private` declarations that `#print axioms` never enumerates.
    """
    permitted = _open_declarations(root)
    errors: list[_QualityError] = []
    for path in challenge.statement_files(root):
        declarations = _declarations_in([path], include_private=True)
        stripped = _strip_lean_comments(path.read_text())
        for line_number, line in enumerate(stripped.splitlines(), start=1):
            if not WHOLE_BODY_SORRY.search(line):
                continue
            owner = _enclosing_declaration(declarations, line_number)
            if owner is not None and owner.name in permitted:
                continue
            owner_name = owner.name if owner is not None else "no declaration"
            errors.append(
                _QualityError(
                    path,
                    line_number,
                    f"sorry belongs to {owner_name}, which "
                    f"{challenge.REGISTRY_RELATIVE_PATH} does not list as an open "
                    "declaration",
                )
            )
    return errors


def _enclosing_declaration(
    declarations: list[_Declaration], line_number: int
) -> _Declaration | None:
    """Return the declaration a line belongs to, or ``None`` before the first."""
    enclosing = None
    for declaration in declarations:
        if declaration.line > line_number:
            break
        enclosing = declaration
    return enclosing


def _check_challenge_statements(
    entry_path: Path,
    registry: Path,
    entry: dict[str, Any],
) -> list[_QualityError]:
    """Require every registered open declaration to exist in the file."""
    if not entry_path.exists():
        return []
    declared = {declaration.name for declaration in _declarations_in([entry_path])}
    return [
        _QualityError(
            registry,
            1,
            f"challenge {entry['slug']} declares {name}, which is not declared "
            f"in {entry['entry_module']}",
        )
        for name in challenge.open_declaration_names(entry)
        if name not in declared
    ]


def _check_challenge_card(
    entry_path: Path,
    registry: Path,
    entry: dict[str, Any],
) -> list[_QualityError]:
    """Keep the generated challenge card in sync with the registry."""
    if not entry_path.exists():
        return []
    if _card_is_current(entry_path.read_text(), challenge.challenge_card(entry)):
        return []
    return [
        _QualityError(
            registry,
            1,
            f"challenge card for {entry['slug']} is out of date; regenerate with "
            "`python -m lean_pool.quality --write-challenge-cards`",
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


def _write_challenge_cards(root: Path) -> None:
    """Regenerate challenge and solution cards from the registry."""
    challenges, errors = challenge.load_challenges(root)
    if errors:
        raise SystemExit("\n".join(f"{path}: {message}" for path, message in errors))
    for entry in challenges:
        if not isinstance(entry, dict) or "entry_module" not in entry:
            continue
        entry_path = _module_to_path(root, str(entry["entry_module"]))
        if entry_path.exists():
            _write_project_card(entry_path, challenge.challenge_card(entry))
        module = challenge.solution_module(entry)
        if module is None:
            continue
        solution_path = _module_to_path(root, module)
        if solution_path.exists():
            _write_project_card(solution_path, challenge.solution_card(entry))


_PROJECT_CARD_RE = re.compile(
    # A generated card is a `/-! ... -/` block whose first content line is an
    # h1 heading and which contains a `Source:` line (projects and
    # challenges) or a `Challenge:` line (solutions). Matching on those keys
    # distinguishes it from sibling docstrings like `/-! ## Mathematical
    # overview ... -/`. Non-greedy + DOTALL so we capture exactly one block.
    r"/-!\s*\n#\s+[^\n]+\n(?:[^\n]*\n)*?(?:Source|Challenge):[^\n]+\n"
    r"(?:[^\n]*\n)*?-/\n*",
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
        _check_challenges,
    ]
    errors = [error for check in checks for error in check(root)]
    if not skip_lean_axioms:
        errors.extend(_check_axioms(root))
        errors.extend(_check_challenge_axioms(root))
        errors.extend(_check_solution_axioms(root))
        errors.extend(_check_option_backdoors(root))
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
        help="Skip the Lean subprocess used for #print axioms and the "
        "option-manipulation environment audit.",
    )
    parser.add_argument(
        "--write-project-cards",
        action="store_true",
        help="Rewrite project-card module docstrings from LeanPool/projects.yml.",
    )
    parser.add_argument(
        "--write-challenge-cards",
        action="store_true",
        help="Rewrite challenge-card module docstrings from Challenge/challenges.yml.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Run the quality checker CLI."""
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo.resolve()
    if args.write_project_cards:
        _write_project_cards(root)
    if args.write_challenge_cards:
        _write_challenge_cards(root)

    errors = run_checks(root, skip_lean_axioms=args.skip_lean_axioms)
    if errors:
        for error in errors:
            print(error.format(root), file=sys.stderr)
        return 1
    print("Quality checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
