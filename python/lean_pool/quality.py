"""Deterministic repository quality checks for completed Lean Pool formalizations."""

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

from lean_pool.indexes import (
    discovers_modules,
    project_modules,
    requires_project_roots,
    structure_errors,
)
from lean_pool.registry import load_document
from lean_pool.validation_cache import ValidationCache, pool_units

ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
CODE_QUALITY_URL = (
    "https://github.com/LeanPool/lean-pool/blob/main/.github/CODE_QUALITY.md"
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
FORBIDDEN_TEXT_RULES = (
    (re.compile(r"\bset_option\b"), "set_option is forbidden"),
    (re.compile(r"\bnolint\b"), "nolint waiver is forbidden"),
    (FORBIDDEN_OPTION_APIS, "programmatic option manipulation is forbidden"),
    (FORBIDDEN_OPTION_NAMES, "gated option name in code is forbidden"),
    (
        re.compile(r"^\s*(?:public\s+)?import\s+Mathlib\s*$"),
        "broad import Mathlib is forbidden",
    ),
    (re.compile(r"\b(?:admit|sorry)\b"), None),
    (FORBIDDEN_SOUNDNESS, "unchecked declaration is forbidden"),
    (FORBIDDEN_DIAGNOSTICS, "diagnostic command is forbidden"),
)
FORBIDDEN_TEXT_CANDIDATES = re.compile(
    "|".join(pattern.pattern for pattern, _ in FORBIDDEN_TEXT_RULES)
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
POOL_CODE_LINE_LIMIT = 10000
LEAN_TEXT_TOKENS = re.compile(r'--|/-|"')
LEAN_BLOCK_TOKENS = re.compile(r"/-|-/")
LEAN_STRING_TOKENS = re.compile(r'\\[\s\S]|"')


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
    while match := LEAN_TEXT_TOKENS.search(text, index):
        start = match.start()
        result.append(text[index:start])
        if match[0] == "--":
            end = text.find("\n", match.end())
            end = len(text) if end == -1 else end
        elif match[0] == "/-":
            end = _block_comment_end(text, match.end())
        else:
            end = _string_end(text, match.end())
        # Preserve every character offset and newline for localized errors.
        result.append(
            "\n".join(" " * len(line) for line in text[start:end].split("\n"))
        )
        index = end
    result.append(text[index:])
    return "".join(result)


def _block_comment_end(text: str, start: int) -> int:
    depth = 1
    for match in LEAN_BLOCK_TOKENS.finditer(text, start):
        depth += 1 if match[0] == "/-" else -1
        if depth == 0:
            return match.end()
    return len(text)


def _string_end(text: str, start: int) -> int:
    for match in LEAN_STRING_TOKENS.finditer(text, start):
        if match[0] == '"':
            return match.end()
    return len(text)


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _lean_content_files(root: Path) -> list[Path]:
    files = [root / "LeanPool.lean"]
    files.extend(sorted((root / "LeanPool").rglob("*.lean")))
    return [path for path in files if path.exists()]


def _generated_index_files(root: Path) -> set[Path]:
    """Return the generated pool library index."""
    return {root / "LeanPool.lean"}


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
    if entry_module == "LeanPool" and discovers_modules(root):
        pending.extend(f"LeanPool.{name}.Imports" for name in project_modules(root))
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
    return _unreachable_errors(root, "LeanPool", _lean_content_files(root))


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
    for path in _lean_content_files(root):
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
    """Scan completed formalizations for forbidden tokens."""
    return [
        error
        for path in _lean_content_files(root)
        for error in _forbidden_text_errors(path)
    ]


def _forbidden_text_errors(path: Path) -> list[_QualityError]:
    errors: list[_QualityError] = []
    stripped = _strip_lean_comments(path.read_text())
    for line_number, line in enumerate(stripped.splitlines(), start=1):
        if not FORBIDDEN_TEXT_CANDIDATES.search(line):
            continue
        for pattern, message in FORBIDDEN_TEXT_RULES:
            if pattern.search(line):
                if message is None:
                    errors.extend(_sorry_errors(path, line_number, line))
                else:
                    errors.append(_QualityError(path, line_number, message))
    return errors


def _sorry_errors(path: Path, line_number: int, line: str) -> list[_QualityError]:
    """Reject unproved terms in comment-stripped source."""
    for token in ("admit", "sorry"):
        if re.search(rf"\b{token}\b", line):
            return [_QualityError(path, line_number, f"{token} is forbidden")]
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
    return _file_size_errors(_lean_content_files(root), POOL_CODE_LINE_LIMIT)


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

def auditEnv (env : Environment) (roots : List Name)
    (onlyModules : List Name) : IO Unit := do
  let manipulators := manipulatorCandidates.filter env.contains
  let injectors := axiomInjectorCandidates.filter env.contains
  let mut visited : NameSet := NameSet.empty
  for (moduleName, data) in env.header.moduleNames.zip env.header.moduleData do
    unless roots.contains moduleName.getRoot do continue
    unless onlyModules.isEmpty || onlyModules.contains moduleName do continue
    for declName in data.constNames do
      unless visited.contains declName do
        visited := visited.insert declName
        if let some info := env.find? declName then
          let exprs := info.type :: (info.value? (allowOpaque := true)).toList
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
  let imports := args.takeWhile (· != "--only")
  let onlyModules := (args.dropWhile (· != "--only")).drop 1 |>.map (·.toName)
  let modules := if imports.isEmpty then [`LeanPool] else imports.map (·.toName)
  Lean.initSearchPath (<- Lean.findSysroot)
  let imports := modules.toArray.map fun module => ({ module } : Lean.Import)
  let env <- Lean.importModules imports {} (trustLevel := 1024)
  for moduleName in onlyModules do
    unless env.header.moduleNames.contains moduleName do
      throw <| IO.userError s!"missing module in audit environment: {moduleName}"
  LeanPoolQuality.OptionAudit.auditEnv env (modules.map (·.getRoot)) onlyModules
  return 0
"""


def _check_option_backdoors(root: Path) -> list[_QualityError]:
    """Audit every compiled pool declaration for backdoors."""
    return _run_option_audit(
        root,
        [m for unit in pool_units(root) for m in unit]
        if discovers_modules(root)
        else ["LeanPool"],
    )


def _run_option_audit(
    root: Path, modules: list[str], *, only_modules: list[str] | None = None
) -> list[_QualityError]:
    """Run the environment audit over one set of importable modules."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as temp_file:
        temp_path = Path(temp_file.name)
        temp_file.write(_OPTION_AUDIT_LEAN)
        temp_file.flush()

    index_path = _module_to_path(root, modules[0])
    try:
        try:
            process = subprocess.run(
                ["lake", "env", "lean", "--run", str(temp_path), *modules]
                + (["--only", *only_modules] if only_modules is not None else []),
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
        index_path=index_path,
    )


def _parse_option_audit_output(
    root: Path,
    stdout: str,
    stderr: str,
    index_path: Path | None = None,
) -> list[_QualityError]:
    """Turn all environment-audit findings and non-completion into errors."""
    errors: list[_QualityError] = []
    for match in _OPTION_AUDIT_FINDING_RE.finditer(stdout):
        module, declaration, detail = match.groups()
        detail = detail.strip()
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
    return _audit_axioms(
        root,
        _parse_declarations(root),
        [m for unit in pool_units(root) for m in unit]
        if discovers_modules(root)
        else "LeanPool",
    )


def _audit_axioms(
    root: Path,
    declarations: list[_Declaration],
    import_module: str | list[str],
) -> list[_QualityError]:
    """Run `#print axioms` over ``declarations`` and grade the results."""
    if not declarations:
        return []

    modules = [import_module] if isinstance(import_module, str) else import_module
    index_path = _module_to_path(root, modules[0])
    commands = "".join(f"import {module}\n" for module in modules) + "\n".join(
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
) -> list[_QualityError]:
    errors: list[_QualityError] = []
    by_name = {declaration.name: declaration for declaration in declarations}
    by_name.update(
        {f"_root_.{declaration.name}": declaration for declaration in declarations}
    )
    # Names may contain `'` (e.g. `foo'`); see _axiom_audit_resolved comment.
    pattern = re.compile(r"^'(.+?)' depends on axioms: \[([^\]]*)\]", re.MULTILINE)
    for match in pattern.finditer(output):
        name = match.group(1)
        if name not in by_name:
            continue
        declaration = by_name[name]
        axioms = {item.strip() for item in match.group(2).split(",") if item.strip()}
        errors.extend(_axiom_errors(declaration, name, axioms))
    return errors


def _axiom_errors(
    declaration: _Declaration, name: str, axioms: set[str]
) -> list[_QualityError]:
    """Grade one declaration's axiom set without proof-hole exceptions."""
    extra_axioms = sorted(axioms - ALLOWED_AXIOMS)
    if not extra_axioms:
        return []
    return [
        _QualityError(
            declaration.path,
            declaration.line,
            f"{name} depends on unallowlisted axioms: {', '.join(extra_axioms)}",
        )
    ]


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
    if not path.exists() and not (path.parent / "projects").is_dir():
        return None, [_QualityError(path, 1, "missing LeanPool/projects.yml")]
    if (path.parent / "projects").is_dir():
        path = path.parent / "projects"
    try:
        data = load_document(path)
    except (yaml.YAMLError, ValueError, OSError) as error:
        return None, [_QualityError(path, 1, f"invalid YAML: {error}")]
    if not isinstance(data, dict):
        return None, [_QualityError(path, 1, "project registry must contain a mapping")]
    return data, []


def _check_projects(
    root: Path,
    validation_cache: ValidationCache | None = None,
    *,
    skip_declarations: bool = False,
) -> list[_QualityError]:
    data, errors = _load_projects_yaml(root)
    if data is None:
        return errors

    path = root / "LeanPool" / "projects.yml"
    if (path.parent / "projects").is_dir():
        path = path.parent / "projects"
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
        errors.extend(
            _check_project(
                root,
                (root / "LeanPool/projects" / f"{project['slug']}.yaml")
                if (root / "LeanPool/projects").is_dir()
                else path,
                index,
                project,
                validation_cache,
                skip_declarations=skip_declarations,
            )
        )
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


def _check_project_indexes(root: Path) -> list[_QualityError]:
    """Enforce the generated pool index and each complete public project root."""
    if not requires_project_roots(root):
        return []
    return [
        _QualityError(path, 1, message + "; run `lake exe mk_all`")
        for path, message in structure_errors(root)
    ]


def _check_project_entry_imports(
    root: Path, projects: list[Any]
) -> list[_QualityError]:
    """Require LeanPool.lean to import every registered project entry module."""
    index_path = root / "LeanPool.lean"
    if not index_path.exists():
        return []
    imports = set(_parse_imports(index_path.read_text()))
    if requires_project_roots(root):
        # Each project root directly imports its registered entry and all sources.
        imports = {
            imported
            for module in (
                {f"LeanPool.{name}.Imports" for name in project_modules(root)}
                if discovers_modules(root)
                else imports
            )
            if module.endswith(".Imports")
            for path in [_module_to_path(root, module)]
            if path.exists()
            for imported in _parse_imports(path.read_text())
        }
    entry_modules = {
        project["entry_module"]
        for project in projects
        if isinstance(project, dict) and isinstance(project.get("entry_module"), str)
    }
    return [
        _QualityError(
            root / "LeanPool" / module.split(".")[1] / "Imports.lean"
            if discovers_modules(root) and module.startswith("LeanPool.")
            else index_path,
            1,
            f"project entry module {module} is not imported by "
            + (
                "a project Imports module; "
                if discovers_modules(root)
                else "LeanPool.lean; "
            )
            + "run `lake exe mk_all`",
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
    validation_cache: ValidationCache | None = None,
    *,
    skip_declarations: bool = False,
) -> list[_QualityError]:
    if not isinstance(project, dict):
        return [_QualityError(path, 1, f"project #{index} must be a mapping")]

    errors = _check_required_project_fields(path, index, project)
    errors.extend(_check_project_values(root, path, index, project))
    if errors:
        return errors

    entry_path = _module_to_path(root, project["entry_module"])
    if not skip_declarations:
        if validation_cache is None:
            errors.extend(_check_project_declarations(root, path, project))
        else:
            errors.extend(
                validation_cache.check(
                    "declarations",
                    [project["entry_module"]],
                    lambda: _check_project_declarations(root, path, project),
                    metadata=project,
                )
            )
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
    # A generated card is a `/-! ... -/` block whose first content line is an
    # h1 heading and which contains a `Source:` line. Matching on that key
    # distinguishes it from sibling docstrings like `/-! ## Mathematical
    # overview ... -/`. Non-greedy + DOTALL so we capture exactly one block.
    r"/-!\s*\n#\s+[^\n]+\n(?:[^\n]*\n)*?Source:[^\n]+\n"
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


def run_checks(
    root: Path,
    *,
    skip_lean_axioms: bool = False,
    skip_project_declarations: bool = False,
    validation_cache: ValidationCache | None = None,
) -> list[_QualityError]:
    """Run all deterministic quality checks."""
    checks = [
        _check_project_indexes,
        _check_reachability,
        _check_headers,
        _check_forbidden_lean_text,
        _check_lake_options,
        _check_style_nolints,
        _check_file_sizes,
        _check_proof_sizes,
    ]
    errors = [error for check in checks for error in check(root)]
    errors.extend(
        _check_projects(
            root, validation_cache, skip_declarations=skip_project_declarations
        )
    )
    if not skip_lean_axioms:
        if validation_cache is None:
            errors.extend(_check_axioms(root))
            errors.extend(_check_option_backdoors(root))
        else:
            errors.extend(_cached_pool_audits(root, validation_cache))
    return sorted(
        errors, key=lambda error: (str(error.path), error.line, error.message)
    )


def _cached_pool_audits(root: Path, cache: ValidationCache) -> list[_QualityError]:
    """Cover all pool declarations, with current static reachability checked above."""
    errors: list[_QualityError] = []
    for modules in pool_units(root):
        paths = [_module_to_path(root, module) for module in modules]
        errors.extend(
            cache.check(
                "axioms",
                modules,
                lambda: _audit_axioms(root, _declarations_in(paths), modules),
            )
        )
        errors.extend(
            cache.check(
                "backdoors",
                modules,
                lambda: _run_option_audit(root, modules, only_modules=modules),
            )
        )
    return errors


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
        "--static-only",
        action="store_true",
        help="Run repository and card checks without Lean subprocesses "
        "(for a verified rebase).",
    )
    parser.add_argument(
        "--write-project-cards",
        action="store_true",
        help="Rewrite project-card module docstrings from the project registry.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Run the quality checker CLI."""
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo.resolve()
    if args.write_project_cards:
        _write_project_cards(root)

    errors = run_checks(
        root,
        skip_lean_axioms=args.skip_lean_axioms or args.static_only,
        skip_project_declarations=args.static_only,
    )
    if errors:
        for error in errors:
            print(error.format(root), file=sys.stderr)
        return 1
    print("Quality checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
