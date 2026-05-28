"""Detect suspiciously partial imports against an upstream GitHub project."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import yaml

from lean_pool.quality import FORBIDDEN_SOUNDNESS, _strip_lean_comments

DEFAULT_LOC_TOLERANCE = 0.10
DEFAULT_MIN_UPSTREAM_LOC = 200
MAX_MISSING_FILES = 8
PROJECTS_YML = "LeanPool/projects.yml"
GITHUB_REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
FORBIDDEN_PROOF_GAP_RE = re.compile(r"\b(?:sorry|admit)\b")
IMPORT_RE = re.compile(r"^\s*import\s+(.+)$")


@dataclass(frozen=True)
class LeanFile:
    """Summary for one Lean file."""

    path: str
    loc: int
    normalized_stem: str


@dataclass(frozen=True)
class LeanStats:
    """Aggregate Lean file stats."""

    files: tuple[LeanFile, ...]

    @property
    def file_count(self) -> int:
        """Return the number of Lean files."""
        return len(self.files)

    @property
    def loc(self) -> int:
        """Return non-comment, non-blank Lean lines."""
        return sum(file.loc for file in self.files)

    @property
    def normalized_stems(self) -> set[str]:
        """Return normalized file stems for filename comparison."""
        return {file.normalized_stem for file in self.files}


@dataclass(frozen=True)
class AuditFinding:
    """A partial-port warning for one LeanPool project."""

    project: str
    upstream_repo: str
    imported_files: int
    upstream_files: int
    imported_loc: int
    upstream_loc: int
    file_ratio: float
    loc_ratio: float
    missing_files: tuple[str, ...]
    truncated_files: tuple[str, ...] = ()

    def format(self) -> str:
        """Format the finding as a concise human-readable paragraph."""
        missing = ", ".join(self.missing_files) if self.missing_files else "none"
        truncated = ", ".join(self.truncated_files) if self.truncated_files else "none"
        return (
            f"{self.project}: imported {self.imported_files}/{self.upstream_files} "
            f"Lean files and {self.imported_loc}/{self.upstream_loc} non-comment "
            f"LOC from {self.upstream_repo}; largest unmatched upstream filenames: "
            f"{missing}; matched files with large LOC gaps: {truncated}"
        )


def run_git(repo: Path, *args: str, allow_failure: bool = False) -> str:
    """Run git in ``repo`` and return stdout."""
    process = subprocess.run(
        ["git", *args],
        cwd=repo,
        check=False,
        capture_output=True,
        text=True,
    )
    if process.returncode and not allow_failure:
        raise RuntimeError(process.stderr.strip() or process.stdout.strip())
    return process.stdout


def git_show(repo: Path, revision: str, path: str) -> str:
    """Return a file from ``revision``."""
    return run_git(repo, "show", f"{revision}:{path}")


def changed_paths(repo: Path, base_ref: str, head_ref: str) -> list[str]:
    """Return paths changed between ``base_ref`` and ``head_ref``."""
    output = run_git(repo, "diff", "--name-only", f"{base_ref}...{head_ref}")
    return [line for line in output.splitlines() if line]


def load_projects(repo: Path, head_ref: str) -> list[dict[str, Any]]:
    """Load ``LeanPool/projects.yml`` from ``head_ref``."""
    data = yaml.safe_load(git_show(repo, head_ref, PROJECTS_YML)) or {}
    projects = data.get("projects") or []
    return [project for project in projects if isinstance(project, dict)]


def project_prefix(entry_module: str) -> str | None:
    """Return the top-level ``LeanPool/<prefix>`` path component."""
    parts = entry_module.split(".")
    if len(parts) != 2 or parts[0] != "LeanPool":
        return None
    return parts[1]


def touched_prefixes(paths: list[str]) -> set[str]:
    """Return top-level LeanPool project prefixes touched by a diff."""
    prefixes: set[str] = set()
    for path in paths:
        parts = path.split("/")
        if len(parts) == 2 and parts[0] == "LeanPool" and parts[1].endswith(".lean"):
            prefixes.add(parts[1].removesuffix(".lean"))
        elif len(parts) >= 3 and parts[0] == "LeanPool":
            prefixes.add(parts[1])
    return prefixes


def github_repo(project: dict[str, Any]) -> str | None:
    """Return ``source.github_repo`` if present and syntactically safe."""
    source = project.get("source")
    if not isinstance(source, dict):
        return None
    repo = source.get("github_repo")
    if not isinstance(repo, str) or not GITHUB_REPO_RE.fullmatch(repo):
        return None
    return repo


def count_lean_loc(text: str) -> int:
    """Count non-comment, non-blank Lean source lines."""
    stripped = _strip_lean_comments(text)
    return sum(1 for line in stripped.splitlines() if line.strip())


def has_forbidden_upstream_construct(text: str) -> bool:
    """Return true when upstream Lean text cannot be imported as Lean Pool content."""
    stripped = _strip_lean_comments(text)
    return any(
        FORBIDDEN_PROOF_GAP_RE.search(line) or FORBIDDEN_SOUNDNESS.search(line)
        for line in stripped.splitlines()
    )


def normalize_name(name: str) -> str:
    """Normalize a file or directory name for rough source/import matching."""
    return re.sub(r"[^a-z0-9]", "", name.lower())


def normalize_stem(path: str | Path) -> str:
    """Normalize a Lean filename stem for rough source/import matching."""
    return normalize_name(Path(path).stem)


def normalize_relative_path(path: str | Path) -> str:
    """Normalize a project-relative Lean path for same-file comparisons.

    Imported files live under ``LeanPool/<Project>/...`` while upstream files
    usually live under the upstream root module. Dropping those leading project
    components lets ``LeanPool/Foo/Bar/Baz.lean`` match ``Foo/Bar/Baz.lean``.
    """
    parts = Path(path).with_suffix("").parts
    if len(parts) >= 3 and parts[0] == "LeanPool":
        parts = parts[2:]
    elif len(parts) >= 2 and parts[0] != "LeanPool":
        parts = parts[1:]
    return "/".join(normalize_name(part) for part in parts)


def module_name(path: Path) -> str:
    """Return the Lean module name suggested by a repository-relative path."""
    return ".".join(path.with_suffix("").parts)


def imported_modules(text: str) -> tuple[str, ...]:
    """Return module names imported by a Lean source file."""
    stripped = _strip_lean_comments(text)
    imports: list[str] = []
    for line in stripped.splitlines():
        match = IMPORT_RE.match(line)
        if match is None:
            continue
        imports.extend(token.strip() for token in match.group(1).split() if token)
    return tuple(imports)


def ignored_lean_path(path: Path) -> bool:
    """Return true for Lean files that should not count as source content."""
    if path.name == "lakefile.lean":
        return True
    ignored_parts = {".git", ".lake", "build", "lake-packages"}
    return any(part in ignored_parts for part in path.parts)


def stats_from_worktree(root: Path) -> LeanStats:
    """Collect importable Lean stats from an upstream checkout."""
    source_files: dict[Path, str] = {}
    for path in sorted(root.rglob("*.lean")):
        relative = path.relative_to(root)
        if not ignored_lean_path(relative):
            source_files[relative] = path.read_text()

    module_paths = {module_name(path): path for path in source_files}
    excluded_paths = {
        path
        for path, text in source_files.items()
        if has_forbidden_upstream_construct(text)
    }
    changed = True
    while changed:
        changed = False
        for path, text in source_files.items():
            if path in excluded_paths:
                continue
            for imported_module in imported_modules(text):
                imported_path = module_paths.get(imported_module)
                if imported_path is not None and imported_path in excluded_paths:
                    excluded_paths.add(path)
                    changed = True
                    break

    files: list[LeanFile] = []
    for relative, text in sorted(source_files.items()):
        if relative in excluded_paths:
            continue
        if has_forbidden_upstream_construct(text):
            continue
        files.append(
            LeanFile(
                path=relative.as_posix(),
                loc=count_lean_loc(text),
                normalized_stem=normalize_stem(relative),
            )
        )
    return LeanStats(tuple(files))


def stats_from_git_project(repo: Path, head_ref: str, prefix: str) -> LeanStats:
    """Collect Lean stats for ``LeanPool/<prefix>`` at ``head_ref``."""
    paths = [
        path
        for path in run_git(
            repo,
            "ls-tree",
            "-r",
            "--name-only",
            head_ref,
            "--",
            f"LeanPool/{prefix}.lean",
            f"LeanPool/{prefix}",
        ).splitlines()
        if path.endswith(".lean")
    ]
    files = [
        LeanFile(
            path=path,
            loc=count_lean_loc(git_show(repo, head_ref, path)),
            normalized_stem=normalize_stem(path),
        )
        for path in paths
    ]
    return LeanStats(tuple(files))


def clone_upstream(repo: str, clone_root: Path) -> Path | None:
    """Clone ``repo`` under ``clone_root`` and return the checkout path."""
    target = clone_root / repo.replace("/", "__")
    if target.exists():
        shutil.rmtree(target)
    process = subprocess.run(
        ["git", "clone", "--depth=1", f"https://github.com/{repo}.git", str(target)],
        check=False,
        capture_output=True,
        text=True,
    )
    if process.returncode:
        print(
            f"partial-port-audit: warning: could not clone {repo}: "
            f"{process.stderr.strip() or process.stdout.strip()}",
            file=sys.stderr,
        )
        return None
    return target


def evaluate_stats(
    project: str,
    upstream_repo: str,
    imported: LeanStats,
    upstream: LeanStats,
    loc_tolerance: float = DEFAULT_LOC_TOLERANCE,
    min_upstream_loc: int = DEFAULT_MIN_UPSTREAM_LOC,
) -> AuditFinding | None:
    """Return a finding when imported stats look too small."""
    if upstream.loc < min_upstream_loc or not upstream.file_count:
        return None
    loc_ratio = imported.loc / upstream.loc if upstream.loc else 1.0
    file_ratio = (
        imported.file_count / upstream.file_count if upstream.file_count else 1.0
    )
    cutoff = 1.0 - loc_tolerance
    imported_stems = imported.normalized_stems
    missing_upstream_files = tuple(
        file
        for file in sorted(upstream.files, key=lambda item: item.loc, reverse=True)
        if file.normalized_stem not in imported_stems
    )
    large_file_cutoff = max(25, int(upstream.loc * loc_tolerance))
    missing_files = tuple(
        file.path for file in missing_upstream_files if file.loc >= large_file_cutoff
    )[:MAX_MISSING_FILES]
    imported_by_path: dict[str, list[LeanFile]] = {}
    for file in imported.files:
        imported_by_path.setdefault(normalize_relative_path(file.path), []).append(file)
    truncated_files = []
    for file in sorted(upstream.files, key=lambda item: item.loc, reverse=True):
        matching_imports = imported_by_path.get(normalize_relative_path(file.path), [])
        if not matching_imports:
            continue
        imported_file = max(matching_imports, key=lambda item: item.loc)
        if imported_file.loc / file.loc < cutoff:
            truncated_files.append(f"{file.path} ({imported_file.loc}/{file.loc} LOC)")
        if len(truncated_files) >= MAX_MISSING_FILES:
            break
    truncated_files_tuple = tuple(truncated_files)
    file_count_suspicious = upstream.file_count >= 3 and file_ratio < cutoff
    if (
        loc_ratio >= cutoff
        and not file_count_suspicious
        and not missing_files
        and not truncated_files_tuple
    ):
        return None
    if not missing_files:
        missing_files = tuple(file.path for file in missing_upstream_files)[
            :MAX_MISSING_FILES
        ]
    return AuditFinding(
        project=project,
        upstream_repo=upstream_repo,
        imported_files=imported.file_count,
        upstream_files=upstream.file_count,
        imported_loc=imported.loc,
        upstream_loc=upstream.loc,
        file_ratio=file_ratio,
        loc_ratio=loc_ratio,
        missing_files=missing_files,
        truncated_files=truncated_files_tuple,
    )


def audit_projects(
    repo: Path,
    base_ref: str,
    head_ref: str,
    clone_root: Path,
    loc_tolerance: float = DEFAULT_LOC_TOLERANCE,
    min_upstream_loc: int = DEFAULT_MIN_UPSTREAM_LOC,
) -> list[AuditFinding]:
    """Audit changed LeanPool projects for partial upstream imports."""
    touched = touched_prefixes(changed_paths(repo, base_ref, head_ref))
    if not touched:
        return []
    findings: list[AuditFinding] = []
    for project in load_projects(repo, head_ref):
        entry_module = project.get("entry_module")
        if not isinstance(entry_module, str):
            continue
        prefix = project_prefix(entry_module)
        if prefix not in touched:
            continue
        upstream_repo = github_repo(project)
        if upstream_repo is None:
            continue
        upstream_path = clone_upstream(upstream_repo, clone_root)
        if upstream_path is None:
            continue
        imported_stats = stats_from_git_project(repo, head_ref, prefix)
        upstream_stats = stats_from_worktree(upstream_path)
        finding = evaluate_stats(
            project=entry_module,
            upstream_repo=upstream_repo,
            imported=imported_stats,
            upstream=upstream_stats,
            loc_tolerance=loc_tolerance,
            min_upstream_loc=min_upstream_loc,
        )
        if finding is not None:
            findings.append(finding)
    return findings


def parse_args(argv: list[str]) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(
        description="Compare changed LeanPool projects with upstream GitHub repos."
    )
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--base-ref", default="origin/main")
    parser.add_argument("--head-ref", default="HEAD")
    parser.add_argument("--loc-tolerance", type=float, default=DEFAULT_LOC_TOLERANCE)
    parser.add_argument(
        "--min-upstream-loc", type=int, default=DEFAULT_MIN_UPSTREAM_LOC
    )
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Run the partial-port audit CLI."""
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo = args.repo.resolve()
    with tempfile.TemporaryDirectory(prefix="lean-pool-upstream-") as temp_dir:
        findings = audit_projects(
            repo=repo,
            base_ref=args.base_ref,
            head_ref=args.head_ref,
            clone_root=Path(temp_dir),
            loc_tolerance=args.loc_tolerance,
            min_upstream_loc=args.min_upstream_loc,
        )
    if args.json:
        print(json.dumps([asdict(finding) for finding in findings], indent=2))
    elif findings:
        print("Suspicious partial upstream imports detected:")
        for finding in findings:
            print(f"- {finding.format()}")
    else:
        print("No suspicious partial upstream imports detected.")
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
