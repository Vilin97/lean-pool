"""Render the standalone PR verdict from challenge comparator results.

The comparator workflow runs pull-request code with a read-only token and
records small JSON data files. A separate ``workflow_run`` job uses this
module from the trusted default branch to render the sticky PR comment. A
green verdict requires both an explicit passing result for every claim and a
successful verifier workflow; contributor-written registry metadata is never
treated as evidence that comparator ran.
"""

from __future__ import annotations

import argparse
import html
import json
import stat
import sys
import zipfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

COMPARATOR_COMMENT_MARKER = "<!-- challenge-comparator-comment -->"
RESULT_STATUSES = ("passed", "failed")
MAX_CLAIMS = 100
MAX_RESULTS = 1_000
MAX_IDENTITY_LENGTH = 512
MAX_COMMENT_LENGTH = 60_000
MAX_REPORT_BYTES = 1_048_576
REPORT_FILE_NAMES = frozenset(
    {
        "pr-number.txt",
        "head-sha.txt",
        "base-sha.txt",
        "merge-sha.txt",
        "merge-tree.txt",
        "claims-state.txt",
        "claims.json",
        "results.json",
    }
)
ResultStatus = Literal["passed", "failed"]


@dataclass(frozen=True)
class ComparatorClaim:
    """One challenge solution claimed by the pull request."""

    slug: str
    module: str | None
    contract_unchanged: bool = True


@dataclass(frozen=True)
class ComparatorResult:
    """The explicit comparator outcome for one challenge."""

    slug: str
    status: ResultStatus


def record_result(path: Path, result: ComparatorResult) -> None:
    """Create or replace one result in a JSON result list.

    Args:
        path: Result file written by the read-only verifier workflow.
        result: Outcome to record.
    """
    results = _load_results(path) if path.exists() else []
    results = [existing for existing in results if existing.slug != result.slug]
    results.append(result)
    path.write_text(json.dumps([asdict(item) for item in results], indent=2) + "\n")


def extract_report(archive_path: Path, report_directory: Path) -> None:
    """Extract a bounded verifier artifact without trusting ZIP paths or types.

    Args:
        archive_path: ZIP downloaded from the read-only verifier run.
        report_directory: Fresh destination for the validated report files.
    """
    report_directory.mkdir(parents=True, exist_ok=True)
    total_size = 0
    seen = set()
    with zipfile.ZipFile(archive_path) as archive:
        for member in archive.infolist():
            if member.filename not in REPORT_FILE_NAMES:
                raise ValueError(
                    f"unexpected comparator report file {member.filename!r}"
                )
            if member.filename in seen:
                raise ValueError(
                    f"duplicate comparator report file {member.filename!r}"
                )
            seen.add(member.filename)
            mode = member.external_attr >> 16
            file_type = stat.S_IFMT(mode)
            if member.is_dir() or file_type not in (0, stat.S_IFREG):
                raise ValueError(
                    f"non-regular comparator report file {member.filename!r}"
                )
            if member.flag_bits & 0x1:
                raise ValueError("encrypted comparator reports are not accepted")
            total_size += member.file_size
            if member.file_size > MAX_REPORT_BYTES or total_size > MAX_REPORT_BYTES:
                raise ValueError("comparator report exceeds the size limit")
            with archive.open(member) as source:
                contents = source.read(MAX_REPORT_BYTES + 1)
                if len(contents) != member.file_size:
                    raise ValueError("comparator report member has an invalid size")
            (report_directory / member.filename).write_bytes(contents)


def render_comment(
    claims: list[ComparatorClaim],
    results: list[ComparatorResult],
    *,
    head_sha: str,
    run_url: str,
    workflow_conclusion: str,
    claims_complete: bool = True,
    verifier_trusted: bool = True,
) -> str:
    """Render a comparator-owned sticky PR comment.

    Args:
        claims: Solution claims found by comparing the head and base registries.
        results: Explicit per-challenge exit results from comparator.
        head_sha: Pull-request head commit judged by the workflow.
        run_url: URL of the verifier workflow run.
        workflow_conclusion: GitHub conclusion of the complete verifier job.
        claims_complete: Whether claim detection itself completed.
        verifier_trusted: Whether the PR left all verifier/reporting code untouched.

    Returns:
        Markdown comment text, or an empty string when the PR makes no claims.
    """
    _validate_claims(claims)
    if not claims_complete:
        return _incomplete_comment(head_sha, run_url)
    if not claims:
        return ""

    results_by_slug = _results_by_slug(results)
    rows = []
    accepted = 0
    failed = False
    for claim in claims:
        result = results_by_slug.get(claim.slug)
        if not verifier_trusted:
            outcome = "⚠️ Verifier inputs are not trusted"
            failed = True
        elif not claim.contract_unchanged:
            outcome = "❌ Challenge contract changed"
            failed = True
        elif claim.module is None:
            outcome = "⚠️ No in-repo solution module"
        elif (
            result is not None
            and result.status == "passed"
            and workflow_conclusion == "success"
        ):
            outcome = "✅ Verified"
            accepted += 1
        elif result is not None and result.status == "failed":
            outcome = "❌ Comparator failed"
            failed = True
        elif workflow_conclusion != "success":
            outcome = "⚠️ Verifier did not complete"
            failed = True
        else:
            outcome = "⚠️ Comparator did not run"
        rows.append(
            f"| {_code(claim.slug)} | {_code(claim.module or 'none')} | {outcome} |"
        )

    all_accepted = accepted == len(claims)
    if all_accepted:
        heading = "## ✅ Challenge comparator — verified"
        summary = (
            "Comparator replayed every challenge solution claimed by this PR "
            "through the Lean kernel and accepted it."
        )
    elif failed:
        heading = "## ❌ Challenge comparator — failed"
        summary = (
            "The verifier workflow did not accept every challenge solution "
            "claimed by this PR. See the linked run for the comparator output."
        )
    else:
        heading = "## ⚠️ Challenge comparator — incomplete"
        summary = (
            "This PR claims a challenge solution, but comparator did not produce "
            "an accepted result for every claim."
        )

    lines = [
        COMPARATOR_COMMENT_MARKER,
        heading,
        "",
        summary,
        "",
        "| Challenge | Solution module | Result |",
        "|---|---|---|",
        *rows,
        "",
        f"Reviewed head: {_code(head_sha)} · [Comparator run]({run_url})",
    ]
    return _bounded_comment("\n".join(lines) + "\n")


def render_pending_comment(
    claims: list[ComparatorClaim],
    *,
    head_sha: str,
) -> str:
    """Render the trusted placeholder posted before comparator finishes."""
    _validate_claims(claims)
    if not claims:
        return ""
    rows = [
        f"| {_code(claim.slug)} | {_code(claim.module or 'none')} | ⏳ Waiting |"
        for claim in claims
    ]
    return _bounded_comment(
        "\n".join(
            [
                COMPARATOR_COMMENT_MARKER,
                "## ⏳ Challenge comparator — pending",
                "",
                "This PR claims a challenge solution. A standalone verdict will "
                "replace this comment when the read-only comparator run finishes; "
                "until then, no solution has been verified.",
                "",
                "| Challenge | Solution module | Result |",
                "|---|---|---|",
                *rows,
                "",
                f"Current head: {_code(head_sha)}",
            ]
        )
        + "\n"
    )


def _incomplete_comment(head_sha: str, run_url: str) -> str:
    """Render a failure note when claim detection itself did not finish."""
    return "\n".join(
        [
            COMPARATOR_COMMENT_MARKER,
            "## ❌ Challenge comparator — failed",
            "",
            "The verifier workflow stopped before it could determine and check "
            "the challenge claims in this PR. No comparator success verdict was "
            "produced.",
            "",
            f"Reviewed head: {_code(head_sha)} · [Comparator run]({run_url})",
            "",
        ]
    )


def _code(value: str) -> str:
    """Render untrusted report text safely as inline HTML code."""
    escaped = html.escape(value, quote=True).replace("|", "&#124;")
    return f"<code>{escaped}</code>"


def _results_by_slug(
    results: list[ComparatorResult],
) -> dict[str, ComparatorResult]:
    """Index unique results by slug, rejecting ambiguous report data."""
    indexed: dict[str, ComparatorResult] = {}
    for result in results:
        if result.slug in indexed:
            raise ValueError(f"duplicate comparator result for {result.slug!r}")
        indexed[result.slug] = result
    return indexed


def _validate_claims(claims: list[ComparatorClaim]) -> None:
    """Reject empty or duplicate claim identities before rendering green."""
    if len(claims) > MAX_CLAIMS:
        raise ValueError(f"at most {MAX_CLAIMS} comparator claims can be rendered")
    slugs = set()
    for claim in claims:
        if not claim.slug or (claim.module is not None and not claim.module):
            raise ValueError("comparator claims need nonempty identities")
        if len(claim.slug) > MAX_IDENTITY_LENGTH or (
            claim.module is not None and len(claim.module) > MAX_IDENTITY_LENGTH
        ):
            raise ValueError("comparator claim identity is too long")
        if claim.slug in slugs:
            raise ValueError(f"duplicate comparator claim for {claim.slug!r}")
        slugs.add(claim.slug)


def _bounded_comment(comment: str) -> str:
    """Keep rendered text below GitHub's issue-comment size limit."""
    if len(comment.encode()) > MAX_COMMENT_LENGTH:
        raise ValueError("comparator comment is too large")
    return comment


def _load_claims(path: Path) -> list[ComparatorClaim]:
    """Load and validate a JSON claim list."""
    values = _load_json_list(path)
    if len(values) > MAX_CLAIMS:
        raise ValueError(f"too many comparator claims in {path}")
    claims = []
    for value in values:
        if not isinstance(value, dict) or not isinstance(value.get("slug"), str):
            raise ValueError(f"invalid comparator claim in {path}")
        module = value.get("module")
        if module is not None and not isinstance(module, str):
            raise ValueError(f"invalid solution module in {path}")
        contract_unchanged = value.get("contract_unchanged", False)
        if not isinstance(contract_unchanged, bool):
            raise ValueError(f"invalid contract verdict in {path}")
        claims.append(
            ComparatorClaim(
                slug=value["slug"],
                module=module,
                contract_unchanged=contract_unchanged,
            )
        )
    return claims


def _load_results(path: Path) -> list[ComparatorResult]:
    """Load and validate a JSON result list."""
    values = _load_json_list(path)
    if len(values) > MAX_RESULTS:
        raise ValueError(f"too many comparator results in {path}")
    results = []
    for value in values:
        if (
            not isinstance(value, dict)
            or not isinstance(value.get("slug"), str)
            or not value["slug"]
            or len(value["slug"]) > MAX_IDENTITY_LENGTH
            or value.get("status") not in RESULT_STATUSES
        ):
            raise ValueError(f"invalid comparator result in {path}")
        results.append(ComparatorResult(slug=value["slug"], status=value["status"]))
    return results


def _load_json_list(path: Path) -> list[Any]:
    """Load a JSON file whose top level must be a list."""
    if path.stat().st_size > MAX_REPORT_BYTES:
        raise ValueError(f"{path} exceeds the comparator report size limit")
    value = json.loads(path.read_text())
    if not isinstance(value, list):
        raise ValueError(f"{path} must contain a JSON list")
    return value


def _parse_args(argv: list[str]) -> argparse.Namespace:
    """Parse report recorder/renderer arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    record_parser = subparsers.add_parser(
        "record", help="Append one explicit comparator result."
    )
    record_parser.add_argument("results_file", type=Path)
    record_parser.add_argument("--slug", required=True)
    record_parser.add_argument("--status", required=True, choices=RESULT_STATUSES)

    render_parser = subparsers.add_parser(
        "render", help="Render the trusted sticky comment from a report directory."
    )
    render_parser.add_argument("report_directory", type=Path)
    render_parser.add_argument("--workflow-conclusion", required=True)
    render_parser.add_argument(
        "--verifier-trusted", required=True, choices=("true", "false")
    )
    render_parser.add_argument("--run-url", required=True)
    render_parser.add_argument("--out", required=True, type=Path)

    pending_parser = subparsers.add_parser(
        "pending", help="Render the pre-verification placeholder comment."
    )
    pending_parser.add_argument("report_directory", type=Path)
    pending_parser.add_argument("--out", required=True, type=Path)

    extract_parser = subparsers.add_parser(
        "extract", help="Validate and extract a verifier report ZIP."
    )
    extract_parser.add_argument("archive", type=Path)
    extract_parser.add_argument("report_directory", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Record a result or render a complete comparator comment."""
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    if args.command == "record":
        record_result(
            args.results_file,
            ComparatorResult(slug=args.slug, status=args.status),
        )
        return 0
    if args.command == "extract":
        extract_report(args.archive, args.report_directory)
        return 0

    report_directory = args.report_directory.resolve()
    state_path = report_directory / "claims-state.txt"
    claims_complete = (
        state_path.exists() and state_path.read_text().strip() == "complete"
    )
    claims = _load_claims(report_directory / "claims.json") if claims_complete else []
    head_sha = (report_directory / "head-sha.txt").read_text().strip()
    if args.command == "pending":
        if not claims_complete:
            raise ValueError("trusted pending claim detection did not complete")
        args.out.write_text(render_pending_comment(claims, head_sha=head_sha))
        return 0

    results_path = report_directory / "results.json"
    results = _load_results(results_path) if results_path.exists() else []
    comment = render_comment(
        claims,
        results,
        head_sha=head_sha,
        run_url=args.run_url,
        workflow_conclusion=args.workflow_conclusion,
        claims_complete=claims_complete,
        verifier_trusted=args.verifier_trusted == "true",
    )
    args.out.write_text(comment)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
