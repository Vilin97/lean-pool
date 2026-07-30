"""Tests for standalone challenge comparator PR comments."""

from pathlib import Path
from stat import S_IFLNK
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

from lean_pool.challenge_report import (
    COMPARATOR_COMMENT_MARKER,
    MAX_CLAIMS,
    MAX_REPORT_BYTES,
    ComparatorClaim,
    ComparatorResult,
    extract_report,
    main,
    record_result,
    render_comment,
    render_pending_comment,
)


def test_success_comment_identifies_claim_head_and_run() -> None:
    """A green comment is a distinct, auditable comparator verdict."""
    comment = render_comment(
        [ComparatorClaim("widget", "Solution.Widget")],
        [ComparatorResult("widget", "passed")],
        head_sha="a" * 40,
        run_url="https://github.com/acme/pool/actions/runs/7",
        workflow_conclusion="success",
    )

    assert comment.startswith(COMPARATOR_COMMENT_MARKER)
    assert "## ✅ Challenge comparator — verified" in comment
    assert "<code>widget</code>" in comment
    assert "<code>Solution.Widget</code>" in comment
    assert f"<code>{'a' * 40}</code>" in comment
    assert "[Comparator run](https://github.com/acme/pool/actions/runs/7)" in comment


def test_success_requires_an_explicit_passing_result() -> None:
    """A green workflow alone cannot manufacture a comparator verdict."""
    comment = render_comment(
        [ComparatorClaim("widget", "Solution.Widget")],
        [],
        head_sha="b" * 40,
        run_url="https://example.invalid/run",
        workflow_conclusion="success",
    )

    assert "## ⚠️ Challenge comparator — incomplete" in comment
    assert "✅ Verified" not in comment
    assert "Comparator did not run" in comment


def test_failed_workflow_cannot_publish_a_green_result() -> None:
    """A recorded pass is not green when a later verifier step failed."""
    comment = render_comment(
        [ComparatorClaim("widget", "Solution.Widget")],
        [ComparatorResult("widget", "passed")],
        head_sha="c" * 40,
        run_url="https://example.invalid/run",
        workflow_conclusion="failure",
    )

    assert "## ❌ Challenge comparator — failed" in comment
    assert "✅ Verified" not in comment
    assert "Verifier did not complete" in comment


def test_verifier_changes_cannot_publish_a_green_result() -> None:
    """A PR-controlled verifier artifact is never accepted as proof."""
    comment = render_comment(
        [ComparatorClaim("widget", "Solution.Widget")],
        [ComparatorResult("widget", "passed")],
        head_sha="0" * 40,
        run_url="https://example.invalid/run",
        workflow_conclusion="success",
        verifier_trusted=False,
    )

    assert "## ❌ Challenge comparator — failed" in comment
    assert "✅ Verified" not in comment
    assert "Verifier inputs are not trusted" in comment


def test_challenge_contract_changes_cannot_publish_green() -> None:
    """Comparator acceptance of a mutated target is not a solution verdict."""
    comment = render_comment(
        [
            ComparatorClaim(
                "widget",
                "Solution.Widget",
                contract_unchanged=False,
            )
        ],
        [ComparatorResult("widget", "passed")],
        head_sha="2" * 40,
        run_url="https://example.invalid/run",
        workflow_conclusion="success",
    )

    assert "## ❌ Challenge comparator — failed" in comment
    assert "Challenge contract changed" in comment
    assert "✅ Verified" not in comment


def test_failed_comparator_has_no_success_wording() -> None:
    """An explicit comparator rejection is rendered only as a failure."""
    comment = render_comment(
        [ComparatorClaim("widget", "Solution.Widget")],
        [ComparatorResult("widget", "failed")],
        head_sha="d" * 40,
        run_url="https://example.invalid/run",
        workflow_conclusion="failure",
    )

    assert "❌ Comparator failed" in comment
    assert "— verified" not in comment
    assert "✅ Verified" not in comment


def test_incomplete_claim_detection_still_renders_a_comment() -> None:
    """Early setup failures do not silently omit the standalone verdict."""
    comment = render_comment(
        [],
        [],
        head_sha="e" * 40,
        run_url="https://example.invalid/run",
        workflow_conclusion="failure",
        claims_complete=False,
    )

    assert comment.startswith(COMPARATOR_COMMENT_MARKER)
    assert "stopped before it could determine and check" in comment
    assert "success verdict was produced" in comment


def test_multi_claim_comment_lists_every_outcome() -> None:
    """One failed claim does not hide another claim's result."""
    comment = render_comment(
        [
            ComparatorClaim("first", "Solution.First"),
            ComparatorClaim("second", "Solution.Second"),
            ComparatorClaim("external", None),
        ],
        [
            ComparatorResult("first", "passed"),
            ComparatorResult("second", "failed"),
        ],
        head_sha="f" * 40,
        run_url="https://example.invalid/run",
        workflow_conclusion="failure",
    )

    assert "<code>first</code>" in comment
    assert "<code>second</code>" in comment
    assert "<code>external</code>" in comment
    assert "No in-repo solution module" in comment


def test_no_claims_produces_no_comment() -> None:
    """Tooling and open-challenge PRs do not inherit historical solutions."""
    assert (
        render_comment(
            [],
            [],
            head_sha="1" * 40,
            run_url="https://example.invalid/run",
            workflow_conclusion="success",
        )
        == ""
    )


def test_pending_comment_exists_before_any_comparator_result() -> None:
    """Trusted PR-target detection gives every claim an immediate comment."""
    comment = render_pending_comment(
        [ComparatorClaim("widget", "Solution.Widget")],
        head_sha="3" * 40,
    )

    assert comment.startswith(COMPARATOR_COMMENT_MARKER)
    assert "## ⏳ Challenge comparator — pending" in comment
    assert "until then, no solution has been verified" in comment
    assert "<code>widget</code>" in comment


def test_oversized_claim_data_fails_before_github_can_reject_comment() -> None:
    """Oversized registry text cannot suppress the sticky comment."""
    claims = [
        ComparatorClaim(f"claim-{index}", "Solution.Widget")
        for index in range(MAX_CLAIMS + 1)
    ]

    try:
        render_pending_comment(claims, head_sha="3" * 40)
    except ValueError as error:
        assert "at most" in str(error)
    else:
        raise AssertionError("oversized claim list was accepted")


def test_record_result_replaces_a_slug_without_losing_others(tmp_path: Path) -> None:
    """Rerunning one comparator result keeps the report deterministic."""
    path = tmp_path / "results.json"
    record_result(path, ComparatorResult("first", "failed"))
    record_result(path, ComparatorResult("second", "passed"))
    record_result(path, ComparatorResult("first", "passed"))

    assert path.read_text() == (
        "[\n"
        "  {\n"
        '    "slug": "second",\n'
        '    "status": "passed"\n'
        "  },\n"
        "  {\n"
        '    "slug": "first",\n'
        '    "status": "passed"\n'
        "  }\n"
        "]\n"
    )


def test_extract_report_accepts_only_bounded_protocol_files(tmp_path: Path) -> None:
    """The privileged consumer extracts the small fixed artifact protocol."""
    archive = tmp_path / "report.zip"
    with ZipFile(archive, "w") as output:
        output.writestr("head-sha.txt", f"{'a' * 40}\n")
        output.writestr("results.json", "[]\n")
    report_directory = tmp_path / "report"

    status = main(["extract", str(archive), str(report_directory)])

    assert status == 0
    assert (report_directory / "head-sha.txt").read_text() == f"{'a' * 40}\n"
    assert (report_directory / "results.json").read_text() == "[]\n"


def test_extract_report_rejects_unexpected_paths(tmp_path: Path) -> None:
    """A report ZIP cannot write outside or pre-seed trusted workflow files."""
    archive = tmp_path / "report.zip"
    with ZipFile(archive, "w") as output:
        output.writestr("changed-paths.txt", "hide/the/unsafe/workflow.yml\n")

    try:
        extract_report(archive, tmp_path / "report")
    except ValueError as error:
        assert "unexpected comparator report file" in str(error)
    else:
        raise AssertionError("unexpected report path was extracted")


def test_extract_report_rejects_symlink_protocol_file(tmp_path: Path) -> None:
    """An artifact cannot redirect later trusted writes through a symlink."""
    archive = tmp_path / "report.zip"
    member = ZipInfo("results.json")
    member.create_system = 3
    member.external_attr = (S_IFLNK | 0o777) << 16
    with ZipFile(archive, "w") as output:
        output.writestr(member, "/dev/null")

    try:
        extract_report(archive, tmp_path / "report")
    except ValueError as error:
        assert "non-regular comparator report file" in str(error)
    else:
        raise AssertionError("symlink report file was extracted")


def test_extract_report_rejects_uncompressed_zip_bomb_size(tmp_path: Path) -> None:
    """A tiny compressed artifact cannot expand past the trusted byte budget."""
    archive = tmp_path / "report.zip"
    with ZipFile(archive, "w", compression=ZIP_DEFLATED) as output:
        output.writestr("results.json", b" " * (MAX_REPORT_BYTES + 1))

    try:
        extract_report(archive, tmp_path / "report")
    except ValueError as error:
        assert "exceeds the size limit" in str(error)
    else:
        raise AssertionError("oversized report was extracted")


def test_report_cli_renders_the_uploaded_artifact(tmp_path: Path) -> None:
    """The companion workflow's exact file protocol produces the verdict."""
    report_directory = tmp_path / "report"
    report_directory.mkdir()
    (report_directory / "claims-state.txt").write_text("complete\n")
    (report_directory / "claims.json").write_text(
        '[{"slug": "widget", "module": "Solution.Widget", '
        '"contract_unchanged": true}]\n'
    )
    (report_directory / "results.json").write_text(
        '[{"slug": "widget", "status": "passed"}]\n'
    )
    (report_directory / "head-sha.txt").write_text(f"{'a' * 40}\n")
    output = tmp_path / "comment.md"

    status = main(
        [
            "render",
            str(report_directory),
            "--workflow-conclusion",
            "success",
            "--verifier-trusted",
            "true",
            "--run-url",
            "https://example.invalid/run",
            "--out",
            str(output),
        ]
    )

    assert status == 0
    assert "## ✅ Challenge comparator — verified" in output.read_text()
