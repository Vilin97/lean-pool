"""Coverage, reconciliation, and end-to-end tests for bounded complete reviews."""

import base64
import hashlib
import json
import re
from dataclasses import replace
from types import SimpleNamespace

import pytest

from lean_pool import review, review_portions


def source_diff(size=500):
    """Make distinguishable source declarations with exact reconstruction checks."""
    return "".join(
        f"diff --git a/LeanPool/P/F{index}.lean b/LeanPool/P/F{index}.lean\n"
        + "@@ -0,0 +1,500 @@\n"
        + "".join(
            f"+theorem unique_{index}_{n} : True := by trivial\n" for n in range(size)
        )
        for index in range(3)
    )


def result(payload):
    """Construct a backend result with observable usage for accounting tests."""
    return review.ReviewResult(
        payload,
        SimpleNamespace(prompt_tokens=10, completion_tokens=3),
        "codex-azure",
        None,
        review.DEFAULT_MODEL,
        "xhigh",
    )


@pytest.mark.parametrize("budget", [1, 57, 1000, 50_000])
def test_lossless_source_ranges(budget):
    """Even huge lines and mid-command boundaries retain every source character."""
    diff = source_diff(20) + "+" + "α" * 3000 + "\nlast line without newline"
    portions = review_portions.split_portions(diff, budget)
    assert "".join(portion.text for portion in portions) == diff
    assert all(len(portion.text) <= budget for portion in portions)
    manifest = review_portions.coverage_manifest(diff, portions)
    assert f"Complete source: {len(diff)} characters" in manifest


@pytest.mark.parametrize("corruption", ["gap", "overlap", "replacement", "missing"])
def test_coverage_rejects_corruption(corruption):
    """Coverage cannot claim success after lost, repeated, or substituted source."""
    diff = source_diff(4)
    portions = review_portions.split_portions(diff, 100)
    if corruption == "missing":
        portions.pop()
    else:
        change = {
            "gap": {"start": 1},
            "overlap": {"start": -1},
            "replacement": {"text": "different source"},
        }[corruption]
        portions[0] = replace(portions[0], **change)
    with pytest.raises(ValueError):
        review_portions.coverage_manifest(diff, portions)


def test_complete_workflow_budget_accounting_and_integration(monkeypatch):
    """Every portion is reviewed, all evidence reconciled, and every call counted."""
    monkeypatch.setattr(review, "MAX_INPUT_TOKENS", 10_000)
    calls = []
    diff = source_diff()

    def send(model, messages, effort):
        assert review._message_tokens(messages) <= 10_000
        user = messages[1]["content"]
        calls.append(user)
        if "## Integration of a complete portion review" in user:
            assert "unique_2_499" in user
            assert "obligations" in user
            return result({"verdict": "pass", "resolutions": []})
        assert "source portion" in user
        assert "partial diff" not in user
        return result(
            {
                "verdict": "pass",
                "findings": [],
                "open_questions": [],
                "evidence_summary": "Reviewed unique_2_499 and local definitions.",
                "source_number": int(
                    re.search(r"source portion (\d+)/", user).group(1)
                ),
            }
        )

    monkeypatch.setattr(review, "_send_review", send)
    answer = review.request_review(review.DEFAULT_MODEL, "rules", diff, "review")
    assert answer.payload["verdict"] == "pass"
    assert answer.portions > 1
    assert [item.payload["source_number"] for item in answer.source_reviews] == list(
        range(1, answer.portions + 1)
    )
    assert answer.calls == answer.portions + 1 == len(calls)
    assert answer.usage.prompt_tokens == len(calls) * 10
    assert answer.usage.completion_tokens == len(calls) * 3
    assert answer.truncation is None
    assert answer.coverage
    # Each actual diff segment (after the PR diff marker) reconstructs the source.
    segments = [
        (
            int(re.search(r"source portion (\d+)/", call).group(1)),
            call.split("## PR diff\n\n```diff\n", 1)[1].rsplit("\n```", 1)[0],
        )
        for call in calls
        if "## Integration of a complete portion review" not in call
    ]
    assert "".join(segment for _, segment in sorted(segments)) == diff


@pytest.mark.parametrize("failure", ["transport", "empty", "malformed"])
def test_portion_failure_cannot_reach_integration(monkeypatch, failure):
    """A partial set of successful calls never yields a final approval."""
    monkeypatch.setattr(review, "MAX_INPUT_TOKENS", 10_000)

    def send(model, messages, effort):
        assert "## Integration of" not in messages[1]["content"]
        if failure == "transport":
            raise RuntimeError("worker failed")
        return result({} if failure == "empty" else {"verdict": "pass"})

    monkeypatch.setattr(review, "_send_review", send)
    with pytest.raises((RuntimeError, ValueError)):
        review.request_review(review.DEFAULT_MODEL, "rules", source_diff(), "review")


def test_integration_cannot_drop_findings_or_questions():
    """A reassuring final verdict is insufficient without explicit resolutions."""
    payloads = [
        {
            "verdict": "discuss",
            "bottom_line": "Check definition",
            "findings": [{"detail": "possible weakened hypothesis"}],
            "evidence_summary": "contract",
            "open_questions": ["Where is X defined?"],
        }
    ]
    evidence, obligations = review_portions.evidence_bundle("manifest", payloads, "")
    assert len(obligations) == 3
    assert json.loads(evidence)["portion_reviews"] == payloads
    assert (
        review_portions.enforce_resolutions({"verdict": "pass"}, obligations)["verdict"]
        == "discuss"
    )
    resolved = {
        "verdict": "pass",
        "resolutions": [
            {
                "id": key,
                "evidence": "Portion 2 defines X and discharges the hypothesis.",
            }
            for key in obligations
        ],
    }
    assert (
        review_portions.enforce_resolutions(resolved, obligations)["verdict"] == "pass"
    )
    resolved["resolutions"].append({"id": "invented", "evidence": "irrelevant"})
    with pytest.raises(ValueError, match="unknown"):
        review_portions.enforce_resolutions(resolved, obligations)


def test_oversized_integration_fails_without_discarding_evidence(monkeypatch):
    """Long model responses cannot be silently truncated to fit synthesis."""
    monkeypatch.setattr(review, "MAX_INPUT_TOKENS", 10_000)

    def send(model, messages, effort):
        assert "## Integration of" not in messages[1]["content"]
        return result(
            {
                "verdict": "pass",
                "open_questions": [],
                "evidence_summary": "important evidence " * 3000,
            }
        )

    monkeypatch.setattr(review, "_send_review", send)
    with pytest.raises(ValueError, match="Integration evidence"):
        review.request_review(review.DEFAULT_MODEL, "rules", source_diff(), "review")


def test_context_overflow_repartitions_without_elision(monkeypatch):
    """A backend context rejection switches to smaller complete source portions."""
    monkeypatch.setattr(review, "MAX_INPUT_TOKENS", 20_000)
    original = source_diff(120)
    calls = []

    def send(model, messages, effort):
        calls.append(messages)
        if len(calls) == 1:
            raise RuntimeError("Azure Codex review failed: context_length_exceeded")
        if "## Integration of" in messages[1]["content"]:
            return result({"verdict": "pass"})
        return result(
            {
                "verdict": "pass",
                "open_questions": [],
                "evidence_summary": "Complete local evidence.",
            }
        )

    monkeypatch.setattr(review, "_send_review", send)
    answer = review.request_review(review.DEFAULT_MODEL, "rules", original, "review")
    assert answer.portions > 1
    assert answer.truncation is None
    assert all(review.ELISION_MARKER not in str(call) for call in calls)


def test_context_and_prior_art_are_budgeted(monkeypatch):
    """Large contextual evidence reduces source space and cannot overflow a call."""
    monkeypatch.setattr(review, "MAX_INPUT_TOKENS", 10_000)
    captured = []

    def send(model, messages, effort):
        captured.append(review._message_tokens(messages))
        return result(
            {"verdict": "pass", "open_questions": [], "evidence_summary": "Evidence."}
        )

    monkeypatch.setattr(review, "_send_review", send)
    review.request_review(
        review.DEFAULT_MODEL,
        "rules",
        source_diff(160),
        "review",
        context=review.PullRequestContext("title", "x" * 6000),
        prior_art_section="prior art " * 100,
    )
    assert len(captured) > 1
    assert max(captured) <= 10_000


def test_missing_text_patch_is_not_complete_coverage(monkeypatch):
    """GitHub omitting a large text patch must stop the review before any model."""
    monkeypatch.setattr(
        review,
        "run_gh",
        lambda *args: json.dumps(
            {
                "filename": "LeanPool/Big.lean",
                "status": "added",
                "additions": 9000,
                "deletions": 0,
            }
        ),
    )
    with pytest.raises(ValueError, match="omitted the source blob"):
        review._assemble_diff_from_files("1", "owner/repo")


@pytest.mark.parametrize("patch", [None, "@@ -0,0 +1,2 @@\n+first line"])
def test_missing_or_truncated_patch_recovers_verified_source(monkeypatch, patch):
    """Even zero GitHub statistics cannot hide real source in a verified blob."""
    data = "first line\nsecond line α\n".encode()
    sha = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()

    def github(*args):
        if "/git/blobs/" in args[1]:
            return json.dumps(
                {"encoding": "base64", "content": base64.b64encode(data).decode()}
            )
        return json.dumps(
            {
                "filename": "LeanPool/Big.lean",
                "status": "added",
                "additions": 0,
                "deletions": 0,
                "patch": patch,
                "sha": sha,
            }
        )

    monkeypatch.setattr(review, "run_gh", github)
    diff = review._assemble_diff_from_files("1", "owner/repo")
    assert "+first line\n+second line α" in diff
    assert "--- /dev/null" in diff


def test_blob_hash_mismatch_fails_closed(monkeypatch):
    """A corrupted or wrong source blob is rejected before producing a diff."""
    monkeypatch.setattr(
        review,
        "run_gh",
        lambda *args: json.dumps(
            {"encoding": "base64", "content": base64.b64encode(b"wrong").decode()}
        ),
    )
    with pytest.raises(ValueError, match="corrupt"):
        review._load_blob("owner/repo", "0" * 40)


def test_content_free_rename_is_verified_from_both_blobs(monkeypatch):
    """Zero changed-line metadata alone cannot certify a pure rename."""
    monkeypatch.setattr(
        review,
        "run_gh",
        lambda *args: json.dumps(
            {
                "filename": "LeanPool/New.lean",
                "previous_filename": "LeanPool/Old.lean",
                "status": "renamed",
                "additions": 0,
                "deletions": 0,
                "sha": "head-blob",
            }
        ),
    )
    monkeypatch.setattr(review, "_load_blob", lambda *args: "same source\n")
    before = []

    def merge_base(number, repo, path):
        before.append(path)
        return "same source\n"

    monkeypatch.setattr(review, "_merge_base_file", merge_base)
    diff = review._assemble_diff_from_files("1", "owner/repo")
    assert before == ["LeanPool/Old.lean"]
    assert "a/LeanPool/Old.lean b/LeanPool/New.lean" in diff
    assert "omitted" not in diff


@pytest.mark.parametrize("kind", ["project", "refactor", "challenge", "solution"])
def test_unresolved_evidence_stays_visible(kind):
    """All comment formats retain concrete source findings and coverage details."""
    payload = review_portions.enforce_resolutions(
        {"verdict": "approve", "summary": "Looks good."},
        {"1:finding:1": "Target is defined as True; this does not prove evenness."},
    )
    body = review.render_comment(
        payload,
        "gpt-6-astra",
        None,
        "codex-azure",
        "test-head",
        kind=kind,
        coverage="test coverage",
        portions=3,
        calls=4,
    )
    assert "Target is defined as True" in body
    assert "needs_discussion" in body
    assert "3 source portions" in body
    assert "test coverage" in body


def test_successful_retry_work_is_counted_and_unknown_usage_disclosed(monkeypatch):
    """A failed batch does not erase earlier completed calls from the usage footer."""
    monkeypatch.setattr(review, "MAX_INPUT_TOKENS", 40_000)
    calls = []

    def send(model, messages, effort):
        calls.append(messages)
        if len(calls) == 2:
            raise RuntimeError("Azure Codex review failed: context_length_exceeded")
        return result(
            {
                "verdict": "pass",
                "open_questions": [],
                "evidence_summary": "Inspected source definitions.",
            }
        )

    monkeypatch.setattr(review, "_send_review", send)
    answer = review.request_review(
        review.DEFAULT_MODEL, "rules", source_diff(700), "review"
    )
    assert answer.calls == len(calls)
    assert len(answer.requests) == answer.calls - 1
    assert answer.usage is None
    footer = review._render_rubric_usage(
        [review.RubricOutcome(review.PROJECT_RUBRICS[0], answer, "pass")], "xhigh"
    )
    assert f"{10 * len(answer.requests):,} in" in footer
    assert "Token totals are partial" in footer


def test_integration_can_retrieve_exact_missing_definitions(monkeypatch):
    """Integration gets source on demand instead of being limited to summaries."""
    diff = (
        "diff --git a/LeanPool/P.lean b/LeanPool/P.lean\n"
        "+def ActualMeaning : Prop := True\n"
    )
    calls = []

    def prepare(evidence, rules):
        return [
            {"role": "system", "content": "review"},
            {"role": "user", "content": rules + evidence},
        ]

    def send(messages):
        text = messages[1]["content"]
        calls.append(text)
        if len(calls) == 1:
            return result(
                {"verdict": "discuss", "source_requests": ["P.ActualMeaning"]}
            )
        assert "+def ActualMeaning : Prop := True" in text
        return result(
            {
                "verdict": "block",
                "source_requests": [],
                "findings": [{"comment": "True does not prove the claimed property."}],
            }
        )

    answer = review._integrate_portions(diff, "{}", {}, 10_000, prepare, send)
    assert answer.payload["verdict"] == "block"
    assert len(calls) == 2


def test_source_requests_cannot_approve_without_answers():
    """Exhausted source follow-ups remain visible unresolved obligations."""

    def prepare(evidence, rules):
        return [
            {"role": "system", "content": "review"},
            {"role": "user", "content": evidence},
        ]

    def send(messages):
        return result({"verdict": "pass", "source_requests": ["MissingDefinition"]})

    answer = review._integrate_portions(
        "+def Known := 0", "{}", {}, 10_000, prepare, send
    )
    assert answer.payload["verdict"] == "discuss"
    assert "MissingDefinition" in str(answer.payload["findings"])


def test_source_requests_never_open_arbitrary_paths():
    """Only the supplied diff can provide source evidence."""
    answer = review_portions.source_excerpts("+def Known := 0", "/etc/passwd", 1000)
    assert "No matching" in answer["status"]


def test_evidence_artifact_contains_all_model_results(monkeypatch, tmp_path):
    """A maintainer can inspect the source reviews behind the integrated verdict."""
    path = tmp_path / "evidence.json"
    monkeypatch.setenv("REVIEW_EVIDENCE_PATH", str(path))
    leaf = result({"evidence_summary": "source definitions"})
    final = replace(result({"verdict": "pass"}), requests=(leaf,), coverage="manifest")
    review._write_review_evidence([final])
    data = json.loads(path.read_text())
    assert data[0]["requests"][0]["payload"]["evidence_summary"] == "source definitions"
    assert data[0]["coverage"] == "manifest"


@pytest.mark.parametrize("resolve", [False, True])
def test_integration_followup_preserves_previous_concerns(resolve):
    """A follow-up cannot erase a newly found issue or unanswered source request."""
    calls = []

    def prepare(evidence, rules):
        return [{"role": "user", "content": evidence}]

    def send(messages):
        bundle = json.loads(messages[0]["content"])
        calls.append(bundle)
        if len(calls) == 1:
            return result(
                {
                    "verdict": "discuss",
                    "bottom_line": "Cross-module meaning needs checking",
                    "findings": [{"comment": "Potentially vacuous definition"}],
                    "open_questions": ["Does the premise have a witness?"],
                    "source_requests": ["MissingDefinition"],
                }
            )
        assert bundle["integration_history"][0]["findings"]
        assert len(bundle["obligations"]) == 4
        assert "No matching" in str(bundle["source_followups"])
        resolutions = (
            [
                {
                    "id": identifier,
                    "evidence": "Concrete supplied evidence resolves this concern",
                }
                for identifier in bundle["obligations"]
            ]
            if resolve
            else []
        )
        return result(
            {"verdict": "pass", "source_requests": [], "resolutions": resolutions}
        )

    answer = review._integrate_portions(
        "+def Known := 0", "{}", {}, 10_000, prepare, send
    )
    assert len(calls) == 2
    assert answer.payload["verdict"] == ("pass" if resolve else "discuss")
    if not resolve:
        assert "Potentially vacuous definition" in str(answer.payload["findings"])
        assert "MissingDefinition" in str(answer.payload["findings"])


@pytest.mark.parametrize("field", ["findings", "open_questions", "source_requests"])
def test_final_integration_concerns_prevent_approval(field):
    """A final pass cannot override unresolved concerns in that same report."""
    payload = {"verdict": "pass", field: ["Unresolved semantic question"]}
    answer = review_portions.enforce_resolutions(payload, {})
    assert answer["verdict"] == "discuss"
    assert "Unresolved semantic question" in str(answer["findings"])


def test_source_excerpt_allowance_uses_characters(monkeypatch):
    """An excerpt can use the remaining token budget at the configured ratio."""
    calls = []
    allowances = []

    def prepare(evidence, rules):
        return [{"role": "user", "content": evidence}]

    def send(messages):
        calls.append(messages)
        return result(
            {"verdict": "pass", "source_requests": ["Known"] if len(calls) == 1 else []}
        )

    def excerpt(diff, query, allowance):
        allowances.append(allowance)
        return {"source": "def Known := 0"}

    monkeypatch.setattr(review_portions, "source_excerpts", excerpt)
    review._integrate_portions("def Known := 0", "{}", {}, 10_000, prepare, send)
    assert 15_000 < allowances[0] < 20_000


def test_many_source_requests_are_not_discarded(monkeypatch):
    """The input budget, rather than an arbitrary request count, bounds retrieval."""
    requested = [f"Definition{index}" for index in range(25)]
    retrieved = []
    calls = []

    def prepare(evidence, rules):
        return [{"role": "user", "content": evidence}]

    def send(messages):
        calls.append(messages)
        return result(
            {"verdict": "pass", "source_requests": requested if len(calls) == 1 else []}
        )

    def excerpt(diff, query, allowance):
        retrieved.append(query)
        return {"query": query, "status": "No matching source"}

    monkeypatch.setattr(review_portions, "source_excerpts", excerpt)
    answer = review._integrate_portions("", "{}", {}, 10_000, prepare, send)
    assert retrieved == requested
    assert answer.payload["verdict"] == "discuss"


def test_completed_calls_are_saved_before_later_failure(monkeypatch, tmp_path):
    """Successful source work survives an integration or transport failure."""
    destination = tmp_path / "review-evidence.json"
    monkeypatch.setenv("REVIEW_EVIDENCE_PATH", str(destination))
    monkeypatch.setattr(
        review, "_send_review", lambda *args: result({"verdict": "pass"})
    )
    session = review._ReviewSession(review.DEFAULT_MODEL, "xhigh")
    session.send([])
    saved = json.loads(destination.with_suffix(".calls.jsonl").read_text())
    assert saved["payload"]["verdict"] == "pass"


def test_followup_budget_includes_serialized_metadata_and_escaping(monkeypatch):
    """Escaping and many per-query envelopes cannot overflow the next call."""
    calls = []

    def prepare(evidence, rules):
        return [{"role": "user", "content": evidence}]

    def send(messages):
        assert review._message_tokens(messages) <= 10_000
        calls.append(messages)
        return result(
            {
                "verdict": "pass",
                "source_requests": [f"D{i}" for i in range(20)]
                if len(calls) == 1
                else [],
            }
        )

    def excerpt(diff, query, allowance):
        return {"query": query, "source": "\\" * allowance, "status": "metadata " * 50}

    monkeypatch.setattr(review_portions, "source_excerpts", excerpt)
    answer = review._integrate_portions("", "{}", {}, 10_000, prepare, send)
    assert len(calls) == 2
    assert answer.payload["verdict"] == "discuss"


def test_final_findings_are_reported_once():
    """A retained finding blocks approval without a duplicate synthetic entry."""
    finding = {"comment": "Unresolved semantic concern"}
    answer = review_portions.enforce_resolutions(
        {"verdict": "pass", "findings": [finding]}, {}
    )
    assert answer["verdict"] == "discuss"
    assert answer["findings"] == [finding]
