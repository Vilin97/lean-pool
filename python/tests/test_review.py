"""Tests for LLM review comment rendering and oversized-diff truncation."""

from __future__ import annotations

import types

# The stub registered by tests/conftest.py; its exception classes carry
# the status_code attributes the review module's error handling inspects.
import openai


def _file_patch(path: str, body_lines: list[str]) -> str:
    """Build one added-file chunk of a unified diff."""
    return "\n".join(
        [
            f"diff --git a/{path} b/{path}",
            "--- /dev/null",
            f"+++ b/{path}",
            f"@@ -0,0 +1,{len(body_lines)} @@",
            *[f"+{line}" for line in body_lines],
        ]
    )


def test_render_comment_includes_marker_and_reviewed_head() -> None:
    """The review comment is sticky and identifies the reviewed commit."""
    from lean_pool.review import LLM_REVIEW_MARKER, render_comment

    body = render_comment(
        {
            "summary": "A concise assessment.",
            "assessment": {
                "fit": "good_fit",
                "level": "graduate",
                "branch": "analysis",
                "mode": "theory_building",
                "obscure_problem": False,
                "code_quality": 4,
                "significance_one_sentence": "A named theorem is formalized.",
            },
            "verdict": "approve",
            "findings": [],
        },
        model="gpt-5.5",
        usage=None,
        tier="flex",
        reviewed_head_sha="abc123",
    )

    assert body.startswith(LLM_REVIEW_MARKER)
    assert "**Reviewed head:** `abc123`" in body
    assert "**Verdict:**" in body
    # A new-project review links the project rules, not the refactor rules.
    assert "REVIEW_RULES.md" in body
    assert "REFACTOR_REVIEW_RULES.md" not in body
    # An untruncated review must not carry the partial-review banner.
    assert "Partial review" not in body


def test_classify_pr_pure_golf_is_refactor() -> None:
    """Modifying only existing project files is a refactor."""
    from lean_pool.review import classify_pr

    files = [
        ("LeanPool/Foo/A.lean", "modified"),
        ("LeanPool/Bar/B.lean", "modified"),
        ("LeanPool.lean", "modified"),
    ]
    assert classify_pr(files) == "refactor"


def test_classify_pr_new_project_is_project() -> None:
    """A project that appears only through added files is a new project."""
    from lean_pool.review import classify_pr

    files = [
        ("LeanPool/NewProj/A.lean", "added"),
        ("LeanPool/NewProj/B.lean", "added"),
        ("LeanPool/projects.yml", "modified"),
        ("LeanPool.lean", "modified"),
    ]
    assert classify_pr(files) == "project"


def test_classify_pr_module_split_is_refactor() -> None:
    """Adding a file to a project that is also modified stays a refactor."""
    from lean_pool.review import classify_pr

    files = [
        ("LeanPool/Foo/A.lean", "modified"),
        ("LeanPool/Foo/ASplit.lean", "added"),
    ]
    assert classify_pr(files) == "refactor"


def test_classify_pr_without_project_files_defaults_to_project() -> None:
    """Infra-only diffs fall back to the conservative project review."""
    from lean_pool.review import classify_pr

    assert classify_pr([("README.md", "modified")]) == "project"


def test_classify_pr_new_challenge_is_challenge() -> None:
    """Putting an open statement on the board gets the challenge review."""
    from lean_pool.review import classify_pr

    files = [
        ("Challenge/TwinPrimes.lean", "added"),
        ("Challenge/challenges.yml", "modified"),
        ("Challenge.lean", "modified"),
    ]
    assert classify_pr(files) == "challenge"


def test_classify_pr_edited_challenge_is_challenge() -> None:
    """Editing a live statement is reviewed as a challenge, not a refactor."""
    from lean_pool.review import classify_pr

    assert classify_pr([("Challenge/TwinPrimes.lean", "modified")]) == "challenge"


def test_classify_pr_challenge_plus_pool_content_is_not_challenge() -> None:
    """A bump repairing both libraries keeps the content classification."""
    from lean_pool.review import classify_pr

    files = [
        ("Challenge/TwinPrimes.lean", "modified"),
        ("LeanPool/Foo/A.lean", "modified"),
    ]
    assert classify_pr(files) == "refactor"


def test_classify_pr_answer_is_solution() -> None:
    """Adding an answer to a challenge already on the board is a solution."""
    from lean_pool.review import classify_pr

    files = [
        ("Solution/TwoPlusTwo.lean", "added"),
        ("Solution.lean", "modified"),
        ("Challenge/challenges.yml", "modified"),
    ]
    assert classify_pr(files) == "solution"


def test_classify_pr_new_challenge_with_its_answer_is_challenge() -> None:
    """A new board entry is judged as one even when its proof rides along."""
    from lean_pool.review import classify_pr

    files = [
        ("Challenge/Widget.lean", "added"),
        ("Solution/Widget.lean", "added"),
        ("Challenge/challenges.yml", "modified"),
    ]
    assert classify_pr(files) == "challenge"


def test_classify_pr_delegated_solution_is_solution() -> None:
    """A solution backed by a pooled project is still a solution PR."""
    from lean_pool.review import classify_pr

    files = [
        ("Solution/Widget.lean", "added"),
        ("LeanPool/WidgetProof/A.lean", "added"),
        ("LeanPool/projects.yml", "modified"),
        ("Challenge/challenges.yml", "modified"),
    ]
    assert classify_pr(files) == "solution"


def test_plain_solution_pr_skips_the_model(tmp_path) -> None:
    """Nothing but an answer and its registry entry: nothing to review."""
    from lean_pool.review import solution_needs_llm_review

    (tmp_path / "Challenge").mkdir()
    (tmp_path / "Challenge" / "challenges.yml").write_text(
        "challenges:\n"
        "  - slug: widget\n"
        "    entry_module: Challenge.Widget\n"
        "    statements:\n"
        "      - declaration: Challenge.Widget.widget_exists\n"
        "        informal: A widget exists.\n"
        "    solution:\n"
        "      module: Solution.Widget\n"
    )
    files = [
        ("Solution/Widget.lean", "added"),
        ("Solution.lean", "modified"),
        ("Challenge/challenges.yml", "modified"),
    ]

    assert solution_needs_llm_review(files, tmp_path) is None


def test_solution_pr_touching_the_statement_is_reviewed(tmp_path) -> None:
    """Anything beyond the answer itself gets a reading."""
    from lean_pool.review import solution_needs_llm_review

    (tmp_path / "Challenge").mkdir()
    (tmp_path / "Challenge" / "challenges.yml").write_text("challenges: []\n")
    files = [
        ("Solution/Widget.lean", "added"),
        ("Challenge/Widget.lean", "modified"),
    ]

    reason = solution_needs_llm_review(files, tmp_path)

    assert reason is not None
    assert "Challenge/Widget.lean" in reason


def test_solution_pr_for_a_definition_hole_is_reviewed(tmp_path) -> None:
    """Comparator matches a hole by name and type only, so a human looks."""
    from lean_pool.review import solution_needs_llm_review

    (tmp_path / "Challenge").mkdir()
    (tmp_path / "Challenge" / "challenges.yml").write_text(
        "challenges:\n"
        "  - slug: widget\n"
        "    entry_module: Challenge.Widget\n"
        "    statements:\n"
        "      - declaration: Challenge.Widget.widget_bound\n"
        "        informal: The answer exceeds 37.\n"
        "    definitions:\n"
        "      - declaration: Challenge.Widget.answer\n"
        "        informal: The answer.\n"
        "    solution:\n"
        "      module: Solution.Widget\n"
    )
    files = [("Solution/Widget.lean", "added")]

    reason = solution_needs_llm_review(files, tmp_path)

    assert reason is not None
    assert "definition hole" in reason


def test_render_comment_solution_mode() -> None:
    """A solution review defers correctness to the comparator check."""
    from lean_pool.review import LLM_REVIEW_MARKER, render_comment

    body = render_comment(
        {
            "summary": "Proves the two-plus-two fixture by decide.",
            "assessment": {
                "touches_challenge_statement": False,
                "definition_hole_risk": "none",
                "proof_quality": 4,
                "assessment_one_sentence": "One-line proof, nothing to flag.",
            },
            "verdict": "approve",
            "findings": [],
        },
        model="gpt-5.5",
        usage=None,
        tier="flex",
        reviewed_head_sha="deadbeef",
        kind="solution",
    )

    assert body.startswith(LLM_REVIEW_MARKER)
    assert "LLM review — challenge solution" in body
    assert "Correctness is decided by" in body
    assert "| Touches the challenge statement | ✅ no |" in body
    assert "| Definition-hole risk | ✅ `none` |" in body
    assert "SOLUTION_REVIEW_RULES.md" in body
    assert "| Fit |" not in body


def test_render_solution_skip_comment_is_sticky_and_explains_itself() -> None:
    """The skip note replaces the review and says what did the checking."""
    from lean_pool.review import LLM_REVIEW_MARKER, render_solution_skip_comment

    body = render_solution_skip_comment("deadbeef")

    assert body.startswith(LLM_REVIEW_MARKER)
    assert "skipped" in body
    assert "Correctness is decided by" in body
    assert "deadbeef" in body


def test_render_comment_challenge_mode() -> None:
    """A challenge review shows faithfulness, vacuity, and a size estimate."""
    from lean_pool.review import LLM_REVIEW_MARKER, render_comment

    body = render_comment(
        {
            "summary": "Adds the twin prime conjecture as an open statement.",
            "assessment": {
                "significance": "high",
                "faithfulness": "faithful",
                "faithfulness_note": "Set.Infinite over {p | p.Prime ∧ (p+2).Prime}.",
                "source_match": "matches",
                "vacuity_risk": "none",
                "difficulty": "open_problem",
                "estimated_lines": 25000,
                "estimate_basis": "No known proof; Zhang-style machinery is absent.",
                "already_formalized": "",
                "assessment_one_sentence": "A correctly stated famous open problem.",
            },
            "verdict": "approve",
            "findings": [],
        },
        model="gpt-5.5",
        usage=None,
        tier="flex",
        reviewed_head_sha="deadbeef",
        kind="challenge",
    )

    assert body.startswith(LLM_REVIEW_MARKER)
    assert "LLM review — challenge" in body
    assert "| Faithful to the prose | ✅ `faithful` |" in body
    assert "| Vacuity risk | ✅ `none` |" in body
    assert "~25,000 lines" in body
    assert "Zhang-style machinery is absent" in body
    assert "CHALLENGE_REVIEW_RULES.md" in body
    # Project- and refactor-only fields must not leak into a challenge review.
    assert "| Fit |" not in body
    assert "| Brittleness |" not in body


def test_render_challenge_assessment_flags_existing_formalization() -> None:
    """A challenge that duplicates existing work says so in the table."""
    from lean_pool.review import render_challenge_assessment

    table = render_challenge_assessment(
        {
            "assessment": {
                "significance": "low",
                "faithfulness": "mismatch",
                "source_match": "unverifiable",
                "vacuity_risk": "possible",
                "difficulty": "exercise",
                "estimated_lines": 40,
                "already_formalized": "Nat.exists_infinite_primes",
            }
        }
    )

    assert "🛑 `mismatch`" in table
    assert "🛑 `Nat.exists_infinite_primes`" in table
    assert "~40 lines" in table


def test_render_comment_refactor_mode() -> None:
    """A refactor review shows the tech-debt table and refactor rules link."""
    from lean_pool.review import LLM_REVIEW_MARKER, render_comment

    body = render_comment(
        {
            "summary": "Collapses many proofs into a single simp_all.",
            "assessment": {
                "scope": "proof golf",
                "introduces_tech_debt": True,
                "maintainability": "regressed",
                "brittleness": "more_brittle",
                "risk": "medium",
                "assessment_one_sentence": "Shorter, but more fragile.",
            },
            "verdict": "needs_discussion",
            "findings": [],
        },
        model="gpt-5.5",
        usage=None,
        tier="flex",
        reviewed_head_sha="deadbeef",
        kind="refactor",
    )

    assert body.startswith(LLM_REVIEW_MARKER)
    assert "LLM review — refactor" in body
    assert "Brittleness" in body
    assert "Introduces tech debt" in body
    assert "REFACTOR_REVIEW_RULES.md" in body
    # Project-only assessment fields must not leak into a refactor review.
    assert "| Fit |" not in body
    assert "| Level |" not in body


def test_fit_diff_under_budget_is_untouched() -> None:
    """A diff inside the token budget is sent verbatim, with no truncation."""
    from lean_pool.review import fit_diff_to_budget

    diff = _file_patch("LeanPool/Foo/A.lean", ["import Mathlib", "-- tiny"]) + "\n"
    fitted, truncation = fit_diff_to_budget(diff, budget_tokens=10_000)

    assert fitted == diff
    assert truncation is None


def test_fit_diff_elides_largest_files_first() -> None:
    """Oversized diffs lose the biggest file bodies but keep paths and heads."""
    from lean_pool.review import (
        CHARS_PER_TOKEN_ESTIMATE,
        ELISION_MARKER,
        fit_diff_to_budget,
    )

    small = _file_patch(
        "LeanPool/Tiny/Small.lean", [f"KEEP_SMALL line {i}" for i in range(5)]
    )
    huge = _file_patch(
        "LeanPool/Big/Certificate.lean",
        [f"BULK_CERT interval case {i} padding 12345/67890" for i in range(400)],
    )
    medium = _file_patch(
        "LeanPool/Mid/Medium.lean",
        [f"KEEP_MEDIUM padding padding {i}" for i in range(50)],
    )
    diff = "\n".join([small, huge, medium]) + "\n"

    budget_tokens = 4_000
    fitted, truncation = fit_diff_to_budget(diff, budget_tokens=budget_tokens)

    assert truncation is not None
    assert truncation.total_files == 3
    assert truncation.elided_files == 1
    assert not truncation.hard_truncated
    assert truncation.original_chars == len(diff)
    assert truncation.final_chars == len(fitted)
    assert len(fitted) <= int(budget_tokens * CHARS_PER_TOKEN_ESTIMATE)
    # The elided file keeps its path, head lines, and an elision marker
    # recording the dropped line counts.
    assert "diff --git a/LeanPool/Big/Certificate.lean" in fitted
    assert "+BULK_CERT interval case 0 " in fitted
    assert "case 399" not in fitted
    assert ELISION_MARKER in fitted
    assert "361 of 401 patch lines omitted" in fitted
    # Small files survive in full, in their original order.
    assert "+KEEP_SMALL line 4" in fitted
    assert "+KEEP_MEDIUM padding padding 49" in fitted
    assert (
        fitted.index("Small.lean")
        < fitted.index("Certificate.lean")
        < fitted.index("Medium.lean")
    )


def test_fit_diff_hard_truncates_as_last_resort() -> None:
    """When even fully elided files overflow, the diff tail is cut outright."""
    from lean_pool.review import ELISION_MARKER, fit_diff_to_budget

    diff = (
        "\n".join(
            _file_patch(
                f"LeanPool/Bulk/File{n}.lean",
                [f"generated case {n}.{i}" for i in range(60)],
            )
            for n in range(40)
        )
        + "\n"
    )
    fitted, truncation = fit_diff_to_budget(diff, budget_tokens=500)

    assert truncation is not None
    assert truncation.hard_truncated
    assert len(fitted) < 1_500
    assert ELISION_MARKER in fitted
    assert "remainder of the diff omitted" in fitted


def test_request_review_refits_after_token_overflow(monkeypatch) -> None:
    """An "input tokens exceed" API rejection refits the diff, not the run."""
    from lean_pool import review

    calls: list[str] = []
    payload_json = '{"summary": "ok", "verdict": "approve", "findings": []}'

    class _FakeCompletions:
        """Rejects the first request as oversized, accepts the second."""

        def create(self, **kwargs):
            """Record the user message and answer like the OpenAI client."""
            assert kwargs["service_tier"] == "flex"
            calls.append(kwargs["messages"][1]["content"])
            if len(calls) == 1:
                raise openai.BadRequestError(
                    "Input tokens exceed the configured limit of 922000 "
                    "tokens. Your messages resulted in 1556823 tokens."
                )
            message = types.SimpleNamespace(content=payload_json)
            return types.SimpleNamespace(
                choices=[types.SimpleNamespace(message=message)], usage=None
            )

    class _FakeClient:
        """Stub OpenAI client exposing chat.completions.create."""

        def __init__(self) -> None:
            """Wire up the fake chat.completions endpoint."""
            self.chat = types.SimpleNamespace(completions=_FakeCompletions())

    monkeypatch.setattr(review, "OpenAI", lambda timeout: _FakeClient())
    monkeypatch.setattr(review, "MAX_INPUT_TOKENS", 3_000)

    big = _file_patch(
        "LeanPool/Big/Generated.lean",
        [f"machine generated bulk case line {i}".ljust(40, ".") for i in range(100)],
    )
    small = _file_patch("LeanPool/Tiny/Card.lean", ["KEEP_ME"] * 10)
    diff = "\n".join([big, small]) + "\n"

    payload, usage, tier, truncation = review.request_review(
        model="gpt-5.5", rules="R" * 200, diff=diff, system_prompt="Review."
    )

    assert payload == {"summary": "ok", "verdict": "approve", "findings": []}
    assert usage is None
    assert tier == "flex"
    # First attempt sent the full diff; the retry elided the big file.
    assert len(calls) == 2
    assert review.ELISION_MARKER not in calls[0]
    assert "case line 99" in calls[0]
    assert review.ELISION_MARKER in calls[1]
    assert len(calls[1]) < len(calls[0])
    assert "+KEEP_ME" in calls[1]
    assert truncation is not None
    assert truncation.elided_files == 1


def test_request_review_reraises_unrelated_bad_request(monkeypatch) -> None:
    """A 400 that is not a token overflow still fails the review loudly."""
    import pytest

    from lean_pool import review

    class _FakeCompletions:
        """Always rejects the request with a non-overflow 400."""

        def create(self, **kwargs):
            """Raise a schema-style 400 regardless of input."""
            raise openai.BadRequestError("Invalid value for response_format.")

    class _FakeClient:
        """Stub OpenAI client exposing chat.completions.create."""

        def __init__(self) -> None:
            """Wire up the fake chat.completions endpoint."""
            self.chat = types.SimpleNamespace(completions=_FakeCompletions())

    monkeypatch.setattr(review, "OpenAI", lambda timeout: _FakeClient())

    with pytest.raises(openai.BadRequestError):
        review.request_review(
            model="gpt-5.5",
            rules="rules",
            diff="diff --git a/x b/x\n",
            system_prompt="s",
        )


def test_render_comment_notes_truncation() -> None:
    """A truncated review states the elision clearly, keeping the contract."""
    from lean_pool.review import LLM_REVIEW_MARKER, DiffTruncation, render_comment

    body = render_comment(
        {"summary": "Reviewed a reduced diff.", "verdict": "needs_discussion"},
        model="gpt-5.5",
        usage=None,
        tier="flex",
        reviewed_head_sha="abc123",
        truncation=DiffTruncation(
            total_files=317,
            elided_files=250,
            original_chars=3_112_190,
            final_chars=1_500_000,
        ),
    )

    # The sticky marker and head-SHA keying are untouched by the notice.
    assert body.startswith(LLM_REVIEW_MARKER)
    assert "**Reviewed head:** `abc123`" in body
    assert "Partial review" in body
    assert "250" in body and "317" in body
    assert "3,112,190" in body
