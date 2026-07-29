"""Tests for LLM review comment rendering and oversized-diff truncation."""

from __future__ import annotations

import json
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
                "proves_the_claim": "proves_it",
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


def test_classify_pr_tooling_lean_is_not_a_project() -> None:
    """A `.lean` file outside the content trees is infra, not a project.

    `scripts/exposition/Extract.lean` clears the workflow's "touches
    Lean?" filter, so PRs #279, #282, and #283 reached the project rules
    and were graded for mathematical fit — inconsistently, since the
    first two came back `not_a_fit` and the third `good_fit`/`approve`.
    All three merged.
    """
    from lean_pool.review import classify_pr

    files = [
        ("scripts/exposition/Extract.lean", "modified"),
        ("python/lean_pool/exposition/generate.py", "modified"),
    ]
    assert classify_pr(files) == "infra"


def test_classify_pr_without_any_lean_is_infra() -> None:
    """A diff with no Lean at all has no contribution to judge."""
    from lean_pool.review import classify_pr

    assert classify_pr([("README.md", "modified")]) == "infra"


def test_classify_pr_project_root_module_still_counts_as_content() -> None:
    """A project's own root module is content even at depth two."""
    from lean_pool.review import classify_pr, touches_reviewable_content

    assert touches_reviewable_content([("Challenge/TwinPrimes.lean", "added")])
    assert touches_reviewable_content([("Solution/Widget.lean", "added")])
    assert touches_reviewable_content([("LeanPool/Foo/A.lean", "added")])
    # The generated root index alone is not somebody's contribution.
    assert not touches_reviewable_content([("LeanPool.lean", "modified")])
    assert classify_pr([("LeanPool/NewProj/A.lean", "added")]) == "project"


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

    result = review.request_review(
        model="gpt-5.5", rules="R" * 200, diff=diff, system_prompt="Review."
    )

    assert result.payload == {"summary": "ok", "verdict": "approve", "findings": []}
    assert result.usage is None
    assert result.tier == "flex"
    # The stubbed response reports no model, so the requested one stands.
    assert result.model == "gpt-5.5"
    # First attempt sent the full diff; the retry elided the big file.
    assert len(calls) == 2
    assert review.ELISION_MARKER not in calls[0]
    assert "case line 99" in calls[0]
    assert review.ELISION_MARKER in calls[1]
    assert len(calls[1]) < len(calls[0])
    assert "+KEEP_ME" in calls[1]
    assert result.truncation is not None
    assert result.truncation.elided_files == 1


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


def test_request_review_sends_effort_and_reports_resolved_model(monkeypatch) -> None:
    """The effort knob reaches the API; the serving snapshot is reported."""
    from lean_pool import review

    seen: list[dict] = []

    class _FakeCompletions:
        """Answers like the OpenAI client, resolving the model alias."""

        def create(self, **kwargs):
            """Record kwargs and answer with a dated snapshot name."""
            seen.append(kwargs)
            message = types.SimpleNamespace(content='{"summary": "ok"}')
            return types.SimpleNamespace(
                choices=[types.SimpleNamespace(message=message)],
                usage=None,
                model="gpt-5.6-sol-2026-06-17",
            )

    class _FakeClient:
        """Stub OpenAI client exposing chat.completions.create."""

        def __init__(self) -> None:
            """Wire up the fake chat.completions endpoint."""
            self.chat = types.SimpleNamespace(completions=_FakeCompletions())

    monkeypatch.setattr(review, "OpenAI", lambda timeout: _FakeClient())

    result = review.request_review(
        model="gpt-5.6",
        rules="rules",
        diff="diff --git a/x b/x\n",
        system_prompt="s",
        effort="xhigh",
    )

    assert seen[0]["reasoning_effort"] == "xhigh"
    assert result.model == "gpt-5.6-sol-2026-06-17"
    assert result.effort == "xhigh"


def test_request_review_drops_rejected_effort(monkeypatch) -> None:
    """An unsupported effort value retries at the model's default effort."""
    from lean_pool import review

    seen: list[dict] = []

    class _FakeCompletions:
        """Rejects the effort parameter once, then answers."""

        def create(self, **kwargs):
            """Refuse reasoning_effort; accept the parameterless retry."""
            seen.append(kwargs)
            if "reasoning_effort" in kwargs:
                raise openai.BadRequestError(
                    "Unsupported value: 'xhigh' is not one of the supported "
                    "values for parameter 'reasoning_effort'."
                )
            message = types.SimpleNamespace(content='{"summary": "ok"}')
            return types.SimpleNamespace(
                choices=[types.SimpleNamespace(message=message)], usage=None
            )

    class _FakeClient:
        """Stub OpenAI client exposing chat.completions.create."""

        def __init__(self) -> None:
            """Wire up the fake chat.completions endpoint."""
            self.chat = types.SimpleNamespace(completions=_FakeCompletions())

    monkeypatch.setattr(review, "OpenAI", lambda timeout: _FakeClient())

    result = review.request_review(
        model="gpt-5.6",
        rules="rules",
        diff="diff --git a/x b/x\n",
        system_prompt="s",
        effort="xhigh",
    )

    assert len(seen) == 2
    assert "reasoning_effort" not in seen[1]
    assert result.payload == {"summary": "ok"}
    assert result.effort is None


def test_pricing_rates_prefix_match_and_long_context() -> None:
    """Snapshot names price by family prefix; big inputs hit the long rate."""
    from lean_pool import review

    short = review.pricing_rates("gpt-5.6-sol-2026-06-17", "flex", 10_000)
    long = review.pricing_rates(
        "gpt-5.6-sol-2026-06-17", "flex", review.LONG_CONTEXT_INPUT_TOKENS
    )
    assert short is not None and long is not None
    assert long[0] > short[0] and long[1] > short[1]
    # The bare alias prices like the Sol model it routes to.
    assert review.pricing_rates("gpt-5.6", "standard", 10_000) == (
        review.pricing_rates("gpt-5.6-sol", "standard", 10_000)
    )
    assert review.pricing_rates("some-unknown-model", "flex", 10_000) is None
    assert review.pricing_rates("gpt-5.6-sol", "batch", 10_000) is None


def test_render_usage_shows_effort_and_long_context_rate() -> None:
    """The footer names the effort and flags long-context pricing."""
    from lean_pool import review

    usage = types.SimpleNamespace(prompt_tokens=400_000, completion_tokens=20_000)
    line = review.render_usage(usage, "gpt-5.6-sol-2026-06-17", "flex", "xhigh")

    assert "**Effort:** `xhigh`" in line
    # 400k in at $5/M plus 20k out at $22.50/M — the long-context rate.
    assert "**Cost:** $2.4500 (long-context rate)" in line

    small = types.SimpleNamespace(prompt_tokens=100_000, completion_tokens=10_000)
    short_line = review.render_usage(small, "gpt-5.6-sol", "flex")
    assert "long-context" not in short_line
    assert "**Effort:**" not in short_line
    # 100k in at $2.50/M plus 10k out at $15/M.
    assert "**Cost:** $0.4000" in short_line


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


def test_every_review_mode_asks_for_literal_unicode(monkeypatch) -> None:
    """The notation rule reaches the model whichever mode is reviewing.

    PR #289's challenge review came back with `over ^R09` where `over ℚ`
    belonged, so a Lean review that cannot render its own notation is a
    regression worth a test.
    """
    from lean_pool import review

    captured: list[dict] = []

    class _Message:
        content = '{"summary": "s", "verdict": "approve", "findings": []}'

    class _Choice:
        message = _Message()

    class _Response:
        choices = [_Choice()]
        usage = None

    class _Completions:
        def create(self, **kwargs):
            captured.append(kwargs)
            return _Response()

    class _Chat:
        completions = _Completions()

    class _Client:
        chat = _Chat()

        def __init__(self, **kwargs):
            pass

    monkeypatch.setattr(review, "OpenAI", _Client)

    for _rules_path, system_prompt in review.REVIEW_MODES.values():
        captured.clear()
        review.request_review(
            model="gpt-5.5",
            rules="rules",
            diff="diff --git a/A b/A",
            system_prompt=system_prompt,
        )
        sent = captured[0]["messages"][0]["content"]
        assert "copy the characters exactly" in sent
        assert "ℚ" in sent


def test_every_review_mode_holds_the_trust_boundary(monkeypatch) -> None:
    """Contributor text is evidence in every mode, never instruction.

    The diff and the PR description are written by the contributor, and
    the pool accepts AI-generated projects by design, so a review kind
    that skipped this rule would take orders from the thing it reviews.
    """
    from lean_pool import review

    captured: list[dict] = []

    class _Message:
        content = '{"summary": "s", "verdict": "approve", "findings": []}'

    class _Choice:
        message = _Message()

    class _Response:
        choices = [_Choice()]
        usage = None

    class _Completions:
        def create(self, **kwargs):
            captured.append(kwargs)
            return _Response()

    class _Chat:
        completions = _Completions()

    class _Client:
        chat = _Chat()

        def __init__(self, **kwargs):
            pass

    monkeypatch.setattr(review, "OpenAI", _Client)

    for _rules_path, system_prompt in review.REVIEW_MODES.values():
        captured.clear()
        review.request_review(
            model="gpt-5.5",
            rules="rules",
            diff="diff --git a/A b/A",
            system_prompt=system_prompt,
        )
        sent = captured[0]["messages"][0]["content"]
        assert "Trust boundary" in sent
        assert "prompt-injection" in sent


def test_pr_context_reaches_the_model_as_a_claim_to_verify() -> None:
    """The description is shown, and framed as something to check."""
    from lean_pool.review import PullRequestContext, build_user_content

    content = build_user_content(
        rules="RULES",
        diff="diff --git a/A b/A",
        truncation=None,
        context=PullRequestContext(
            title="Import the Widget formalization",
            body="Formalizes Theorem 3 of arXiv:2401.00001.",
        ),
    )

    assert "Import the Widget formalization" in content
    assert "arXiv:2401.00001" in content
    # The source anchor REVIEW_RULES.md allows in the PR description is
    # only usable if it is presented as a claim, not as a finding.
    assert "claim to verify against the diff" in content
    # Rules still lead; the diff still arrives.
    assert content.index("RULES") < content.index("arXiv:2401.00001")
    assert "## PR diff" in content


def test_build_user_content_without_context_is_unchanged() -> None:
    """A review with no PR metadata still sends rules and diff alone."""
    from lean_pool.review import build_user_content

    content = build_user_content("RULES", "diff --git a/A b/A", None)

    assert "What the PR says about itself" not in content
    assert "## Review rules" in content


def test_render_pr_context_truncates_a_huge_description() -> None:
    """A release-note-sized body is capped without losing the opening."""
    from lean_pool.review import (
        MAX_PR_BODY_CHARS,
        PullRequestContext,
        render_pr_context,
    )

    rendered = render_pr_context(
        PullRequestContext(title="T", body="OPENING CLAIM. " + "x" * 40_000)
    )

    assert rendered is not None
    assert "OPENING CLAIM." in rendered
    assert "description truncated" in rendered
    assert len(rendered) < MAX_PR_BODY_CHARS + 1_000


def test_fetch_pr_context_round_trips_markdown(monkeypatch) -> None:
    """Newlines and backslashes in a description survive the fetch."""
    from lean_pool import review

    body = "Line one\n\n```\nlatex \\alpha\ttab\n```\nEnd."
    monkeypatch.setattr(
        review,
        "run_gh",
        lambda *a, **k: json.dumps({"title": "T", "body": body}),
    )

    context = review.fetch_pr_context("1", "o/r")

    assert context.title == "T"
    assert context.body == body


def test_fetch_pr_context_tolerates_a_null_description(monkeypatch) -> None:
    """A PR opened with no description yields an empty body, not None."""
    from lean_pool import review

    monkeypatch.setattr(
        review, "run_gh", lambda *a, **k: json.dumps({"title": "T", "body": ""})
    )

    assert review.fetch_pr_context("1", "o/r").body == ""


def test_project_assessment_leads_with_the_ungated_checks() -> None:
    """Claim, source, and prior art outrank the fields that echo the verdict."""
    from lean_pool.review import render_project_assessment

    table = render_project_assessment(
        {
            "assessment": {
                "fit": "borderline",
                "level": "research",
                "branch": "graph theory",
                "mode": "theory_building",
                "proves_the_claim": "weaker_than_claimed",
                "claim_note": "Proved for n = 14 only, not all n.",
                "assumed_inputs": "Szöllősi–Östergård classification, disclosed",
                "already_formalized": "SimpleGraph.nonempty_hom_of_forall_finite",
                "source_match": "matches",
                "code_quality": 4,
                "significance_one_sentence": "A conditional fourteen-point case.",
            }
        }
    )

    assert "Proves the claim" in table
    assert "weaker_than_claimed" in table
    assert "Proved for n = 14 only" in table
    assert "Already formalized" in table
    assert "Assumed, not proved" in table
    assert "Szöllősi–Östergård" in table
    # The ungated checks lead; `fit` and `level` echo the verdict that is
    # already rendered above the table, so they come last.
    assert table.index("Proves the claim") < table.index("| Fit |")
    assert table.index("Already formalized") < table.index("| Fit |")
    assert table.index("Assumed, not proved") < table.index("| Fit |")
    assert table.index("| Fit |") < table.index("| Level |")
    # The field that was `no` in all 147 past reviews is gone.
    assert "Obscure problem" not in table


def test_prior_art_hedge_is_not_rendered_as_a_duplicate() -> None:
    """A prose non-answer must not wear the stop icon a real hit earns.

    The first production run under these rules answered
    `already_formalized` with "unverifiable from the supplied diff" on a
    PR it approved; rendering that with 🛑 said the opposite.
    """
    from lean_pool.review import render_project_assessment

    hedged = render_project_assessment(
        {"assessment": {"already_formalized": "unverifiable from the supplied diff"}}
    )
    hit = render_project_assessment(
        {"assessment": {"already_formalized": "SimpleGraph.nonempty_hom"}}
    )

    assert "🛑" not in hedged
    assert "🟡 unverifiable from the supplied diff" in hedged
    assert "🛑 `SimpleGraph.nonempty_hom`" in hit


def test_project_assessment_omits_empty_optional_rows() -> None:
    """A clean project shows no prior-art or assumption row at all."""
    from lean_pool.review import render_project_assessment

    table = render_project_assessment(
        {
            "assessment": {
                "fit": "good_fit",
                "level": "research",
                "proves_the_claim": "proves_it",
                "already_formalized": "",
                "assumed_inputs": "",
                "code_quality": 4,
            }
        }
    )

    assert "Already formalized" not in table
    assert "Assumed, not proved" not in table
    assert "✅ `proves_it`" in table


def test_request_changes_comment_says_it_is_not_a_close() -> None:
    """39% of past `request_changes` verdicts were merged after a human look."""
    from lean_pool.review import render_comment

    body = render_comment(
        {"summary": "s", "verdict": "request_changes", "findings": []},
        model="gpt-5.6-sol",
        usage=None,
        tier="flex",
        reviewed_head_sha="abc123",
    )
    approved = render_comment(
        {"summary": "s", "verdict": "approve", "findings": []},
        model="gpt-5.6-sol",
        usage=None,
        tier="flex",
        reviewed_head_sha="abc123",
    )

    assert "an ask, not a close" in body
    assert "an ask, not a close" not in approved


def test_infra_skip_comment_is_sticky_and_explains_itself() -> None:
    """A tooling PR gets a note, not a mathematical-fit verdict."""
    from lean_pool.review import LLM_REVIEW_MARKER, render_infra_skip_comment

    body = render_infra_skip_comment("abc123")

    assert body.startswith(LLM_REVIEW_MARKER)
    assert "**Reviewed head:** `abc123`" in body
    assert "no project, challenge, or solution here to judge" in body
    # No verdict, because there is no contribution to have a verdict about.
    assert "**Verdict:**" not in body


def test_render_pr_context_handles_an_empty_description() -> None:
    """An author who wrote no description is reported as such, not blank."""
    from lean_pool.review import PullRequestContext, render_pr_context

    rendered = render_pr_context(PullRequestContext(title="T", body="   "))

    assert rendered is not None
    assert "no description provided" in rendered
