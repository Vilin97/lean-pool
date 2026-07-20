"""Tests for LLM review comment rendering."""

from __future__ import annotations

import sys
import types

openai_stub = types.ModuleType("openai")
openai_stub.APIStatusError = Exception
openai_stub.OpenAI = object
openai_stub.RateLimitError = Exception
sys.modules.setdefault("openai", openai_stub)


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
