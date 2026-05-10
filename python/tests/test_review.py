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
