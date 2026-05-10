"""LLM-driven pull request review for Lean Pool.

Reads the rules from ``.github/REVIEW_RULES.md``, fetches the PR diff via the
GitHub CLI, asks the configured OpenAI model to evaluate the contribution,
and posts a single PR comment with a one-paragraph summary, a structured
assessment table (fit / level / branch / mode / code-quality / etc.), a
verdict, and any specific findings.

The reviewer prefers OpenAI's ``flex`` tier (cheaper, slower, occasionally
unavailable). When flex returns 429 Resource Unavailable, the request is
retried with ``service_tier="auto"`` (standard pricing). The rendered
comment shows which tier was actually used and prices the request at that
tier's rate.

Per-token prices live in the ``PRICING_PER_M`` table below — the OpenAI
API does not return cost in its responses, so we maintain a small lookup
keyed on ``(model, tier)``. Update it when bumping ``DEFAULT_MODEL`` or
when OpenAI changes pricing.

Environment variables:
    OPENAI_API_KEY: OpenAI credentials (required).
    PR_NUMBER:      Pull request number to review (required).
    GH_TOKEN:       Token for the GitHub CLI (required in CI).
    REVIEW_MODEL:   Model name; defaults to :data:`DEFAULT_MODEL`.

Run:
    uv run python -m lean_pool.review
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from textwrap import dedent
from typing import Any

from openai import APIStatusError, OpenAI, RateLimitError

REPO_ROOT = Path(__file__).resolve().parents[2]
RULES_PATH = REPO_ROOT / ".github" / "REVIEW_RULES.md"
DEFAULT_MODEL = "gpt-5.5"
# Flex tier requests can take longer than the default 10-minute timeout.
REQUEST_TIMEOUT_SECONDS = 6000.0

# USD per 1M tokens, keyed by (model, tier) -> (input_per_M, output_per_M).
# Source: https://developers.openai.com/api/docs/pricing — update when
# bumping DEFAULT_MODEL or when OpenAI changes pricing.
PRICING_PER_M: dict[str, dict[str, tuple[float, float]]] = {
    "gpt-5.5": {
        "flex": (2.50, 15.00),
        "standard": (5.00, 30.00),
    },
    "gpt-5.4-mini": {
        "flex": (0.375, 2.25),
        "standard": (0.75, 4.50),
    },
}

VERDICT_ICON = {
    "approve": "✅",
    "request_changes": "🛑",
    "needs_discussion": "🤔",
}
FIT_ICON = {
    "good_fit": "✅",
    "borderline": "🟡",
    "not_a_fit": "🛑",
}

SYSTEM_PROMPT = dedent(
    """\
    You are a senior mathematician and Lean engineer reviewing pull
    requests to Lean Pool, a curated repository of formal-mathematics
    projects. Your job is to tell the maintainer, in one paragraph plus
    a short structured assessment, whether this PR is worth merging.

    Write to a colleague: direct, no encouragement, no editorializing,
    no convention justifications, no "great work."

    Mechanical style issues (presence of sorry, headers, naming, simp
    discipline, line length, axiom audit, etc.) are caught by linters
    elsewhere in CI. Do NOT flag those, even if you notice them.

    Always respond with a single JSON object matching the schema in the
    rules document. The `assessment` block is the core deliverable —
    that is what tells the maintainer whether to bother reading the PR.
    `findings` is for actual specific suggestions; an empty list is
    fine and often correct.
    """
)


def run_gh(*args: str, stdin: str | None = None) -> str:
    """Run ``gh`` with the given arguments and return stdout.

    Args:
        *args: Arguments to pass after ``gh``.
        stdin: Optional string piped to the subprocess on stdin.

    Returns:
        The captured stdout, decoded as text.

    Raises:
        subprocess.CalledProcessError: If gh exits non-zero.
    """
    result = subprocess.run(
        ["gh", *args],
        check=True,
        capture_output=True,
        text=True,
        input=stdin,
    )
    return result.stdout


def fetch_diff(pr_number: str) -> str:
    """Return the full unified diff for ``pr_number``, untruncated."""
    return run_gh("pr", "diff", pr_number)


def request_review(model: str, rules: str, diff: str) -> tuple[dict, Any, str]:
    """Ask the model to apply ``rules`` to ``diff``.

    Tries the ``flex`` service tier first; if OpenAI returns 429 Resource
    Unavailable, retries with ``service_tier="auto"`` (standard tier).

    Returns:
        ``(payload, usage, tier)`` where ``payload`` is the parsed JSON
        review, ``usage`` is the OpenAI ``CompletionUsage`` object (or
        ``None``), and ``tier`` is ``"flex"`` or ``"standard"``.
    """
    client = OpenAI(timeout=REQUEST_TIMEOUT_SECONDS)
    user_content = f"## Review rules\n\n{rules}\n\n## PR diff\n\n```diff\n{diff}\n```"
    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": user_content},
    ]

    try:
        response = client.chat.completions.create(
            model=model,
            messages=messages,
            response_format={"type": "json_object"},
            service_tier="flex",
        )
        tier = "flex"
    except (RateLimitError, APIStatusError) as e:
        # Flex either out of capacity (429 RateLimitError) or unsupported
        # for this model (e.g. 500 InternalServerError on gpt-5.5).
        # Either way, fall back to standard.
        if isinstance(e, RateLimitError) or (500 <= e.status_code < 600):
            response = client.chat.completions.create(
                model=model,
                messages=messages,
                response_format={"type": "json_object"},
                service_tier="auto",
            )
            tier = "standard"
        else:
            raise

    content = response.choices[0].message.content or "{}"
    return json.loads(content), response.usage, tier


def render_usage(usage: Any, model: str, tier: str) -> str:
    """Render a one-line token / tier / cost footer.

    Returns an empty string if ``usage`` is unavailable. Cost is computed
    from :data:`PRICING_PER_M` and suppressed when the model/tier pair is
    not listed there.
    """
    if usage is None:
        return ""
    in_tok = getattr(usage, "prompt_tokens", 0) or 0
    out_tok = getattr(usage, "completion_tokens", 0) or 0

    parts = [f"**Tokens:** {in_tok:,} in / {out_tok:,} out", f"**Tier:** `{tier}`"]
    rates = PRICING_PER_M.get(model, {}).get(tier)
    if rates is not None:
        in_price, out_price = rates
        cost = (in_tok * in_price + out_tok * out_price) / 1_000_000
        parts.append(f"**Cost:** ${cost:.4f}")
    else:
        parts.append(f"_(no pricing recorded for `{model}` at `{tier}` tier)_")
    return " · ".join(parts)


def render_assessment(payload: dict) -> str:
    """Render the structured assessment block as a Markdown table."""
    a = payload.get("assessment") or {}
    if not a:
        return ""

    fit = a.get("fit", "")
    fit_cell = f"{FIT_ICON.get(fit, '•')} `{fit}`" if fit else "?"
    quality = a.get("code_quality")
    quality_cell = f"{quality} / 5" if quality is not None else "?"

    rows = [
        ("Fit", fit_cell),
        ("Level", f"`{a.get('level', '?')}`"),
        ("Branch", a.get("branch", "?")),
        ("Mode", f"`{a.get('mode', '?')}`"),
        ("Obscure problem", "yes" if a.get("obscure_problem") else "no"),
        ("Code quality", quality_cell),
    ]
    table = "| Aspect | Value |\n|---|---|\n"
    for k, v in rows:
        table += f"| {k} | {v} |\n"

    sig = (a.get("significance_one_sentence") or "").strip()
    if sig:
        table += f"\n_{sig}_"
    return table


def render_comment(
    payload: dict,
    model: str,
    usage: Any,
    tier: str,
) -> str:
    """Render the model's payload as a Markdown PR comment body."""
    summary = (payload.get("summary") or "").strip()
    verdict = (payload.get("verdict") or "").strip()
    findings = payload.get("findings") or []

    lines = [f"## 🤖 LLM review (`{model}`)", ""]

    if verdict:
        icon = VERDICT_ICON.get(verdict, "•")
        lines.extend([f"**Verdict:** {icon} `{verdict}`", ""])

    if summary:
        lines.extend([summary, ""])

    assessment = render_assessment(payload)
    if assessment:
        lines.extend([assessment, ""])

    if findings:
        lines.append(f"### Findings ({len(findings)})")
        lines.append("")
        for f in findings:
            path = f.get("file") or ""
            line_no = f.get("line", 0) or 0
            if path and line_no:
                ref = f"`{path}:{line_no}`"
            elif path:
                ref = f"`{path}`"
            else:
                ref = "_PR-wide_"
            rule = f.get("rule", "")
            body = (f.get("comment") or "").strip()
            lines.append(f"- **{rule}** — {ref}")
            lines.append(f"  {body}")
        lines.append("")

    lines.append("---")
    usage_line = render_usage(usage, model, tier)
    if usage_line:
        lines.append(usage_line)
    lines.append(
        "_Automated review against "
        "[`.github/REVIEW_RULES.md`](../blob/main/.github/REVIEW_RULES.md). "
        "Disagree? Reply on the PR; rules can be updated in a PR of their own._"
    )
    return "\n".join(lines)


def post_comment(pr_number: str, body: str) -> None:
    """Post ``body`` as a top-level PR comment."""
    run_gh("pr", "comment", pr_number, "--body-file", "-", stdin=body)


def main() -> int:
    """Entry point: orchestrate fetch, review, and post."""
    pr_number = os.environ.get("PR_NUMBER")
    if not pr_number:
        print("PR_NUMBER not set", file=sys.stderr)
        return 2
    if not os.environ.get("OPENAI_API_KEY"):
        print("OPENAI_API_KEY not set", file=sys.stderr)
        return 2

    model = os.environ.get("REVIEW_MODEL", DEFAULT_MODEL)
    rules = RULES_PATH.read_text(encoding="utf-8")
    diff = fetch_diff(pr_number)

    if not diff.strip():
        print("Empty diff; nothing to review.", file=sys.stderr)
        return 0

    payload, usage, tier = request_review(model=model, rules=rules, diff=diff)
    comment = render_comment(payload, model=model, usage=usage, tier=tier)
    post_comment(pr_number, comment)
    return 0


if __name__ == "__main__":
    sys.exit(main())
