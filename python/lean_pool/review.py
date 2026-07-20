"""LLM-driven pull request review for Lean Pool.

Detects whether the PR adds a new project or refactors projects already in
the pool — the same added-vs-modified split ``/profile`` uses — and reviews
it under the matching rules. New-project PRs are judged on fit and
significance (``.github/REVIEW_RULES.md``); refactor PRs are judged on tech
debt and maintainability (``.github/REFACTOR_REVIEW_RULES.md``). Either way
it fetches the PR diff via the GitHub CLI, asks the configured OpenAI model
to evaluate the contribution, and posts or updates a sticky PR comment with
the reviewed head SHA, a one-paragraph summary, a structured assessment
table, a verdict, and any specific findings.

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
    GITHUB_REPOSITORY:
                    Repository in owner/name form (optional outside CI).
    REVIEW_HEAD_SHA:
                    Head SHA being reviewed (optional; fetched if absent).
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
PROJECT_RULES_PATH = REPO_ROOT / ".github" / "REVIEW_RULES.md"
REFACTOR_RULES_PATH = REPO_ROOT / ".github" / "REFACTOR_REVIEW_RULES.md"
DEFAULT_MODEL = "gpt-5.5"
# Flex tier requests can take longer than the default 10-minute timeout.
REQUEST_TIMEOUT_SECONDS = 6000.0
LLM_REVIEW_MARKER = "<!-- lean-pool-llm-review -->"

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
# Refactor-assessment icons. Both maintainability and brittleness read
# "green = better after the refactor, red = worse."
DEBT_ICON = {True: "🛑", False: "✅"}
MAINTAINABILITY_ICON = {
    "improved": "✅",
    "unchanged": "➖",
    "regressed": "🛑",
}
BRITTLENESS_ICON = {
    "more_robust": "✅",
    "unchanged": "➖",
    "more_brittle": "🛑",
}
RISK_ICON = {"low": "✅", "medium": "🟡", "high": "🛑"}

SYSTEM_PROMPT_PROJECT = dedent(
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

SYSTEM_PROMPT_REFACTOR = dedent(
    """\
    You are a senior Lean engineer reviewing a refactor pull request to
    Lean Pool. This PR modifies projects that are ALREADY in the pool —
    proof golf, tactic rewrites, module reorganizations, API renames. It
    does not add a new project, so mathematical fit and significance are
    NOT in question and you must not assess them.

    The maintainer's question is narrower: does this refactor leave the
    code better or worse to maintain? Focus on tech debt — proofs made
    more brittle (e.g. a structured proof collapsed into an opaque
    `simp_all` / `aesop` / `grind` that will break on the next Mathlib
    bump and is hard to debug), lost proof structure, compile-cost
    regressions, reusability lost, dead leftovers — and on any other
    issue a maintainer would regret later.

    Write to a colleague: direct, no encouragement, no "nice cleanup."
    For a refactor, `simp` vs `simp only` and heavy-automation brittleness
    ARE in scope. Do NOT flag things other CI already covers: sorry /
    axioms, headers, naming, line length, maxHeartbeats, or whether any
    statement changed (the /profile comment reports that separately).

    Always respond with a single JSON object matching the schema in the
    rules document. The `assessment` block is the core deliverable.
    `findings` is for specific, actionable concerns; an empty list is
    fine and correct for a clean mechanical golf.
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


def resolve_repo_full_name() -> str:
    """Return the current GitHub repository as ``owner/name``."""
    if repo := os.environ.get("GITHUB_REPOSITORY"):
        return repo
    return run_gh("repo", "view", "--json", "nameWithOwner", "--jq", ".nameWithOwner")


def fetch_diff(pr_number: str, repo_full_name: str) -> str:
    """Return the full unified diff for ``pr_number``, untruncated.

    GitHub's pull-request diff endpoint returns HTTP 406 once a diff
    exceeds 20,000 lines, which makes ``gh pr diff`` fail outright on
    very large PRs. Fall back to assembling the diff from the per-file
    ``pulls/{n}/files`` endpoint, which paginates and is not subject to
    the same cap.
    """
    try:
        return run_gh("pr", "diff", pr_number, "--repo", repo_full_name)
    except subprocess.CalledProcessError as exc:
        stderr = exc.stderr or ""
        if "diff exceeded" not in stderr and "too_large" not in stderr:
            raise
        return _assemble_diff_from_files(pr_number, repo_full_name)


def _assemble_diff_from_files(pr_number: str, repo_full_name: str) -> str:
    """Reconstruct a unified diff from per-file PR patches.

    Streams ``pulls/{n}/files`` through ``gh api --paginate --jq '.[]'``
    so each file's metadata arrives as one JSON object per line, then
    wraps each ``patch`` field with the headers that ``gh pr diff``
    would emit (``diff --git``, ``---``, ``+++``). Files without a
    ``patch`` field (binary, renames with no content change, etc.) are
    emitted with a placeholder so the LLM still sees that they changed.
    """
    raw = run_gh(
        "api",
        f"repos/{repo_full_name}/pulls/{pr_number}/files",
        "--paginate",
        "--jq",
        ".[]",
    )
    chunks: list[str] = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        entry = json.loads(line)
        filename = entry["filename"]
        previous = entry.get("previous_filename") or filename
        patch = entry.get("patch")
        chunks.append(f"diff --git a/{previous} b/{filename}")
        if patch is None:
            chunks.append("(binary or empty patch — content omitted)")
            continue
        chunks.append(f"--- a/{previous}")
        chunks.append(f"+++ b/{filename}")
        chunks.append(patch)
    return "\n".join(chunks) + "\n"


def fetch_head_sha(pr_number: str, repo_full_name: str) -> str:
    """Return the current head SHA for ``pr_number``."""
    return run_gh(
        "api", f"repos/{repo_full_name}/pulls/{pr_number}", "--jq", ".head.sha"
    )


def fetch_pr_files(pr_number: str, repo_full_name: str) -> list[tuple[str, str]]:
    """Return ``(filename, status)`` for every file in ``pr_number``.

    ``status`` is GitHub's file status: ``added``, ``modified``,
    ``removed``, ``renamed``, ``changed``, or ``copied``. The endpoint
    paginates, so this is safe on PRs that touch thousands of files.
    """
    raw = run_gh(
        "api",
        f"repos/{repo_full_name}/pulls/{pr_number}/files",
        "--paginate",
        "--jq",
        ".[] | [.filename, .status] | @tsv",
    )
    files: list[tuple[str, str]] = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        name, _, status = line.partition("\t")
        files.append((name, status))
    return files


def project_of(path: str) -> str | None:
    """Return the pooled project a Lean file belongs to, or ``None``.

    Project content lives at ``LeanPool/<Project>/...``; the auto-generated
    root ``LeanPool.lean`` and non-project files return ``None``.
    """
    parts = path.split("/")
    if len(parts) > 2 and parts[0] == "LeanPool":
        return parts[1]
    return None


def classify_pr(files: list[tuple[str, str]]) -> str:
    """Classify a PR as ``"refactor"`` or ``"project"``.

    Mirrors ``/profile``'s added-vs-modified split lifted to the PR level: a
    PR that adds a *new project* (a project directory that appears only
    through added ``.lean`` files) is a ``"project"`` PR and gets the full
    fit/significance review. A PR that only changes files in projects
    already in the pool — the pure-golf / reorganization case — is a
    ``"refactor"`` and gets the tech-debt review. When no project files are
    touched at all, default to ``"project"`` (the conservative review).
    """
    added_projects: set[str] = set()
    existing_projects: set[str] = set()
    for name, status in files:
        if not name.endswith(".lean"):
            continue
        project = project_of(name)
        if project is None:
            continue
        if status == "added":
            added_projects.add(project)
        else:  # modified / removed / renamed / changed / copied
            existing_projects.add(project)
    new_projects = added_projects - existing_projects
    if not new_projects and existing_projects:
        return "refactor"
    return "project"


def request_review(
    model: str, rules: str, diff: str, system_prompt: str
) -> tuple[dict, Any, str]:
    """Ask the model to apply ``rules`` to ``diff`` under ``system_prompt``.

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
        {"role": "system", "content": system_prompt},
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


def render_project_assessment(payload: dict) -> str:
    """Render a new-project assessment block as a Markdown table."""
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


def render_refactor_assessment(payload: dict) -> str:
    """Render a refactor assessment block as a Markdown table."""
    a = payload.get("assessment") or {}
    if not a:
        return ""

    debt = a.get("introduces_tech_debt")
    debt_cell = (
        f"{DEBT_ICON.get(bool(debt), '•')} {'yes' if debt else 'no'}"
        if debt is not None
        else "?"
    )
    maint = a.get("maintainability", "")
    maint_cell = f"{MAINTAINABILITY_ICON.get(maint, '•')} `{maint}`" if maint else "?"
    brit = a.get("brittleness", "")
    brit_cell = f"{BRITTLENESS_ICON.get(brit, '•')} `{brit}`" if brit else "?"
    risk = a.get("risk", "")
    risk_cell = f"{RISK_ICON.get(risk, '•')} `{risk}`" if risk else "?"

    rows = [
        ("Scope", a.get("scope", "?")),
        ("Introduces tech debt", debt_cell),
        ("Maintainability", maint_cell),
        ("Brittleness", brit_cell),
        ("Risk", risk_cell),
    ]
    table = "| Aspect | Value |\n|---|---|\n"
    for k, v in rows:
        table += f"| {k} | {v} |\n"

    sentence = (a.get("assessment_one_sentence") or "").strip()
    if sentence:
        table += f"\n_{sentence}_"
    return table


def render_comment(
    payload: dict,
    model: str,
    usage: Any,
    tier: str,
    reviewed_head_sha: str,
    kind: str = "project",
) -> str:
    """Render the model's payload as a Markdown PR comment body.

    ``kind`` is ``"project"`` (fit/significance review) or ``"refactor"``
    (tech-debt review); it selects the header, the assessment table, and
    the rules doc linked in the footer.
    """
    summary = (payload.get("summary") or "").strip()
    verdict = (payload.get("verdict") or "").strip()
    findings = payload.get("findings") or []

    heading = (
        f"## 🤖 LLM review — refactor (`{model}`)"
        if kind == "refactor"
        else f"## 🤖 LLM review (`{model}`)"
    )
    lines = [LLM_REVIEW_MARKER, heading, ""]

    if reviewed_head_sha:
        lines.extend([f"**Reviewed head:** `{reviewed_head_sha}`", ""])

    if verdict:
        icon = VERDICT_ICON.get(verdict, "•")
        lines.extend([f"**Verdict:** {icon} `{verdict}`", ""])

    if summary:
        lines.extend([summary, ""])

    assessment = (
        render_refactor_assessment(payload)
        if kind == "refactor"
        else render_project_assessment(payload)
    )
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
    rules_doc = "REFACTOR_REVIEW_RULES.md" if kind == "refactor" else "REVIEW_RULES.md"
    lines.append(
        "_Automated review against "
        f"[`.github/{rules_doc}`](../blob/main/.github/{rules_doc}). "
        "Disagree? Reply on the PR; rules can be updated in a PR of their own._"
    )
    return "\n".join(lines)


def post_comment(pr_number: str, body: str, repo_full_name: str) -> None:
    """Create or update the sticky LLM review PR comment."""
    comments_json = run_gh(
        "api",
        f"repos/{repo_full_name}/issues/{pr_number}/comments?per_page=100",
    )
    comments = json.loads(comments_json)
    existing_id = next(
        (
            comment["id"]
            for comment in comments
            if (comment.get("body") or "").startswith(LLM_REVIEW_MARKER)
        ),
        None,
    )
    if existing_id is not None:
        run_gh(
            "api",
            "-X",
            "PATCH",
            f"repos/{repo_full_name}/issues/comments/{existing_id}",
            "--input",
            "-",
            stdin=json.dumps({"body": body}),
        )
    else:
        run_gh(
            "pr",
            "comment",
            pr_number,
            "--repo",
            repo_full_name,
            "--body-file",
            "-",
            stdin=body,
        )


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
    repo_full_name = resolve_repo_full_name().strip()

    # Detect whether this is a new-project PR or a refactor of projects
    # already in the pool, and review it under the matching rules.
    kind = classify_pr(fetch_pr_files(pr_number, repo_full_name))
    if kind == "refactor":
        rules = REFACTOR_RULES_PATH.read_text(encoding="utf-8")
        system_prompt = SYSTEM_PROMPT_REFACTOR
    else:
        rules = PROJECT_RULES_PATH.read_text(encoding="utf-8")
        system_prompt = SYSTEM_PROMPT_PROJECT
    print(f"Reviewing PR #{pr_number} as a {kind} PR.", file=sys.stderr)

    diff = fetch_diff(pr_number, repo_full_name)

    if not diff.strip():
        print("Empty diff; nothing to review.", file=sys.stderr)
        return 0

    reviewed_head_sha = (
        os.environ.get("REVIEW_HEAD_SHA")
        or fetch_head_sha(pr_number, repo_full_name).strip()
    )
    payload, usage, tier = request_review(
        model=model, rules=rules, diff=diff, system_prompt=system_prompt
    )
    comment = render_comment(
        payload,
        model=model,
        usage=usage,
        tier=tier,
        reviewed_head_sha=reviewed_head_sha,
        kind=kind,
    )
    post_comment(pr_number, comment, repo_full_name=repo_full_name)
    return 0


if __name__ == "__main__":
    sys.exit(main())
