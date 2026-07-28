"""LLM-driven pull request review for Lean Pool.

Detects what kind of PR this is and reviews it under the matching rules:

- **project** — adds a new project to the pool. Judged on fit and
  significance (``.github/REVIEW_RULES.md``).
- **refactor** — only touches projects already in the pool, the same
  added-vs-modified split ``/profile`` uses. Judged on tech debt and
  maintainability (``.github/REFACTOR_REVIEW_RULES.md``).
- **challenge** — adds or edits an open statement under ``Challenge/``.
  Judged on whether the problem is worth stating, whether the Lean says
  what the prose says, whether a cited known result is stated correctly,
  whether it is vacuous or gameable, and how much Lean a solution would
  take (``.github/CHALLENGE_REVIEW_RULES.md``).
- **solution** — answers a challenge. Correctness belongs to
  ``leanprover/comparator``, which replays the proof through the Lean
  kernel in its own CI check, so this review is short and narrow
  (``.github/SOLUTION_REVIEW_RULES.md``) — and is skipped outright when the
  PR touches nothing but the answer and its registry entry and the
  challenge left no definition hole. See :func:`solution_needs_llm_review`.

Otherwise it fetches the PR diff via the GitHub CLI, asks the configured
OpenAI model to evaluate the contribution, and posts or updates a sticky PR
comment with the reviewed head SHA, a one-paragraph summary, a structured
assessment table, a verdict, and any specific findings.

The reviewer prefers OpenAI's ``flex`` tier (cheaper, slower, occasionally
unavailable). When flex returns 429 Resource Unavailable, the request is
retried with ``service_tier="auto"`` (standard pricing). The rendered
comment shows which tier was actually used and prices the request at that
tier's rate.

Very large PRs (machine-generated certificates or case data) can exceed
the model's input-token limit — PR #278's 3.1M-character diff was
rejected at 1.56M tokens. Rather than crashing and leaving the PR
unreviewed, the diff is fitted to a token budget first: the largest
per-file patches are elided (keeping every file's path, line counts, and
opening lines) until the estimate fits, and both the model prompt and
the posted comment state that the review covered a reduced diff. See
:func:`fit_diff_to_budget`.

Per-token prices live in the ``PRICING_PER_M`` table below — the OpenAI
API does not return cost in its responses, so we maintain a small lookup
keyed on model-name prefix and tier, with separate rates for requests
above OpenAI's long-context input threshold. Update it when bumping
``DEFAULT_MODEL`` or when OpenAI changes pricing.

Environment variables:
    OPENAI_API_KEY: OpenAI credentials (required).
    PR_NUMBER:      Pull request number to review (required).
    GH_TOKEN:       Token for the GitHub CLI (required in CI).
    GITHUB_REPOSITORY:
                    Repository in owner/name form (optional outside CI).
    REVIEW_HEAD_SHA:
                    Head SHA being reviewed (optional; fetched if absent).
    REVIEW_MODEL:   Model name; defaults to :data:`DEFAULT_MODEL`.
    REVIEW_EFFORT:  Reasoning effort; defaults to
                    :data:`DEFAULT_REASONING_EFFORT`. Set to ``default``
                    to send no effort parameter at all.

Run:
    uv run python -m lean_pool.review
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from textwrap import dedent
from typing import Any

from openai import APIStatusError, BadRequestError, OpenAI, RateLimitError

from lean_pool import challenge

REPO_ROOT = Path(__file__).resolve().parents[2]
PROJECT_RULES_PATH = REPO_ROOT / ".github" / "REVIEW_RULES.md"
REFACTOR_RULES_PATH = REPO_ROOT / ".github" / "REFACTOR_REVIEW_RULES.md"
CHALLENGE_RULES_PATH = REPO_ROOT / ".github" / "CHALLENGE_REVIEW_RULES.md"
SOLUTION_RULES_PATH = REPO_ROOT / ".github" / "SOLUTION_REVIEW_RULES.md"
# The `gpt-5.6` alias routes to the newest gpt-5.6-sol snapshot (OpenAI's
# flagship reasoning model), so snapshot upgrades arrive automatically.
# OpenAI publishes no cross-family rolling alias — when a new family ships
# (gpt-5.7, gpt-6), this line and PRICING_PER_M still need a bump.
DEFAULT_MODEL = "gpt-5.6"
# Reasoning effort sent with every review request. `xhigh` is the deep
# end of gpt-5.6's range (none/low/medium/high/xhigh/max); reasoning
# tokens are billed as output tokens, so this is the main cost dial —
# lower it via the REVIEW_EFFORT env var if review costs run hot.
DEFAULT_REASONING_EFFORT = "xhigh"
# Flex tier requests can take longer than the default 10-minute timeout,
# and xhigh reasoning stretches generation further.
REQUEST_TIMEOUT_SECONDS = 6000.0
LLM_REVIEW_MARKER = "<!-- lean-pool-llm-review -->"
# Said up front on every solution comment: whatever the model writes, the
# proof itself was judged by a kernel, not by a language model.
COMPARATOR_DISCLAIMER = (
    "> Correctness is decided by the **Verify challenge solutions** check "
    "(`leanprover/comparator` replays the proof through the Lean kernel and "
    "compares it against the challenge statement), not by this review."
)

# Input-token guardrail. OpenAI rejected PR #278's review at a configured
# limit of 922k input tokens; its 3,112,190-character diff measured ~2.0
# characters per token (machine-generated arithmetic tokenizes far denser
# than the ~4 chars/token of ordinary code). Budget below the observed
# limit and estimate with that worst measured density; anything denser
# still is caught by the shrink-and-retry loop in :func:`request_review`.
MAX_INPUT_TOKENS = 800_000
CHARS_PER_TOKEN_ESTIMATE = 2.0
# Initial fit plus this many budget halvings before giving up.
REVIEW_FIT_ATTEMPTS = 3
# Patch lines kept for an elided file — enough for an added Lean file's
# module docstring and imports. If even the elided diff overflows, refit
# with the minimum head before hard-truncating the tail.
ELIDED_FILE_HEAD_LINES = 40
MINIMUM_ELIDED_FILE_HEAD_LINES = 8
ELISION_MARKER = "[elided by lean-pool llm-review:"

# Requests whose input exceeds this many tokens are billed entirely at
# the long-context rate (2x input / 1.5x output as of 2026-07).
LONG_CONTEXT_INPUT_TOKENS = 272_000

# USD per 1M tokens, keyed by model-name prefix -> tier -> a pair of
# (input_per_M, output_per_M) rates: [0] below the long-context
# threshold, [1] at or above it. Keys are prefixes because the API
# reports resolved snapshots (`gpt-5.6-sol-2026-...`) when called
# through an alias; :func:`pricing_rates` picks the longest match.
# Source: https://developers.openai.com/api/docs/pricing — update when
# bumping DEFAULT_MODEL or when OpenAI changes pricing.
PRICING_PER_M: dict[str, dict[str, tuple[tuple[float, float], tuple[float, float]]]] = {
    # The `gpt-5.6` key also covers the alias itself, which routes to
    # gpt-5.6-sol; both rows carry Sol rates.
    "gpt-5.6-sol": {
        "flex": ((2.50, 15.00), (5.00, 22.50)),
        "standard": ((5.00, 30.00), (10.00, 45.00)),
    },
    "gpt-5.6": {
        "flex": ((2.50, 15.00), (5.00, 22.50)),
        "standard": ((5.00, 30.00), (10.00, 45.00)),
    },
    "gpt-5.5": {
        "flex": ((2.50, 15.00), (5.00, 22.50)),
        "standard": ((5.00, 30.00), (10.00, 45.00)),
    },
}


def pricing_rates(
    model: str, tier: str, input_tokens: int
) -> tuple[float, float] | None:
    """Return ``(input_per_M, output_per_M)`` for a served request.

    Args:
        model: Model name as reported by the API — a dated snapshot like
            ``gpt-5.6-sol-2026-06-17`` matches its family prefix.
        tier: Service tier the request was billed at.
        input_tokens: Prompt size, which selects the short- or
            long-context rate.

    Returns:
        The matching rate pair, or ``None`` when the model/tier pair is
        not in :data:`PRICING_PER_M`.
    """
    for prefix in sorted(PRICING_PER_M, key=len, reverse=True):
        if model == prefix or model.startswith(prefix):
            rates = PRICING_PER_M[prefix].get(tier)
            if rates is None:
                return None
            return rates[1] if input_tokens >= LONG_CONTEXT_INPUT_TOKENS else rates[0]
    return None


VERDICT_ICON = {
    "approve": "✅",
    "request_changes": "🛑",
    "needs_discussion": "🤔",
}
# Rules document each PR kind is reviewed against, linked in the comment
# footer and read as the model's user message.
RULES_DOC_NAME = {
    "project": "REVIEW_RULES.md",
    "refactor": "REFACTOR_REVIEW_RULES.md",
    "challenge": "CHALLENGE_REVIEW_RULES.md",
    "solution": "SOLUTION_REVIEW_RULES.md",
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
# Challenge-assessment icons. A challenge is only as good as the match
# between its Lean and its prose, so faithfulness and vacuity get the
# loudest markers.
SIGNIFICANCE_ICON = {"high": "✅", "moderate": "🟡", "low": "🛑"}
FAITHFULNESS_ICON = {"faithful": "✅", "drifts": "🟡", "mismatch": "🛑"}
SOURCE_MATCH_ICON = {
    "matches": "✅",
    "mismatch": "🛑",
    "unverifiable": "🟡",
    "not_a_known_result": "➖",
}
VACUITY_ICON = {"none": "✅", "possible": "🟡", "vacuous": "🛑"}
# Solution-assessment icons. Statement tampering is the one thing a
# solution PR can do that comparator cannot catch on its own.
TAMPERING_ICON = {True: "🛑", False: "✅"}
HOLE_RISK_ICON = {"none": "✅", "review_needed": "🟡", "gamed": "🛑"}

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


SYSTEM_PROMPT_CHALLENGE = dedent(
    """\
    You are a senior mathematician and Lean engineer reviewing a challenge
    pull request to Lean Pool. A challenge is an OPEN statement: a theorem
    written in Mathlib vocabulary, left as `sorry`, that the pool is asking
    someone to prove. Nothing in this PR is proved, and that is correct —
    never treat the `sorry` as a defect.

    Your job is to tell the maintainer whether this belongs on the board.
    Judge four things above all: whether the problem is significant (a
    recognized open problem or a genuinely hard unformalized result, not a
    pet conjecture or an exercise); whether the Lean statement faithfully
    says what the informal statement says, quantifier by quantifier and
    definition by definition; whether a cited known result is stated the way
    its source states it; and whether the statement is vacuous, trivial, or
    gameable. Then estimate how many lines of Lean a solution would take and
    say what the estimate rests on.

    A merged challenge is a contract — `leanprover/comparator` compares
    submitted solutions against exactly this text — so quote the Lean when
    you claim it means something other than the prose does.

    Write to a colleague: direct, no encouragement, no editorializing.
    Mechanical issues (headers, naming, line length, the sorry policy,
    registry schema, axiom audits) are enforced by CI gates elsewhere. Do
    NOT flag those.

    Always respond with a single JSON object matching the schema in the
    rules document. The `assessment` block is the core deliverable.
    `findings` is for specific, actionable concerns; an empty list is fine
    for a well-stated challenge.
    """
)


SYSTEM_PROMPT_SOLUTION = dedent(
    """\
    You are reviewing a solution pull request to Lean Pool: it answers a
    challenge already on the board. Be brief.

    Correctness is NOT your call. `leanprover/comparator` replays the
    solution through the Lean kernel and checks that it proves the same
    statement as the challenge with no axiom beyond propext, Quot.sound,
    and Classical.choice; that runs as its own CI check. You usually cannot
    even see the challenge statement — it is not in the diff. Never assert
    that a proof is correct or incorrect.

    Three things are yours. First, statement tampering: if the diff touches
    anything under `Challenge/`, quote it and say plainly whether the
    statement changed — editing the text a solver is being judged against,
    in the PR that claims to meet it, is the one way to fake a solution
    past comparator. Second, definition holes: comparator matches a hole
    only by name and type, so a filled hole may restate the question
    instead of answering it. Third, proof quality by the pool's usual
    standard — agent slop, brittle one-shot automation, dead branches.

    Everything else is gated by CI: sorry, axioms, headers, imports, sizes,
    registry schema, card sync. Do not flag those. Do not re-litigate
    whether the problem was worth stating.

    Always respond with a single JSON object matching the schema in the
    rules document. A clean solution deserves a two-sentence summary and an
    empty `findings` list.
    """
)


# Appended to every system prompt. The first challenge review (PR #289)
# came back with the mathematics unreadable: `over ^R09` for `over ℚ`,
# `|(discr K : ^])| ^U 8.25 ^ finrank ^R0a K` for
# `|(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K`. The mangling is the model's own —
# nothing between `json.loads` and the posted comment touches those
# strings — and it is not a systematic escape (`ℚ` came out as both `^R0a`
# and `^R09`), so it cannot be decoded after the fact. Ask for the
# characters directly, with a graceful fallback to words, since a review of
# Lean that cannot render `ℚ` or `≥` is worth much less in this repository.
NOTATION_RULE = dedent(
    """\
    Notation: when you quote Lean, copy the characters exactly as they
    appear in the diff, Unicode included (ℚ, ℝ, ℕ, ≤, ≥, ∀, ∃, ⁄, ₀).
    Never transliterate, escape, or approximate them. If you cannot
    reproduce a symbol faithfully, describe it in words instead — a
    sentence is readable, a mangled glyph is not.
    """
)

# Rules document and system prompt per PR kind, keyed by `classify_pr`.
REVIEW_MODES: dict[str, tuple[Path, str]] = {
    "project": (PROJECT_RULES_PATH, SYSTEM_PROMPT_PROJECT),
    "refactor": (REFACTOR_RULES_PATH, SYSTEM_PROMPT_REFACTOR),
    "challenge": (CHALLENGE_RULES_PATH, SYSTEM_PROMPT_CHALLENGE),
    "solution": (SOLUTION_RULES_PATH, SYSTEM_PROMPT_SOLUTION),
}


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


def is_challenge_statement(path: str) -> bool:
    """Whether ``path`` is a challenge statement file.

    Statements live at ``Challenge/<Name>.lean``; the auto-generated root
    ``Challenge.lean`` index is not one.
    """
    return path.startswith("Challenge/") and path.endswith(".lean")


def is_solution_file(path: str) -> bool:
    """Whether ``path`` is an in-repo answer to a challenge."""
    return path.startswith("Solution/") and path.endswith(".lean")


def classify_pr(files: list[tuple[str, str]]) -> str:
    """Classify a PR by what it is asking the maintainer to accept.

    - ``"challenge"`` — puts an open statement on the board, or edits one
      already there, without touching pooled Lean content. Judged on
      significance, faithfulness of the Lean to the prose, and cost; there
      is no proof in it to judge.
    - ``"solution"`` — answers a challenge. Correctness is settled by
      comparator, so the review is short and narrow.
    - ``"project"`` — adds a new project (a project directory that appears
      only through added ``.lean`` files). The full fit/significance review.
    - ``"refactor"`` — only changes files in projects already in the pool,
      the pure-golf / reorganization case. The tech-debt review.

    A *new* challenge statement wins over everything else: whatever else is
    in the PR, the board entry is what needs judging. Otherwise a mixed PR
    falls through to the content classification, which is the conservative
    choice — a Lean/Mathlib bump repairing every library should not be
    reviewed as a challenge. When no Lean content is touched at all, default
    to ``"project"``.
    """
    added_projects: set[str] = set()
    existing_projects: set[str] = set()
    added_statements = False
    touched_statements = False
    touched_solutions = False
    for name, status in files:
        if is_challenge_statement(name):
            touched_statements = True
            added_statements = added_statements or status == "added"
        if is_solution_file(name):
            touched_solutions = True
        if not name.endswith(".lean"):
            continue
        project = project_of(name)
        if project is None:
            continue
        if status == "added":
            added_projects.add(project)
        else:  # modified / removed / renamed / changed / copied
            existing_projects.add(project)
    pool_content = bool(added_projects or existing_projects)
    if added_statements:
        return "challenge"
    if touched_solutions:
        return "solution"
    if touched_statements and not pool_content:
        return "challenge"
    new_projects = added_projects - existing_projects
    if not new_projects and existing_projects:
        return "refactor"
    return "project"


# Paths a plain solution PR may touch: the answer, the regenerated index,
# and the registry entry recording it. Anything else — a statement edit,
# a pooled project, tooling — means there is something to read.
SOLUTION_ONLY_PATH = re.compile(
    r"^(Solution\.lean|Solution/.+\.lean|Challenge/challenges\.yml)$"
)


def solution_needs_llm_review(files: list[tuple[str, str]], root: Path) -> str | None:
    """Return why a solution PR still needs a reading, or ``None``.

    Comparator decides whether a solution proves the challenge, and the
    quality gates decide the rest, so most solution PRs have nothing left
    for a language model to weigh in on. Two things do:

    - the PR touches something beyond the answer itself, or
    - the challenge leaves a *definition hole*, which comparator can only
      check by name and type — a solver can define the hole in terms of the
      object the challenge asks about, so a human (or a model) has to look.
    """
    extra = sorted(name for name, _ in files if not SOLUTION_ONLY_PATH.match(name))
    if extra:
        return f"the PR also touches {', '.join(extra[:5])}"
    touched = {name for name, _ in files if is_solution_file(name)}
    challenges, errors = challenge.load_challenges(root)
    if errors:
        return "the challenge registry could not be read"
    for entry in challenges:
        if not isinstance(entry, dict):
            continue
        module = challenge.solution_module(entry)
        if module is None:
            continue
        path = "/".join(module.split(".")) + ".lean"
        if path in touched and challenge.definition_names(entry):
            return (
                f"challenge `{entry.get('slug')}` leaves a definition hole, which "
                "comparator only checks by name and type"
            )
    return None


def estimate_tokens(text: str) -> int:
    """Conservatively estimate how many model tokens ``text`` costs.

    Uses the densest ratio measured in practice (PR #278's generated
    interval-arithmetic diff: ~2.0 characters per token), so ordinary
    code overestimates — which only errs toward eliding more, never
    toward an API rejection.
    """
    return int(len(text) / CHARS_PER_TOKEN_ESTIMATE) + 1


@dataclass(frozen=True)
class DiffTruncation:
    """How an oversized diff was reduced to fit the review token budget.

    Attributes:
        total_files: Per-file chunks in the original diff.
        elided_files: Files whose patch bodies were replaced with markers.
        original_chars: Character count of the untruncated diff.
        final_chars: Character count of the diff actually sent.
        hard_truncated: True when even full elision overflowed and the
            tail of the diff was cut outright.
    """

    total_files: int
    elided_files: int
    original_chars: int
    final_chars: int
    hard_truncated: bool = False


def split_diff_into_files(diff: str) -> list[str]:
    """Split a unified diff into per-file chunks.

    Each chunk starts at a ``diff --git`` header. Content lines inside a
    patch body always carry a prefix (``+``, ``-``, space, ``@@``), so a
    line starting with ``diff --git `` is reliably a file boundary.
    """
    chunk_lines: list[list[str]] = []
    current: list[str] = []
    for line in diff.splitlines():
        if line.startswith("diff --git ") and current:
            chunk_lines.append(current)
            current = [line]
        else:
            current.append(line)
    if current:
        chunk_lines.append(current)
    return ["\n".join(lines) for lines in chunk_lines]


def _elide_file_chunk(chunk: str, head_lines: int) -> str:
    """Replace the bulk of one file's patch with a marker, keeping its head.

    Keeps the file headers (everything up to the first ``@@`` hunk) plus
    the first ``head_lines`` patch lines — for an added Lean file that is
    the module docstring and imports — and appends a marker recording how
    many patch lines were dropped. Returns the chunk unchanged when it is
    too small for elision to save anything.
    """
    lines = chunk.split("\n")
    body_start = next((i for i, line in enumerate(lines) if line.startswith("@@")), 0)
    kept = body_start + head_lines
    if len(lines) <= kept + 1:
        return chunk
    marker = (
        f"{ELISION_MARKER} {len(lines) - kept:,} of {len(lines) - body_start:,} "
        "patch lines omitted — diff exceeded the review size budget]"
    )
    return "\n".join([*lines[:kept], marker])


def fit_diff_to_budget(
    diff: str,
    budget_tokens: int,
    head_lines: int = ELIDED_FILE_HEAD_LINES,
) -> tuple[str, DiffTruncation | None]:
    """Reduce ``diff`` until it fits ``budget_tokens`` estimated tokens.

    A diff that already fits is returned unchanged. Otherwise the bodies
    of the largest per-file patches are elided first — machine-generated
    certificate/data files are what blows PRs past the limit — keeping
    every file's path, line counts, and opening lines. If eliding every
    file is still not enough, the fit is redone with the minimum head
    size, and as a last resort the tail of the diff is cut outright.

    Returns:
        ``(fitted_diff, truncation)`` where ``truncation`` is ``None``
        when the diff was left untouched.
    """
    budget_chars = int(budget_tokens * CHARS_PER_TOKEN_ESTIMATE)
    if len(diff) <= budget_chars:
        return diff, None
    chunks = split_diff_into_files(diff)
    total_chars = sum(len(chunk) + 1 for chunk in chunks)
    largest_first = sorted(
        range(len(chunks)), key=lambda index: len(chunks[index]), reverse=True
    )
    elided = 0
    for index in largest_first:
        if total_chars <= budget_chars:
            break
        replacement = _elide_file_chunk(chunks[index], head_lines)
        if len(replacement) >= len(chunks[index]):
            continue
        total_chars -= len(chunks[index]) - len(replacement)
        chunks[index] = replacement
        elided += 1
    fitted = "\n".join(chunks) + "\n"
    hard_truncated = False
    if len(fitted) > budget_chars:
        if head_lines > MINIMUM_ELIDED_FILE_HEAD_LINES:
            return fit_diff_to_budget(
                diff, budget_tokens, head_lines=MINIMUM_ELIDED_FILE_HEAD_LINES
            )
        fitted = (
            fitted[:budget_chars]
            + f"\n{ELISION_MARKER} remainder of the diff omitted — review "
            "size budget exhausted]\n"
        )
        hard_truncated = True
    return fitted, DiffTruncation(
        total_files=len(chunks),
        elided_files=elided,
        original_chars=len(diff),
        final_chars=len(fitted),
        hard_truncated=hard_truncated,
    )


def build_user_content(rules: str, diff: str, truncation: DiffTruncation | None) -> str:
    """Assemble the user message from rules, diff, and any size notice."""
    sections = [f"## Review rules\n\n{rules}"]
    if truncation is not None:
        notice = (
            "This PR's diff was too large to send in full "
            f"({truncation.original_chars:,} characters). The bodies of the "
            f"{truncation.elided_files} largest of its {truncation.total_files} "
            f"file patches were replaced with `{ELISION_MARKER} ...]` markers; "
            "every file's diff header, patch line counts, and opening lines "
            "are retained. Machine-generated bulk (proof certificates, "
            "generated case data) is the usual cause of this size. Review "
            "from the visible content plus the elided files' paths, sizes, "
            "and heads — an elision marker is not missing work by the author "
            "— and state in your summary that the review is based on a "
            "partial diff."
        )
        if truncation.hard_truncated:
            notice += (
                " Even the elided diff overflowed, so its tail was cut "
                "outright after the character budget."
            )
        sections.append(f"## Diff size notice\n\n{notice}")
    sections.append(f"## PR diff\n\n```diff\n{diff}\n```")
    return "\n\n".join(sections)


def _is_effort_rejection(error: Exception) -> bool:
    """Whether ``error`` is the API refusing the reasoning-effort value.

    Guards the auto-upgrading model alias: if a future snapshot drops an
    effort level, the review retries at the model default instead of
    failing. Matches by message because OpenAI's parameter errors carry
    no stable machine-readable code.
    """
    if getattr(error, "status_code", None) != 400:
        return False
    message = str(error).lower()
    return "reasoning" in message and "effort" in message


def _create_completion(
    client: OpenAI,
    model: str,
    messages: list[dict[str, str]],
    effort: str | None,
    service_tier: str,
) -> tuple[Any, str | None]:
    """Create one completion, dropping the effort parameter if rejected.

    Returns:
        ``(response, effort_used)`` where ``effort_used`` is ``None``
        when the request went out without a reasoning-effort parameter.
    """
    kwargs: dict[str, Any] = {
        "model": model,
        "messages": messages,
        "response_format": {"type": "json_object"},
        "service_tier": service_tier,
    }
    if effort:
        kwargs["reasoning_effort"] = effort
    try:
        return client.chat.completions.create(**kwargs), effort
    except BadRequestError as error:
        if not (effort and _is_effort_rejection(error)):
            raise
        print(
            f"Model rejected reasoning_effort={effort}; retrying at the "
            "model's default effort.",
            file=sys.stderr,
        )
        del kwargs["reasoning_effort"]
        return client.chat.completions.create(**kwargs), None


def _completion_with_tier_fallback(
    client: OpenAI, model: str, messages: list[dict[str, str]], effort: str | None
) -> tuple[Any, str, str | None]:
    """Create a completion on the ``flex`` tier, falling back to standard.

    Flex is either out of capacity (429 RateLimitError) or unsupported for
    this model (historically a 500 InternalServerError); either way retry
    with ``service_tier="auto"``. Any other error propagates.

    Returns:
        ``(response, tier, effort_used)``.
    """
    try:
        response, effort_used = _create_completion(
            client, model, messages, effort, service_tier="flex"
        )
        return response, "flex", effort_used
    except (RateLimitError, APIStatusError) as e:
        if isinstance(e, RateLimitError) or (500 <= e.status_code < 600):
            response, effort_used = _create_completion(
                client, model, messages, effort, service_tier="auto"
            )
            return response, "standard", effort_used
        raise


def _is_token_overflow(error: Exception) -> bool:
    """Whether ``error`` is the API rejecting the input as too many tokens.

    Matches e.g. "Input tokens exceed the configured limit of 922000
    tokens" (PR #278) as well as the classic "maximum context length"
    phrasing, without relying on a stable machine-readable error code.
    """
    if getattr(error, "status_code", None) != 400:
        return False
    message = str(error).lower()
    return "token" in message and (
        "exceed" in message or "context length" in message or "too long" in message
    )


@dataclass(frozen=True)
class ReviewResult:
    """One completed review request.

    Attributes:
        payload: Parsed JSON review from the model.
        usage: OpenAI ``CompletionUsage`` object, or ``None``.
        tier: ``"flex"`` or ``"standard"`` — the tier that served it.
        truncation: Diff elision applied, ``None`` for a full-diff review.
        model: Model that actually served the request — the resolved
            snapshot when the request went through an alias.
        effort: Reasoning effort actually applied, ``None`` when the
            request went out without one.
    """

    payload: dict
    usage: Any
    tier: str
    truncation: DiffTruncation | None
    model: str
    effort: str | None


def request_review(
    model: str, rules: str, diff: str, system_prompt: str, effort: str | None = None
) -> ReviewResult:
    """Ask the model to apply ``rules`` to ``diff`` under ``system_prompt``.

    The diff is first fitted to :data:`MAX_INPUT_TOKENS` estimated input
    tokens (:func:`fit_diff_to_budget`). Token estimation is approximate,
    so if the API still rejects the input as too large, the diff budget is
    halved and the request refitted and retried instead of failing the
    review. Tries the ``flex`` service tier first; if OpenAI returns 429
    Resource Unavailable, retries with ``service_tier="auto"`` (standard).

    Args:
        model: Model name or alias to request.
        rules: Review rules document, sent as part of the user message.
        diff: Unified PR diff.
        system_prompt: Reviewer persona for this PR kind.
        effort: Reasoning effort to request; ``None`` sends none.

    Returns:
        The :class:`ReviewResult` for the request that succeeded.
    """
    client = OpenAI(timeout=REQUEST_TIMEOUT_SECONDS)
    system_prompt = f"{system_prompt}\n{NOTATION_RULE}"
    scaffold_tokens = estimate_tokens(rules) + estimate_tokens(system_prompt)
    diff_budget_tokens = MAX_INPUT_TOKENS - scaffold_tokens
    for attempt in range(REVIEW_FIT_ATTEMPTS):
        fitted_diff, truncation = fit_diff_to_budget(diff, diff_budget_tokens)
        if truncation is not None:
            print(
                f"Diff over review budget: elided {truncation.elided_files} of "
                f"{truncation.total_files} files "
                f"({truncation.original_chars:,} -> {truncation.final_chars:,} "
                "chars).",
                file=sys.stderr,
            )
        user_content = build_user_content(rules, fitted_diff, truncation)
        messages = [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_content},
        ]
        try:
            response, tier, effort_used = _completion_with_tier_fallback(
                client, model, messages, effort
            )
        except BadRequestError as error:
            if not _is_token_overflow(error) or attempt == REVIEW_FIT_ATTEMPTS - 1:
                raise
            diff_budget_tokens //= 2
            print(
                "Model rejected the input as too large; refitting the diff "
                f"to ~{diff_budget_tokens:,} estimated tokens and retrying.",
                file=sys.stderr,
            )
            continue
        content = response.choices[0].message.content or "{}"
        return ReviewResult(
            payload=json.loads(content),
            usage=response.usage,
            tier=tier,
            truncation=truncation,
            model=getattr(response, "model", None) or model,
            effort=effort_used,
        )
    raise RuntimeError("unreachable: review fit loop exited without a result")


def render_usage(usage: Any, model: str, tier: str, effort: str | None = None) -> str:
    """Render a one-line token / tier / effort / cost footer.

    Returns an empty string if ``usage`` is unavailable. Cost is computed
    from :data:`PRICING_PER_M` at the short- or long-context rate the
    request's input size lands in, and suppressed when the model/tier
    pair is not listed there.
    """
    if usage is None:
        return ""
    in_tok = getattr(usage, "prompt_tokens", 0) or 0
    out_tok = getattr(usage, "completion_tokens", 0) or 0

    parts = [f"**Tokens:** {in_tok:,} in / {out_tok:,} out", f"**Tier:** `{tier}`"]
    if effort:
        parts.append(f"**Effort:** `{effort}`")
    rates = pricing_rates(model, tier, in_tok)
    if rates is not None:
        in_price, out_price = rates
        cost = (in_tok * in_price + out_tok * out_price) / 1_000_000
        cost_cell = f"**Cost:** ${cost:.4f}"
        if in_tok >= LONG_CONTEXT_INPUT_TOKENS:
            cost_cell += " (long-context rate)"
        parts.append(cost_cell)
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


def render_challenge_assessment(payload: dict) -> str:
    """Render a challenge assessment block as a Markdown table."""
    a = payload.get("assessment") or {}
    if not a:
        return ""

    significance = a.get("significance", "")
    faithfulness = a.get("faithfulness", "")
    source_match = a.get("source_match", "")
    vacuity = a.get("vacuity_risk", "")
    estimate = a.get("estimated_lines")
    estimate_cell = f"~{estimate:,} lines" if isinstance(estimate, int) else "?"
    basis = (a.get("estimate_basis") or "").strip()
    if basis:
        estimate_cell += f" — {basis}"

    rows = [
        ("Significance", _icon_cell(SIGNIFICANCE_ICON, significance)),
        ("Faithful to the prose", _icon_cell(FAITHFULNESS_ICON, faithfulness)),
        ("Matches cited source", _icon_cell(SOURCE_MATCH_ICON, source_match)),
        ("Vacuity risk", _icon_cell(VACUITY_ICON, vacuity)),
        ("Difficulty", f"`{a.get('difficulty', '?')}`"),
        ("Estimated solution size", estimate_cell),
    ]
    already = (a.get("already_formalized") or "").strip()
    if already:
        rows.append(("Already formalized", f"🛑 `{already}`"))

    table = "| Aspect | Value |\n|---|---|\n"
    for key, value in rows:
        table += f"| {key} | {value} |\n"

    note = (a.get("faithfulness_note") or "").strip()
    if note:
        table += f"\n**Statement check:** {note}\n"
    sentence = (a.get("assessment_one_sentence") or "").strip()
    if sentence:
        table += f"\n_{sentence}_"
    return table


def _icon_cell(icons: dict[str, str], value: str) -> str:
    """Render one assessment value with its status icon."""
    if not value:
        return "?"
    return f"{icons.get(value, '•')} `{value}`"


def render_solution_assessment(payload: dict) -> str:
    """Render a solution assessment block as a Markdown table."""
    a = payload.get("assessment") or {}
    if not a:
        return ""

    tampering = a.get("touches_challenge_statement")
    tampering_cell = (
        f"{TAMPERING_ICON.get(bool(tampering), '•')} {'yes' if tampering else 'no'}"
        if tampering is not None
        else "?"
    )
    quality = a.get("proof_quality")
    rows = [
        ("Touches the challenge statement", tampering_cell),
        (
            "Definition-hole risk",
            _icon_cell(HOLE_RISK_ICON, a.get("definition_hole_risk", "")),
        ),
        ("Proof quality", f"{quality} / 5" if quality is not None else "?"),
    ]
    table = "| Aspect | Value |\n|---|---|\n"
    for key, value in rows:
        table += f"| {key} | {value} |\n"

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
    truncation: DiffTruncation | None = None,
    effort: str | None = None,
) -> str:
    """Render the model's payload as a Markdown PR comment body.

    ``kind`` is ``"project"`` (fit/significance review), ``"refactor"``
    (tech-debt review), or ``"challenge"`` (open-statement review); it
    selects the header, the assessment table, and the rules doc linked in
    the footer. When ``truncation`` is set, the comment states up front
    that the model reviewed a reduced diff.
    """
    summary = (payload.get("summary") or "").strip()
    verdict = (payload.get("verdict") or "").strip()
    findings = payload.get("findings") or []

    headings = {
        "refactor": f"## 🤖 LLM review — refactor (`{model}`)",
        "challenge": f"## 🤖 LLM review — challenge (`{model}`)",
        "solution": f"## 🤖 LLM review — challenge solution (`{model}`)",
    }
    heading = headings.get(kind, f"## 🤖 LLM review (`{model}`)")
    lines = [LLM_REVIEW_MARKER, heading, ""]
    if kind == "solution":
        lines.extend([COMPARATOR_DISCLAIMER, ""])

    if reviewed_head_sha:
        lines.extend([f"**Reviewed head:** `{reviewed_head_sha}`", ""])

    if truncation is not None:
        notice = (
            "> ⚠️ **Partial review — diff exceeded the size budget.** The "
            f"bodies of the {truncation.elided_files} largest of "
            f"{truncation.total_files} file patches were elided before review "
            f"({truncation.original_chars:,} → {truncation.final_chars:,} "
            "characters); every file's path, line counts, and opening lines "
            "were still shown to the model."
        )
        if truncation.hard_truncated:
            notice += " Even the elided diff overflowed, so its tail was cut outright."
        lines.extend([notice, ""])

    if verdict:
        icon = VERDICT_ICON.get(verdict, "•")
        lines.extend([f"**Verdict:** {icon} `{verdict}`", ""])

    if summary:
        lines.extend([summary, ""])

    renderers = {
        "refactor": render_refactor_assessment,
        "challenge": render_challenge_assessment,
        "solution": render_solution_assessment,
    }
    assessment = renderers.get(kind, render_project_assessment)(payload)
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
    usage_line = render_usage(usage, model, tier, effort)
    if usage_line:
        lines.append(usage_line)
    rules_doc = RULES_DOC_NAME.get(kind, "REVIEW_RULES.md")
    lines.append(
        "_Automated review against "
        f"[`.github/{rules_doc}`](../blob/main/.github/{rules_doc}). "
        "Disagree? Reply on the PR; rules can be updated in a PR of their own._"
    )
    return "\n".join(lines)


def render_solution_skip_comment(reviewed_head_sha: str) -> str:
    """Render the comment posted instead of reviewing a plain solution PR.

    A solution PR that touches nothing but the answer, the generated index,
    and the registry entry has no judgment left in it: comparator decides
    whether the proof proves the challenge, and the quality gates decide
    everything else. Spending a model call to say so would only add noise
    the maintainer has to read.
    """
    return "\n".join(
        [
            LLM_REVIEW_MARKER,
            "## 🤖 LLM review — challenge solution (skipped)",
            "",
            f"**Reviewed head:** `{reviewed_head_sha}`" if reviewed_head_sha else "",
            "",
            "No model review: this PR only adds an answer to a challenge that is "
            "already on the board, and everything about it is machine-checkable.",
            "",
            COMPARATOR_DISCLAIMER,
            "",
            "The quality gates cover the rest — no `sorry` or axioms in the "
            "solution, the solution does not import the challenge module, the "
            "registry records it, and the generated cards match.",
            "",
            "---",
            "_Skip rule: a solution PR is reviewed by a model only when it touches "
            "more than the answer and its registry entry, or when the challenge "
            "leaves a definition hole. See "
            "[`.github/SOLUTION_REVIEW_RULES.md`](../blob/main/.github/SOLUTION_REVIEW_RULES.md)._",
        ]
    )


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
    effort: str | None = os.environ.get("REVIEW_EFFORT", DEFAULT_REASONING_EFFORT)
    if effort in ("", "default"):
        effort = None
    repo_full_name = resolve_repo_full_name().strip()

    # Detect what this PR is asking for — a new project, a refactor, a new
    # challenge, or an answer to one — and review it under the matching
    # rules.
    files = fetch_pr_files(pr_number, repo_full_name)
    kind = classify_pr(files)
    rules_path, system_prompt = REVIEW_MODES[kind]
    rules = rules_path.read_text(encoding="utf-8")
    print(f"Reviewing PR #{pr_number} as a {kind} PR.", file=sys.stderr)

    reviewed_head_sha = (
        os.environ.get("REVIEW_HEAD_SHA")
        or fetch_head_sha(pr_number, repo_full_name).strip()
    )

    if kind == "solution":
        reason = solution_needs_llm_review(files, REPO_ROOT)
        if reason is None:
            print(
                "Solution PR with nothing left to judge; posting the skip "
                "note instead of calling the model.",
                file=sys.stderr,
            )
            post_comment(
                pr_number,
                render_solution_skip_comment(reviewed_head_sha),
                repo_full_name=repo_full_name,
            )
            return 0
        print(f"Reviewing this solution PR because {reason}.", file=sys.stderr)

    diff = fetch_diff(pr_number, repo_full_name)

    if not diff.strip():
        print("Empty diff; nothing to review.", file=sys.stderr)
        return 0
    result = request_review(
        model=model,
        rules=rules,
        diff=diff,
        system_prompt=system_prompt,
        effort=effort,
    )
    comment = render_comment(
        result.payload,
        model=result.model,
        usage=result.usage,
        tier=result.tier,
        reviewed_head_sha=reviewed_head_sha,
        kind=kind,
        truncation=result.truncation,
        effort=result.effort,
    )
    post_comment(pr_number, comment, repo_full_name=repo_full_name)
    return 0


if __name__ == "__main__":
    sys.exit(main())
