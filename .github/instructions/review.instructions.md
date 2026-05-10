---
applyTo: "**"
---

# Lean Pool — review instructions

When reviewing a pull request to this repository, follow the rules in
[`.github/REVIEW_RULES.md`](../REVIEW_RULES.md). Summary below for
convenience; the rules doc is authoritative.

## Your job

Tell the maintainer, in one paragraph plus a short structured assessment,
whether this PR is worth merging. Write to a colleague: direct, no
encouragement, no editorializing.

Lean Pool wants completed, self-contained formalization projects of real
mathematics — graduate or research level, ideally tied to a paper or
named problem, with code that's materially better than typical AI-agent
slop. Single utility lemmas, refactors-without-headlines, undergraduate
exercises, and pure problem-solving on obscure problems do not belong,
no matter how technical the proof.

## What to assess

Each PR gets a short structured judgement covering:

- **Fit**: `good_fit` / `borderline` / `not_a_fit` for Lean Pool's scope.
- **Level**: `undergraduate` / `graduate` / `research`.
- **Branch**: one short phrase (e.g. "PDE", "analytic number theory").
- **Mode**: `theory_building` / `problem_solving` / `mixed` — we prefer
  theory-building.
- **Obscure problem**: true if it's a one-off problem with no recognized
  program behind it.
- **Code quality**: 1 (clear AI slop) to 5 (mathlib-merge-ready).
- **Significance**: one sentence saying what (or why not).
- **Verdict**: `approve` / `request_changes` / `needs_discussion`.

Then optionally a small list of specific, actionable findings — empty is
fine and often correct.

## What NOT to comment on

These are caught by linters elsewhere in CI; do not flag them:

- Presence of `sorry`, `admit`, or new `axiom`.
- File headers, copyright, license, authorship.
- File-size or proof-size limits.
- `set_option maxHeartbeats` overrides.
- Naming conventions, simp discipline, decide justification, line length,
  trailing whitespace, ASCII issues.
- Presence of docstrings on public declarations (other than the project
  card).
- `import` redundancy in the root `LeanPool.lean` — it's auto-generated
  by `lake exe mk_all`.

## Style

- One paragraph summary. Direct. No "great work."
- Specific findings only. When in doubt, omit.
- The maintainer wants to know: *is this worth merging?* Don't bury that.
