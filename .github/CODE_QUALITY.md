# Code Quality Automation

Lean Pool uses deterministic CI for mechanical quality checks and LLM review for judgment calls. This page separates checks that are enforced today from planned automation.

## Enforced CI Gates

### 1. Lean Baseline

[`lean_action_ci.yml`](workflows/lean_action_ci.yml) currently runs:

- `lake exe mk_all --check`
- `lake build LeanPool`
- a warning scan over the build log
- `lake exe runLinter LeanPool`
- `lake exe lint-style LeanPool`
- `python -m lean_pool.quality --repo ..`

The Lean workflow runs on Lean, Lake, project metadata, quality-checker, and workflow changes. It restores and saves Lake caches and pulls Mathlib oleans with `lake exe cache get` when the cache is cold.

### 2. Repository Quality Checker

[`python/lean_pool/quality.py`](../python/lean_pool/quality.py) enforces the repository-specific content rules.

Current checks:

- every `.lean` file under `LeanPool/`, plus `LeanPool.lean`, is reachable from `LeanPool.lean`
- every content `.lean` file except `LeanPool.lean` has the exact four-line file header
- content files do not contain `set_option`, broad `import Mathlib`, `sorry`, `admit`, unchecked declarations (`axiom`, `constant`, `unsafe`, `partial`, `opaque`, `@[extern]`), or diagnostic commands (`#check`, `#print`, `#eval`, `#reduce`, `#guard_msgs`, `#lint`)
- Lake configuration does not pass forbidden option overrides, trace options, linter disables, or heartbeat overrides
- no Lean content file exceeds 10000 non-blank, non-comment code lines
- no theorem/lemma proof body exceeds 200 non-blank, non-comment code lines, using the current text heuristic
- `LeanPool/projects.yml` exists, is valid YAML, and contains a `projects` list
- project entries have required fields: `slug`, `title`, `entry_module`, `authors`, `source`, `status`, `main_declarations`, and `tags`
- project entries also carry documentation metadata: `summary`, `branch`, `main_results`, and `msc`
- project `status` is `verified`
- project `source` includes exactly one recognized primary source key among `arxiv`, `doi`, and `url`
- project authors, main declarations, and tags are nonempty string lists
- project summaries and branches are nonempty strings, MSC codes are a nonempty string list, and `main_results` is a nonempty list of `declaration` / `informal` entries
- project `main_results[*].declaration` values include every `main_declarations` entry, so compact project cards and richer documentation metadata cannot drift
- project `slug` and `entry_module` values are unique
- every top-level project module `LeanPool/Foo.lean`, except `LeanPool/Basic.lean`, is registered as an `entry_module`
- project entry modules and listed main declarations resolve in Lean
- generated entry-point project cards match `LeanPool/projects.yml`
- public declarations depend only on the allowed axiom set: `Classical.choice`, `propext`, and `Quot.sound`

The checker also has `--write-project-cards` to regenerate entry-point module docstrings from `LeanPool/projects.yml`.

### 3. PR Separation

[`content-pr-guard.yml`](workflows/content-pr-guard.yml) enforces PR scope separation.

Content files are:

- `LeanPool.lean`
- `LeanPool/**/*.lean`
- `LeanPool/projects.yml`

A PR may touch only content files or only non-content files. Mixing these categories fails CI. Branch protection to require this check before merge is future work.

### 4. Python CI

[`python_ci.yml`](workflows/python_ci.yml) runs:

- `uv sync --locked --group dev`
- `uv run ruff check .`
- `uv run ruff format --check .`
- `uv sync --locked --group test`
- `uv run pytest --cov`

### 5. Workflow Hygiene

[`workflow_lint.yml`](workflows/workflow_lint.yml) runs `actionlint` and checks that GitHub Actions are SHA-pinned.

### 6. LLM Review

[`llm-review.yml`](workflows/llm-review.yml) runs after successful Lean Action CI on a PR head, or manually through `/review` and `workflow_dispatch`. It fetches the PR diff with `gh`, applies [`.github/REVIEW_RULES.md`](REVIEW_RULES.md), and posts a sticky PR comment containing the reviewed head SHA, structured assessment, verdict, findings, token counts, tier, and estimated cost.

The review workflow checks out the base branch only. It does not execute PR-head code.

### 7. Proof Profiling

[`proof-profile.yml`](workflows/proof-profile.yml) is advisory. It runs on PR open, `/profile` comments from trusted users, and `workflow_dispatch`.

Current behavior:

- checks out the PR head
- restores Lake caches and fetches Mathlib cache if needed
- profiles new and modified Lean files under `LeanPool/`
- posts or updates a sticky PR comment
- uploads the raw profile log as an artifact

Proof profiling does not block merge.

### 8. Dependency Updates

[`update.yml`](workflows/update.yml) is manually dispatched. It uses `leanprover-community/mathlib-update-action` to check for Mathlib updates and create a PR on success or an issue on failure.

Scheduled update checks are future work.

### 9. Stale Bot

[`stale.yml`](workflows/stale.yml) runs daily:

- PRs idle over 30 days are labeled `stale`
- stale PRs idle another 14 days are closed
- issues idle over 90 days are labeled `stale`
- stale issues idle another 30 days are closed
- `pinned`, `roadmap`, and `good-first-issue` labels are exempt

### 10. Documentation

[`docs.yml`](workflows/docs.yml) builds doc-gen4 documentation with the nested
[`docbuild/`](../docbuild/) Lake project. Pull requests build the docs site as a
check. Pushes to `main` build `LeanPool:docs` and deploy
`docbuild/.lake/build/doc` to GitHub Pages.

## Future Work

The following items are documented goals but are not fully implemented or enforced yet:

- branch protection requiring the CI gates before merge
- scheduled Lean/Mathlib update checks
- LeanExplore semantic dedup comments in PRs; the prototype CLI is [`python/lean_pool/semantic_dedup.py`](../python/lean_pool/semantic_dedup.py)
- controlled tag vocabulary for `LeanPool/projects.yml`; tags are currently only checked as nonempty strings
- generated domain/status indexes
- directory index-file policy: every directory under `LeanPool/` containing Lean files should have an import-only index file with a module docstring
- AST-aware proof-size measurement; the current 200-line proof cap uses a text heuristic
- repository-wide slowest-proof reports and persisted performance trend artifacts
