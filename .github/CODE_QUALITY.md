# Code Quality Automation

Lean Pool uses deterministic CI for mechanical quality checks and LLM review for judgment calls. This page separates checks that are enforced today from planned automation.

## Enforced CI Gates

### 1. Lean Baseline

[`lean_action_ci.yml`](workflows/lean_action_ci.yml) currently runs:

- `lake exe mk_all --check` (all three library indexes)
- `lake build LeanPool`
- a warning scan over the build log
- [`scripts/ci/build-challenges.sh`](../scripts/ci/build-challenges.sh) — `lake build Challenge Solution` with a warning scan that tolerates only Lean's `declaration uses 'sorry'` notices, which challenge statements are expected to emit
- `lake exe runLinter` on `LeanPool`, `Challenge`, and `Solution`
- `lake exe lint-style` on `LeanPool`, `Challenge`, and `Solution`
- `python -m lean_pool.quality --repo ..`

The Lean workflow runs on Lean, Lake, project metadata, quality-checker, and workflow changes. It restores and saves Lake caches and pulls Mathlib oleans with `lake exe cache get` when the cache is cold.

### 2. Repository Quality Checker

[`python/lean_pool/quality.py`](../python/lean_pool/quality.py) enforces the repository-specific content rules.

Current checks:

- every `.lean` file under `LeanPool/`, plus `LeanPool.lean`, is reachable from `LeanPool.lean`
- every content `.lean` file except `LeanPool.lean` has the exact four-line file header
- content files do not contain `set_option`, `nolint` waivers, broad `import Mathlib`, `sorry`, `admit`, unchecked declarations (`axiom`, `constant`, `unsafe`, `partial`, `opaque`, `@[extern]`), or diagnostic commands (`#check`, `#print`, `#eval`, `#reduce`, `#guard_msgs`, `#lint`)
- content files do not manipulate elaborator options programmatically: option-API tokens (`withOptions`, `modifyOptions`, `withRecDepth`, `withCurrHeartbeats`, `KVMap`/`Options`/`Option` setters, ...) and gated option names (`maxRecDepth`, `maxHeartbeats`, `maxSynthPendingDepth`, `linter.*`) are forbidden in code (comments are fine) — ``withOptions (fun o => o.set `maxRecDepth 100000)`` inside an elaborator is still `set_option maxRecDepth 100000`
- Lake configuration does not pass forbidden option overrides, trace options, linter disables, or heartbeat / recursion-depth overrides
- the style-linter allowlist `scripts/nolints-style.txt` has no active entries
- no Lean content file exceeds 10000 non-blank, non-comment code lines
- no theorem/lemma proof body exceeds 200 non-blank, non-comment code lines, using the current text heuristic
- `LeanPool/projects.yml` exists, is valid YAML, and contains a `projects` list
- project entries have required fields: `slug`, `title`, `entry_module`, `authors`, `source`, `status`, `provenance`, `main_declarations`, and `tags`
- project entries also carry documentation metadata: `summary`, `branch`, `main_results`, and `msc`
- project `status` is `verified`
- project `provenance` records who wrote the Lean proofs and is one of `human`, `AI`, or `mix` (see [`candidates/provenance.md`](../candidates/provenance.md) for the rubric): `human` when the proofs were written by people, `AI` when they mostly came from an AI system, and `mix` when both contributed substantially
- project `source` includes at least one recognized primary source key among `arxiv`, `doi`, and `url` (more than one is fine)
- project authors, main declarations, and tags are nonempty string lists
- project summaries and branches are nonempty strings, MSC codes are a nonempty string list, and `main_results` is a nonempty list of `declaration` / `informal` entries
- project `main_results[*].declaration` values include every `main_declarations` entry, so compact project cards and richer documentation metadata cannot drift
- project `slug` and `entry_module` values are unique
- every top-level project module `LeanPool/Foo.lean`, except `LeanPool/Basic.lean`, is registered as an `entry_module`
- project entry modules and listed main declarations resolve in Lean
- generated entry-point project cards match `LeanPool/projects.yml`
- public declarations depend only on the allowed axiom set: `Classical.choice`, `propext`, and `Quot.sound`
- a Lean environment audit (run via `lake env lean --run` with extensions disabled, so project notation cannot interfere) walks **every** declaration compiled into a pool module — including elaborator auxiliaries and generated declarations the textual scans cannot see — and rejects any that references option-manipulating constants, embeds a gated option-name literal (however the `Name` was assembled), directly references an axiom-injecting constant (`sorryAx`, `ofReduceBool`, ...), or is itself an axiom declared inside a pool module (which is how `native_decide` and `addDecl`-of-an-axiom backdoors surface)

Challenge-mode checks (the `Challenge/` library — open statements awaiting a proof, see [Challenge mode](../CONTRIBUTING.md#challenge-mode)):

- every rule above applies to `Challenge/**/*.lean` too — header, no `set_option`, no `nolint`, no programmatic option manipulation, no unchecked declarations, no diagnostic commands, reachability from `Challenge.lean`, proof-size cap, and the environment backdoor audit
- `sorry` is allowed **only** in `Challenge/`, and only as the whole proof body of a declaration (`:= sorry`); a `sorry` buried in a larger term is rejected, and `admit` is rejected everywhere
- challenge statement files cap at 500 code lines and may import only `Mathlib.*` modules, so a statement never rests on pool code that could be refactored underneath it
- `Challenge/challenges.yml` exists and every entry carries `slug`, `title`, `summary`, `branch`, `entry_module`, `proposers`, `source` (at least one of `arxiv`/`doi`/`url`), `license`, `provenance`, `status`, `statements` (each with `declaration` and a nonempty `informal` statement), `tags`, and `msc`; `definitions` (definition holes) and a positive `estimated_lines` are optional
- `status` is `open` or `solved`; a solved challenge carries a `solution` block naming an in-repo `module`, a pool `project`, or a `url`, and an open one carries none
- slugs, entry modules, and open declaration names are unique; every declaration named in the registry lives in that challenge's namespace and is declared in its file; every statement file is registered
- generated challenge cards match `Challenge/challenges.yml` — the card carries the informal statement next to the Lean, which is what the [challenge review](CHALLENGE_REVIEW_RULES.md) judges faithfulness against
- `#print axioms` over the challenge library: declarations the registry lists as open must depend on `sorryAx` (a statement quietly proved in place is rejected — the statement is the contract solvers work against), every other declaration must not, and nothing may use an axiom outside the allowed set
- the environment audit tolerates a `sorryAx` reference only for registered open declarations and their generated companions; combined findings (`sorryAx` plus an axiom declaration, an option backdoor, ...) still fail

Solution checks (the `Solution/` library — answers to challenges, see [Solving a challenge](../CONTRIBUTING.md#solving-a-challenge)):

- solutions are held to the pool's rules, `sorry` included: a solution is a proof
- a solution may not import the challenge module it answers — comparator exports the two environments separately and compares them, and importing would inherit the statement instead of restating it
- every file under `Solution/` is the recorded `solution.module` of some challenge, and a solved challenge's solution module exists and declares every registered statement name (comparator matches challenge and solution by declaration name)
- `#print axioms` over the solution library, run in its own Lean process because a solution declares the same names as its challenge: no `sorryAx`, no axiom outside the allowed set. The environment backdoor audit runs separately over `Solution` for the same reason
- generated solution cards match the registry

The checker also has `--write-project-cards` and `--write-challenge-cards` to regenerate entry-point module docstrings from `LeanPool/projects.yml` and `Challenge/challenges.yml` (the latter writes challenge *and* solution cards).

### 3. PR Separation

[`content-pr-guard.yml`](workflows/content-pr-guard.yml) enforces PR scope separation.

Content files are:

- `LeanPool.lean`
- `LeanPool/**/*.lean`
- `LeanPool/projects.yml`
- `Challenge.lean`
- `Challenge/**/*.lean`
- `Challenge/challenges.yml`
- `Solution.lean`
- `Solution/**/*.lean`

A PR may touch only content files or only non-content files. Mixing these categories fails CI, except that a Lean/Mathlib version bump may pair content with the toolchain, manifest, lakefile, their `docbuild/` equivalents, and this workflow. Challenge statements and solutions count as content, so a PR that solves a challenge can add the answer, a pooled project, and the registry flip together.

The same workflow enforces one challenge-mode rule: **a PR may not modify a challenge statement and touch a solution at the same time.** The merged statement is the text comparator judges a solution against, so editing it in the PR that claims to meet it is the one way to fake a solution past the kernel. Statement repairs land on their own.

Branch protection to require these checks before merge is future work.

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

[`llm-review.yml`](workflows/llm-review.yml) runs after successful Lean Action CI on a PR head, or manually through `/review` and `workflow_dispatch`. It fetches the PR diff with `gh`, classifies the PR, and posts a sticky PR comment containing the reviewed head SHA, structured assessment, verdict, findings, token counts, tier, and estimated cost.

The rules applied depend on what the PR does:

| PR kind | Detected by | Rules |
|---|---|---|
| project | adds a project directory that appears only through added `.lean` files | [`REVIEW_RULES.md`](REVIEW_RULES.md) — fit and significance |
| refactor | only touches projects already in the pool | [`REFACTOR_REVIEW_RULES.md`](REFACTOR_REVIEW_RULES.md) — tech debt and maintainability |
| challenge | adds a `Challenge/**/*.lean` statement, or edits one without touching pooled Lean content | [`CHALLENGE_REVIEW_RULES.md`](CHALLENGE_REVIEW_RULES.md) — significance, faithfulness of the Lean to the prose, source fidelity, vacuity/gameability, and the estimated size of a solution |
| solution | touches `Solution/**/*.lean` | [`SOLUTION_REVIEW_RULES.md`](SOLUTION_REVIEW_RULES.md) — statement tampering, definition-hole gaming, and proof quality. Correctness belongs to comparator (§11), not to the model |

A solution PR is **not** sent to the model at all when it touches nothing but the answer, the generated index, and its registry entry, and the challenge leaves no definition hole: everything about such a PR is machine-checked, so the workflow posts a short note saying so instead. See `solution_needs_llm_review` in [`review.py`](../python/lean_pool/review.py).

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

### 11. Challenge Solution Verification

[`challenge-verify.yml`](workflows/challenge-verify.yml) runs
[`leanprover/comparator`](https://github.com/leanprover/comparator) over every
challenge the registry records as solved. Comparator exports the challenge and
solution environments separately with `lean4export`, checks that the statements
agree, and replays the proof through the Lean kernel accepting no axiom beyond
`propext`, `Quot.sound`, and `Classical.choice`. This is what makes
`status: solved` a verified claim, and it is the check the solution review
defers to.

The three external tools are pinned to exact commits and cached by pin:

- `landrun` (the sandbox comparator runs builds under), built with Go from
  `zouuup/landrun`
- `lean4export`, pinned to the tag matching [`lean-toolchain`](../lean-toolchain)
  — it reads this repository's oleans, so its Lean version has to match
- `comparator` itself, which builds at its own (newer) toolchain

Bumping any pin is a deliberate change: they are part of the trusted base for
every "solved" claim. The same pins are used by
[`leanprover/lean-eval`](https://github.com/leanprover/lean-eval).

Like the Lean build, this workflow compiles pull-request code. It runs on
`pull_request`, so the token is read-only and no secret is in scope; landrun is
defence in depth on top of the ephemeral runner.

## Future Work

The following items are documented goals but are not fully implemented or enforced yet:

- branch protection requiring the CI gates before merge
- scheduled Lean/Mathlib update checks
- doc-gen4 pages for the `Challenge` and `Solution` libraries, so the board is browsable on the docs site alongside the pool
- LeanExplore semantic dedup comments in PRs; the prototype CLI is [`python/lean_pool/semantic_dedup.py`](../python/lean_pool/semantic_dedup.py)
- controlled tag vocabulary for `LeanPool/projects.yml`; tags are currently only checked as nonempty strings
- generated domain/status indexes
- directory index-file policy: every directory under `LeanPool/` containing Lean files should have an import-only index file with a module docstring
- AST-aware proof-size measurement; the current 200-line proof cap uses a text heuristic
- repository-wide slowest-proof reports and persisted performance trend artifacts
