# Code Quality Automation

Lean Pool uses deterministic CI for mechanical quality checks and LLM review for judgment calls. Anything in this document should be enforceable by script, Lean, or GitHub Actions.

## Hard CI Gates

### 1. Mathlib baseline

Run the same class of checks mathlib relies on, adapted to `LeanPool`:

- `lake exe mk_all --check`
- `lake build LeanPool`
- `lake exe runLinter LeanPool`
- mathlib text-style linting (`lint-style-action` or local equivalent)
- doc-gen4 build once docs are enabled
- import/reachability checks: every `.lean` file is imported by `LeanPool.lean`
- import hygiene: content files may not use broad `import Mathlib`

Copy useful mathlib CI hygiene directly where possible: `actionlint`, SHA-pinned Actions, and any still-relevant workflow/style linters.

### 2. Kernel and soundness audit

No content PR may introduce unsound or unchecked declarations.

Fail CI on:

- `sorry` or `admit`
- new `axiom` / `constant`
- `unsafe`, `partial`, `opaque`, or `@[extern]`
- theorem dependencies outside the permitted axiom set: `Classical.choice`, `propext`, `Quot.sound`

### 3. No option overrides

Forbid `set_option` in repository Lean files. No waiver.

Also fail on Lean option overrides passed through `lakefile.toml`, `lakefile.lean`, or `moreLeanArgs`, except package-wide defaults deliberately maintained as repository policy in `lakefile.toml`.

### 4. Clean diagnostics

Lean CI should be warning-clean.

Fail CI on:

- compiler warnings
- deprecation warnings
- linter warnings
- leftover diagnostic commands in content files: `#check`, `#print`, `#eval`, `#reduce`, `#guard_msgs`, `#lint`
- trace/debug options

Expected diagnostic tests, if any, must live under a dedicated test directory rather than in `LeanPool/`.

### 5. Size limits

Hard caps, no waivers:

- no `.lean` file over 10000 non-blank, non-comment lines
- no single theorem/lemma proof body over 200 lines

Use an AST-aware linter for proof ranges. A temporary text heuristic is acceptable for v0.

### 6. Structured project metadata

Use `LeanPool/projects.yml` as the source of truth for project cards and provenance.

Each top-level project entry must include:

- `slug`
- `title`
- `entry_module`
- `authors`
- `source` (`arxiv`, `doi`, or `url`)
- `status` (must be `verified`)
- `main_declarations`
- `tags`
- optional `msc`

Only fully verified projects — no `sorry`/`admit`, no extra axioms, no `unsafe`/`partial`/`opaque`/`@[extern]` — may merge. The other rules above already enforce this; `status: verified` is the contract a contributor signs.

CI validates the YAML schema, checks that referenced modules and declarations exist, enforces a controlled tag vocabulary, requires unique `slug` and `entry_module` across projects, and diff-checks generated Lean project-card docstrings.

### 7. File headers

Every `.lean` file starts with a structured header:

```lean
/-
Copyright (c) 2026 <authors>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <names>
-/
```

CI parses the header and fails on missing or malformed required fields. Project-level source, MSC, tags, and status live in `LeanPool/projects.yml`, not ad hoc comments.

### 8. Docs and indexes

Every directory under `LeanPool/` containing Lean files must have an import-only index file with a module docstring.

CI checks:

- index files exist
- index files contain only imports plus the generated/project docstring
- `LeanPool.lean` is up to date
- doc-gen4 builds
- generated domain/status indexes are up to date

## Advisory Automation

### 10. Proof performance

Track proof performance, but do not hard-fail on wall-clock timing.

CI should:

- report the slowest changed proofs
- report the slowest proofs repository-wide
- persist timing/heartbeat artifacts for trend tracking
- hard-fail only on deterministic budget violations, such as heartbeat failures or forbidden option overrides

## Repository Hygiene

### 11. Stale bot

Run `actions/stale` daily:

- PRs idle over 30 days: label `stale`
- stale PRs idle another 14 days: close
- issues idle over 90 days: label `stale`
- stale issues idle another 30 days: close
- exempt `pinned`, `roadmap`, and `good-first-issue`

## Implementation Order

1. Mathlib baseline, workflow linting, and SHA-pinned Actions.
2. No `set_option`, no diagnostics, no `sorry`, and no debug commands.
3. Kernel/soundness audit.
4. `LeanPool/projects.yml`, generated project cards, and file headers.
5. Docs/index generation and doc-gen4 build.
6. Size limits.
7. LeanExplore semantic dedup comments.
8. Proof-performance reporting.
9. Stale bot.
