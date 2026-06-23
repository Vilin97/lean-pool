---
name: version-bump
description: Migrate the entire Lean Pool to a new Lean/Mathlib version — bump the toolchain + Mathlib + docbuild pins, repair every project's API breakage and build warnings, pass all CI gates, and open a non-draft PR. Use when the user asks to bump / migrate / upgrade the pool to a specific Lean or Mathlib version (e.g. "bump to v4.33.0-rc1", "migrate to the latest Mathlib").
argument-hint: <target-version> e.g. v4.33.0-rc1
---

# Lean Pool whole-pool version bump

Migrate the whole pool to the **target version given as the argument** (e.g. `v4.33.0-rc1`). If no version was given, ask for it before starting. Treat the constraints below as the directive.

## Hard constraints (never violate)
1. **No statement drops.** Every `theorem`/`lemma`/`def`/`instance`/`structure`/`inductive`/`class`/`abbrev` that exists now must still exist when done.
2. **Modify a statement only when the statement itself does not compile** under the target (a renamed/removed Mathlib symbol in its type, or a name that now collides with a new Mathlib decl). Then make the *minimal* meaning-preserving change (usually a rename keeping statement + proof). Everything else: change only proof bodies / tactics / syntax. `def`→`theorem` keyword changes for `Prop`-valued decls flagged by the `defProp` linter are allowed (same statement).
3. **Keep RAM under 24 GB** the whole time.
4. **Work in a new git worktree** (e.g. `~/Github/lean-pool-v<ver>`), not the main checkout.
5. **Open a non-draft PR** once finished. Aim for all CI gates green before declaring done.
6. Never add `sorry`/`admit`/`native_decide`/new `axiom`/`unsafe`/`partial`/`maxHeartbeats` increases/`set_option linter.* false`/nolint waivers. **Fix the code, not the check.** Never edit `.github/workflows`, `quality.py`, lint configs, or `lakefile.toml`'s `[leanOptions]`.

## Recipe (learned from the v4.32.0-rc1 bump — see memory `v432-bump-recipe.md`)

### 0. Setup
- Confirm the tags exist upstream: `git ls-remote --tags` for `leanprover-community/mathlib4`, `leanprover/lean4`, `leanprover/doc-gen4`.
- `git worktree add -b <branch> <dir> main`.
- Bump `lean-toolchain`, `lakefile.toml` (mathlib `rev`), `docbuild/lean-toolchain`, `docbuild/lakefile.toml` (doc-gen4 `rev`).
- `lake update mathlib` then `lake exe cache get`; later `cd docbuild && lake update doc-gen4` (verify its manifest's mathlib rev matches the main one).

### 1. RAM control — CRITICAL, get this right first
- **Lake 5.0 ignores `LAKE_JOBS` and `-j`.** The only working lever is `export LEAN_NUM_THREADS=2` in `~/.zshenv` (so agent shells inherit it) — caps lake to ~3 concurrent compiles. **Remove this line at the end.**
- **The real RAM hog is the lean-lsp MCP**: each query spawns a ~3 GB `lean --worker`; under parallel agents these pile up to 30+ GB. Disable it with a persistent `pkill -9 -f 'lean-lsp-mcp'` loop (1 s) so its calls fast-fail and agents fall back to CLI. Do NOT reap only `lean --worker` — that makes an agent's in-flight MCP call hang and stalls the whole run.
- Run a watchdog Monitor on total Lean RSS; if it nears the cap, kill `v<ver>` processes and lower concurrency.

### 2. Discover breakage
- `lake build LeanPool` (capped). Bucket errors per project and per root cause.

### 3. Fix errors — parallel agent Workflow (opt-in)
- Use the **Workflow** tool: one agent per failing project, a custom `poolMap(items, k, …)` for concurrency **2–3** (the default 10 is too much RAM), `effort:'high'`, **CLI-only** (tell agents lean-lsp is disabled; use `lake build LeanPool.<P>`, `lake env lean <file>`, `rg` over `.lake/packages/mathlib`).
- Bake the hard constraints into every agent prompt. Have each return a structured summary (statementsModified, introducedForbidden).
- Recurring v4.32-era API deltas (re-derive for the new version): `coe_injective'`→`coe_injective` (SetLike/DFunLike field), `return`→`pure` in metaprogram `do`-blocks, `Set.diff_*`→`Set.sdiff_*` family, `Symmetric`→local `IsSymmetric` (Mathlib's `Symmetric` deprecated for `Std.Symm`), `@[expose] public` collisions, `defProp` `def`→`theorem`.
- Transient API "rate limited" / "session limit" failures kill whole rounds — just re-run the not-green subset. **Commit after each clean milestone** (an agent can leave the tree broken; commit = cheap recovery).

### 4. Verify + guards
- Whole-pool `lake build LeanPool` → 0 errors.
- **Drop-guard:** for each changed file, diff declaration *names* (`git show main:<f>` vs current) — any name present on main but missing now must be an intended forced rename, not a drop.
- **Forbidden scan:** `git diff main` added lines must contain no `sorry`/`admit`/`native_decide`/`maxHeartbeats`/linter-disable.

### 5. Warnings — CI fails on ANY `warning:` line
- Collect warnings from the build; run a second per-project Workflow to clear them (deprecation renames per the warning's "Use X instead", unused-simp-arg removal, no-op/never-executed tactic removal, `defProp` `def`→`theorem`, import narrowing). Rebuild to 0 warnings.

### 6. CI gates
`lake exe mk_all --check`, `lake exe runLinter LeanPool`, `lake exe lint-style LeanPool`, and `cd python && uv run python -m lean_pool.quality --repo ..`.
- **Watch the defProp × proof-size catch-22:** `def`→`theorem` can push a `Prop`'s large proof over quality.py's 200-line gate, and quality.py only delimits proofs at `theorem`/`lemma` (it lumps a following run of `def`s into the preceding theorem's count). Fix by extracting the proof's `match`/case sub-blocks into new `private lemma`s placed before the theorem, AND reordering any independent `def` block out of the measured region (before the first theorem). Proofs only — no signature changes.

### 7. PR
- The `content-pr-guard` **exempts** bump metadata: a PR may carry content (`LeanPool/**/*.lean`) alongside ONLY `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `docbuild/{lean-toolchain,lakefile.toml,lake-manifest.json}`. Anything else non-content alongside content fails the guard.
- Commit, push, `gh pr create --base main` **non-draft**. PR body: list every statement-level change (collision renames, `def`→`theorem`) with reasons, and the verification (build 0/0, all gates pass).
- **Confirm all PR checks pass on the head commit SHA** (`gh pr checks`, and verify the runs' `head_sha` == HEAD) before reporting done. Don't trust a stale CI run from an earlier failing commit.

### 8. Cleanup
- Remove the `LEAN_NUM_THREADS=2` line from `~/.zshenv`; stop the lean-lsp reaper and watchdog monitors. Offer to remove the worktree/branch.
