---
name: version-bump-project
description: Repair a SINGLE Lean Pool project's build against a new Lean/Mathlib release. Used by the mathlib-bump workflow's repair fan-out, one job per broken project. Use when asked to fix one project (not the whole pool) for a target version.
argument-hint: <Project> <target-version> e.g. Polytopes v4.33.0-rc1
---

# Repair one project for a new Mathlib release

Fix **only** `LeanPool/<Project>` so that `lake build LeanPool.<Project>`
succeeds with **zero errors and zero warnings** under the target release. The
project and version are the arguments; if either is missing, stop and say so.

This runs headless in CI with no reviewer present. The whole-pool equivalent is
the `version-bump` skill; this is its per-project unit of work. Pool projects
never import each other, so your project is independent of every other repair
running in parallel — never edit outside your project's directory.

## Hard constraints (never violate)

1. **No statement drops.** Every `theorem`/`lemma`/`def`/`instance`/`structure`/
   `inductive`/`class`/`abbrev` that exists now must still exist when you finish.
   A statement that Mathlib has since absorbed is *still* not yours to delete —
   leave it and note it in your summary; that call belongs to the reviewer.
2. **Change a statement only when the statement itself does not compile** under
   the target (a renamed or removed Mathlib symbol in its type, or a name that
   now collides with a new Mathlib declaration). Then make the *minimal*
   meaning-preserving change — usually a rename that keeps the statement and
   proof intact. Everything else: change proof bodies, tactics, and syntax only.
   A `def` → `theorem` keyword change for a `Prop`-valued declaration flagged by
   the `defProp` linter is allowed (same statement).
3. **Never** add `sorry`, `admit`, `native_decide`, a new `axiom`, `unsafe`,
   `partial`, a `maxHeartbeats`/`maxRecDepth` increase, `set_option linter.* false`,
   or any nolint waiver. **Fix the code, not the check.** These are enforced by
   `python/lean_pool/quality.py` on the assembled branch, so adding one does not
   get the bump merged — it just wastes the run.
4. **Never** edit `.github/`, `python/lean_pool/quality.py`, lint configs,
   `lakefile.toml`'s `[leanOptions]`, `lean-toolchain`, or any file outside
   `LeanPool/<Project>/` (and `LeanPool/<Project>.lean` if it exists).
5. **Do not** commit, push, or open a PR. The workflow captures your working
   tree as a patch and assembles it. Just leave the files fixed on disk.

## Environment

- The toolchain and Mathlib cache are already installed; `lake exe cache get`
  has run. The pins are already at the target version.
- **CLI only — the lean-lsp MCP is not available.** Use:
  - `lake build LeanPool.<Project>` to check your work (this is the ground truth)
  - `lake env lean <file>` to check a single file quickly
  - `rg <pattern> .lake/packages/mathlib` to find what a symbol was renamed to
- `diagnostics.txt` in the working directory holds the exact errors this project
  produced during the probe build. Start there.

## Recipe

1. **Read `diagnostics.txt`** and bucket the errors by root cause. Most projects
   fail for one or two reasons repeated many times, not N independent reasons.
2. **Identify each root cause in Mathlib.** For a renamed lemma, `rg` the old
   name in `.lake/packages/mathlib` — deprecation aliases usually carry a
   `Use X instead` note naming the replacement. Trust the deprecation note over
   a guess.
3. **Apply the minimal fix** across the project. Prefer a mechanical rename over
   a proof rewrite; prefer a proof rewrite over any signature change.
4. **Rebuild** with `lake build LeanPool.<Project>` until there are no errors.
5. **Clear warnings too** — CI fails on any `warning:` line. Typical sources:
   deprecation renames (do what the warning says), unused `simp` arguments,
   no-op or never-executed tactics, and the `defProp` `def` → `theorem` case.
6. **Self-check before finishing:**
   - `git diff` — is every changed file inside your project?
   - Diff declaration *names* against the base revision. Anything present before
     and missing now is a violation of constraint 1 unless it was a forced
     rename you can justify.
   - `git diff | rg 'sorry|admit|native_decide|maxHeartbeats|set_option linter'`
     must be empty.

## Report

Finish with a short structured summary — it is the return value, not a message
to a human:

```
project: <Project>
status: clean | errors-remain | warnings-remain
root_causes: <one line each>
statements_modified: <qualified name + why, or "none">
absorbed_by_mathlib: <declarations that now duplicate Mathlib, or "none">
notes: <anything the reviewer must check by hand>
```

If you cannot get the project clean, say so plainly in `status` and report what
remains. A partial, honest repair is useful; a green report that is not green is
not. Never disable a check to make the build pass.
