# Contributing to Lean Pool

Lean Pool welcomes serious, medium- to large-scale formalizations of mathematics and related disciplines (see [`MOTIVATION.md`](MOTIVATION.md)). Browse [`LeanPool/`](LeanPool/) for examples and [`candidates/CRITERIA.txt`](candidates/CRITERIA.txt) for what we include.

## Opt out

If you would like to withdraw your project from Lean Pool, open an issue.

## Submitting a project

There are two paths:

- **Propose a repo.** Open an issue with the GitHub URL and a maintainer can import it. Repos that Reservoir does not index can be added to [`candidates/manual.txt`](candidates/manual.txt).
- **Open a content PR.** Add your project under `LeanPool/<YourProject>/`, register it in [`LeanPool/projects.yml`](LeanPool/projects.yml) — the card must declare `provenance` (`human`, `AI`, or `mix`; see below) — and regenerate the index with `lake exe mk_all`.

Either way the result must pass CI (build, linters, and quality checks — see [Linting and testing](#linting-and-testing)) and an [LLM review](.github/REVIEW_RULES.md) of fit and significance. Accepted projects must be `sorry`-free, introduce no axioms beyond `Classical.choice`/`propext`/`Quot.sound`, and avoid `unsafe`/`partial`. Each project card must also declare its **provenance** — who wrote the Lean proofs — as `human` (written by people), `AI` (mostly produced by an AI system), or `mix` (both contributed substantially). (Proof profiling via `/profile` is available but informational, not a gate: added files get an absolute profile, while modified files get a base→head compile-cost comparison — useful for checking that a refactor doesn't regress compile time.)

## Challenge mode

A **challenge** is the mirror image of a project: instead of a finished proof, it is an open *statement* — a theorem written in Mathlib vocabulary, left as `sorry`, that the pool is asking someone to prove. Challenges live in [`Challenge/`](Challenge/), the only place in the repository where `sorry` is allowed. Browse the board with `make challenges`.

Anyone can submit one. Open a content PR that adds:

- `Challenge/<YourChallenge>.lean` — the statement, with the standard four-line file header, imports **only** from `Mathlib.*`, and each open declaration proved by exactly `:= sorry`;
- an entry in [`Challenge/challenges.yml`](Challenge/challenges.yml) — `slug`, `title`, `summary`, `branch`, `entry_module`, `proposers`, `source`, `license`, `provenance`, `status: open`, `statements` (each with a `declaration` and its `informal` English statement), `tags`, `msc`, plus optional `definitions` (definition holes) and `estimated_lines`;
- the regenerated indexes: `lake exe mk_all` and `cd python && uv run python -m lean_pool.quality --repo .. --write-challenge-cards`.

The gates then enforce that the board stays honest: `sorry` appears only as the whole proof body of a declaration the registry lists, every *other* declaration in the file is closed (checked with `#print axioms`, so scaffolding can't hide behind an open statement), the registered statements really are open, imports are Mathlib-only, and the generated card matches the registry. Everything else — headers, `set_option`, axioms, the option-backdoor audit, size caps — applies exactly as it does to pooled projects.

A challenge PR gets its own [LLM review](.github/CHALLENGE_REVIEW_RULES.md), which asks a different question than the project review: is the problem significant (both informally and as formalized), does the Lean statement faithfully say what the prose says, does a cited known result match its source, is the statement vacuous or gameable, and roughly how many lines of Lean would a solution take.

## Solving a challenge

A challenge statement never changes once merged: it is the text every solution is judged against. So a solution goes in [`Solution/`](Solution/) as its own module, which **restates** the statement under the same name and proves it. It must not import the challenge module — comparator exports the two environments separately and checks that the statements agree, and importing would defeat exactly that check (a gate enforces it).

Open a content PR that adds `Solution/<Challenge>.lean` and flips the registry entry to `status: solved` with a `solution:` block (`module:`, plus optional `authors:`, `project:`, and `verified:`), then regenerate the index and cards. A solution that needs real work should prove it in a pooled project under `LeanPool/` and leave a thin bridge here.

Correctness is decided by [`leanprover/comparator`](https://github.com/leanprover/comparator), which replays the solution through the Lean kernel and checks that it proves *the same* statement with no axiom beyond `propext`/`Quot.sound`/`Classical.choice`. [`challenge-verify.yml`](.github/workflows/challenge-verify.yml) runs it on every solved challenge in CI, with `landrun`, `lean4export`, and comparator pinned to exact commits. Locally:

```bash
make comparator                       # one-time: build the judge
make verify-challenge C=<slug>        # replay a solution
```

`make comparator` also builds a `lean4export` at this repository's toolchain (comparator pins a newer one, which cannot read our oleans). Sandboxing needs [`landrun`](https://github.com/Zouuup/landrun), which is Linux-only; elsewhere pass `--insecure-no-sandbox` to `scripts/challenge/verify-solution.sh` and understand that compiling a solution runs its code. `python -m lean_pool.challenge config <slug>` prints the JSON configuration if you want to drive comparator yourself.

A failed verification is loud rather than tidy: a solution missing the theorem ends in a `lean4export` panic ("Constant … not found in environment"), a weakened statement in `Challenge and solution theorem statement do not match`, and one that still leans on `sorry` in `Illegal axiom detected: 'sorryAx'`. All are rejections — the script exits non-zero and prints the `Verified:` line only on success.

Because a kernel decides correctness, the [solution review](.github/SOLUTION_REVIEW_RULES.md) is deliberately thin, and is skipped altogether when the PR touches nothing but the answer, the generated index, and the registry entry. It runs when there is something a machine cannot settle: a definition hole, a pooled project to judge as a project, or anything else in the diff. Editing a challenge statement in the same PR as a solution is rejected outright by the PR guard.

**Definition holes.** A challenge may leave a `def ... := sorry` for the solver to fill in (register it under `definitions:`). Comparator only checks that the name, type, universes, and safety level match, so a hole can be gamed — a solution may define it in terms of the very object the challenge asks about. Holes always need human review on top of a green comparator run.

## Dev setup

Requires Lean (via [`elan`](https://leanprover-community.github.io/install/), with the toolchain pinned in [`lean-toolchain`](lean-toolchain)) and Python 3.13+ with [`uv`](https://docs.astral.sh/uv/).

```bash
make setup            # pull Mathlib oleans, build the whole pool (~1.5h), install Python tooling
cd python && uv sync  # Python tooling only; add `--group test` for pytest
```

`make setup` builds every project in the pool, which takes about 1.5 hours from cold. **You almost never need that.** The projects are independent — none imports another — so to work on one project you only need Mathlib's prebuilt oleans plus your own project:

```bash
lake exe cache get                # prebuilt Mathlib oleans (fast)
lake build LeanPool.YourProject   # builds only your project — minutes, not hours
# or: make build-project P=YourProject
lake build Challenge              # the whole challenge board — seconds
```

The whole-library checks (`lake exe runLinter LeanPool`, `lake exe lint-style LeanPool`, the quality checker) do need the full pool built, but CI runs them on your PR — you don't have to reproduce them locally.

## Pull requests

- **Don't mix content and non-content changes.** A content PR may modify **only** `LeanPool.lean`, `LeanPool/**/*.lean`, `LeanPool/projects.yml`, `Challenge.lean`, `Challenge/**/*.lean`, `Challenge/challenges.yml`, `Solution.lean`, and `Solution/**/*.lean`. Infra / CI / tooling / doc changes may touch other files, but must not be bundled with content. The same guard rejects a PR that edits a challenge statement alongside a solution. Both are enforced by [`content-pr-guard.yml`](.github/workflows/content-pr-guard.yml).
- **Never change the checks or gates.** Do not modify `.github/workflows/`, `.github/CODE_QUALITY.md`, `python/lean_pool/quality.py`, `scripts/nolints-style.txt`, the `[leanOptions]`/lint settings in `lakefile.toml`, or any other CI step or linter config — and do not add a waiver of any kind (a `size-limit-ok` comment, a `nolints-style.txt` entry, `set_option linter.X false`, etc.) — unless explicitly asked. If a check fails, fix the code, not the check. This applies to everyone, and especially to AI agents.
- **Branches.** `yourname/description` for solo work; `feature/`/`fix/` prefixes when shared. Open PRs early (draft + `WIP` is fine) and use `Closes #123` to link issues.

## Linting and testing

**Lean.** CI runs `lake exe mk_all --check`, `lake build LeanPool`, `scripts/ci/build-challenges.sh` (the `Challenge`/`Solution` build, where only the expected `sorry` notices are tolerated), `lake exe runLinter` and `lake exe lint-style` on all three libraries, the quality checker (see [`lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)), and comparator on every solved challenge (see [`challenge-verify.yml`](.github/workflows/challenge-verify.yml)). Conventions live in [`.github/CODE_QUALITY.md`](.github/CODE_QUALITY.md).

**Python.** From `python/`: `uv run ruff check`, `uv run ruff format`, and `uv run --group test pytest`.

## Coding guidelines

- **Naming.** Full words, not abbreviations (`configuration`, not `config`).
- **Comments.** Only when the *why* is non-obvious; don't restate what the code does.
- **Functions.** Keep bodies under ~40 lines; write self-documenting code.
- **Logging.** Use loggers in library code; CLI entry points may print user-facing output.
- **Python.** Absolute imports at the top of the file; modern type hints (`|`, built-in `list`/`dict`); module-level and Google-style function docstrings.
- **Lean.** See [`.github/CODE_QUALITY.md`](.github/CODE_QUALITY.md).
