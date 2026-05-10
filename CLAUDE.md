This file is a concatenation of README.md and CONTRIBUTING.md.

# lean-pool

Lean Pool sits between [`mathlib`](https://github.com/leanprover-community/mathlib4) and `merely-true`, preserving Lean 4 formalizations that don't fit mathlib's scope. Instead of mathlib's high-bar human review, Lean Pool relies on deterministic linters and LLM judgment, so it can grow faster while staying sorry-free, well-typed, and pinned to the latest Mathlib.

### How it works

```
discover → lint → review → promote
```

1. **Discover** Lean packages from the [Reservoir](https://reservoir.lean-lang.org) manifest plus a hand-curated list of GitHub repos.
2. **Lint** with deterministic checks: no `sorry`/`admit`, no extra axioms beyond `Classical.choice`/`propext`/`Quot.sound`, no `unsafe`/`partial`, file headers, and size limits.
3. **Review** with an LLM against [`.github/REVIEW_RULES.md`](.github/REVIEW_RULES.md) to assess fit, significance, and code quality.
4. **Promote** accepted projects into `LeanPool/` and register them in [`LeanPool/projects.yml`](LeanPool/projects.yml).

### Key capabilities

- Manual Lean and Mathlib version bumping via [`update.yml`](.github/workflows/update.yml), which opens a PR or issue when explicitly dispatched. Scheduled update checks are future work.
- Automated PR review via [`llm-review.yml`](.github/workflows/llm-review.yml), running after Lean Action CI succeeds or when you comment `/review`.
- Proof profiling via [`proof-profile.yml`](.github/workflows/proof-profile.yml), reporting elaboration times when you comment `/profile`.
- A prototype [LeanExplore](https://leanexplore.com/) duplicate-search CLI in [`semantic_dedup.py`](python/lean_pool/semantic_dedup.py). Wiring this into PR comments is future work.

### Repository layout

| Path | Contents |
| --- | --- |
| [`LeanPool/`](LeanPool/) | The pooled Lean library. Each subfolder is one project. |
| [`LeanPool/projects.yml`](LeanPool/projects.yml) | Project registry: slug, authors, main theorem, source, tags. |
| [`python/`](python/) | Aggregation, quality, and LLM review tooling. |
| [`candidates/`](candidates/) | Candidate intake: criteria, manual list, decision log, rendered table. |
| [`.github/`](.github/) | CI workflows, code-quality gates, review rules. |
| [`scripts/`](scripts/) | Misc support files. |

### Getting started

Lean Pool requires Lean (via [`elan`](https://leanprover-community.github.io/install/), with the toolchain pinned in [`lean-toolchain`](lean-toolchain)) and Python 3.13+ with [`uv`](https://docs.astral.sh/uv/).

```bash
make setup    # pull Mathlib oleans, build LeanPool, install Python tooling
```

### Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md).

### Credits

Created as part of the [UW Lean Hackathon](https://uw2026leanhackathon.github.io/) by [Vasily Ilin](https://github.com/Vilin97) and [Justin Asher](https://github.com/justincasher).

# Contributing to Lean Pool

Lean Pool sits between `mathlib` and `merely-true` — like arXiv for formal mathematics. Contributions of all sizes are welcome.


## Finding Work

Check the [issues](https://github.com/Vilin97/lean-pool/issues) for things to work on.


## Dev Setup

### Prerequisites

- **Lean** via [elan](https://leanprover-community.github.io/install/) (toolchain pinned in `lean-toolchain`)
- **Python 3.13+**
- **[uv](https://docs.astral.sh/uv/)** (Python package manager)

### Lean

```bash
lake build
```

### Python

```bash
cd python
uv sync               # install runtime + dev (lint/format) deps
uv sync --group test  # also install test deps when running pytest
```

See [`python/README.md`](python/README.md) for common commands.


## Branch and PR Workflow

**Direct commits to `main` are not allowed by project policy.** All changes go through pull requests. Branch protection to enforce this policy is future work.

**Branch naming.** Use `yourname/description` for solo work (e.g., `justin/aggregator-draft`). Use `feature/` or `fix/` prefixes for branches where multiple people may contribute (e.g., `feature/manifest-summary`, `fix/timeout-default`).

**Open PRs early.** Push and open a PR as soon as you have something, even if incomplete. Use GitHub's draft PR feature and label with `WIP` if needed.

**Link issues.** Use `Closes #123` in the PR description to automatically close the related issue on merge.

**Commit messages.** Write clear, concise commit messages in imperative tense (e.g., "Add manifest fetcher", not "Added manifest fetcher"). Do not include AI-generated tags (e.g., "Generated with Claude", "Co-authored-by: Codex") in commits or PRs.

**Do not mix content and non-content changes.** A PR that imports a formalization or changes a project may modify **only** `LeanPool.lean` (the `mk_all` index), `LeanPool/**/*.lean`, and `LeanPool/projects.yml`. Infra / CI / tooling / doc changes may touch non-content files, but must not be bundled with content files. The PR separation CI check (`.github/workflows/content-pr-guard.yml`) enforces this.


## Linting and Testing

**Never change the checks or gates themselves.** Do not modify `.github/workflows/`, `.github/CODE_QUALITY.md`, `python/lean_pool/quality.py`, `scripts/nolints-style.txt`, the `[leanOptions]`/lint settings in `lakefile.toml`, or any other CI step, quality gate, or linter configuration — and do not add an exception or waiver of any kind (a `size-limit-ok` comment, a `nolints-style.txt` entry, `set_option linter.X false`, etc.) — unless the user has explicitly asked for that exact change. If a check fails, fix the code, not the check. This applies to everyone, and especially to AI agents working on the repo.

### Lean

CI currently runs `lake exe mk_all --check`, `lake build LeanPool`, `lake exe runLinter LeanPool`, `lake exe lint-style LeanPool`, and the repository quality checker (see [`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)). Build locally with `lake build`. Project-wide code-quality conventions and future work are documented in [`.github/CODE_QUALITY.md`](.github/CODE_QUALITY.md).

### Python

Run from `python/` before pushing:

```bash
uv run ruff check    # lint
uv run ruff format   # format
```

When you add Python code, add tests under `python/tests/` and run them with:

```bash
uv run --group test pytest
```


## Coding Guidelines

### General

**Naming.** Avoid abbreviations in variable, function, and class names. Use full words for clarity (e.g., `configuration` not `config`, `manifest` not `mfst`).

**Comments.** Add inline comments only when the *why* is non-obvious — a hidden constraint, a subtle invariant, or a workaround. Don't restate what the code does.

**Functions.** Keep function bodies under 40 lines (soft limit). Write self-documenting code with descriptive variable and function names.

**Logging.** Use loggers, not `print` statements, in library code. CLI entry points may print user-facing output.

### Python

**Absolute imports.** Use absolute imports throughout (e.g., `from lean_pool.aggregator.reservoir import fetch_manifest`). All imports must be at the top of the file.

**Type hints.** Use modern Python type hints (PEP 604 and PEP 585): `|` instead of `Union`, `| None` instead of `Optional`, and built-in collection types (`list`, `dict`, `set`, `tuple`) instead of their `typing` equivalents.

**Documentation.** Every module must have a module-level docstring. Every non-trivial function must have a Google-style docstring.

### Lean

See [`.github/CODE_QUALITY.md`](.github/CODE_QUALITY.md) for the full list of automated checks and conventions.
