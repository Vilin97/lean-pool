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

Direct commits to `main` are not allowed. All changes go through pull requests.

**Branch naming.** Use `yourname/description` for solo work (e.g., `justin/aggregator-draft`). Use `feature/` or `fix/` prefixes for branches where multiple people may contribute (e.g., `feature/manifest-summary`, `fix/timeout-default`).

**Open PRs early.** Push and open a PR as soon as you have something, even if incomplete. Use GitHub's draft PR feature and label with `WIP` if needed.

**Link issues.** Use `Closes #123` in the PR description to automatically close the related issue on merge.

**Commit messages.** Write clear, concise commit messages in imperative tense (e.g., "Add manifest fetcher", not "Added manifest fetcher"). Do not include AI-generated tags (e.g., "Generated with Claude", "Co-authored-by: Codex") in commits or PRs.

**Review and merge.** All PRs require at least one review from another contributor before merging.


## Linting and Testing

### Lean

CI currently runs `lake exe mk_all --check`, `lake build LeanPool`, and `lake exe runLinter LeanPool` (see [`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)). Build locally with `lake build`. Project-wide code-quality conventions and planned automated checks are documented in [`.github/CODE_QUALITY.md`](.github/CODE_QUALITY.md); many are roadmap items not yet enforced in CI.

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
