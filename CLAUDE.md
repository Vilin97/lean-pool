This file is a concatenation of README.md and CONTRIBUTING.md.

<p align="center">
  <img src="logo.png" alt="Lean Pool logo" width="240">
</p>

# lean-pool

[![Lean Action CI](https://github.com/Vilin97/lean-pool/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Vilin97/lean-pool/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/docs-online-blue)](https://vilin97.github.io/lean-pool/)
[![License](https://img.shields.io/github/license/Vilin97/lean-pool)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20513444.svg)](https://doi.org/10.5281/zenodo.20513444)

Lean Pool sits between [`mathlib`](https://github.com/leanprover-community/mathlib4) and [`merely-true`](https://github.com/merely-true/merely-true), preserving Lean 4 formalizations that don't fit mathlib's scope. Instead of mathlib's high-bar human review, it relies on deterministic linters and LLM judgment, so it can grow faster while staying `sorry`-free and pinned to the latest Mathlib. See [`MOTIVATION.md`](MOTIVATION.md) for the why, and browse the API docs at <https://vilin97.github.io/lean-pool/>.

<!-- BEGIN STATS -->
**92** formalization projects · **637,028** lines of Lean
<!-- END STATS -->

<sub>(stats above are refreshed automatically by [`readme-stats.yml`](.github/workflows/readme-stats.yml) — edit [`python/lean_pool/stats.py`](python/lean_pool/stats.py), not the numbers)</sub>

So far, projects have been added by hand: each is a suitable, permissively licensed (Apache-2.0 or MIT) Lean repository, bumped to the latest Lean and Mathlib, made to pass [CI](.github/workflows/lean_action_ci.yml) — it builds warning-free and clears Mathlib's linters, the style checker, and the repository quality gates (no `sorry`/`admit`, no axioms beyond `Classical.choice`/`propext`/`Quot.sound`, no `unsafe`/`partial`, file headers, size limits) — and an [LLM review](.github/REVIEW_RULES.md) of fit and significance, then merged.

### Getting started

Requires Lean (via [`elan`](https://leanprover-community.github.io/install/), with the toolchain pinned in [`lean-toolchain`](lean-toolchain)) and Python 3.13+ with [`uv`](https://docs.astral.sh/uv/).

```bash
make setup    # pull Mathlib oleans, build the whole pool (~1.5h), install Python tooling
```

To work on a single project you don't need the whole pool built — see the
[fast per-project build](CONTRIBUTING.md#dev-setup) in `CONTRIBUTING.md`.

### Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md).

### Credits

Created as part of the [UW Lean Hackathon](https://uw2026leanhackathon.github.io/) by [Vasily Ilin](https://github.com/Vilin97) and [Justin Asher](https://github.com/justincasher).

# Contributing to Lean Pool

Lean Pool welcomes serious, medium- to large-scale formalizations of mathematics and related disciplines (see [`MOTIVATION.md`](MOTIVATION.md)). Browse [`LeanPool/`](LeanPool/) for examples and [`candidates/CRITERIA.txt`](candidates/CRITERIA.txt) for what we include.

## Opt out

If you would like to withdraw your project from Lean Pool, open an issue.

## Submitting a project

There are two paths:

- **Propose a repo.** Open an issue with the GitHub URL and a maintainer can import it. Repos that Reservoir does not index can be added to [`candidates/manual.txt`](candidates/manual.txt).
- **Open a content PR.** Add your project under `LeanPool/<YourProject>/`, register it in [`LeanPool/projects.yml`](LeanPool/projects.yml), and regenerate the index with `lake exe mk_all`.

Either way the result must pass CI (build, linters, and quality checks — see [Linting and testing](#linting-and-testing)) and an [LLM review](.github/REVIEW_RULES.md) of fit and significance. Accepted projects must be `sorry`-free, introduce no axioms beyond `Classical.choice`/`propext`/`Quot.sound`, and avoid `unsafe`/`partial`. (Proof profiling via `/profile` is available but informational, not a gate.)

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
```

The whole-library checks (`lake exe runLinter LeanPool`, `lake exe lint-style LeanPool`, the quality checker) do need the full pool built, but CI runs them on your PR — you don't have to reproduce them locally.

## Pull requests

- **Don't mix content and non-content changes.** A content PR may modify **only** `LeanPool.lean`, `LeanPool/**/*.lean`, and `LeanPool/projects.yml`. Infra / CI / tooling / doc changes may touch other files, but must not be bundled with content. This is enforced by [`content-pr-guard.yml`](.github/workflows/content-pr-guard.yml).
- **Never change the checks or gates.** Do not modify `.github/workflows/`, `.github/CODE_QUALITY.md`, `python/lean_pool/quality.py`, `scripts/nolints-style.txt`, the `[leanOptions]`/lint settings in `lakefile.toml`, or any other CI step or linter config — and do not add a waiver of any kind (a `size-limit-ok` comment, a `nolints-style.txt` entry, `set_option linter.X false`, etc.) — unless explicitly asked. If a check fails, fix the code, not the check. This applies to everyone, and especially to AI agents.
- **Branches.** `yourname/description` for solo work; `feature/`/`fix/` prefixes when shared. Open PRs early (draft + `WIP` is fine) and use `Closes #123` to link issues.

## Linting and testing

**Lean.** CI runs `lake exe mk_all --check`, `lake build LeanPool`, `lake exe runLinter LeanPool`, `lake exe lint-style LeanPool`, and the quality checker (see [`lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)). Conventions live in [`.github/CODE_QUALITY.md`](.github/CODE_QUALITY.md).

**Python.** From `python/`: `uv run ruff check`, `uv run ruff format`, and `uv run --group test pytest`.

## Coding guidelines

- **Naming.** Full words, not abbreviations (`configuration`, not `config`).
- **Comments.** Only when the *why* is non-obvious; don't restate what the code does.
- **Functions.** Keep bodies under ~40 lines; write self-documenting code.
- **Logging.** Use loggers in library code; CLI entry points may print user-facing output.
- **Python.** Absolute imports at the top of the file; modern type hints (`|`, built-in `list`/`dict`); module-level and Google-style function docstrings.
- **Lean.** See [`.github/CODE_QUALITY.md`](.github/CODE_QUALITY.md).
