<p align="center">
  <img src="logo.png" alt="Lean Pool logo" width="240">
</p>

# lean-pool

[![Lean Action CI](https://github.com/Vilin97/lean-pool/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Vilin97/lean-pool/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/docs-online-blue)](https://vilin97.github.io/lean-pool/)
[![License](https://img.shields.io/github/license/Vilin97/lean-pool)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20513444.svg)](https://doi.org/10.5281/zenodo.20513444)

Lean Pool sits between [`mathlib`](https://github.com/leanprover-community/mathlib4) and [`merely-true`](https://github.com/merely-true/merely-true), preserving Lean 4 formalizations that don't fit mathlib's scope. Instead of mathlib's high-bar human review, it relies on deterministic linters and LLM judgment, so it can grow faster while staying `sorry`-free and pinned to the latest Mathlib. See [`MOTIVATION.md`](MOTIVATION.md) for the why, and browse the API docs at <https://vilin97.github.io/lean-pool/>.

So far, projects have been added by hand: each is a suitable, permissively licensed (Apache-2.0 or MIT) Lean repository, bumped to the latest Lean and Mathlib, made to pass [CI](.github/workflows/lean_action_ci.yml) — it builds warning-free and clears Mathlib's linters, the style checker, and the repository quality gates (no `sorry`/`admit`, no axioms beyond `Classical.choice`/`propext`/`Quot.sound`, no `unsafe`/`partial`, file headers, size limits) — and an [LLM review](.github/REVIEW_RULES.md) of fit and significance, then merged.

### Getting started

Requires Lean (via [`elan`](https://leanprover-community.github.io/install/), with the toolchain pinned in [`lean-toolchain`](lean-toolchain)) and Python 3.13+ with [`uv`](https://docs.astral.sh/uv/).

```bash
make setup    # pull Mathlib oleans, build LeanPool, install Python tooling
```

### Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md).

### Credits

Created as part of the [UW Lean Hackathon](https://uw2026leanhackathon.github.io/) by [Vasily Ilin](https://github.com/Vilin97) and [Justin Asher](https://github.com/justincasher).
