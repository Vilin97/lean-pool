<p align="center">
  <img src="logo.png" alt="Lean Pool logo" width="240">
</p>

# lean-pool

Lean Pool sits between [`mathlib`](https://github.com/leanprover-community/mathlib4) and `merely-true`, preserving Lean 4 formalizations that don't fit mathlib's scope. Instead of mathlib's high-bar human review, Lean Pool relies on deterministic linters and LLM judgment, so it can grow faster while staying sorry-free, well-typed, and pinned to the latest Mathlib.

Browse the generated API documentation at <https://vilin97.github.io/lean-pool/>.

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
