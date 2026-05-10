# lean-pool

> [!NOTE]
> **Lean Pool is arXiv for formal mathematics.** It sits between [`mathlib`](https://github.com/leanprover-community/mathlib4) and `merely-true` — preserving Lean 4 formalizations of papers and projects that don't fit mathlib's scope but deserve a durable, compilable home.

A bottleneck on mathlib's growth is high-quality human review. Lean Pool replaces most of that review with a layered system of deterministic linters and LLM judgment, so the pool can grow much faster while staying sorry-free, well-typed, and pinned to the latest Mathlib.

## What's in the pool

| Project | Source | One-liner |
| --- | --- | --- |
| [`RamanujanTauMissesPrimes`](LeanPool/RamanujanTauMissesPrimes.lean) | [arXiv:2603.29970](https://arxiv.org/abs/2603.29970) | ABC implies Ramanujan's τ misses almost all primes. |
| [`FelConjecture`](LeanPool/FelConjecture.lean) | [arXiv:2602.03716](https://arxiv.org/abs/2602.03716) | Fel's conjecture on syzygies of numerical semigroups. |
| [`ArchonFirstProofResults`](LeanPool/ArchonFirstProofResults.lean) | [frenzymath/Archon-FirstProof-Results](https://github.com/frenzymath/Archon-FirstProof-Results) | A harmonic-mean inequality for real-rooted polynomials, plus ε-light vertex subsets via the Batson–Spielman–Srivastava barrier method. |

The full registry — slugs, authors, main theorems, tags — lives in [`LeanPool/projects.yml`](LeanPool/projects.yml).

## How it works

> [!TIP]
> If you only read one section, read this one.

```
Reservoir + manual list  →  shallow clone  →  linters  →  LLM review  →  candidates table  →  promote to LeanPool/
```

1. **Discover.** [`reservoir.py`](python/lean_pool/aggregator/reservoir.py) pulls the [Reservoir](https://reservoir.lean-lang.org) manifest of Lean packages. [`manual.py`](python/lean_pool/aggregator/manual.py) supplements it with hand-curated GitHub repos that Reservoir misses (no `lake-manifest.json`, low star count, etc.).
2. **Clone.** [`cloner.py`](python/lean_pool/aggregator/cloner.py) shallow-clones each candidate into `candidates/raw_data/clones/`.
3. **Lint.** [`quality.py`](python/lean_pool/quality.py) runs deterministic checks — no `sorry`/`admit`, no extra axioms beyond `Classical.choice`/`propext`/`Quot.sound`, no `unsafe`/`partial`, header format, size limits, schema validation for `projects.yml`.
4. **Review.** [`review.py`](python/lean_pool/review.py) calls an LLM against [`.github/REVIEW_RULES.md`](.github/REVIEW_RULES.md) to assess fit, significance, and code quality — the judgment calls a linter can't make.
5. **Render.** [`render.py`](python/lean_pool/aggregator/render.py) regenerates [`candidates/README.md`](candidates/README.md) as a filterable table of every reviewed repo.
6. **Promote.** Accepted projects are vendored into `LeanPool/` and registered in `projects.yml`. They build alongside everything else against the pinned Mathlib version.

## Key capabilities

- **Automatic Lean and Mathlib version bumping** — [`update.yml`](.github/workflows/update.yml) opens a PR when a new Mathlib release lands.
- **Automated PR review** — [`llm-review.yml`](.github/workflows/llm-review.yml) runs on PR open or by typing `/review` in a comment.
- **Proof profiling** — [`proof-profile.yml`](.github/workflows/proof-profile.yml) reports elaboration times when you comment `/profile`.
- **Docs and search** — pooled declarations are reachable through [LeanExplore](https://leanexplore.com/), and [`semantic_dedup.py`](python/lean_pool/semantic_dedup.py) flags candidates that duplicate existing results.

## Repository layout

| Path | Contents |
| --- | --- |
| [`LeanPool/`](LeanPool/) | The pooled Lean library. Each subfolder is one project. |
| [`LeanPool/projects.yml`](LeanPool/projects.yml) | Project registry — slug, authors, main theorem, source, tags. |
| [`python/`](python/) | Aggregation, quality, and LLM review tooling. |
| [`candidates/`](candidates/) | Candidate intake — criteria, manual list, decision log, rendered table. |
| [`.github/`](.github/) | CI workflows, code-quality gates, review rules. |
| [`scripts/`](scripts/) | Misc support files. |

## Getting started

> [!IMPORTANT]
> Lean Pool requires Lean (via [`elan`](https://leanprover-community.github.io/install/), with the toolchain pinned in [`lean-toolchain`](lean-toolchain)) and Python 3.13+ with [`uv`](https://docs.astral.sh/uv/).

```bash
lake build                 # build the Lean library
cd python && uv sync       # install Python tooling
```

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the full dev setup, branch and PR workflow, and coding guidelines.

## Contributing

> [!CAUTION]
> Direct commits to `main` are not allowed. Every change goes through a pull request and at least one review.

Open PRs early (drafts welcome), use `yourname/description` branch names for solo work, and write commit messages in imperative tense. Full guidelines in [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Credits

Created as part of the [UW Lean Hackathon](https://uw2026leanhackathon.github.io/) by [Vasily Ilin](https://github.com/Vilin97) and [Justin Asher](https://github.com/justincasher).
