# Import notes: ramanujan-tau-misses-primes

Source: <https://github.com/AxiomMath/ramanujan-tau-misses-primes>
(paper [arXiv:2603.29970](https://arxiv.org/abs/2603.29970)).

## License

Upstream is MIT-licensed (`LICENSE`, "Copyright (c) 2026 Axiom Math."), which is
compatible with Lean Pool's Apache-2.0 licensing; the vendored files carry the
standard Lean Pool Apache-2.0 header attributing the upstream authors (Evan Chen,
Kenny Lau, Ken Ono, Jujian Zhang).

## Files vendored

- `RamanujanTauMissesPrimes/solution.lean` → `LeanPool/RamanujanTauMissesPrimes/Solution.lean`

`RamanujanTauMissesPrimes/problem.lean` (the upstream problem-statement file) was
**not** vendored: it contains `sorry`s by design — it is only the unproven task
statement — and `solution.lean` is self-contained (it redefines every relevant
declaration), so nothing depends on it. The `input/` directory (TeX sources, task
spec) is not Lean content and was not vendored.

## Port (Lean v4.26.0 → v4.30.0-rc2 / current Mathlib)

- Replaced the broad `import Mathlib` with the specific Mathlib modules used.
- Stripped the upstream `set_option linter.* false in` directives and fixed the
  underlying lints (unused `simp` arguments, `<;>` over single goals,
  `simp ... at` → `simp only ... at`, etc.).
- Renamed several upstream identifiers/lemmas to their current Mathlib names
  (e.g. `Set.eq_empty_of_forall_not_mem` → `Set.eq_empty_of_forall_notMem`,
  `le_or_lt` → `le_or_gt`, `push_neg` → `push Not`, `refine'` → `refine`).
- Added module/declaration documentation strings required by `runLinter`
  (`docBlame`); wrapped over-long lines; replaced `open scoped Classical` with
  localized `open Classical in` on the three definitions that need it.

No `sorry`/`admit`, no extra axioms, and no `unsafe`/`partial`/`opaque`/`@[extern]`
in the vendored file; `main_theorem`, `reduction_lemma`, `abc_bound_E2`,
`abc_bound_E4` all type-check.
