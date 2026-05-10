# Import notes — lattice-triangle

Imported from <https://github.com/AxiomMath/lattice-triangle> ("On the paucity of
lattice triangles", accompanying [arXiv:2603.23928](https://arxiv.org/abs/2603.23928)).

## License

Upstream is MIT-licensed (`Copyright (c) 2026 Axiom Math.`), which is compatible
with Lean Pool's Apache-2.0 license. Vendored file headers use the Lean Pool
Apache-2.0 header with the upstream authors (Evan Chen, Kenny Lau, Ken Ono,
Jujian Zhang).

## What was vendored

- `LatticeTriangle/solution.lean` → `LeanPool/LatticeTriangle/Solution.lean`.

`LatticeTriangle/problem.lean` was **not** vendored: it only restates the main
theorem with a `sorry`, and `solution.lean` is self-contained — it re-declares
every definition and proves `analyticEngine_lower_bound` with no `sorry`s.
No file was excluded for technical reasons.

## Porting work (Lean v4.26.0 → v4.30.0-rc2)

The upstream solution compiled against the new toolchain with no Mathlib API
breakage. The bulk of the work was bringing it up to Lean Pool's quality gates:

- Stripped all `set_option linter.* false` directives and fixed the warnings
  they were suppressing: unused variables / unused `simp` arguments,
  `tac1 <;> tac2` where `tac1; tac2` suffices, lines over 100 characters,
  blank lines inside proofs, `refine'` / `induction'` / `cases'`, the `show`
  tactic where `change` is wanted, and `simp [...]` followed by a rigid tactic
  (rewritten to `simp only [...]` or to a `simp`-free form).
- Fixed deprecations surfaced by the bump: `push_neg` → `push Not`,
  `Set.ncard_image_of_injOn` → `Set.InjOn.ncard_image`.
- Replaced `import Mathlib` with the specific Mathlib modules actually used.
- Added documentation strings to the top-level definitions.
- A few "kitchen sink" auto-generated proofs (`re_complex_lhs_eq_real_lhs`,
  `exponent_algebra`, the bounds in `mq_bounds`, the `calc` in
  `zmod_eq_zero_forward`) were replaced with short direct proofs.

All of `lake exe mk_all --check`, `lake build LeanPool` (warning-free),
`lake exe runLinter LeanPool`, `lake exe lint-style LeanPool`, and
`python -m lean_pool.quality --repo ..` pass.
