# Import notes: `erdos1196`

Source: <https://github.com/math-inc/Erdos1196> (Apache-2.0 — compatible with Lean Pool).

Vendored the full Lean development `PrimitiveSetsAboveX/` (13 files) into
`LeanPool/Erdos1196/`. It formalizes Erdős Problem #1196: every primitive set
`A ⊆ ℕ ∩ [x, ∞)` satisfies `∑_{a ∈ A} 1 / (a log a) ≤ 1 + O(1 / log x)` as
`x → ∞`. Main results: `PrimitiveSetsAboveX.mainTheorem` and the
`formal-conjectures`-style `Erdos1196.erdos_1196`. Both depend only on the
permitted axioms (`propext`, `Classical.choice`, `Quot.sound`). No file was
excluded; no `sorry`/`admit`/`axiom` upstream.

## Changes applied during the import

- **Toolchain bump** `leanprover/lean4:v4.30.0-rc1` → `v4.30.0-rc2` (Lean Pool's
  pin). No proof repairs were needed — the two release candidates are
  compatible.
- **Module system stripped.** Upstream used the new `module` / `public import` /
  `@[expose] public section` syntax; rewritten to plain `import` (no `module`
  header, no `public` section) to match the existing Lean Pool convention.
  Semantically a no-op (non-module files expose everything by default).
- **Header.** Prepended the standard four-line Lean Pool copyright header to every
  file (year 2026, author "Math Inc." — the upstream repository carries no
  individual author names; the development was produced by Math Inc.).
- **Imports.** Internal `import PrimitiveSetsAboveX.X` rewritten to
  `import LeanPool.Erdos1196.X`. Upstream already used precise Mathlib imports
  (no broad `import Mathlib`).
- **Diagnostics.** Removed the lone `#print axioms` command from `Main.lean`.
- **Namespace restructuring in `HitMass.lean`.** Four declarations were written
  with dotted names (`MarkovLayer.kernelRowBound`,
  `PrimitiveSet.{firstHitMassAtStep_eq_tsum_indicator_arrivalMass,
  tsum_indicator_ofReal_visitProbability_eq_visitMass,
  summable_indicator_visitProbability_and_tsum_le_one_of_visitMass_le_one}`)
  inside `namespace PrimitiveSetsAboveX`. They are now placed inside explicit
  nested `namespace MarkovLayer` / `namespace PrimitiveSet` blocks instead. The
  fully-qualified names (and hence dot-notation use, e.g. `chain.kernelRowBound`)
  are unchanged; this only makes the repository quality checker's namespace
  bookkeeping resolve them correctly.

The original `PrimitiveSetsAboveX.lean` umbrella file is not vendored verbatim;
its role is taken by `LeanPool/Erdos1196.lean`, which imports the same public
modules and carries the generated project card.
