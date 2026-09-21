/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.MaxDifference

/-!
# The maximal difference theorem for s-numbers — proofs

This module is the *Solution* of a Palomar submission. Comparator checks that
every declaration named in `comparator.json` has, in this module's environment,
exactly the same name and type as its counterpart in
`PalomarChallenges.MaxDifference`, and that it uses no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`.

Nothing is declared here. The advertised statements

* `SNumbers.approximationNumber_le_mul_hilbertNumber` —
  `aₙ(S) ≤ ((n+1)^{n+1}/nⁿ) · hₙ(S)`,
* `SNumbers.approximationNumber_le_e_mul_hilbertNumber` —
  `aₙ(S) ≤ e · (n+1) · hₙ(S)`,

and the definitions they rest on — `ContinuousLinearMap.rank`,
`SNumbers.approximationSet`, `SNumbers.approximationNumber`, `SNumbers.L2`,
`SNumbers.hilbertSet`, `SNumbers.hilbertNumber` — all arrive through the import
above, under their own names in the development: from `SNumbers/Basic.lean`,
`SNumbers/Approximation.lean`, `SNumbers/Hilbert.lean` and
`SNumbers/MaxDifference.lean`. The Challenge module restates exactly those,
which is why no wrapper is needed and why the names Palomar records are the
names the development actually uses.

The mathematics sits in `SNumbers/MaxDifference.lean`, where the bound is
obtained by chaining the growth lemma for the determinant quantities `Δₖ(S)`
with the upper bound `Δₙ₊₁(S) ≤ hₙ(S) · Δₙ(S)` and cancelling `Δₙ(S) > 0`.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
