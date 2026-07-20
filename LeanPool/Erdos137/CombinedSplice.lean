/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.SpliceFiniteness
import LeanPool.Erdos137.SquarefreeCapacity

/-!
# Erdős Problem #137: the combined four-range splice

A single "control panel" unifying the three deterministic non-powerfulness routes proved elsewhere
in the repository, parametric in three range predicates `Mid Sq High : ℕ → ℕ → Prop`. Given a
`CoversAll4` decomposition of every `(k, n)` (with `k ≥ 3`, `1 ≤ n`) into

* the **small** range `n ≤ k`            — discharged unconditionally by Bertrand
  (`upper_half_prime_not_powerful`);
* the **middle/prime** range `Mid`        — a prime `p > k` is a block term
  (`prime_range_not_powerful`, fed by `PrimeInBlockOnRange Mid`);
* the **squarefree-count** range `Sq`     — the squarefree count beats the deterministic capacity
  (`squarefree_range_not_powerful`, fed by `SqfreeCapacityBeatenOnRange Sq`);
* the **high** range `High`               — any externally supplied non-powerfulness input, whose
  predicate carries its own side conditions (e.g. `High k n := 6 ≤ k ∧ k^3 < n` to plug in the crude
  `g = 6` threshold `not_powerful_of_large_g6`, or `5 ≤ k ∧ k^{5/3+η} < n` for the smooth `g = 5`
  bound), so the ambient `3 ≤ k` guard need not match the route's own,

it concludes `¬ Powerful (F k n)` for every such `(k, n)`. The analytic inputs (Baker–Harman–Pintz
on `Mid`, Pandey-type squarefree counts on `Sq`, the abc block bound behind `High`) live ENTIRELY
inside the three premises: Lean never assumes any of them, so nothing here pretends to formalize
BHP, Pandey, Mertens, or abc. This is the four-range analogue of
`abstract_splice_no_counterexamples`, with the new squarefree-count range slotted between the prime
range and the high range.
-/

namespace Erdos137

noncomputable section

/-- **Four-range coverage.** Every `(k, n)` with `k ≥ 3`, `1 ≤ n` is small (`n ≤ k`), middle
(`Mid`), squarefree-rich (`Sq`), or high (`High`). On the intended instantiation `Mid` is the
Baker–Harman–Pintz prime-gap range, `Sq` is the Pandey squarefree-count range, and `High` is a
crude or smooth radical threshold; coverage is the (external) statement that these four ranges
exhaust `n > 0`. -/
def CoversAll4 (Mid Sq High : ℕ → ℕ → Prop) : Prop :=
  ∀ k n : ℕ, 3 ≤ k → 1 ≤ n → n ≤ k ∨ Mid k n ∨ Sq k n ∨ High k n

/-- **The combined four-range splice.** Parametric in `Mid Sq High`. Given a `CoversAll4`
decomposition, a ranged prime input on `Mid`, a squarefree-capacity input on `Sq`, and a
non-powerfulness input on `High`, the product `F k n` is not powerful for every `k ≥ 3`, `1 ≤ n`.
Each case is discharged by the corresponding deterministic theorem; the analytic content stays in
the premises. -/
theorem abstract_prime_sqfree_high_splice {Mid Sq High : ℕ → ℕ → Prop}
    (hCover : CoversAll4 Mid Sq High)
    (hMid : PrimeInBlockOnRange Mid)
    (hSq : SqfreeCapacityBeatenOnRange Sq)
    (hHigh : ∀ k n, 3 ≤ k → 1 ≤ n → High k n → ¬ Powerful (F k n))
    {k n : ℕ} (hk : 3 ≤ k) (hn : 1 ≤ n) : ¬ Powerful (F k n) := by
  rcases hCover k n hk hn with hsmall | hmid | hsq | hhigh
  · exact upper_half_prime_not_powerful (by omega) hn hsmall
  · exact prime_range_not_powerful hMid hk hn hmid
  · exact squarefree_range_not_powerful hSq hk hn hsq
  · exact hHigh k n hk hn hhigh

end  -- noncomputable section

end Erdos137
