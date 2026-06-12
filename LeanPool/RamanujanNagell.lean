/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait, Xinze Li
-/

import LeanPool.RamanujanNagell.Basic
import LeanPool.RamanujanNagell.Helpers

/-!
# The Ramanujan-Nagell theorem

Source: arxiv:2604.09808
Authors: Barinder S. Banwait, Xinze Li
Status: verified
Main declarations: `ramanujanNagellExact`
Tags: number-theory, diophantine-equations, quadratic-integers
MSC: 11D61, 11D45, 11R11
-/

/-!
## Mathematical overview

The Ramanujan-Nagell theorem states that the only integer solutions of
`x² + 7 = 2ⁿ` are `(x, n) = (±1, 3), (±3, 4), (±5, 5), (±11, 7), (±181, 15)`.
The proof works in the ring `R = ℤ[(1 + √-7)/2]` of integers of `ℚ(√-7)`,
realized as `QuadraticAlgebra ℤ (-2) 1`: a smart-rounding division algorithm
for the norm `N(x + yθ) = x² + xy + 2y²` shows directly that `R` is a
Euclidean domain, hence a PID and a UFD. The equation factors as a product of
conjugate elements of `R`, unique factorization forces those factors to be
associate to powers of the primes `θ`, `θ'` above `2`, and a unit/congruence
analysis isolates the five exponents.

## References

The problem was posed by S. Ramanujan (1913) and the integer solutions were
determined by T. Nagell, *The Diophantine equation x² + 7 = 2ⁿ*, Arkiv för
Matematik 4 (1961), 185-187. A textbook account appears in L. J. Mordell,
*Diophantine Equations*, Academic Press, 1969, Chapter 20. This formalization
is described in B. S. Banwait, *A formal proof of the Ramanujan-Nagell theorem
in Lean 4*, arXiv:2604.09808.
-/
