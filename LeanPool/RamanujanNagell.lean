/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait, Xinze Li
-/

import LeanPool.RamanujanNagell.Basic
import LeanPool.RamanujanNagell.Helpers
import LeanPool.RamanujanNagell.QuadraticIntegers.FieldIsomorphism
import LeanPool.RamanujanNagell.QuadraticIntegers.QuadraticIntegerROI
import LeanPool.RamanujanNagell.QuadraticIntegers.RingOfIntegers

/-!
# The Ramanujan-Nagell theorem

Source: url:https://github.com/BarinderBanwait/ramanujan_nagell
Authors: Barinder S. Banwait, Xinze Li
Status: verified
Main declarations: `RamanujanNagell`
Tags: number-theory, diophantine-equations, quadratic-integers
MSC: 11D61, 11D45, 11R11
-/

/-!
## Mathematical overview

The Ramanujan-Nagell theorem states that the only integer solutions of
`x² + 7 = 2ⁿ` are `(x, n) = (±1, 3), (±3, 4), (±5, 5), (±11, 7), (±181, 15)`.
The proof works in the ring of integers `ℤ[θ]` of `ℚ(√-7)`, which has class
number one: the equation factors as a product of conjugate algebraic integers,
unique factorization forces those factors to be associate to powers of the
prime above `2`, and a unit/congruence analysis isolates the five exponents.

## References

The problem was posed by S. Ramanujan (1913) and the integer solutions were
determined by T. Nagell, *The Diophantine equation x² + 7 = 2ⁿ*, Arkiv för
Matematik 4 (1961), 185-187. A textbook account appears in L. J. Mordell,
*Diophantine Equations*, Academic Press, 1969, Chapter 20.
-/
