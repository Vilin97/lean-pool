/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import LeanPool.DeadEnds.Solution

/-!
# Dead Ends in Square-Free Digit Walks

Source: arxiv:2602.05095
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
Status: verified
Main declarations: `LeanPool.DeadEnds.baseBDeadEnd_density_formula`
Tags: number-theory, combinatorics
MSC: 11N25
-/

/-!
## Mathematical overview

Fix an integer `b ≥ 2`. A positive integer `N` is a *base-`b` dead end* if `N`
is square-free yet `b * N + d` fails to be square-free for every digit
`d ∈ {0, 1, …, b - 1}` — appending any digit in base `b` leaves the square-free
world. The project studies the asymptotic density

`D_b = lim_{X → ∞} #{N ≤ X : N is a base-b dead end} / X`.

For a prime `p` and `T ⊆ {0, …, b - 1}` it defines the local density factor
`μ_p(b, T)` counting residues mod `p²` avoiding the relevant square divisibility
conditions, the convergent Euler product `α(b, T) = ∏_p μ_p(b, T)`, and the
inclusion-exclusion sum `∑_{T ⊆ {0,…,b-1}} (-1)^{|T|} α(b, T)`.

The main results show that `D_b` exists (`baseBDeadEnd_density_exists`), is
unique as a limit (`baseBDeadEnd_density_unique`), each Euler product converges
(`jointSquarefreeDensity_convergent`) and equals the corresponding joint
square-free density (`jointSquarefreeDensity_is_asymptotic_density`), and `D_b`
is given by the inclusion-exclusion formula
(`baseBDeadEnd_density_formula`, `explicitDensityFormula_correct`).

(After the first arXiv version, the authors learned from K. Soundararajan that
the result was previously obtained by Mirsky in 1947.)

## Provenance

Imported from <https://github.com/AxiomMath/dead-ends>; initial code generated
by [Axiom Math](https://axiommath.ai). The upstream `Deadends/solution.lean`
contains no `sorry`s; the companion `Deadends/problem.lean` is only the problem
statement (with `sorry` placeholders) and is fully subsumed by the solution
file, so it is not vendored. Upstream is MIT-licensed; redistributed here under
Apache-2.0 as part of Lean Pool. Ported from Lean v4.26.0 to Lean Pool's
v4.30.0-rc2.
-/
