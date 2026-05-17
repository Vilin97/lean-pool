/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/

import LeanPool.LatticeTriangle.Solution

/-!
# On the paucity of lattice triangles

Source: arxiv:2603.23928
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
Status: verified
Main declarations: `analyticEngine_lower_bound`
Tags: number-theory, combinatorics
MSC: 11H06, 11B30
-/

/-!
## Mathematical overview

Fix `η ∈ (0, 1/6)` and `θ ∈ (0, 1)`. For `n ≥ 1` the *truncated obtuse region*
`truncatedObtuseRegion n η` is the set of integer pairs `(p, q)` with
`η n ≤ p, q`, `p + q < n / 2`, and `gcd(p, q, n) = 1`. For a pair `(p, q)` the
counting function `countingFunctionS n p q` records how many units `a ∈ (ℤ/nℤ)ˣ`
send both `a p` and `a q` into the initial intervals `{1, …, 2p-1}` and
`{1, …, 2q-1}` of `ℤ/nℤ`. The *bad pairs* `badPairsSet n η` are those pairs in
the truncated obtuse region for which additionally `gcd(q, P⁺(n)) = 1` and
`countingFunctionS n p q < 5`, where `P⁺(n) = largestPrimeFactor n`.

The main result, `analyticEngine_lower_bound`, is the "analytic engine": for
every `ε > 0` the fraction of bad pairs among all pairs of the truncated obtuse
region is eventually below `ε`, in the limit `n → ∞` along integers whose largest
prime factor is at least `n ^ θ`. The proof combines a lower bound on
`(truncatedObtuseRegion n η).ncard` with an upper bound on
`(badPairsSet n η).ncard` obtained from a Fourier expansion of the counting
function in terms of Ramanujan sums.

## Provenance

Imported from <https://github.com/AxiomMath/lattice-triangle>; the formalization
was produced with [Axiom Math](https://axiommath.ai) and accompanies the paper
[arXiv:2603.23928](https://arxiv.org/abs/2603.23928). The upstream solution file
contains no `sorry`s. Ported from Lean v4.26.0 to Lean Pool's v4.30.0-rc2.
-/
