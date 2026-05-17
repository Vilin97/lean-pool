/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc.
-/

import LeanPool.Erdos1196.Basic
import LeanPool.Erdos1196.Preliminaries
import LeanPool.Erdos1196.Markov
import LeanPool.Erdos1196.PrimitiveWeight
import LeanPool.Erdos1196.HitMass
import LeanPool.Erdos1196.Main
import LeanPool.Erdos1196.FormalConjecturesErdos1196

/-!
# Primitive Sets Above x (Erdos Problem 1196)

Source: url:https://github.com/math-inc/Erdos1196
Authors: Math Inc.
Status: verified
Main declarations: `PrimitiveSetsAboveX.mainTheorem`, `Erdos1196.erdos_1196`
Tags: number-theory, combinatorics, analysis
MSC: 11N25, 05D05
-/

/-!
## Mathematical overview

A set `A ⊆ ℕ` is *primitive* if no element of `A` divides another. This development proves
that every primitive set `A ⊆ ℕ ∩ [x, ∞)` satisfies
`∑_{a ∈ A} 1 / (a log a) ≤ 1 + O(1 / log x)` as `x → ∞`, the quantitative form of Erdős
Problem `#1196`. The argument builds an explicit sub-Markov chain on the divisibility poset
whose visiting probabilities are proportional to `1 / (n log n)`; the first-hit mass of a
primitive set is then at most `1`, and the normalization estimate for the constant `B_x`
converts this into the logarithmic-series bound.

The exported modules follow the structure of the proof: arithmetic and tail estimates
(`LeanPool.Erdos1196.Preliminaries`), the normalization decomposition of `B_x`
(`LeanPool.Erdos1196.Markov`), the Markov-layer and hit-mass arguments
(`LeanPool.Erdos1196.HitMass`), the final quantitative theorem
`PrimitiveSetsAboveX.mainTheorem` (`LeanPool.Erdos1196.Main`), and the
`formal-conjectures`-style theorem `Erdos1196.erdos_1196`
(`LeanPool.Erdos1196.FormalConjecturesErdos1196`).

## Provenance

Imported from <https://github.com/math-inc/Erdos1196>. Upstream contains no `sorry`s.
Ported from Lean `v4.30.0-rc1` to Lean Pool's `v4.30.0-rc2`.
-/
