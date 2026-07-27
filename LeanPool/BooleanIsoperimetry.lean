/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import LeanPool.BooleanIsoperimetry.CoherentGap
import LeanPool.BooleanIsoperimetry.Harper
import LeanPool.BooleanIsoperimetry.MacaulayMin
import LeanPool.BooleanIsoperimetry.SetFamilyShadow

/-!
# Harper's Vertex-Isoperimetric Theorem on the Boolean Cube

Source: doi:10.1016/S0021-9800(66)80059-5
Authors: Alexey Milovanov
Status: verified
Main declarations: `BooleanIsoperimetry.harper_theorem`
Tags: extremal-combinatorics, isoperimetry, boolean-cube
MSC: 05D05, 05C35
-/

/-!
## Mathematical overview

The vertices of the `n`-dimensional Boolean cube are represented as finite sets of
active coordinates. The formalization orders them first by cardinality and then by
reverse binary order within each layer. The first `k` vertices in this simplicial
order form the canonical generalized Hamming ball of size `k`.

The main result, `BooleanIsoperimetry.harper_theorem`, proves that for every family `A` of `k` cube
vertices, the closed radius-one Hamming neighborhood of the simplicial initial
segment of size `k` is no larger than the corresponding neighborhood of `A`. The
development includes the required binomial-cascade identities, Kruskal--Katona
shadow estimates, coordinate compressions, and the final induction over cube
dimension.

## Provenance

Imported from <https://github.com/AlexeyMilovanov/BooleanIsoperimetry>, branch
`lean-v4.31`, and ported to Lean 4.32.0-rc1 for this import. The proof follows
P. Frankl and Z. Füredi, "A short proof for a theorem of Harper about
Hamming-spheres," *Discrete Mathematics* 34 (1981),
doi:10.1016/0012-365X(81)90009-1. The formalization was developed with extensive
LLM assistance under the author's supervision.
-/
