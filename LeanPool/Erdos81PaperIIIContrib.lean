/-
Copyright (c) 2026 Juan Pablo Traverso Gianini and Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import LeanPool.Erdos81PaperIIIContrib.SumZeroTriangles

/-!
# Near-perfect triangle packings from sum-zero triples

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/preprints/PAPER_III/05_formalization/lean_v1.4_freeze/Contrib/SumZeroTriangles.lean
Authors: Juan Pablo Traverso Gianini, Aristotle
Status: verified
Main declarations: `SumZeroTriangles.exists_triangle_packing_clique`
Tags: extremal-combinatorics, triangle-packing, cyclic-groups
MSC: 05B07, 05C70
-/

/-!
## Mathematical overview

This reusable formalization byproduct accompanying Paper III constructs a family of pairwise
edge-disjoint triangles in any finite complete graph such that every vertex is incident to at most
three uncovered edges. The construction labels vertices by a cyclic group and uses the triples of
distinct labels whose sum is zero.
-/
