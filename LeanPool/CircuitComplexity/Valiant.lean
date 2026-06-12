/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Internal.Valiant

/-! # Valiant's Depth Reduction Lemma

The **length** of a directed path is the number of nodes in it. The
**depth** of a directed graph is the length of a longest directed walk.

**Lemma** (Valiant, 1977). *In any directed graph with `S` edges and
depth `d = 2 ^ k`, for any `1 ≤ r ≤ k`, it is possible to remove
`r * S / k` edges so that the depth of the resulting graph does not
exceed `d / 2 ^ r`.*

Reference: L. G. Valiant, *Graph-theoretic arguments in low-level
complexity*, MFCS 1977. Stated as Lemma 1.4 in Jukna, *Boolean
Function Complexity*.

Note on cycles: depth is defined here as the supremum (in `ℕ`) of
*walk* lengths, with no injectivity requirement on the walk. In the
presence of a directed cycle, walks can be made arbitrarily long, so
the supremum's underlying set is unbounded; by `ℕ`'s convention this
gives `depth = 0`. Consequently, `G.depth ≤ 2 ^ k` is satisfied
trivially (with `F = ∅`) for cyclic graphs, and is the meaningful
bound only on acyclic graphs — the case where Jukna's labeling
argument proceeds.

The proof machinery — canonical labelings, the edge partition by
first-differing bit, averaging, and the relabeling-after-removal
bound — lives in `Circ.Internal.Valiant`.
-/

namespace CircuitComplexity.Valiant

open Digraph

/-- **Valiant's Depth Reduction Lemma** (Valiant, 1977).

In any finite directed graph `G` with `S` edges and depth at most
`2 ^ k`, for any `r ≤ k`, there exists a set `F` of edges such
that:

* `F` is a subset of the edge set,
* `k * F.card ≤ r * S` (equivalent to `|F| ≤ r * S / k` without
  integer division), and
* after removing `F`, the resulting digraph has depth at most
  `2 ^ k / 2 ^ r`.

For cyclic `G` the hypothesis is satisfied trivially (with `depth = 0`)
and the conclusion holds with `F = ∅`. The substantive content is the
acyclic case, handled via Jukna's canonical labeling argument. -/
theorem depth_reduction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj]
    {k r : Nat} (hrk : r ≤ k)
    (hd : G.depth ≤ 2 ^ k) :
    ∃ F : Finset (V × V),
      F ⊆ G.edgeFinset ∧
      k * F.card ≤ r * G.edgeFinset.card ∧
      (G.deleteEdges F).depth ≤ 2 ^ k / 2 ^ r := by
  by_cases hac : IsAcyclic G
  · obtain ⟨I, hIsub, hIcard, hIsum⟩ := exists_r_levels_small G hrk hac hd
    refine ⟨I.biUnion fun i => levelEdges G k i, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨i, _, hie⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp hie).1
    · calc k * (I.biUnion fun i => levelEdges G k i).card
          ≤ k * ∑ i ∈ I, (levelEdges G k i).card :=
            Nat.mul_le_mul_left k Finset.card_biUnion_le
        _ ≤ r * G.edgeFinset.card := hIsum
    · have hbound := depth_deleteEdges_levelEdges_le G hac hd I hIsub
      rw [hIcard] at hbound
      have hpow : (2 : ℕ) ^ k / 2 ^ r = 2 ^ (k - r) :=
        Nat.pow_div hrk (by decide)
      rw [hpow]
      exact hbound
  · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
    rw [deleteEdges_empty_depth]
    change sSup _ ≤ _
    rw [Nat.sSup_of_not_bddAbove hac]
    exact Nat.zero_le _

end CircuitComplexity.Valiant
