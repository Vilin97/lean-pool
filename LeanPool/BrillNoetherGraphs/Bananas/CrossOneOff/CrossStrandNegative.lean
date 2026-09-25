/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrand

/-!
# Cross-strand reduced negative-rank witness

This is the small, independently useful part of the far-mark calculation.
The reducedness theorem supplies the rank `-1` conclusion directly; no
additional rank-zero argument is bundled into it.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec


theorem cross_strand_rank_minus_one_of_distinct_interior
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β γ : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (q : B.PathPosition γ)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hq : B.IsInteriorPosition γ q)
    (hαβ : α ≠ β)
    (hqx : B.pathVertex γ q ≠ B.pathVertex α i)
    (hqy : B.pathVertex γ q ≠ B.pathVertex β j) :
    rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j) -
        oneChip (B.pathVertex γ q)) = -1 := by
  have hRed := q_reduced_distinct_interior_path_strands
    hg B α β γ i j q hi hj hq hαβ hqx hqy
  have hRank := rank_eq_neg_one_of_qReduced_debt B.graph
    (B.pathVertex γ q)
    (oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j) -
      oneChip (B.pathVertex γ q)) hRed (by
        simp [oneChip, hqx, hqy])
  exact hRank

end Bananas
