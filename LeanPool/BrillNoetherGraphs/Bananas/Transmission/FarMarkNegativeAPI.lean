/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossStrandNegative

/-! Normalized-coordinate adapter for the verified cross-strand negative-rank
calculation. -/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-! The normalized/raw coordinate adapter (`normalizedPathPosition`,
`strandVertex_eq_pathVertex_normalized`, `normalizedPathPosition_isInterior`)
lives in `BananaBasics.lean`. -/

theorem rank_strand_pair_sub_neg_of_distinct_interior
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β γ : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (q : B.PathPosition γ)
    (hi : 0 < i.val ∧ i.val < B.length α)
    (hj : 0 < j.val ∧ j.val < B.length β)
    (hq : 0 < q.val ∧ q.val < B.length γ)
    (hαβ : α ≠ β)
    (hqx : strandVertex B γ q ≠ strandVertex B α i)
    (hqy : strandVertex B γ q ≠ strandVertex B β j) :
    rank B.graph
      (oneChip (strandVertex B α i) + oneChip (strandVertex B β j) -
        oneChip (strandVertex B γ q)) = -1 := by
  let pα := normalizedPathPosition B α i
  let pβ := normalizedPathPosition B β j
  let pγ := normalizedPathPosition B γ q
  have hpα : B.IsInteriorPosition α pα := by
    exact normalizedPathPosition_isInterior B α i hi
  have hpβ : B.IsInteriorPosition β pβ := by
    exact normalizedPathPosition_isInterior B β j hj
  have hpγ : B.IsInteriorPosition γ pγ := by
    exact normalizedPathPosition_isInterior B γ q hq
  have hqx' : B.pathVertex γ pγ ≠ B.pathVertex α pα := by
    intro h
    apply hqx
    simpa [pα, pγ, strandVertex_eq_pathVertex_normalized] using h
  have hqy' : B.pathVertex γ pγ ≠ B.pathVertex β pβ := by
    intro h
    apply hqy
    simpa [pβ, pγ, strandVertex_eq_pathVertex_normalized] using h
  have hRaw := cross_strand_rank_minus_one_of_distinct_interior
    hg B α β γ pα pβ pγ hpα hpβ hpγ hαβ hqx' hqy'
  simpa [pα, pβ, pγ, strandVertex_eq_pathVertex_normalized] using hRaw

end Bananas
