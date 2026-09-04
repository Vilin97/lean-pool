/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Scott.Height.Defs
/-!
# Rank Bounds: sr, AttainedScottRank, and rank-height relations

This file defines `sr` (the supremum of element ranks without the +1 adjustment)
and `AttainedScottRank`, and proves bounds relating `sr`, `scottRank`, and
`scottHeight`.

## Main Definitions

- `sr`: Supremum of element ranks (without +1), as opposed to `scottRank` (with +1).
- `AttainedScottRank`: Whether the supremum in `sr` is attained by some element.

## Main Results

- `sr_le_scottRank`: sr ≤ scottRank always.
- `sr_le_scottHeight_of`: sr ≤ scottHeight (conditional on CRH).
- `scottRank_le_scottHeight_succ_of`: scottRank ≤ scottHeight + 1 (conditional on CRH).
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

/-- The supremum of element ranks without the +1 adjustment.

This is denoted `sr(M)` in some references (e.g., Marker). Compare with `scottRank`
which is `⨆ m, elementRank m + 1` (denoted `SR(M)` or `α(M)`). -/
private noncomputable def sr (M : Type w) [L.Structure M] [Countable M] : Ordinal.{0} :=
  ⨆ (m : M), elementRank (L := L) m

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- sr ≤ scottRank always holds, since scottRank = ⨆ m, elementRank m + 1 ≥ ⨆ m, elementRank m. -/
private theorem sr_le_scottRank (M : Type w) [L.Structure M] [Countable M] :
    sr (L := L) M ≤ scottRank (L := L) M := by
  unfold sr scottRank
  have : Small.{0} M := Countable.toSmall M
  apply Ordinal.iSup_le
  intro m
  calc elementRank (L := L) m
      ≤ elementRank (L := L) m + 1 := le_self_add
    _ ≤ ⨆ m, elementRank (L := L) m + 1 := Ordinal.le_iSup _ m

/-- The element-rank supremum `sr` is bounded by `scottHeight`.

Since `scottHeight M` is a complete stabilization ordinal (conditional on
`CountableRefinementHypothesis`), every `elementRank m ≤ scottHeight M`, so
the supremum `sr M = ⨆ m, elementRank m ≤ scottHeight M`. -/
private theorem sr_le_scottHeight_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    sr (L := L) M ≤ scottHeight (L := L) M := by
  unfold sr
  have : Small.{0} M := Countable.toSmall M
  apply Ordinal.iSup_le
  intro m
  exact elementRank_le_completeStab (scottHeight_stabilizesCompletely_of hcount M) m

/-- `scottRank M ≤ scottHeight M + 1`.

Since `scottRank M = ⨆ m, elementRank m + 1` and each `elementRank m ≤ scottHeight M`
(via `elementRank_le_completeStab` at the complete stabilization ordinal `scottHeight M`),
we get `scottRank M ≤ scottHeight M + 1`. Conditional on
`CountableRefinementHypothesis`. -/
private theorem scottRank_le_scottHeight_succ_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M ≤ scottHeight (L := L) M + 1 := by
  unfold scottRank
  have : Small.{0} M := Countable.toSmall M
  apply Ordinal.iSup_le
  intro m
  have h_bound := elementRank_le_completeStab (scottHeight_stabilizesCompletely_of hcount M) m
  have h := (Ordinal.add_le_add_iff_right 1).mpr h_bound
  convert h using 2 <;> simp [Nat.cast_one]

/-- A structure has attained Scott rank if some element achieves the supremum `sr`.

This is an important distinction in the theory of Scott rank: when the rank is
attained, the structure has a "witness" element of maximal complexity. -/
private def AttainedScottRank (M : Type w) [L.Structure M] [Countable M] : Prop :=
  ∃ (m : M), elementRank (L := L) m = sr (L := L) M

end Language

end FirstOrder
