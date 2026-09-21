/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.RowSpanRank
import LeanPool.RegtsSevenster.RS.Novel.Skein.FragmentEquiv

/-!
# Connection pairings and the edge-rank hypothesis

The hypothesis class of the main theorem — `pairClose`, the
connection pairing, `EdgeRankBounded` and `EdgeRankParameter` — is
defined in `RS/Definitions.lean`: ranks of infinite matrices are
avoided by bounding the `Module.rank` of the range of the curried
pairing.

This module proves the two facts about it: the bound weakens as the
base grows (`EdgeRankBounded.mono` — the literature takes `R ≥ 1`
where the definition admits any natural number, and nothing is
gained or lost), and the row-span reading agrees with the
literature's supremum over finite submatrices
(`edgeRankBounded_iff_submatrixRank`).
-/

namespace RS

/-- Edge-rank boundedness is monotone in the base. -/
theorem EdgeRankBounded.mono {f : ClosedFragment → ℂ} {R R' : ℕ}
    (hf : EdgeRankBounded f R) (hRR : R ≤ R') :
    EdgeRankBounded f R' := fun t =>
  le_trans (hf t) (Cardinal.power_le_power_right
    (by exact_mod_cast hRR))

/-- The rank condition as the literature states it, at arity `t`:
every finite submatrix of the connection matrix — a finite set `S` of
row fragments against a finite set `T` of column fragments — has rank
at most `n`. -/
def SubmatrixRankBounded (f : ClosedFragment → ℂ) (t n : ℕ) : Prop :=
  ∀ S T : Finset (Fragment (Fin t)),
    (submatrixOn (connectionPairing f t) S T).rank ≤ n

/-- **The two readings of the connection rank agree.**  Bounding the
dimension of the row span of the connection pairing, as
`EdgeRankBounded` does, is the same condition as bounding the ranks of
all the finite submatrices of the connection matrix, which is how the
rank of that infinite matrix is defined in the literature. -/
theorem edgeRankBounded_iff_submatrixRank (f : ClosedFragment → ℂ)
    (R : ℕ) :
    EdgeRankBounded f R ↔ ∀ t : ℕ, SubmatrixRankBounded f t (R ^ t) := by
  refine forall_congr' fun t => ?_
  have h := rank_range_lift_le_iff (connectionPairing f t) (R ^ t)
  rw [Nat.cast_pow] at h
  exact h

end RS
