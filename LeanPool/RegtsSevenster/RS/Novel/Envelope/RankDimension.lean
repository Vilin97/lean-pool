/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.DimensionDefinitions
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SkeinTower

/-!
# Connection ranks as skein dimensions

The first isomorphism theorem identifies the connection-map range
with the skein Hom space. At even arity this is the endomorphism
algebra used by the commutant estimate.
-/

@[expose] public section

namespace RS

/-- The connection rank is the dimension of the corresponding
skein Hom space. -/
theorem connectionRank_eq_homSpace_finrank
    (f : ClosedFragment → ℂ) (t : ℕ) :
    connectionRank f t = Module.finrank ℂ (HomSpace f t) :=
  (HomSpace.equivRange f t).finrank_eq.symm

/-- At even arity, connection rank is the dimension of the
endomorphism algebra on half as many strands. -/
theorem connectionRank_eq_skeinEnd_finrank {R : ℕ}
    (f : EdgeRankParameter R) (n : ℕ) :
    connectionRank f.val (2 * n) = Module.finrank ℂ (skeinEnd f n) := by
  rw [connectionRank_eq_homSpace_finrank, two_mul]
  rfl

/-- Under the edge-rank hypothesis, natural connection rank agrees
with the actual module rank of the connection-map range. -/
theorem connectionRank_cast_eq_rank {R : ℕ}
    (f : EdgeRankParameter R) (t : ℕ) :
    (connectionRank f.val t : Cardinal) =
      Module.rank ℂ (LinearMap.range (connectionMap f.val t)) := by
  rw [connectionRank_eq_homSpace_finrank, Module.finrank_eq_rank,
    (HomSpace.equivRange f.val t).rank_eq]

/-- The natural connection ranks satisfy every edge-rank bound
of the parameter, independently of its original packaged base. -/
theorem connectionRank_le_pow {f : ClosedFragment → ℂ} {B : ℕ}
    (h : EdgeRankBounded f B) (t : ℕ) :
    connectionRank f t ≤ B ^ t := by
  apply Module.finrank_le_of_rank_le
  simpa only [Nat.cast_pow] using h t

end RS
