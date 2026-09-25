/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNonrecurrence

/-!
# Nonrecurrence and canonical rank supports

This is the finite-residue formulation of Lemma 4.7 in
the twice-marked banana paper.  On a connected genus-two graph, Riemann--Roch
identifies an effective degree-one marked twist with membership of its vertex
in the rank support of the canonical complementary twist.  Consequently the
paper's nonrecurrence condition is exactly pairwise disjointness of those
canonical supports.
-/

namespace Bananas

open Utilities

/-- A degree-one marked twist is effective exactly when its vertex belongs to
the rank support of the corresponding canonical complementary twist. -/
theorem mem_rankSupport_canonical_sub_markedTwist_iff
    {M : TwiceMarked} (hconn : _root_.graphConnected M.graph)
    (hgenus : genus M.graph = 2) (w : M.graph.V) (n : ℕ) :
    w ∈ rankSupport M.graph
        (canonicalDivisor M.graph - (n : ℤ) • (oneChip M.u - oneChip M.v)) ↔
      0 ≤ rank M.graph
        (oneChip w + (n : ℤ) • (oneChip M.u - oneChip M.v)) := by
  let X : CFDiv M.graph :=
    oneChip w + (n : ℤ) • (oneChip M.u - oneChip M.v)
  have hDeg : deg X = 1 := by
    dsimp [X]
    rw [deg.map_add, deg_one_chip, map_zsmul, deg.map_sub,
      deg_one_chip, deg_one_chip]
    norm_num
  have hRR := riemann_roch_for_graphs hconn X
  rw [hgenus, hDeg] at hRR
  have hDual : rank M.graph (canonicalDivisor M.graph - X) = rank M.graph X := by
    omega
  change 0 ≤ rank M.graph
    ((canonicalDivisor M.graph - (n : ℤ) • (oneChip M.u - oneChip M.v)) -
      oneChip w) ↔ 0 ≤ rank M.graph X
  have hRewrite :
      (canonicalDivisor M.graph - (n : ℤ) • (oneChip M.u - oneChip M.v)) -
          oneChip w = canonicalDivisor M.graph - X := by
    dsimp [X]
    abel
  rw [hRewrite, hDual]

/-- The canonical supports indexed by two distinct nonzero residues are
disjoint. -/
def CanonicalMarkedSupportsPairwiseDisjoint (M : TwiceMarked) (k : ℕ) : Prop :=
  ∀ n m : Fin k, n.val ≠ 0 → m.val ≠ 0 → n ≠ m →
    Disjoint
      (rankSupport M.graph
        (canonicalDivisor M.graph - (n.val : ℤ) • (oneChip M.u - oneChip M.v)))
      (rankSupport M.graph
        (canonicalDivisor M.graph - (m.val : ℤ) • (oneChip M.u - oneChip M.v)))

/-- Lemma 4.7: nonrecurrence is equivalent to pairwise disjointness of the
canonical support complexes of the nonzero marked twists. -/
theorem nonRecurrent_iff_canonicalMarkedSupportsPairwiseDisjoint
    {M : TwiceMarked} {k : ℕ} (hconn : _root_.graphConnected M.graph)
    (hgenus : genus M.graph = 2) :
    NonRecurrent M k ↔ CanonicalMarkedSupportsPairwiseDisjoint M k := by
  constructor
  · intro hNonrec n m hn hm hne
    rw [Set.disjoint_left]
    intro w hwn hwm
    have hnRank : 0 ≤ rank M.graph
        (oneChip w + (n.val : ℤ) • (oneChip M.u - oneChip M.v)) :=
      (mem_rankSupport_canonical_sub_markedTwist_iff hconn hgenus w n.val).mp hwn
    have hmRank : 0 ≤ rank M.graph
        (oneChip w + (m.val : ℤ) • (oneChip M.u - oneChip M.v)) :=
      (mem_rankSupport_canonical_sub_markedTwist_iff hconn hgenus w m.val).mp hwm
    exact hne (hNonrec w n m hn hm hnRank hmRank)
  · intro hDisjoint w n m hn hm hnRank hmRank
    by_contra hne
    have hnMem : w ∈ rankSupport M.graph
        (canonicalDivisor M.graph - (n.val : ℤ) • (oneChip M.u - oneChip M.v)) :=
      (mem_rankSupport_canonical_sub_markedTwist_iff hconn hgenus w n.val).mpr hnRank
    have hmMem : w ∈ rankSupport M.graph
        (canonicalDivisor M.graph - (m.val : ℤ) • (oneChip M.u - oneChip M.v)) :=
      (mem_rankSupport_canonical_sub_markedTwist_iff hconn hgenus w m.val).mpr hmRank
    have h := hDisjoint n m hn hm hne
    exact (Set.disjoint_left.mp h hnMem hmMem).elim

end Bananas
