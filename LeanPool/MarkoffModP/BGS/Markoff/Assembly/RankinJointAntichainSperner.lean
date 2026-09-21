/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.RankinJointAntichainWidth
import LeanPool.MarkoffModP.BGS.Combinatorics.SymmetricChainBasic

/-!
# Sperner handoff for the joint maximal-order antichain

This file isolates the final semantic obligation for a central-coefficient
width bound.  It is enough to encode the nontrivial maximal orders injectively
into any finite ranked poset with a symmetric-chain decomposition, in such a
way that comparison of encoded points implies divisibility of the original
orders.  The joint antichain then has cardinality at most the central rank.
-/

namespace BGS.Markoff

open BGS.Combinatorics

/-- A comparison-reflecting factorization encoding transports the joint
divisor antichain into any explicitly symmetric-chain-decomposed poset. -/
theorem nontrivialMiddleGameMaximalOrders_card_le_centralRank_of_encoding
    {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P]
    {rank : P -> Nat} {total p bound : Nat}
    (hp : 1 < p)
    (decomposition : SymmetricChainDecomposition P rank total)
    (encode : Nat -> P)
    (hinjective : Function.Injective encode)
    (hcomparison :
      ∀ {a b : Nat},
        a ∈ nontrivialMiddleGameMaximalOrders p bound ->
        b ∈ nontrivialMiddleGameMaximalOrders p bound ->
        encode a <= encode b -> a ∣ b) :
    (nontrivialMiddleGameMaximalOrders p bound).card <=
      Fintype.card {point : P // rank point = total / 2} := by
  let embedding : Nat ↪ P := ⟨encode, hinjective⟩
  let encoded : Finset P :=
    (nontrivialMiddleGameMaximalOrders p bound).map embedding
  have hencodedAntichain :
      IsAntichain (· <= ·) (encoded : Set P) := by
    intro x hx y hy hxy hle
    have hx' : x ∈ encoded := by simpa using hx
    have hy' : y ∈ encoded := by simpa using hy
    change x ∈
      (nontrivialMiddleGameMaximalOrders p bound).map embedding at hx'
    change y ∈
      (nontrivialMiddleGameMaximalOrders p bound).map embedding at hy'
    rcases Finset.mem_map.mp hx' with ⟨a, ha, hax⟩
    rcases Finset.mem_map.mp hy' with ⟨b, hb, hby⟩
    have hdiv : a ∣ b := by
      apply hcomparison ha hb
      change embedding a <= embedding b
      rw [hax, hby]
      exact hle
    have hab : a = b :=
      nontrivialMiddleGameMaximalOrders_eq_of_dvd hp ha hb hdiv
    apply hxy
    calc
      x = embedding a := hax.symm
      _ = embedding b := congrArg embedding hab
      _ = y := hby
  have hcentral :=
    decomposition.antichain_card_le_central_rank
      encoded hencodedAntichain
  simpa [encoded] using hcentral

/-- The central rank supplied by a factorization encoding can be inserted
directly into the Corvaja--Zannier witness cap, with the two exceptional
divisors restored. -/
theorem bound_le_rankinCentralRankWitnessCap_of_encoding
    {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P]
    {rank : P -> Nat} {total p bound : Nat}
    (hp : 1 < p)
    (hbound :
      bound <= 189 * (middleGameMaximalOrders p bound).card ^ 3)
    (decomposition : SymmetricChainDecomposition P rank total)
    (encode : Nat -> P)
    (hinjective : Function.Injective encode)
    (hcomparison :
      ∀ {a b : Nat},
        a ∈ nontrivialMiddleGameMaximalOrders p bound ->
        b ∈ nontrivialMiddleGameMaximalOrders p bound ->
        encode a <= encode b -> a ∣ b) :
    bound <= rankinWidthWitnessCap
      (Fintype.card {point : P // rank point = total / 2} + 2) := by
  apply bound_le_rankinJointAntichainWitnessCap hbound
  exact nontrivialMiddleGameMaximalOrders_card_le_centralRank_of_encoding
    hp decomposition encode hinjective hcomparison

end BGS.Markoff
