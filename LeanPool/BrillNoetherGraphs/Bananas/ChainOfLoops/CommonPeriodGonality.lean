/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.ChainOfLoops.BridgeChainTransport
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.EqualTorsionKGeneral
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralGonality

/-!
# Exact gonality of common-period chains

This file transports the transmission-theoretic gonality theorem across the
reader-facing bridge-chain model.  The mathematical chain theorem is proved on
the vertex-wedge chain, where common-period `k`-general transmission composes;
contracting every displayed bridge preserves degree and rank.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Connectivity is preserved by the displayed bridge-chain construction. -/
theorem graph_connected_bridgeChain
    (M : MarkedGraph) (L : List MarkedGraph)
    (hMconn : _root_.graphConnected M.graph)
    (hLconn : ∀ N ∈ L, _root_.graphConnected N.graph) :
    _root_.graphConnected (M.bridgeChain L).graph := by
  induction L generalizing M with
  | nil => exact hMconn
  | cons N rest ih =>
      apply ih (M.bridge N)
      · exact graph_connected_bridgeGraph M.graph N.graph M.right N.left
          hMconn (hLconn N (by simp))
      · intro P hP
        exact hLconn P (by simp [hP])

/-- Exact gonality transports from the target of a rank-preserving contraction
back to its source.  The upper-bound divisor is written explicitly as `k`
chips at the preserved left mark, so no surjectivity of the divisor map is
needed. -/
theorem exact_gonality_of_leftRankTransport
    {source target : MarkedGraph} (transport : LeftRankTransport source target)
    {k : ℕ}
    (hTargetConn : _root_.graphConnected target.graph)
    (hTargetK : KGeneralTransmission
      (mark target.graph target.left target.right) k)
    (hsmall : k ≤ ((genus source.graph).toNat + 3) / 2) :
    BNExists source.graph 1 (k : ℤ) ∧
      ∀ d : ℤ, d < k → ¬ BNExists source.graph 1 d := by
  let targetMarked := mark target.graph target.left target.right
  have hTargetGenusNonneg : 0 ≤ genus target.graph :=
    genus_nonneg_of_graph_connected target.graph hTargetConn
  have hTargetGenus : genus target.graph = (genus target.graph).toNat :=
    (Int.toNat_of_nonneg hTargetGenusNonneg).symm
  have hsmallTarget :
      k ≤ ((genus target.graph).toNat + 3) / 2 := by
    rw [transport.genus_eq]
    exact hsmall
  have hExactTarget := hTargetK.exact_gonality
    hTargetConn hTargetGenus hsmallTarget
  change BNExists target.graph 1 (k : ℤ) ∧
    (∀ d : ℤ, d < k → ¬ BNExists target.graph 1 d) at hExactTarget
  constructor
  · let D : CFDiv source.graph := (k : ℤ) • oneChip source.left
    refine ⟨D, ?_, ?_⟩
    · dsimp [D]
      rw [map_zsmul, deg_one_chip]
      simp
    · have hRankTarget := hTargetK.rank_period_smul_one_chip_ge_one hTargetConn
      change rank target.graph ((k : ℤ) • oneChip target.left) ≥ 1 at hRankTarget
      have hMap : transport.mapDiv D =
          (k : ℤ) • oneChip target.left := by
        dsimp [D]
        rw [transport.map_zsmul, transport.map_one_chip]
      rw [← hMap, transport.rank_map] at hRankTarget
      exact hRankTarget
  · intro d hdk
    rintro ⟨D, hdeg, hrank⟩
    exact hExactTarget.2 d hdk
      ⟨transport.mapDiv D, by rw [transport.deg_map, hdeg], by
        rw [transport.rank_map]
        exact hrank⟩

/-- A bridge-chain of connected factors with common `k`-general transmission
has gonality exactly `k`, whenever `k` is at most the generic gonality of the
total genus. -/
theorem exact_gonality_bridgeChain_of_commonPeriod
    (M : MarkedGraph) (L : List MarkedGraph) (k : ℕ)
    (hMconn : _root_.graphConnected M.graph)
    (hMK : KGeneralTransmission (mark M.graph M.left M.right) k)
    (hLconn : ∀ N ∈ L, _root_.graphConnected N.graph)
    (hLK : ∀ N ∈ L,
      KGeneralTransmission (mark N.graph N.left N.right) k)
    (hsmall : k ≤ ((genus (M.bridgeChain L).graph).toNat + 3) / 2) :
    BNExists (M.bridgeChain L).graph 1 (k : ℤ) ∧
      ∀ d : ℤ, d < k → ¬ BNExists (M.bridgeChain L).graph 1 d := by
  let target := M.chain L
  have hTargetConn : _root_.graphConnected target.graph :=
    graph_connected_markedChain M L hMconn hLconn
  have hTargetK : KGeneralTransmission
      (mark target.graph target.left target.right) k :=
    kGeneralTransmission_markedChain_of_commonPeriod
      M L k hMconn hMK hLconn hLK
  exact exact_gonality_of_leftRankTransport
    (contractBridgeChain M L) hTargetConn hTargetK hsmall

end Bananas
