/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ChainTwoLoopsSameLeft
public import LeanPool.BrillNoetherGraphs.Bananas.Basics.MarkedIso
public import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionSixChainConclusion

/-!
# The right-loop branch of Proposition 3.7

`ChainTwoLoopsSameLeft.lean` proves the complete arbitrary-mark classification
when both marks lie on the left cycle of a vertex wedge.  This file transports
that theorem across commutativity of vertex wedges, supplying the symmetric
right-cycle statement required by the paper's Proposition 3.7.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph

/-- Full same-loop clause of Proposition 3.7 for arbitrary distinct marks on
the right cycle.  Every divisor is submodular exactly when that cycle has two
vertices. -/
theorem chainTwoLoops_allSubmodular_same_right_arbitrary_iff
    (leftLength rightLength : Fin 2 → ℕ)
    (hLeftLength : ∀ edge, 0 < leftLength edge)
    (hRightLength : ∀ edge, 0 < rightLength edge)
    (leftGlue : (TwoPathCycle.spec leftLength hLeftLength).graph.V)
    (rightGlue p q : (TwoPathCycle.spec rightLength hRightLength).graph.V)
    (hpq : p ≠ q) :
    AllSubmodular
        (mark
          (vertexWedge
            (TwoPathCycle.spec leftLength hLeftLength).graph
            (TwoPathCycle.spec rightLength hRightLength).graph
            leftGlue rightGlue)
          (wedgeRightVertex
            (TwoPathCycle.spec leftLength hLeftLength).graph
            (TwoPathCycle.spec rightLength hRightLength).graph
            leftGlue rightGlue p)
          (wedgeRightVertex
            (TwoPathCycle.spec leftLength hLeftLength).graph
            (TwoPathCycle.spec rightLength hRightLength).graph
            leftGlue rightGlue q)) ↔
      rightLength 0 + rightLength 1 = 2 := by
  let G := (TwoPathCycle.spec leftLength hLeftLength).graph
  let H := (TwoPathCycle.spec rightLength hRightLength).graph
  let W := vertexWedge G H leftGlue rightGlue
  let W' := vertexWedge H G rightGlue leftGlue
  let phi : CFGraphIso W W' := vertexWedgeComm G H leftGlue rightGlue
  let M := mark W
    (wedgeRightVertex G H leftGlue rightGlue p)
    (wedgeRightVertex G H leftGlue rightGlue q)
  let N := mark W' (Sum.inl p) (Sum.inl q)
  have hu : phi.vertexEquiv M.u = N.u := by
    change phi.vertexEquiv (wedgeRightVertex G H leftGlue rightGlue p) = Sum.inl p
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H leftGlue rightGlue p
  have hv : phi.vertexEquiv M.v = N.v := by
    change phi.vertexEquiv (wedgeRightVertex G H leftGlue rightGlue q) = Sum.inl q
    dsimp [phi]
    exact vertexWedge_comm_apply_right G H leftGlue rightGlue q
  have hTransport : AllSubmodular N ↔ AllSubmodular M :=
    allSubmodular_map_of_marks_iff phi hu hv
  have hLeft : AllSubmodular N ↔ rightLength 0 + rightLength 1 = 2 := by
    simpa only [N, W'] using
      chainTwoLoops_allSubmodular_same_left_arbitrary_iff
        rightLength leftLength hRightLength hLeftLength rightGlue p q leftGlue hpq
  change AllSubmodular M ↔ rightLength 0 + rightLength 1 = 2
  exact hTransport.symm.trans hLeft

end Bananas
