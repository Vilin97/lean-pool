/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.GraphColouringMatching.Basic
public import Mathlib.SetTheory.Cardinal.Defs

/-!
# Cardinal edge accounting for arbitrary matching decompositions

The edge equivalence gives an indexed cardinal sum without finiteness of the
vertices, edges, or palette. The lift only reconciles the two type universes.
This is distinct from natural-number counting, which requires finite edges.
-/

public section

universe u v

namespace SimpleGraph.MatchingDecomposition

/-- The cardinality of the graph edges is the indexed cardinal sum of its matching classes.
No finiteness assumptions are required, and unused colours contribute zero. -/
theorem cardinal_edges_eq_sum {V : Type u} {C : Type v} {G : SimpleGraph V}
    (D : MatchingDecomposition G C) :
    Cardinal.lift.{v} (Cardinal.mk G.edgeSet) =
      Cardinal.sum (fun c => Cardinal.mk (D.matching c).edgeSet) := by
  rw [← Cardinal.mk_sigma]
  exact Cardinal.mk_congr (Equiv.ulift.trans D.edgeEquivSigma)

end SimpleGraph.MatchingDecomposition
