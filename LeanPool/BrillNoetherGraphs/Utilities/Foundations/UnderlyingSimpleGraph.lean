/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Parameters
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Tactic

/-!
# The underlying simple graph of a `CFGraph`

`underlyingSimpleGraph` and the equivalence between the cut definition of
connectivity and `SimpleGraph.Connected`.  This provides a general interface
from chip-firing multigraphs to Mathlib's simple-graph connectivity theory.
-/

@[expose] public section

namespace Utilities

/-- The simple graph underlying a chip-firing multigraph. -/
def underlyingSimpleGraph (G : CFGraph) : SimpleGraph G.V where
  Adj v w := numEdges G v w > 0
  -- `SimpleGraph.symm` now asks for `Std.Symm Adj` (a one-field class), not the
  -- bare `Symmetric Adj` function type (Mathlib v4.33): wrap the old proof in
  -- the anonymous constructor.
  symm := ⟨fun v w => by
    rw [num_edges_symmetric]
    intro h
    exact h⟩
  loopless := ⟨fun v h => by
    change numEdges G v v > 0 at h
    simp at h⟩

@[simp] theorem underlyingSimpleGraph_adj
    (G : CFGraph) (v w : G.V) :
    (underlyingSimpleGraph G).Adj v w ↔ numEdges G v w > 0 :=
  Iff.rfl

instance underlyingSimpleGraphDecidableAdj (G : CFGraph) :
    DecidableRel (underlyingSimpleGraph G).Adj := by
  intro v w
  exact inferInstanceAs (Decidable (numEdges G v w > 0))

private theorem walk_has_edge_across_cut
    {V : Type*} {U : SimpleGraph V} {a b : V} (S : Set V)
    (p : U.Walk a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ v ∈ S, ∃ w ∉ S, U.Adj v w := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons u v w huv p ih =>
      by_cases hv : v ∈ S
      · exact ih hv hb
      · exact ⟨u, ha, v, hv, huv⟩

/-- The cut definition of connectivity used by `CFGraph` agrees with
connectivity of the underlying simple graph. -/
theorem graph_connected_iff_underlyingSimpleGraph_connected (G : CFGraph) :
    graphConnected G ↔ (underlyingSimpleGraph G).Connected := by
  classical
  let U := underlyingSimpleGraph G
  constructor
  · intro hG
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let q : G.V := Classical.arbitrary G.V
    refine ⟨q, ?_⟩
    intro w
    by_contra hqw
    let S : Finset G.V := Finset.univ.filter (U.Reachable q)
    have hqS : q ∈ S := by
      simp [S]
    have hwS : w ∉ S := by
      simpa [S] using hqw
    obtain ⟨v, hvS, z, hzS, hvz⟩ := hG S ⟨q, w, hqS, hwS⟩
    have hqv : U.Reachable q v := by
      simpa [S] using hvS
    have hvzAdj : U.Adj v z := by
      exact hvz
    have hqz : U.Reachable q z := hqv.trans hvzAdj.reachable
    exact hzS (by simpa [S] using hqz)
  · intro hU S hS
    obtain ⟨a, b, haS, hbS⟩ := hS
    obtain ⟨p⟩ := hU.preconnected a b
    obtain ⟨v, hvS, w, hwS, hvw⟩ :=
      walk_has_edge_across_cut (S : Set G.V) p haS hbS
    exact ⟨v, hvS, w, hwS, hvw⟩

end Utilities
