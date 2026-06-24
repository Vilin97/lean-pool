/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Graph.Edges
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Definition of the Bruhat-Tits graph

In this file we define the Bruhat-Tits graph as a simple graph and show it is connected.

-/

open Module


suppress_compilation

namespace BruhatTits

-- Let R be a discrete valuation ring and K its field of fractions
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

instance : Inhabited (Vertices R) := ⟨⟦Lattice.standard R⟧⟩

/--
The Bruhat-Tits graph defined as a simple graph. The vertices are given by the homothety
classes of lattices. Two vertices are connected by an edge if they are neighbours, i.e. if their
distance is equal to `1`.
-/
@[simps -isSimp]
def BTgraph : SimpleGraph (Vertices R) where
  Adj L M := BruhatTits.IsNeighbour L M
  symm := ⟨fun L M => (isNeighbour_symm L M).mp⟩
  loopless := ⟨by
    intro L (h : inv L L = 1)
    rw [inv_self] at h
    simp at h⟩

/-- There is a path between any two vertices. -/
lemma reachable (M L : Vertices R) {n : ℕ} : (h : inv M L = n) → BTgraph.Reachable M L := by
  revert M L
  induction n with
  | zero =>
    intro M L h
    rw [← eq_iff] at h
    subst h
    rfl
  | succ k ih =>
    intro M L h
    obtain ⟨T, hLT, hTM⟩ := exists_intermediate_vertex _ M L h
    refine (SimpleGraph.Adj.reachable hTM).symm.trans (ih T L ?_)
    rw [inv_symm]
    exact hLT

/-- The Bruhat-Tits graph is connected. -/
lemma BTgraph_connected : SimpleGraph.Connected (BTgraph (R := R)) where
  preconnected M L := reachable M L rfl

end BruhatTits
