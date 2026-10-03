/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Gluing

/-!
# Simplicial elimination outside a prescribed clique

In a finite chordal graph, a proper clique can be retained while some vertex
outside it is eliminated. The proof works in the connected component of an
outside vertex and uses the existing one- and two-vertex Dirac interfaces.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Simpliciality inside a connected component is simpliciality in the whole graph. -/
theorem ConnectedComponent.isSimplicial_coe (c : G.ConnectedComponent) (x : c)
    (hx : c.toSimpleGraph.IsSimplicial x) : G.IsSimplicial x.1 := by
  intro a ha b hb hab
  have haC : a ∈ c.supp := (c.mem_supp_congr_adj ha).mp x.2
  have hbC : b ∈ c.supp := (c.mem_supp_congr_adj hb).mp x.2
  have ha' : (⟨a, haC⟩ : c) ∈ c.toSimpleGraph.neighborSet x := ha
  have hb' : (⟨b, hbC⟩ : c) ∈ c.toSimpleGraph.neighborSet x := hb
  exact hx ha' hb' (fun h => hab (congrArg Subtype.val h))

/-- A finite chordal graph has a simplicial vertex outside any proper clique. -/
theorem IsChordal.exists_isSimplicial_not_mem_clique [Finite V]
    (hG : G.IsChordal) {S : Set V} (hS : G.IsClique S)
    (houtside : ∃ u, u ∉ S) : ∃ z, z ∉ S ∧ G.IsSimplicial z := by
  classical
  obtain ⟨u, hu⟩ := houtside
  let c := G.connectedComponentMk u
  have hC : c.toSimpleGraph.IsChordal := hG.induce c.supp
  by_cases hcomplete : ∀ x y : c, x ≠ y → c.toSimpleGraph.Adj x y
  · refine ⟨u, hu, c.isSimplicial_coe ⟨u, rfl⟩ ?_⟩
    intro a _ b _ hab
    exact hcomplete a b hab
  · obtain ⟨x, y, hne, hxy, hx, hy⟩ :=
      hC.exists_two_nonadj_isSimplicial c.connected_toSimpleGraph hcomplete
    by_cases hxS : x.1 ∈ S
    · have hyS : y.1 ∉ S := by
        intro hyS
        exact hxy (hS hxS hyS (fun h => by
          have heq : x = y := Subtype.ext h
          exact hne heq))
      exact ⟨y.1, hyS, c.isSimplicial_coe y hy⟩
    · exact ⟨x.1, hxS, c.isSimplicial_coe x hx⟩

end SimpleGraph
