/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.CubicColouring

/-!
# Subcubic Brooks theorem: Main

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- Brooks' theorem for subcubic graphs: a finite simple graph with maximum degree `≤ 3` and no
4-clique is 3-colourable. -/
theorem brooks_cubic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 3) (hK4 : G.CliqueFree 4) : G.Colorable 3 := by
  classical
  rw [G.colorable_iff_forall_connectedComponent]
  intro c
  let : Fintype c := Fintype.ofFinite c
  let H := c.toSimpleGraph
  let : DecidableRel H.Adj := Classical.decRel _
  have hconn : H.Connected := c.connected_toSimpleGraph
  have hemb : H ↪g G := SimpleGraph.Embedding.induce c.supp
  have hdeg : ∀ v, H.degree v ≤ 3 := by
    intro v
    -- Cardinality is independent of the component's chosen finite enumeration.
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      Fintype.card_eq_nat_card, H, ConnectedComponent.toSimpleGraph] using
      (induce_degree_le G c.supp v).trans ((G.degree_le_maxDegree v.val).trans hΔ)
  have hfree : H.CliqueFree 4 := hK4.comap ⟨hemb.toCopy⟩
  by_cases hlow : ∃ v, H.degree v < 3
  · exact connected_colorable_three_of_exists_degree_lt H hconn hdeg hlow
  · apply connected_colorable_three_of_degree_eq_three H hconn _ hfree
    intro v
    exact Nat.le_antisymm (hdeg v) (not_lt.mp (not_exists.mp hlow v))

end BrooksSubcubic
end
