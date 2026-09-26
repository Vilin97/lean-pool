/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.StallingsFolding.Folding

/-!
# Folding a closed set of vertices

Restricting to an edge-closed set containing the basepoint preserves all based
loops. The restricted folding theorem only needs a potential on that set, so
unrelated connected components impose no hypotheses. This extension was added
during the AI-assisted Lean Pool port of Arthur Freitas Ramos' development.
-/

@[expose] public section

namespace Stallings
namespace InverseMultigraph

variable {V : Type*} [DecidableEq V] (G : InverseMultigraph V)

/-- The induced inverse multigraph on a finite set of vertices. -/
def restrict (vertices : Finset V) : InverseMultigraph {v // v ∈ vertices} where
  edges v x := Finset.univ.filter fun w => w.val ∈ G.edges v.val x
  inverse_edges v x w := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      G.inverse_edges v.val x w.val

/-- A vertex set is closed when every edge starting in it also ends in it. -/
def IsClosed (vertices : Finset V) : Prop :=
  ∀ ⦃v x w⦄, v ∈ vertices → w ∈ G.edges v x → w ∈ vertices

/-- A path in the induced graph is also a path in the original graph. -/
theorem Walk.of_restrict {vertices : Finset V} {v z : {v // v ∈ vertices}} {w : Word}
    (h : (G.restrict vertices).Walk v w z) : G.Walk v.val w z.val := by
  induction h with
  | nil v => exact Walk.nil v.val
  | cons edge tail ih =>
      exact Walk.cons (Finset.mem_filter.mp edge).2 ih

/-- Paths starting in a closed vertex set can be lifted to its induced graph. -/
theorem Walk.restrict {vertices : Finset V} (hclosed : G.IsClosed vertices)
    {v z : V} {w : Word} (h : G.Walk v w z) :
    ∀ hv : v ∈ vertices, ∃ hz : z ∈ vertices,
      (G.restrict vertices).Walk ⟨v, hv⟩ w ⟨z, hz⟩ := by
  induction h with
  | nil v =>
      intro hv
      exact ⟨hv, Walk.nil _⟩
  | cons edge tail ih =>
      intro hv
      rcases ih (hclosed hv edge) with ⟨hz, htail⟩
      refine ⟨hz, Walk.cons ?_ htail⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, edge⟩

/-- Restricting to a closed set containing the basepoint preserves its loop subgroup. -/
theorem restrict_loopSubgroup_eq (vertices : Finset V) (hclosed : G.IsClosed vertices)
    (base : {v // v ∈ vertices}) :
    (G.restrict vertices).loopSubgroup base = G.loopSubgroup base.val := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    rintro g ⟨w, hw, hwalk⟩
    exact Subgroup.subset_closure ⟨w, hw, hwalk.of_restrict G⟩
  · apply (Subgroup.closure_le _).2
    rintro g ⟨w, hw, hwalk⟩
    obtain ⟨hbase, hrestricted⟩ := hwalk.restrict G hclosed base.property
    exact Subgroup.subset_closure ⟨w, hw, hrestricted⟩

/-- Folding an edge-closed set containing the basepoint preserves the original
based-loop subgroup. The potential is required only on the selected vertices. -/
theorem fold_restrict_loopSubgroup_eq [LinearOrder V] (vertices : Finset V)
    (hclosed : G.IsClosed vertices) (base : {v // v ∈ vertices})
    (potential : {v // v ∈ vertices} → Free)
    (hpotential : HasCosetPotential (G.restrict vertices) (G.loopSubgroup base.val) potential)
    (hbase : potential base = 1) :
    (foldAutomaton (G.restrict vertices) base).loopSubgroup = G.loopSubgroup base.val := by
  have hloops := G.restrict_loopSubgroup_eq vertices hclosed base
  rw [← hloops] at hpotential ⊢
  exact foldAutomaton_loopSubgroup_eq (G.restrict vertices) base potential hpotential hbase

end InverseMultigraph
end Stallings
