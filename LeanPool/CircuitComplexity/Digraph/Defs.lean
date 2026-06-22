/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Lattice.Nat

/-! # Basic digraph definitions

General-purpose definitions on top of Mathlib's `Digraph`: directed walks
and simple paths, `depth` (longest walk length), `IsAcyclic`, the
`edgeFinset` of a digraph with decidable adjacency on a finite vertex
type, and `deleteEdges`.

Depth-reduction-specific machinery (canonical labeling, acyclicity
arguments, edge partitions by first-differing bit, etc.) lives in
`Circ.Internal.Valiant`.
-/

namespace Digraph

variable {V : Type*}

/-- `G.IsDirectedPath p` says that `p : Fin m → V` is a directed walk
in the digraph `G`: consecutive vertices are joined by an edge. -/
def IsDirectedPath (G : Digraph V) {m : Nat} (p : Fin m → V) : Prop :=
  ∀ i : Fin m, ∀ h : i.val + 1 < m, G.Adj (p i) (p ⟨i.val + 1, h⟩)

/-- `G.IsSimplePath p` says that `p : Fin m → V` is a *simple* directed
path: an injective directed walk. -/
def IsSimplePath (G : Digraph V) {m : Nat} (p : Fin m → V) : Prop :=
  G.IsDirectedPath p ∧ Function.Injective p

/-- The **depth** of a digraph is the length — number of nodes — of a
longest directed walk in it. Walks are not required to be injective,
so cyclic graphs have `depth = 0` by the `Nat.sSup` convention on
unbounded sets. -/
noncomputable def depth (G : Digraph V) : Nat :=
  sSup { m | ∃ p : Fin m → V, G.IsDirectedPath p }

/-- The directed edge set of a digraph with decidable adjacency on a
finite vertex type. -/
def edgeFinset [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  have _hV : DecidableEq V := ‹_›
  Finset.univ.filter (fun p => G.Adj p.1 p.2)

lemma mem_edgeFinset [Fintype V] [DecidableEq V] {G : Digraph V}
    [DecidableRel G.Adj] {e : V × V} : e ∈ G.edgeFinset ↔ G.Adj e.1 e.2 := by
  simp [edgeFinset]

/-- The digraph obtained from `G` by deleting a finite set of directed
edges `F`. -/
def deleteEdges (G : Digraph V) (F : Finset (V × V)) : Digraph V where
  Adj u v := G.Adj u v ∧ (u, v) ∉ F

instance [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (F : Finset (V × V)) : DecidableRel (G.deleteEdges F).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ _))

/-- A digraph is **acyclic** when its set of directed-walk lengths is
bounded. For finite vertex types this is equivalent to having no
directed cycles. -/
def IsAcyclic (G : Digraph V) : Prop :=
  BddAbove { m | ∃ p : Fin m → V, G.IsDirectedPath p }

/-- The directed-walk set of `G.deleteEdges ∅` agrees with that of `G`,
so the two graphs have the same depth. -/
lemma deleteEdges_empty_depth (G : Digraph V) :
    (G.deleteEdges ∅).depth = G.depth := by
  unfold Digraph.depth
  congr 1
  ext m
  refine ⟨fun ⟨p, hp⟩ => ⟨p, fun i h => (hp i h).1⟩, fun ⟨p, hp⟩ => ⟨p, ?_⟩⟩
  intro i h
  exact ⟨hp i h, Finset.notMem_empty _⟩

end Digraph
