/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Relation

/-!
# Trusted statement layer for Sabidussi compatibility

This module contains only the public data and predicates occurring in the headline theorem. It is
the trusted import boundary for `leanprover/comparator`; proof modules build on it, but it does not
import them.
-/

namespace Sabidussi

/-- A finite labelled endpoint multigraph. Parallel edges and loops are allowed. -/
structure LoopMultigraph (V E : Type*) [Fintype V] [Fintype E] where
  /-- The two numbered endpoints of each labelled edge. -/
  endAt : E → Fin 2 → V

namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- A labelled edge together with one of its two numbered ends. -/
abbrev HalfEdge (E : Type*) := E × Fin 2

/-- The endpoint vertex of a half-edge. -/
def vertex (G : LoopMultigraph V E) (h : HalfEdge E) : V := G.endAt h.1 h.2

/-- Half-edges incident with a vertex. A loop contributes both of its numbered ends. -/
def halfEdgesAt (G : LoopMultigraph V E) (v : V) :=
  {h : HalfEdge E // G.vertex h = v}

instance (G : LoopMultigraph V E) (v : V) : Fintype (G.halfEdgesAt v) :=
  Subtype.fintype fun h : HalfEdge E ↦ G.vertex h = v

/-- Degree counted in half-edge incidences. -/
def degree (G : LoopMultigraph V E) (v : V) : ℕ :=
  Fintype.card (G.halfEdgesAt v)

variable {V E : Type*} [Fintype V] [Fintype E]

/-- A nonempty closed Euler tour using every labelled edge exactly once. -/
structure EulerTour (G : LoopMultigraph V E) where
  /-- The edge positions are `Fin (n + 1)`. -/
  n : ℕ
  /-- Every edge object occurs at exactly one position. -/
  edge : Fin (n + 1) ≃ E
  /-- The end from which the edge at a position is traversed. -/
  depart : Fin (n + 1) → Fin 2
  /-- The arrival end at a position is the departure vertex at the next position. -/
  continuous : ∀ i,
    G.endAt (edge i) (Fin.rev (depart i)) =
      G.endAt (edge (finRotate (n + 1) i)) (depart (finRotate (n + 1) i))

namespace EulerTour

variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)

/-- Positions in the cyclic edge word. -/
abbrev Pos := Fin (T.n + 1)

/-- The next edge position. -/
def next (i : T.Pos) : T.Pos := finRotate (T.n + 1) i

/-- The previous edge position. -/
def prev (i : T.Pos) : T.Pos := (finRotate (T.n + 1)).symm i

end EulerTour

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

/-- The ordinary natural-number degree of `v` in an edge set. Edge ends are counted, so this
definition also has the standard behavior for multigraphs. -/
def degreeIn (F : Finset E) (v : V) : ℕ :=
  ((F ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h ↦ G.endAt h.1 h.2 = v).card

/-- Two labelled edges meet if some numbered end of one has the same endpoint as some numbered
end of the other. An edge meets itself, and parallel edges meet at both endpoints. -/
def EdgeAdjacent (e f : E) : Prop :=
  ∃ i j : Fin 2, G.endAt e i = G.endAt f j

/-- Edge-chain connectivity of a nonempty edge-supported subgraph. -/
def EdgeConnected (F : Finset E) : Prop :=
  ∃ root ∈ F, ∀ e ∈ F,
    Relation.ReflTransGen
      (fun x y : E ↦ x ∈ F ∧ y ∈ F ∧ G.EdgeAdjacent x y) root e

/-- The vertices incident with at least one edge of `F`. -/
def edgeSupport (F : Finset E) : Finset V :=
  Finset.univ.filter fun v ↦ ∃ e ∈ F, ∃ i : Fin 2, G.endAt e i = v

/-- An ordinary circuit: a nonempty connected edge-supported subgraph in which every supported
vertex has degree two. -/
structure OrdinaryCircuit where
  /-- The edges of the circuit. -/
  edges : Finset E
  /-- An ordinary circuit is nonempty. -/
  nonempty : edges.Nonempty
  /-- The circuit is edge-connected. -/
  connected : G.EdgeConnected edges
  /-- Every supported vertex has ordinary degree two. -/
  twoRegular : ∀ v : V, v ∈ G.edgeSupport edges → G.degreeIn edges v = 2

/-- A partition of all labelled edges into ordinary connected 2-regular circuits. -/
structure OrdinaryCircuitDecomposition where
  /-- The list of ordinary circuits partitioning the edges. -/
  circuits : List G.OrdinaryCircuit
  /-- Every labelled edge lies in exactly one circuit. -/
  coveredOnce : ∀ e : E, (circuits.filter fun C ↦ e ∈ C.edges).length = 1

/-- Compatibility stated for ordinary circuits. -/
def OrdinaryCircuitDecomposition.Compatible {G : LoopMultigraph V E}
    (S : G.OrdinaryCircuitDecomposition) (T : G.EulerTour) : Prop :=
  ∀ (i : T.Pos) (C : G.OrdinaryCircuit), C ∈ S.circuits →
    ¬ (T.edge (T.prev i) ∈ C.edges ∧ T.edge i ∈ C.edges)

end LoopMultigraph
end Sabidussi
