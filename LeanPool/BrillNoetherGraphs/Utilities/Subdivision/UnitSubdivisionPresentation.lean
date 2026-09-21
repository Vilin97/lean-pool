/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.GraphIsoLaplacianEquiv
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionGraph
import Mathlib.Tactic

/-!
# Every finite multigraph as a unit subdivision

This module is the base case for a later weighted-core suppression argument.
For an arbitrary `CFGraph G`, it gives every *occurrence* in the edge multiset
its own ordered edge slot, labels the vertices by `Fin`, assigns length one to
every slot, and identifies `G` with the resulting `SubdivisionGraph.Spec.graph`
by a `LaplacianEquiv`.

The edge enumeration deliberately uses Mathlib's multiset-as-type `G.edges`.
Thus two equal pairs occurring with multiplicity two give two different terms
of `G.edges`, hence two different slots.  No conversion through `toFinset` is
used, so parallel edges are never collapsed.
-/

namespace Utilities.Certificate.UnitSubdivisionPresentation

open Finset Multiset

open ExplicitPotential SubdivisionGraph

universe u

variable (G : CFGraph.{u})

/-- A fixed finite label for each vertex of `G`. -/
noncomputable def vertexEquiv : G.V ≃ Fin (Fintype.card G.V) :=
  Fintype.equivFin G.V

/-- A fixed finite label for each occurrence in the edge multiset of `G`.

The domain is the multiset-as-type: its second dependent coordinate
distinguishes repeated copies of the same endpoint pair.
-/
noncomputable def edgeEquiv : G.edges ≃ Fin G.edges.card := by
  simpa using Fintype.equivFin G.edges

/-- The actual multiset occurrence occupying an ordered edge slot. -/
noncomputable def edgeOccurrence (slot : Fin G.edges.card) : G.edges :=
  (edgeEquiv G).symm slot

/-- The endpoint pair underlying an ordered edge slot. -/
noncomputable def edgeAt (slot : Fin G.edges.card) : G.V × G.V :=
  (edgeOccurrence G slot : G.V × G.V)

@[simp] theorem edgeEquiv_edgeOccurrence (slot : Fin G.edges.card) :
    edgeEquiv G (edgeOccurrence G slot) = slot := by
  simp [edgeOccurrence]

@[simp] theorem edgeOccurrence_edgeEquiv (occurrence : G.edges) :
    edgeOccurrence G (edgeEquiv G occurrence) = occurrence := by
  simp [edgeOccurrence]

/-- Distinct multiset occurrences always receive distinct slots, even when
their coerced endpoint pairs are equal. -/
@[simp] theorem edgeEquiv_inj (first second : G.edges) :
    edgeEquiv G first = edgeEquiv G second ↔ first = second :=
  (edgeEquiv G).injective.eq_iff

@[simp] theorem edgeAt_edgeEquiv (occurrence : G.edges) :
    edgeAt G (edgeEquiv G occurrence) =
      (occurrence : G.V × G.V) := by
  simp [edgeAt]

theorem edgeAt_mem (slot : Fin G.edges.card) :
    edgeAt G slot ∈ G.edges := by
  exact Multiset.coe_mem

theorem edgeAt_fst_ne_snd (slot : Fin G.edges.card) :
    (edgeAt G slot).1 ≠ (edgeAt G slot).2 := by
  intro hEqual
  have hMember := edgeAt_mem G slot
  rcases hEdge : edgeAt G slot with ⟨tail, head⟩
  simp only [hEdge] at hEqual hMember
  subst head
  exact G.loopless tail hMember

/-- The ordered loopless core having one slot for every edge occurrence. -/
noncomputable def core :
    ExplicitPotential.Core (Fintype.card G.V) G.edges.card where
  tail slot := vertexEquiv G (edgeAt G slot).1
  head slot := vertexEquiv G (edgeAt G slot).2

@[simp] theorem core_tail (slot : Fin G.edges.card) :
    (core G).tail slot = vertexEquiv G (edgeAt G slot).1 := rfl

@[simp] theorem core_head (slot : Fin G.edges.card) :
    (core G).head slot = vertexEquiv G (edgeAt G slot).2 := rfl

@[simp] theorem core_tail_edgeEquiv (occurrence : G.edges) :
    (core G).tail (edgeEquiv G occurrence) =
      vertexEquiv G (occurrence : G.V × G.V).1 := by
  simp

@[simp] theorem core_head_edgeEquiv (occurrence : G.edges) :
    (core G).head (edgeEquiv G occurrence) =
      vertexEquiv G (occurrence : G.V × G.V).2 := by
  simp

/-- Every edge occurrence receives length one. -/
def unitLength : Fin G.edges.card → ℕ := fun _slot => 1

@[simp] theorem unitLength_apply (slot : Fin G.edges.card) :
    unitLength G slot = 1 := rfl

/-- The unit-length subdivision presentation of an arbitrary `CFGraph`. -/
noncomputable def spec :
    SubdivisionGraph.Spec (Fintype.card G.V) G.edges.card where
  core := core G
  length := unitLength G
  core_nonempty := Fintype.card_pos
  core_loopless := by
    intro slot hEqual
    exact edgeAt_fst_ne_snd G slot
      ((vertexEquiv G).injective hEqual)
  length_pos := by simp

@[simp] theorem spec_length (slot : Fin G.edges.card) :
    (spec G).length slot = 1 := rfl

/-- With unit lengths, a unit step is exactly an original edge occurrence. -/
noncomputable def stepEquiv : (spec G).Step ≃ G.edges where
  toFun step := edgeOccurrence G step.1
  invFun occurrence :=
    ⟨edgeEquiv G occurrence, ⟨0, by simp⟩⟩
  left_inv := by
    intro step
    rcases step with ⟨slot, offset⟩
    apply Sigma.ext
    · simp
    · simp only [spec_length]
      apply heq_of_eq
      apply Fin.ext
      have hlt := offset.isLt
      have hLength : (spec G).length slot = 1 := spec_length G slot
      omega
  right_inv := by
    intro occurrence
    simp

@[simp] theorem stepEquiv_apply (step : (spec G).Step) :
    stepEquiv G step = edgeOccurrence G step.1 := rfl

@[simp] theorem stepEquiv_symm_fst (occurrence : G.edges) :
    ((stepEquiv G).symm occurrence).1 = edgeEquiv G occurrence := rfl

/-- There are no interior vertices when every slot has length one. -/
theorem noInterior (interior : (spec G).Interior) : False := by
  exact Fin.elim0 interior.2

/-- The original vertices are exactly all vertices of the unit subdivision. -/
noncomputable def graphVertexEquiv : G.V ≃ (spec G).graph.V where
  toFun vertex := (spec G).coreVertex (vertexEquiv G vertex)
  invFun vertex :=
    match vertex with
    | Sum.inl coreVertex => (vertexEquiv G).symm coreVertex
    | Sum.inr interior => False.elim (noInterior G interior)
  left_inv := by
    intro vertex
    simp [SubdivisionGraph.Spec.coreVertex]
  right_inv := by
    intro vertex
    rcases vertex with coreVertex | interior
    · simp [SubdivisionGraph.Spec.coreVertex]
    · exact False.elim (noInterior G interior)

@[simp] theorem graphVertexEquiv_apply (vertex : G.V) :
    graphVertexEquiv G vertex =
      (spec G).coreVertex (vertexEquiv G vertex) := rfl

/-- The endpoints emitted by a unit step are the relabeled endpoints of its
underlying original edge occurrence. -/
theorem unitEdge_eq (step : (spec G).Step) :
    (spec G).unitEdge step =
      (graphVertexEquiv G (edgeAt G step.1).1,
       graphVertexEquiv G (edgeAt G step.1).2) := by
  rcases step with ⟨slot, offset⟩
  rcases offset with ⟨offset, hOffset⟩
  have hOffsetZero : offset = 0 := by
    change offset < 1 at hOffset
    omega
  subst offset
  unfold SubdivisionGraph.Spec.unitEdge
  apply Prod.ext
  · rw [(spec G).stepLeft_zero slot]
    rfl
  · calc
      (spec G).stepRight slot ⟨0, hOffset⟩ =
          (spec G).coreVertex ((spec G).core.head slot) := by
            simpa [spec_length] using (spec G).stepRight_last slot
      _ = graphVertexEquiv G
          (edgeAt G slot).2 := rfl

/-- Filtering the type of occurrences has the same cardinality as filtering
the underlying multiset.  This is the bookkeeping lemma that retains parallel
edge multiplicities in the final `num_edges` proof. -/
theorem card_filter_occurrences {α : Type*} [DecidableEq α]
    (edges : Multiset α) (predicate : α → Prop) [DecidablePred predicate] :
    ((Finset.univ : Finset edges).filter
      (fun occurrence : edges => predicate (occurrence : α))).card =
      (edges.filter predicate).card := by
  change ((Finset.univ : Finset edges).val.filter
      (fun occurrence : edges => predicate (occurrence : α))).card = _
  calc
    _ = Multiset.countP predicate
        ((Finset.univ : Finset edges).val.map
          fun occurrence : edges => (occurrence : α)) := by
          exact (Multiset.countP_map
            (fun occurrence : edges => (occurrence : α))
            (Finset.univ : Finset edges).val predicate).symm
    _ = Multiset.countP predicate edges := by
      rw [Multiset.map_univ_coe]
    _ = (edges.filter predicate).card :=
      Multiset.countP_eq_card_filter predicate edges

/-- Unit subdivision preserves every unordered edge multiplicity. -/
theorem num_edges_graphVertexEquiv (x y : G.V) :
    num_edges (spec G).graph (graphVertexEquiv G x)
        (graphVertexEquiv G y) =
      num_edges G x y := by
  rw [(spec G).num_edges_eq_card_filter_steps]
  unfold num_edges
  let stepPredicate : (spec G).Step → Prop := fun step =>
    (spec G).unitEdge step =
        (graphVertexEquiv G x, graphVertexEquiv G y) ∨
      (spec G).unitEdge step =
        (graphVertexEquiv G y, graphVertexEquiv G x)
  let occurrencePredicate : G.edges → Prop := fun occurrence =>
    (occurrence : G.V × G.V) = (x, y) ∨
      (occurrence : G.V × G.V) = (y, x)
  have hPredicate (step : (spec G).Step) :
      stepPredicate step ↔ occurrencePredicate (stepEquiv G step) := by
    rw [show stepPredicate step =
        ((spec G).unitEdge step =
            (graphVertexEquiv G x, graphVertexEquiv G y) ∨
          (spec G).unitEdge step =
            (graphVertexEquiv G y, graphVertexEquiv G x)) by rfl]
    rw [unitEdge_eq G step]
    simp only [occurrencePredicate, Prod.ext_iff,
      (graphVertexEquiv G).injective.eq_iff]
    rfl
  have hFilter :
      ((Finset.univ.filter stepPredicate).map
          (stepEquiv G).toEmbedding) =
        Finset.univ.filter occurrencePredicate := by
    ext occurrence
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨step, hStep, rfl⟩
      exact (hPredicate step).mp hStep
    · intro hOccurrence
      refine ⟨(stepEquiv G).symm occurrence, ?_, by simp⟩
      apply (hPredicate _).mpr
      simpa
  change (Finset.univ.filter stepPredicate).card =
    (G.edges.filter fun edge => edge = (x, y) ∨ edge = (y, x)).card
  rw [← card_filter_occurrences G.edges
    (fun edge => edge = (x, y) ∨ edge = (y, x))]
  change (Finset.univ.filter stepPredicate).card =
    (Finset.univ.filter occurrencePredicate).card
  rw [← hFilter, Finset.card_map]

/-- Every finite loopless multigraph is Laplacian-equivalent to the
unit-length subdivision with one distinct slot per edge occurrence. -/
noncomputable def laplacianEquiv :
    LaplacianEquiv G (spec G).graph where
  toEquiv := graphVertexEquiv G
  num_edges_eq := num_edges_graphVertexEquiv G

/-- Full finite-length transmission existence is unchanged when an arbitrary
finite graph is presented as its occurrence-safe unit subdivision.  Parallel
edges remain distinct slots, and both marks are carried to their corresponding
embedded core vertices. -/
theorem transmissionExistence_iff (u v : G.V) :
    TransmissionExistence (spec G).graph
        (graphVertexEquiv G u) (graphVertexEquiv G v) ↔
      TransmissionExistence G u v :=
  (laplacianEquiv G).transmissionExistence_map_iff u v

end Utilities.Certificate.UnitSubdivisionPresentation
