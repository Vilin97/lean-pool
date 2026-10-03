/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Line-graph colourings and decompositions into matchings

The vertices of Mathlib's line graph are actual graph edges. A colour class
therefore defines a matching subgraph with precisely the incident vertices,
not a spanning subgraph with isolated vertices. Conversely, a partition of
the edges into matching subgraphs defines a proper colouring of the line graph.

Neither construction requires a finite graph, a finite palette, or a default
colour. Empty classes are allowed. These are classical equivalences of
representations, not new graph-theoretic bounds.
-/

public section

namespace SimpleGraph

variable {V C : Type*} {G : SimpleGraph V}

/-- A palette-indexed partition of the actual edges into Mathlib matchings.
Distinct matchings may share vertices, but every edge belongs to exactly one. -/
@[ext]
structure MatchingDecomposition (G : SimpleGraph V) (C : Type*) where
  /-- The matching assigned to a colour; it may be empty. -/
  matching : C → G.Subgraph
  /-- Each colour class is a matching with no isolated vertices. -/
  isMatching : ∀ c, (matching c).IsMatching
  /-- Every actual edge has a unique colour class. -/
  partition : ∀ e : G.edgeSet, ∃! c, e.1 ∈ (matching c).edgeSet

namespace Coloring

/-- The subgraph formed by the edges with one specified line-graph colour. -/
def edgeMatching (K : G.lineGraph.Coloring C) (c : C) : G.Subgraph where
  verts := {v | ∃ w, ∃ h : G.Adj v w, K ⟨s(v, w), h⟩ = c}
  Adj v w := ∃ h : G.Adj v w, K ⟨s(v, w), h⟩ = c
  adj_sub h := h.choose
  edge_vert h := ⟨_, h⟩
  symm.symm v w := by
    rintro ⟨h, hc⟩
    refine ⟨h.symm, ?_⟩
    simpa only [Sym2.eq_swap] using hc

/-- Membership in a matching class is exactly equality of the edge's colour. -/
@[simp]
theorem mem_edgeMatching_edgeSet (K : G.lineGraph.Coloring C) (c : C)
    (e : G.edgeSet) : e.1 ∈ (K.edgeMatching c).edgeSet ↔ K e = c := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf v w =>
    change (∃ h : G.Adj v w, K ⟨s(v, w), h⟩ = c) ↔ _
    exact ⟨fun ⟨_, hc⟩ => hc, fun hc => ⟨he, hc⟩⟩

/-- Edges of the same colour have unique neighbours at each incident vertex. -/
theorem edgeMatching_isMatching (K : G.lineGraph.Coloring C) (c : C) :
    (K.edgeMatching c).IsMatching := by
  rintro v ⟨w, h, hc⟩
  refine ⟨w, ⟨h, hc⟩, ?_⟩
  rintro u ⟨hu, hcu⟩
  have heq : (⟨s(v, u), hu⟩ : G.edgeSet) = ⟨s(v, w), h⟩ := by
    by_contra hne
    have hadj : G.lineGraph.Adj ⟨s(v, u), hu⟩ ⟨s(v, w), h⟩ :=
      lineGraph_adj_iff_exists.mpr ⟨hne, v, by simp, by simp⟩
    exact K.valid hadj (hcu.trans hc.symm)
  have hp := Sym2.eq_iff.mp (congrArg Subtype.val heq)
  rcases hp with hp | hp
  · exact hp.2
  · exact hp.2.trans hp.1

/-- A line-graph colouring partitions the original edges into matching subgraphs. -/
def matchingDecomposition (K : G.lineGraph.Coloring C) : MatchingDecomposition G C where
  matching := K.edgeMatching
  isMatching := K.edgeMatching_isMatching
  partition e := ⟨K e, (K.mem_edgeMatching_edgeSet _ e).mpr rfl,
    fun c hc => ((K.mem_edgeMatching_edgeSet c e).mp hc).symm⟩

end Coloring

namespace MatchingDecomposition

/-- The unique class containing an actual edge. No default colour is required. -/
noncomputable def edgeColour (D : MatchingDecomposition G C) (e : G.edgeSet) : C :=
  Classical.choose (D.partition e)

/-- The chosen colour class contains the edge. -/
theorem mem_edgeColour_matching (D : MatchingDecomposition G C) (e : G.edgeSet) :
    e.1 ∈ (D.matching (D.edgeColour e)).edgeSet :=
  (Classical.choose_spec (D.partition e)).1

/-- The edge belongs to a specified class precisely when it has that colour. -/
theorem mem_matching_iff (D : MatchingDecomposition G C) (e : G.edgeSet) (c : C) :
    e.1 ∈ (D.matching c).edgeSet ↔ D.edgeColour e = c := by
  constructor
  · intro hc
    exact ((Classical.choose_spec (D.partition e)).2 c hc).symm
  · rintro rfl
    exact D.mem_edgeColour_matching e

/-- Each original edge is equivalent to its colour and its edge in that matching. -/
noncomputable def edgeEquivSigma (D : MatchingDecomposition G C) :
    G.edgeSet ≃ Σ c, (D.matching c).edgeSet where
  toFun e := ⟨D.edgeColour e, ⟨e.1, D.mem_edgeColour_matching e⟩⟩
  invFun e := ⟨e.2.1, (D.matching e.1).edgeSet_subset e.2.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨c, e, he⟩
    have hc := (D.mem_matching_iff ⟨e, (D.matching c).edgeSet_subset he⟩ c).mp he
    apply Sigma.ext hc
    exact (Subtype.heq_iff_coe_eq (fun x => by
      change x ∈ (D.matching (D.edgeColour ⟨e, (D.matching c).edgeSet_subset he⟩)).edgeSet ↔
        x ∈ (D.matching c).edgeSet
      rw [hc])).mpr rfl

/-- The edge classes of distinct colours are disjoint, even when their vertices overlap. -/
theorem edgeSet_disjoint (D : MatchingDecomposition G C) {a b : C} (hab : a ≠ b) :
    Disjoint (D.matching a).edgeSet (D.matching b).edgeSet := by
  rw [Set.disjoint_left]
  intro e ha hb
  let edge : G.edgeSet := ⟨e, (D.matching a).edgeSet_subset ha⟩
  exact hab (((D.mem_matching_iff edge a).mp ha).symm.trans
    ((D.mem_matching_iff edge b).mp hb))

/-- The union of all matching classes is exactly the original edge set. -/
theorem iUnion_edgeSet (D : MatchingDecomposition G C) :
    (⋃ c, (D.matching c).edgeSet) = G.edgeSet := by
  ext e
  constructor
  · intro he
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp he
    exact (D.matching c).edgeSet_subset hc
  · intro he
    exact Set.mem_iUnion.mpr ⟨D.edgeColour ⟨e, he⟩,
      D.mem_edgeColour_matching ⟨e, he⟩⟩

/-- A decomposition into matchings gives a proper colouring of the line graph. -/
noncomputable def lineGraphColoring (D : MatchingDecomposition G C) :
    G.lineGraph.Coloring C := Coloring.mk D.edgeColour (by
  intro e f hadj hsame
  obtain ⟨hne, v, hv, hv'⟩ := lineGraph_adj_iff_exists.mp hadj
  obtain ⟨u, hu⟩ := Sym2.mem_iff_exists.mp hv
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv'
  have he := D.mem_edgeColour_matching e
  have hf := D.mem_edgeColour_matching f
  rw [← hsame] at hf
  rw [hu, Subgraph.mem_edgeSet] at he
  rw [hw, Subgraph.mem_edgeSet] at hf
  have huw := (D.isMatching (D.edgeColour e)).eq_of_adj_left he hf
  exact hne (Subtype.ext (hu.trans (huw ▸ hw.symm))))

/-- Converting a decomposition to a colouring preserves each matching exactly. -/
@[simp]
theorem edgeMatching_lineGraphColoring (D : MatchingDecomposition G C) (c : C) :
    D.lineGraphColoring.edgeMatching c = D.matching c := by
  apply Subgraph.IsMatching.injOn_edgeSet
    (Coloring.edgeMatching_isMatching D.lineGraphColoring c) (D.isMatching c)
  ext e
  constructor
  · intro he
    let edge : G.edgeSet := ⟨e, (D.lineGraphColoring.edgeMatching c).edgeSet_subset he⟩
    exact (D.mem_matching_iff edge c).mpr
      ((D.lineGraphColoring.mem_edgeMatching_edgeSet c edge).mp he)
  · intro he
    let edge : G.edgeSet := ⟨e, (D.matching c).edgeSet_subset he⟩
    exact (D.lineGraphColoring.mem_edgeMatching_edgeSet c edge).mpr
      ((D.mem_matching_iff edge c).mp he)

/-- The decomposition-to-colouring-to-decomposition round trip is exact. -/
@[simp]
theorem matchingDecomposition_lineGraphColoring (D : MatchingDecomposition G C) :
    D.lineGraphColoring.matchingDecomposition = D := by
  apply MatchingDecomposition.ext
  funext c
  exact D.edgeMatching_lineGraphColoring c

end MatchingDecomposition

namespace Coloring

/-- The colouring-to-decomposition-to-colouring round trip is exact. -/
@[simp]
theorem lineGraphColoring_matchingDecomposition (K : G.lineGraph.Coloring C) :
    K.matchingDecomposition.lineGraphColoring = K := by
  ext e
  have he := K.matchingDecomposition.mem_edgeColour_matching e
  exact ((K.mem_edgeMatching_edgeSet _ e).mp he).symm

end Coloring

/-- Proper line-graph colourings are equivalent to palette-indexed matching partitions. -/
noncomputable def lineGraphColoringEquivMatchingDecomposition :
    G.lineGraph.Coloring C ≃ MatchingDecomposition G C where
  toFun := Coloring.matchingDecomposition
  invFun := MatchingDecomposition.lineGraphColoring
  left_inv := Coloring.lineGraphColoring_matchingDecomposition
  right_inv := MatchingDecomposition.matchingDecomposition_lineGraphColoring

/-- Existence of a colouring on any palette is equivalent to a matching partition. -/
theorem nonempty_lineGraphColoring_iff_matchingDecomposition :
    Nonempty (G.lineGraph.Coloring C) ↔ Nonempty (MatchingDecomposition G C) :=
  lineGraphColoringEquivMatchingDecomposition.nonempty_congr

/-- Edge colourability with at most `k` colours is equivalent to a decomposition
into `k` matchings; unused colours are represented by empty matchings. -/
theorem lineGraph_colorable_iff_matchingDecomposition (k : ℕ) :
    G.lineGraph.Colorable k ↔ Nonempty (MatchingDecomposition G (Fin k)) :=
  nonempty_lineGraphColoring_iff_matchingDecomposition

end SimpleGraph
