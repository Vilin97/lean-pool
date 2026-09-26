/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Overlay

/-!
# The polygonal overlay, assembled into a plane graph

`Schoenflies/Overlay.lean` does the separating half of `lem:polygonal-overlay`: after cutting
at the right points, two pieces of the subdivision whose interiors meet are the **same
segment**, in one order or the other. This module turns that into a plane graph.

The only thing standing between "the same segment" and "the same edge" is that a segment has
two names, `(a, b)` and `(b, a)`. `orientPiece` removes the choice by fixing a total order on
plane points — `Precedes`, lexicographic in the coordinates — and putting the smaller end
first. Two names for one segment then orient to the *same* name, so "represent each duplicated
subsegment once" stops being deduplication up to reversal and becomes deduplication up to
equality, which `List.dedup` does without knowing any geometry. Nothing geometric rests on
which order it is: only `precedes_total` and `eq_of_precedes_of_precedes` are ever used.

The graph is `overlayGraph`, a `Graph Plane Piece`: its edges are the oriented, deduplicated
pieces, and its vertices are their ends. `IsLink P x y` says that `P` is an edge and that `x`
and `y` are its two ends in one order or the other — which is why
`eq_or_eq_of_isLink_of_isLink` is a two-line case split rather than an argument.

The three clauses of `Graph.IsDrawing` come out as follows.

* *Each edge is drawn by an arc between its ends* — `isArcBetween_segment`, given
  nondegeneracy, which `subdivide_ne` preserves and orienting does not disturb.
* *An edge's arc meets the vertex set only at its own ends* — a vertex is an end of some
  edge, hence a cut point, and `subdivide_avoids` says a cut point is interior to nothing.
* *Distinct edges meet only at shared vertices* — a common point that is an end of neither
  would be interior to both, and `subdivide_separated` would make the two pieces the same
  segment, hence (after orienting) the same name. Once it is an end of one it is a cut point,
  so it cannot be interior to the other either, and it is an end of both.

## Blueprint

* `Precedes`, `orientPiece` — the canonical orientation of a segment.
* `overlayPieces`, `overlayGraph`, `segmentDrawing` — the graph of Lemma 3.7.
* `polygonal_overlay` — Lemma 3.7 (polygonal overlay), the whole statement.
-/

public section

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### A total order on plane points

It exists to pick one of two points canonically. Only two facts about it are used: that it
compares any two points, and that it cannot rank two distinct points both ways round. -/

/-- The lexicographic order on plane points: first coordinate, then second. -/
def Precedes (p q : Plane) : Prop := p 0 < q 0 ∨ (p 0 = q 0 ∧ p 1 ≤ q 1)

theorem precedes_total (p q : Plane) : Precedes p q ∨ Precedes q p := by
  rcases lt_trichotomy (p 0) (q 0) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total (p 1) (q 1) with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

theorem eq_of_precedes_of_precedes {p q : Plane} (h : Precedes p q) (h' : Precedes q p) :
    p = q := by
  -- Both coordinates are pinned: the first by trichotomy, the second by antisymmetry of `≤`.
  have key : p 0 = q 0 ∧ p 1 = q 1 := by
    rcases h with h | ⟨ha, hb⟩ <;> rcases h' with h' | ⟨ha', hb'⟩
    · exact absurd h (asymm h')
    · exact absurd h (by rw [ha']; exact lt_irrefl _)
    · exact absurd h' (by rw [ha]; exact lt_irrefl _)
    · exact ⟨ha, le_antisymm hb hb'⟩
  ext i
  fin_cases i
  · exact key.1
  · exact key.2

/-! ### The canonical orientation of a piece -/

open scoped Classical in
/-- A piece with its ends in lexicographic order. Two names for one segment orient to the
same name; that is the whole purpose. -/
noncomputable def orientPiece (P : Piece) : Piece :=
  if Precedes P.1 P.2 then P else (P.2, P.1)

theorem orientPiece_of_precedes {P : Piece} (h : Precedes P.1 P.2) : orientPiece P = P := by
  classical
  exact ite_eq_left h

theorem orientPiece_of_not_precedes {P : Piece} (h : ¬ Precedes P.1 P.2) :
    orientPiece P = (P.2, P.1) := by
  classical
  exact ite_eq_right h

/-- Orienting does not move the segment. -/
@[simp] theorem orientPiece_seg (P : Piece) : (orientPiece P).seg = P.seg := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact segment_symm ℝ _ _

/-- Nor the interior. -/
@[simp] theorem orientPiece_interior (P : Piece) : (orientPiece P).interior = P.interior := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact openSegment_symm ℝ _ _

/-- Nor which points are its ends. -/
theorem orientPiece_ends (P : Piece) (z : Plane) :
    (z = (orientPiece P).1 ∨ z = (orientPiece P).2) ↔ (z = P.1 ∨ z = P.2) := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact or_comm

theorem orientPiece_nondeg {P : Piece} (h : P.Nondeg) : (orientPiece P).Nondeg := by
  by_cases hp : Precedes P.1 P.2
  · rw [orientPiece_of_precedes hp]; exact h
  · rw [orientPiece_of_not_precedes hp]; exact fun e => h e.symm

/-- The output is oriented — which is what makes `orientPiece` idempotent. -/
theorem precedes_orientPiece (P : Piece) : Precedes (orientPiece P).1 (orientPiece P).2 := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]; exact h
  · rw [orientPiece_of_not_precedes h]
    exact (precedes_total P.1 P.2).resolve_left h

@[simp] theorem orientPiece_idem (P : Piece) : orientPiece (orientPiece P) = orientPiece P :=
  orientPiece_of_precedes (precedes_orientPiece P)

/-- **Orienting forgets the name it was given.** This is the fact that makes deduplication
carry no geometry. -/
@[simp] theorem orientPiece_swap (P : Piece) : orientPiece (P.2, P.1) = orientPiece P := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
    by_cases h' : Precedes P.2 P.1
    · -- Each end precedes the other, so they are the same point and the pair is its own
      -- reversal.
      have he : P.1 = P.2 := eq_of_precedes_of_precedes h h'
      rw [orientPiece_of_precedes (P := (P.2, P.1)) h']
      exact Prod.ext he.symm he
    · rw [orientPiece_of_not_precedes (P := (P.2, P.1)) h']
  · rw [orientPiece_of_not_precedes h,
      orientPiece_of_precedes (P := (P.2, P.1)) ((precedes_total P.1 P.2).resolve_left h)]

/-! ### Deduplication

`cover` only sees which pieces are in the list, so both steps of the assembly — orienting and
deduplicating — leave it alone. -/

theorem cover_eq_of_mem_iff {l₁ l₂ : List Piece} (h : ∀ P, P ∈ l₁ ↔ P ∈ l₂) :
    cover l₁ = cover l₂ := by
  ext x
  simp only [cover, mem_iUnion, exists_prop]
  exact ⟨fun ⟨P, hP, hx⟩ => ⟨P, (h P).1 hP, hx⟩, fun ⟨P, hP, hx⟩ => ⟨P, (h P).2 hP, hx⟩⟩

theorem cover_map_orientPiece (l : List Piece) : cover (l.map orientPiece) = cover l := by
  ext x
  simp only [cover, mem_iUnion, exists_prop, List.mem_map]
  constructor
  · rintro ⟨P, ⟨Q, hQ, rfl⟩, hx⟩
    exact ⟨Q, hQ, by rwa [orientPiece_seg] at hx⟩
  · rintro ⟨Q, hQ, hx⟩
    exact ⟨orientPiece Q, ⟨Q, hQ, rfl⟩, by rwa [orientPiece_seg]⟩

open scoped Classical in
/-- The edges of the overlay: the pieces of the subdivision, oriented and then deduplicated.
Orienting is what makes the deduplication a plain list operation. -/
noncomputable def overlayPieces (pieces : List Piece) (points : List Plane) : List Piece :=
  ((subdivide pieces points).map orientPiece).dedup

theorem mem_overlayPieces {pieces : List Piece} {points : List Plane} {P : Piece} :
    P ∈ overlayPieces pieces points ↔ ∃ Q ∈ subdivide pieces points, orientPiece Q = P := by
  rw [overlayPieces, List.mem_dedup, List.mem_map]

/-- The list of edges has no duplicates. -/
theorem overlayPieces_nodup (pieces : List Piece) (points : List Plane) :
    (overlayPieces pieces points).Nodup :=
  List.nodup_dedup _

/-- Neither orienting nor deduplicating changes what the pieces occupy. -/
theorem overlayPieces_cover (pieces : List Piece) (points : List Plane) :
    cover (overlayPieces pieces points) = cover pieces := by
  rw [overlayPieces,
    cover_eq_of_mem_iff (l₂ := (subdivide pieces points).map orientPiece) fun _ => List.mem_dedup,
    cover_map_orientPiece, subdivide_cover]

theorem overlayPieces_nondeg {pieces : List Piece} (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) : ∀ P ∈ overlayPieces pieces points, P.Nondeg := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  exact orientPiece_nondeg (subdivide_ne points hnd Q hQ)

/-- Every end of every edge is a cut point: orienting does not change which points are ends,
and `subdivide_ends_are_cuts` covers the subdivision. -/
theorem overlayPieces_ends_cut {pieces : List Piece} {points : List Plane}
    (hEnds : EndsAreCut pieces points) :
    ∀ P ∈ overlayPieces pieces points, ∀ z, (z = P.1 ∨ z = P.2) → z ∈ points := by
  intro P hP z hz
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  exact subdivide_ends_are_cuts hEnds Q hQ z ((orientPiece_ends Q z).1 hz)

/-- And a cut point is interior to no edge. -/
theorem overlayPieces_avoids {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∀ p ∈ points, ∀ P ∈ overlayPieces pieces points, p ∉ P.interior := by
  intro p hp P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  rw [orientPiece_interior]
  exact subdivide_avoids points hnd p hp Q hQ

/-- **Distinct edges have disjoint interiors.** This is where separation is spent: two pieces
sharing an interior point are the same segment, so after orienting they are the same *name*,
and a deduplicated list holds a name once. -/
theorem overlayPieces_disjoint_interiors {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) {P Q : Piece}
    (hP : P ∈ overlayPieces pieces points) (hQ : Q ∈ overlayPieces pieces points)
    (hPQ : P ≠ Q) {x : Plane} (hxP : x ∈ P.interior) : x ∉ Q.interior := by
  intro hxQ
  obtain ⟨P', hP', rfl⟩ := mem_overlayPieces.1 hP
  obtain ⟨Q', hQ', rfl⟩ := mem_overlayPieces.1 hQ
  rw [orientPiece_interior] at hxP hxQ
  rcases subdivide_separated hnd hEnds hMeets hP' hQ' hxP hxQ with h | h
  · exact hPQ (by rw [h])
  · exact hPQ (by rw [h, orientPiece_swap])

/-! ### The graph -/

/-- The ends of a list of pieces. -/
@[expose] def endSet (edges : List Piece) : Set Plane := {v | ∃ P ∈ edges, v = P.1 ∨ v = P.2}

/-- The overlay graph: the oriented deduplicated pieces as edges, their ends as vertices.

An edge links `x` and `y` exactly when they are its two ends in one order or the other, which
is what makes `eq_or_eq_of_isLink_of_isLink` a case split with no content. -/
@[expose] noncomputable def overlayGraph (pieces : List Piece) (points : List Plane) :
    Graph Plane Piece where
  vertexSet := endSet (overlayPieces pieces points)
  IsLink P x y := P ∈ overlayPieces pieces points ∧
    ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1))
  edgeSet := {P | P ∈ overlayPieces pieces points}
  isLink_symm := fun _ _ => ⟨fun _ _ h => ⟨h.1, by tauto⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro P x y v w ⟨-, hxy⟩ ⟨-, hvw⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro P
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun hP => ⟨P.1, P.2, hP, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hP, _⟩ => hP⟩
  left_mem_of_isLink := by
    rintro P x y ⟨hP, h⟩
    exact ⟨P, hP, by tauto⟩

variable {pieces : List Piece} {points : List Plane} {P : Piece} {x y v : Plane}

@[simp] theorem overlayGraph_vertexSet :
    V(overlayGraph pieces points) = endSet (overlayPieces pieces points) := rfl

@[simp] theorem overlayGraph_mem_edgeSet :
    P ∈ E(overlayGraph pieces points) ↔ P ∈ overlayPieces pieces points := Iff.rfl

@[simp] theorem overlayGraph_isLink :
    (overlayGraph pieces points).IsLink P x y ↔
      P ∈ overlayPieces pieces points ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := Iff.rfl

theorem overlayGraph_mem_vertexSet :
    v ∈ V(overlayGraph pieces points) ↔ ∃ P ∈ overlayPieces pieces points, v = P.1 ∨ v = P.2 :=
  Iff.rfl

/-- An end of an edge is a vertex. -/
theorem overlayGraph_inc (hP : P ∈ overlayPieces pieces points) (h : v = P.1 ∨ v = P.2) :
    (overlayGraph pieces points).Inc P v := by
  rcases h with rfl | rfl
  · exact ⟨P.2, hP, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨P.1, hP, Or.inr ⟨rfl, rfl⟩⟩

/-! ### The drawing

A straight edge is drawn by the affine parametrization of its segment, so the arc clause of
`IsDrawing` is `isArcBetween_segment` and nothing else. -/

/-- Every piece is drawn by the affine parametrization of its segment. -/
@[expose] noncomputable def segmentDrawing (P : Piece) : ℝ → Plane := AffineMap.lineMap P.1 P.2

@[simp] theorem edgeArc_segmentDrawing (P : Piece) :
    Graph.edgeArc segmentDrawing P = P.seg :=
  (segment_eq_image_lineMap ℝ P.1 P.2).symm

/-- **The overlay graph is a plane graph.** -/
theorem overlayGraph_isDrawing (pieces : List Piece) (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) :
    Graph.IsDrawing (overlayGraph pieces points) segmentDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · -- An edge is a nondegenerate segment, and `segmentDrawing` IS its parametrization.
    intro P hP
    have hne : P.Nondeg := overlayPieces_nondeg points hnd P (by simpa using hP)
    refine ⟨AffineMap.lineMap_continuous.continuousOn, injOn_lineMap hne, ?_⟩
    have h0 : segmentDrawing P 0 = P.1 := by simp [segmentDrawing]
    have h1 : segmentDrawing P 1 = P.2 := by simp [segmentDrawing]
    rw [h0, h1]
    exact ⟨by simpa using hP, Or.inl ⟨rfl, rfl⟩⟩
  · -- A vertex is an end of some edge, hence a cut point, hence interior to nothing; and a
    -- point of a segment that is not interior to it is one of its ends.
    rintro P a b w ⟨hP, h⟩ hw hwarc
    rw [edgeArc_segmentDrawing] at hwarc
    obtain ⟨R, hR, hwR⟩ := hw
    have hwint : w ∉ P.interior :=
      overlayPieces_avoids hnd w (overlayPieces_ends_cut hEnds R hR w hwR) P hP
    have hend : w = P.1 ∨ w = P.2 := by
      by_contra hcon
      push Not at hcon
      exact hwint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hwarc)
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hend
    · exact hend.symm
  · -- A common point is an end of both edges: if it were an end of neither it would be
    -- interior to both, and if it were an end of just one it would be a cut point, hence not
    -- interior to the other.
    rintro P Q hP hQ hPQ p hpP hpQ
    rw [overlayGraph_mem_edgeSet] at hP hQ
    rw [edgeArc_segmentDrawing] at hpP hpQ
    have key : ∀ A B : Piece, A ∈ overlayPieces pieces points →
        B ∈ overlayPieces pieces points → A ≠ B → p ∈ A.seg → p ∈ B.seg →
        (p = A.1 ∨ p = A.2) := by
      intro A B hA hB hAB hpA hpB
      by_contra hcon
      push Not at hcon
      have hintA : p ∈ A.interior :=
        mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hpA
      by_cases hendB : p = B.1 ∨ p = B.2
      · exact overlayPieces_avoids hnd p (overlayPieces_ends_cut hEnds B hB p hendB) A hA hintA
      · push Not at hendB
        have hintB : p ∈ B.interior :=
          mem_openSegment_of_ne_left_right (Ne.symm hendB.1) (Ne.symm hendB.2) hpB
        exact overlayPieces_disjoint_interiors hnd hEnds hMeets hA hB hAB hintA hintB
    have hendP := key P Q hP hQ hPQ hpP hpQ
    have hendQ := key Q P hQ hP (Ne.symm hPQ) hpQ hpP
    exact ⟨⟨P, hP, hendP⟩, overlayGraph_inc hP hendP, overlayGraph_inc hQ hendQ⟩

/-- What the graph occupies is what its edges occupy: every vertex is an end of an edge, so
the vertices add nothing. -/
theorem overlayGraph_pointSet (pieces : List Piece) (points : List Plane) :
    Graph.pointSet (overlayGraph pieces points) segmentDrawing = cover pieces := by
  rw [← overlayPieces_cover pieces points]
  ext z
  simp only [Graph.pointSet, mem_union, mem_iUnion, exists_prop, overlayGraph_vertexSet,
    endSet, Set.mem_ofPred_eq, overlayGraph_mem_edgeSet, edgeArc_segmentDrawing, cover]
  constructor
  · rintro (⟨P, hP, hzP⟩ | ⟨P, hP, hzP⟩)
    · refine ⟨P, hP, ?_⟩
      rcases hzP with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    · exact ⟨P, hP, hzP⟩
  · rintro ⟨P, hP, hzP⟩
    exact Or.inr ⟨P, hP, hzP⟩

/-! ### Finiteness

Without this the whole face and outer-face machinery of `Schoenflies/Graph/Drawing.lean` and
`Schoenflies/Graph/OuterFace.lean` is inapplicable to the overlay, since every statement there
carries a `[G.Finite]` instance. Both sets come from one finite list, so it is immediate — but
it has to be said, and the instance has to be found by typeclass search at the call site. -/

theorem finite_endSet (edges : List Piece) : (endSet edges).Finite := by
  -- The end set is the image of a finite list under the two projections.
  have : endSet edges ⊆ (fun P : Piece => P.1) '' {P | P ∈ edges}
      ∪ (fun P : Piece => P.2) '' {P | P ∈ edges} := by
    rintro v ⟨P, hP, rfl | rfl⟩
    · exact Or.inl ⟨P, hP, rfl⟩
    · exact Or.inr ⟨P, hP, rfl⟩
  exact Set.Finite.subset
    ((edges.finite_toSet.image _).union (edges.finite_toSet.image _)) this

instance overlayGraph_finite (pieces : List Piece) (points : List Plane) :
    Graph.Finite (overlayGraph pieces points) where
  finite_vertexSet := finite_endSet _
  finite_edgeSet := (overlayPieces pieces points).finite_toSet

/-- **Lemma 3.7 (polygonal overlay).** Finitely many nondegenerate segments are the point set
of a *finite* plane graph.

The finiteness clause is not decoration. Every statement about faces and about the outer face
carries a `[G.Finite]` instance, and an existential that produced only `IsDrawing` would hide
the graph behind a binder with no way to recover the instance — so the overlay could not be
fed to the face machinery at all. -/
theorem polygonal_overlay (pieces : List Piece) (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∃ G : Graph Plane Piece, Graph.Finite G ∧ Graph.IsDrawing G segmentDrawing ∧
      Graph.pointSet G segmentDrawing = cover pieces := by
  obtain ⟨points, hEnds, hMeets⟩ := exists_cut_points pieces
  exact ⟨overlayGraph pieces points, overlayGraph_finite pieces points,
    overlayGraph_isDrawing pieces points hnd hEnds hMeets,
    overlayGraph_pointSet pieces points⟩

end Schoenflies
