/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.OverlayGraph
public import LeanPool.Schoenflies.Graph.CycleJordan

/-!
# Simple polygonal arcs

`Schoenflies/PolyPath.lean` joins two points of a region by a polygonal *path* — a vertex list
whose carrier stays inside the region. A path may cross itself, so it is not an arc. This
module supplies the missing half of Lemma 1.1 and, with it, Lemma 1.2, by running the
blueprint's recipe: *subdivide at all intersections, delete duplicate subsegments, and take a
simple path in the resulting finite graph.*

The three steps are already available.

* Subdividing and deduplicating is `Schoenflies.overlayGraph`: a finite list of nondegenerate
  segments becomes a finite plane graph whose point set is exactly their union
  (`Schoenflies.overlayGraph_pointSet`).
* A simple path in that graph is `Graph.IsPath`, produced by `Graph.Reaches.exists_isPath`.
* Its realisation is an arc between its ends, by `Graph.IsDrawing.path_isArcBetween`.

## What actually has to be proved here

Two things, and neither is in the list above.

**The graph is connected when the union is.** The overlay is built from geometry, so nothing
so far says that two points joined *in the plane* are joined *along edges*. The argument is a
clopen one: for a vertex `a`, the points carried by the edges the walk relation can reach from
`a` form a compact set, the points carried by the other edges form another, the two are
disjoint — a common point would be a vertex incident with edges from both classes, by the
drawing condition — and together they are the whole union. Preconnectedness then forces the
second class to carry nothing.

**The realisation of a path is `poly` of a vertex list.** `Graph.IsDrawing.path_isArcBetween`
delivers `Graph.edgesCover`, a union of edge arcs with no order in it, while `IsPolygonal` and
every polygonal consumer downstream want a vertex list. `Schoenflies.exists_poly_eq_edgesCover`
recovers one by induction along the walk. Its statement returns the list, not the bare
existence of *some* polygonal set, so a consumer that needs the vertices — the redrawing
argument does — still has them.

Both endpoints have to be vertices of the overlay, which is arranged by putting them on the
list of cut points: `EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in
that list, so lengthening it is free.

## Blueprint

* `Schoenflies.segsOf`, `Schoenflies.cover_segsOf` — a vertex list read as a list of
  nondegenerate segments, the input format the overlay wants.
* `Schoenflies.overlayGraph_reaches` — the overlay graph of a connected union is connected.
* `Schoenflies.exists_simple_poly_of_cover` — Lemma 1.2 (finite polygonal unions), for a union
  given as a finite list of nondegenerate segments.
* `Schoenflies.exists_simple_poly_of_poly`, `Schoenflies.exists_simple_poly_of_isPolygonal` —
  Lemma 1.2 for a set presented as a polygonal carrier.
* `Schoenflies.exists_simple_poly_of_biUnion`, `Schoenflies.exists_simple_poly_of_union` —
  Lemma 1.2 as the blueprint states it, for a finite union of polygonal sets.
* `Schoenflies.exists_simple_poly_of_isPreconnected`,
  `Schoenflies.exists_simple_arc_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), in
  full: any two points of a region are joined in it by a *simple* polygonal arc.

## Two lemmas that belong elsewhere

`Schoenflies.cover_flatMap_list` generalises `Schoenflies.cover_flatMap` to an arbitrary index
list and belongs beside it in `Schoenflies/Subdivide.lean`; `Schoenflies.subset_of_finite_diff`
is a general fact about preconnected sets. Both are here only because their homes are on
`main`.
-/

public section

open Metric Set
open scoped Graph

namespace Schoenflies

variable {pieces : List Piece} {points : List Plane} {Ω : Set Plane} {a b x y : Plane}

/-! ### One more shape of `poly`

`poly_cons_cons` peels a segment off a list of length at least two. The overlay's induction
peels one off a list known only to be nonempty, so it needs the head as a term rather than as
a pattern. -/

/-- Prepending a vertex to a nonempty list adds the segment to its head. -/
theorem poly_cons_of_ne_nil {vs : List Plane} (h : vs ≠ []) (u : Plane) :
    poly (u :: vs) = segment ℝ u (vs.head h) ∪ poly vs := by
  match vs, h with
  | _ :: _, _ => rfl

/-! ### The segments of a vertex list

`poly` is a *chain*: consecutive vertices, with repetitions allowed. The overlay takes a list
of pieces and insists that each be nondegenerate, so a repetition has to be dropped rather
than passed on. Dropping one is harmless — a degenerate segment is a single point, and that
point is an end of the neighbouring segment — except when the whole chain degenerates to a
point, which is the second disjunct of `cover_segsOf`. -/

open scoped Classical in
/-- The nondegenerate segments of a polygonal chain, in order. A repeated vertex contributes
nothing. -/
noncomputable def segsOf : List Plane → List Piece
  | [] => []
  | [_] => []
  | u :: v :: rest => if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest)

@[simp] theorem segsOf_nil : segsOf [] = [] := rfl

@[simp] theorem segsOf_singleton (v : Plane) : segsOf [v] = [] := rfl

open scoped Classical in
theorem segsOf_cons_cons (u v : Plane) (rest : List Plane) :
    segsOf (u :: v :: rest) =
      if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest) := rfl

/-- Every segment produced is nondegenerate — which is the whole point of the definition. -/
theorem segsOf_nondeg (vs : List Plane) : ∀ P ∈ segsOf vs, P.Nondeg := by
  classical
  induction vs with
  | nil => simp
  | cons u tl ih =>
    match tl, ih with
    | [], _ => simp
    | v :: rest, ih =>
      rw [segsOf_cons_cons]
      split_ifs with huv
      · exact ih
      · intro P hP
        rcases List.mem_cons.1 hP with rfl | hP
        · exact huv
        · exact ih P hP

/-- The segments of a chain occupy the chain — unless the chain has collapsed to a point (or
to nothing), in which case there are no segments at all. -/
theorem cover_segsOf (vs : List Plane) :
    cover (segsOf vs) = poly vs ∨ (segsOf vs = [] ∧ (poly vs).Subsingleton) := by
  classical
  induction vs with
  | nil => exact Or.inr ⟨rfl, by simp⟩
  | cons u tl ih =>
    match tl, ih with
    | [], _ => exact Or.inr ⟨rfl, by simp [Set.Subsingleton]⟩
    | v :: rest, ih =>
      rw [segsOf_cons_cons, poly_cons_cons]
      by_cases huv : u = v
      · -- A repeated vertex contributes the point `u`, which the rest of the chain already
        -- holds.
        subst huv
        rw [ite_eq_left rfl, segment_same]
        have hmem : u ∈ poly (u :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
        rcases ih with h | ⟨h1, h2⟩
        · exact Or.inl (by rw [h, union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)])
        · refine Or.inr ⟨h1, ?_⟩
          rw [union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)]
          exact h2
      · rw [ite_eq_right huv, cover_cons]
        refine Or.inl ?_
        rcases ih with h | ⟨h1, h2⟩
        · rw [h]; rfl
        · -- The rest of the chain is the single point `v`, already an end of the new segment.
          rw [h1, cover_nil, union_empty,
            h2.eq_singleton_of_mem (mem_poly_of_mem (List.mem_cons_self ..)),
            union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u v))]
          rfl

/-- When a chain carries two distinct points it has not collapsed, so its segments occupy
exactly it. -/
theorem cover_segsOf_eq {vs : List Plane} (ha : a ∈ poly vs) (hb : b ∈ poly vs)
    (hab : a ≠ b) : cover (segsOf vs) = poly vs := by
  rcases cover_segsOf vs with h | ⟨-, h⟩
  · exact h
  · exact absurd (h ha hb) hab

/-! ### The realisation of a walk is a polygonal chain

`Graph.edgesCover` is a union with no order in it. The walk supplies the order, and the
induction reads the vertex list off it. -/

/-- **The realisation of a nonempty walk of the overlay graph is the carrier of a vertex
list**, running from the walk's source to its target.

The list is returned rather than an unnamed polygonal set: the consumers of Lemma 1.1 that
overlay the arc with something else need its vertices. -/
theorem exists_poly_eq_edgesCover {u v : Plane} {W : List Piece}
    (hW : (overlayGraph pieces points).IsWalk u W v) (hne : W ≠ []) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = u ∧ vs.getLast h = v ∧
      poly vs = Graph.edgesCover segmentDrawing W := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hW ih =>
    -- The edge's arc is the segment from the source to the waypoint, in whichever order the
    -- edge names its ends.
    have hedge : Graph.edgeArc segmentDrawing e = segment ℝ u w := by
      rw [edgeArc_segmentDrawing]
      rcases (overlayGraph_isLink.1 hl).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact segment_symm ℝ _ _
    rcases eq_or_ne W [] with rfl | hWne
    · have hwv : w = v := hW.eq_of_nil
      subst hwv
      refine ⟨[u, w], by simp, rfl, by simp, ?_⟩
      rw [poly_pair, Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty, hedge]
    · obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := ih hWne
      refine ⟨u :: vs, by simp, rfl, ?_, ?_⟩
      · rw [List.getLast_cons hvs]; exact hlast
      · rw [poly_cons_of_ne_nil hvs, hhead, hpoly, Graph.edgesCover_cons, hedge]

/-! ### The overlay graph of a connected union is connected

Nothing built so far relates the plane topology of the union to the walk relation of the
graph. This is where they meet. -/

/-- Both ends of an edge reach the same vertices. -/
theorem overlayGraph_reaches_end {P : Piece} (hP : P ∈ overlayPieces pieces points)
    (hz : x = P.1 ∨ x = P.2) :
    (overlayGraph pieces points).Reaches a P.1 ↔ (overlayGraph pieces points).Reaches a x := by
  have hlink : (overlayGraph pieces points).IsLink P P.1 P.2 :=
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  rcases hz with rfl | rfl
  · exact Iff.rfl
  · exact ⟨fun h => h.trans (Graph.Reaches.of_isLink hlink),
      fun h => h.trans (Graph.Reaches.of_isLink hlink).symm⟩

/-- A cut point on the union is a vertex: it lies on some edge, and a cut point is interior to
no edge, so it is one of that edge's two ends. -/
theorem overlayGraph_mem_vertexSet_of_mem_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hxp : x ∈ points) (hx : x ∈ cover pieces) : x ∈ V(overlayGraph pieces points) := by
  rw [← overlayPieces_cover pieces points] at hx
  simp only [cover, mem_iUnion, exists_prop] at hx
  obtain ⟨P, hP, hxP⟩ := hx
  have hint : x ∉ P.interior := overlayPieces_avoids hnd x hxp P hP
  refine ⟨P, hP, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

/-- **The overlay graph of a connected union is connected**, in the form the construction
needs: any vertex reaches any other.

The proof is a clopen argument in the plane. Split the edges into those whose ends the walk
relation reaches from `a` and those it does not; each class carries a compact set, the two
carried sets cover the union, and they are disjoint — a common point would, by the drawing
condition, be a vertex incident with an edge of each class, and incidence is reachability.
Preconnectedness then leaves the second class carrying nothing. -/
theorem overlayGraph_reaches (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces))
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points)
    (hap : a ∈ points) (hbp : b ∈ points) (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    (overlayGraph pieces points).Reaches a b := by
  classical
  have hdraw : Graph.IsDrawing (overlayGraph pieces points) segmentDrawing :=
    overlayGraph_isDrawing pieces points hnd hEnds hMeets
  have haV : a ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hap ha
  have hbV : b ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hbp hb
  -- Every edge carries a link between its two ends; this is the only fact about the graph
  -- used below beyond the drawing condition.
  have hlink : ∀ P ∈ overlayPieces pieces points,
      (overlayGraph pieces points).IsLink P P.1 P.2 := fun P hP =>
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  -- The two classes of edges, and the point sets they carry.
  set S : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      (overlayGraph pieces points).Reaches a P.1}, P.seg with hS
  set T : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      ¬ (overlayGraph pieces points).Reaches a P.1}, P.seg with hT
  have hSclosed : IsClosed S :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  have hTclosed : IsClosed T :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  -- The two classes carry the whole union between them.
  have hunion : ∀ z ∈ cover pieces, z ∈ S ∨ z ∈ T := by
    intro z hz
    rw [← overlayPieces_cover pieces points] at hz
    simp only [cover, mem_iUnion, exists_prop] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    by_cases hr : (overlayGraph pieces points).Reaches a P.1
    · exact Or.inl (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
    · exact Or.inr (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
  -- And they carry disjoint sets: a common point is a vertex incident with an edge of each.
  have hdisj : ∀ z, z ∈ S → z ∈ T → False := by
    intro z hzS hzT
    simp only [hS, hT, mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hzS hzT
    obtain ⟨P, ⟨hP, hPr⟩, hzP⟩ := hzS
    obtain ⟨Q, ⟨hQ, hQr⟩, hzQ⟩ := hzT
    have hPQ : P ≠ Q := by rintro rfl; exact hQr hPr
    obtain ⟨-, hincP, hincQ⟩ := hdraw.edge_inter (overlayGraph_mem_edgeSet.2 hP)
      (overlayGraph_mem_edgeSet.2 hQ) hPQ
      (by rwa [edgeArc_segmentDrawing]) (by rwa [edgeArc_segmentDrawing])
    have hzendP : z = P.1 ∨ z = P.2 := hincP.eq_or_eq_of_isLink (hlink P hP)
    have hzendQ : z = Q.1 ∨ z = Q.2 := hincQ.eq_or_eq_of_isLink (hlink Q hQ)
    exact hQr ((overlayGraph_reaches_end hQ hzendQ).2
      ((overlayGraph_reaches_end hP hzendP).1 hPr))
  -- `a` is carried by the reachable class, so that class is nonempty.
  have haS : a ∈ S := by
    obtain ⟨P, hP, hend⟩ := id haV
    refine mem_biUnion (show P ∈ _ from
      ⟨hP, (overlayGraph_reaches_end hP hend).2 (Graph.Reaches.refl haV)⟩) ?_
    rcases hend with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  -- Preconnectedness: the far class carries nothing that the union contains.
  have hbS : b ∈ S := by
    by_contra hbnot
    have hbT : b ∈ T := (hunion b hb).resolve_left hbnot
    have hsub : cover pieces ⊆ Tᶜ ∪ Sᶜ := by
      intro w hw
      rcases hunion w hw with h | h
      · exact Or.inl fun h' => hdisj w h h'
      · exact Or.inr fun h' => hdisj w h' h
    obtain ⟨z, hzc, hzT, hzS⟩ := hconn Tᶜ Sᶜ hTclosed.isOpen_compl hSclosed.isOpen_compl
      hsub ⟨a, ha, fun h => hdisj a haS h⟩ ⟨b, hb, fun h => hdisj b h hbT⟩
    exact (hunion z hzc).elim hzS hzT
  -- `b` is a vertex on an edge of the reachable class, hence an end of it.
  simp only [hS, mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hbS
  obtain ⟨P, ⟨hP, hPr⟩, hbP⟩ := hbS
  have hbend : b = P.1 ∨ b = P.2 :=
    hdraw.vertex_mem_edgeArc (hlink P hP) hbV (by rwa [edgeArc_segmentDrawing])
  exact (overlayGraph_reaches_end hP hbend).1 hPr

/-! ### Lemma 1.2, and then Lemma 1.1 -/

/-- **Lemma 1.2 (finite polygonal unions).** If a finite union of nondegenerate segments is
connected, any two distinct points of it are joined inside it by a *simple* polygonal arc.

The arc is returned as a vertex list, not merely as a set: the consumers that overlay it with
another polygonal object need its vertices, and an existential over sets would not give them
back. -/
theorem exists_simple_poly_of_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces)) (hab : a ≠ b)
    (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = a ∧ vs.getLast h = b ∧
      poly vs ⊆ cover pieces ∧ IsArcBetween (poly vs) a b := by
  classical
  -- Put the two endpoints on the cut list, so that they become vertices of the overlay. The
  -- two cut conditions ask only that certain points occur in the list, so this is free.
  obtain ⟨pts₀, hEnds₀, hMeets₀⟩ := exists_cut_points pieces
  set pts : List Plane := a :: b :: pts₀ with hpts
  have hEnds : EndsAreCut pieces pts := fun P hP z hz => by
    simp [hpts, hEnds₀ P hP z hz]
  have hMeets : MeetsAreCut pieces pts := by
    intro P hP Q hQ hPQ hne
    obtain ⟨u, v, huv, hu, hv⟩ := hMeets₀ P hP Q hQ hPQ hne
    exact ⟨u, v, huv, by simp [hpts, hu], by simp [hpts, hv]⟩
  have hdraw : Graph.IsDrawing (overlayGraph pieces pts) segmentDrawing :=
    overlayGraph_isDrawing pieces pts hnd hEnds hMeets
  -- A walk from `a` to `b`, thinned to a path.
  have hreach : (overlayGraph pieces pts).Reaches a b :=
    overlayGraph_reaches hnd hconn hEnds hMeets (by simp [hpts]) (by simp [hpts]) ha hb
  obtain ⟨W, hpath⟩ := hreach.exists_isPath
  have hWne : W ≠ [] := by
    rintro rfl
    exact hab hpath.isWalk.eq_of_nil
  -- Its realisation is an arc, and it is the carrier of a vertex list.
  have harc : IsArcBetween (Graph.edgesCover segmentDrawing W) a b :=
    hdraw.path_isArcBetween hpath hWne
  obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := exists_poly_eq_edgesCover hpath.isWalk hWne
  refine ⟨vs, hvs, hhead, hlast, ?_, ?_⟩
  · rw [hpoly, ← overlayGraph_pointSet pieces pts]
    exact Graph.edgesCover_subset_pointSet fun e he => hpath.edge_mem he
  · rw [hpoly]; exact harc

/-- **Lemma 1.2**, for a set presented as a polygonal chain. -/
theorem exists_simple_poly_of_poly {vs : List Plane} (hconn : IsPreconnected (poly vs))
    (hab : a ≠ b) (ha : a ∈ poly vs) (hb : b ∈ poly vs) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ poly vs ∧ IsArcBetween (poly ws) a b := by
  have hcov : cover (segsOf vs) = poly vs := cover_segsOf_eq ha hb hab
  have := exists_simple_poly_of_cover (segsOf_nondeg vs) (hcov ▸ hconn) hab
    (hcov ▸ ha) (hcov ▸ hb)
  rwa [hcov] at this

/-- **Lemma 1.2**, for a set given only as polygonal. -/
theorem exists_simple_poly_of_isPolygonal {A : Set Plane} (hA : IsPolygonal A)
    (hconn : IsPreconnected A) (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ A ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨vs, rfl⟩ := hA
  exact exists_simple_poly_of_poly hconn hab ha hb

/-! ### A finite union of polygonal arcs

The blueprint states Lemma 1.2 for a finite union, which `Schoenflies.cover` already is. The
only thing standing between the two readings is that a member of the union may have collapsed
to a single point, contributing no segment at all. A collapsed member is harmless: were its
point missing from the segments, it would be clopen in the union, which a connected set with
more than one point does not tolerate. -/

/-- Peeling the head off a union indexed by a list. -/
theorem biUnion_list_cons {α : Type*} (f : α → Set Plane) (x : α) (l : List α) :
    (⋃ y ∈ x :: l, f y) = f x ∪ ⋃ y ∈ l, f y := by
  ext z
  simp only [mem_iUnion, exists_prop, List.mem_cons, mem_union]
  constructor
  · rintro ⟨y, rfl | hy, hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨y, hy, hz⟩
  · rintro (hz | ⟨y, hy, hz⟩)
    · exact ⟨x, Or.inl rfl, hz⟩
    · exact ⟨y, Or.inr hy, hz⟩

/-- `Schoenflies.cover_flatMap`, over an arbitrary index list rather than a list of pieces.
Belongs beside it in `Schoenflies/Subdivide.lean`; it is here because that module is on
`main`. -/
theorem cover_flatMap_list {α : Type*} (f : α → List Piece) (l : List α) :
    cover (l.flatMap f) = ⋃ x ∈ l, cover (f x) := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.flatMap_cons, cover_append, ih, biUnion_list_cons]

/-- A preconnected set with two distinct points absorbs finitely many stray points: it cannot
be a closed set together with finitely many extra points, since each extra point would be
clopen in it. -/
theorem subset_of_finite_diff {U C : Set Plane} (hU : IsPreconnected U) (hC : IsClosed C)
    (hfin : (U \ C).Finite) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) : U ⊆ C := by
  intro z hz
  by_contra hzC
  -- `D` meets `U` in exactly `U \ {z}`, and it is closed.
  set D : Set Plane := C ∪ ((U \ C) \ {z}) with hD
  have hDclosed : IsClosed D := hC.union ((hfin.subset Set.sdiff_subset).isClosed)
  have hzD : z ∉ D := fun h => h.elim hzC fun h' => h'.2 rfl
  have hmemD : ∀ w ∈ U, w ≠ z → w ∈ D := fun w hw hwz =>
    (em (w ∈ C)).elim Or.inl fun h => Or.inr ⟨⟨hw, h⟩, hwz⟩
  -- `{z}` is clopen in `U`, so `U = {z}` — which two distinct points forbid.
  obtain ⟨w, hwU, hwD, hwz⟩ := hU Dᶜ ({z} : Set Plane)ᶜ hDclosed.isOpen_compl
    isClosed_singleton.isOpen_compl
    (fun w hw => (em (w = z)).elim (fun h => Or.inl (h ▸ hzD)) fun h => Or.inr h)
    ⟨z, hz, hzD⟩
    ((em (a = z)).elim (fun h => ⟨b, hb, fun hbz => hab (h.trans (mem_singleton_iff.1 hbz).symm)⟩)
      fun h => ⟨a, ha, h⟩)
  exact hwD (hmemD w hwU hwz)

/-- **Lemma 1.2 (finite polygonal unions).** A connected finite union of polygonal chains joins
any two of its distinct points by a simple polygonal arc inside it. -/
theorem exists_simple_poly_of_biUnion {L : List (List Plane)}
    (hconn : IsPreconnected (⋃ vs ∈ L, poly vs)) (hab : a ≠ b)
    (ha : a ∈ ⋃ vs ∈ L, poly vs) (hb : b ∈ ⋃ vs ∈ L, poly vs) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ vs ∈ L, poly vs) ∧ IsArcBetween (poly ws) a b := by
  classical
  have hnd : ∀ P ∈ L.flatMap segsOf, P.Nondeg := by
    intro P hP
    obtain ⟨vs, -, hPvs⟩ := List.mem_flatMap.1 hP
    exact segsOf_nondeg vs P hPvs
  have hcovsub : ∀ vs : List Plane, cover (segsOf vs) ⊆ poly vs := by
    intro vs
    rcases cover_segsOf vs with h | ⟨h, -⟩
    · exact h.subset
    · rw [h, cover_nil]; exact empty_subset _
  have hflat : cover (L.flatMap segsOf) = ⋃ vs ∈ L, cover (segsOf vs) :=
    cover_flatMap_list segsOf L
  have hsub : cover (L.flatMap segsOf) ⊆ ⋃ vs ∈ L, poly vs := by
    rw [hflat]
    exact iUnion₂_mono fun vs _ => hcovsub vs
  -- What the segments miss is finitely many collapsed members.
  have hdiff : ((⋃ vs ∈ L, poly vs) \ cover (L.flatMap segsOf)).Finite := by
    have hsmall : ∀ vs : List Plane, (poly vs \ cover (segsOf vs)).Subsingleton := by
      intro vs
      rcases cover_segsOf vs with h | ⟨-, h⟩
      · rw [h]; simp
      · exact h.anti Set.sdiff_subset
    refine (Set.Finite.biUnion L.finite_toSet
      fun vs _ => (hsmall vs).finite).subset ?_
    rintro z ⟨hzU, hzC⟩
    simp only [mem_iUnion, exists_prop] at hzU
    obtain ⟨vs, hvs, hz⟩ := hzU
    refine mem_biUnion hvs ⟨hz, fun hmem => hzC ?_⟩
    rw [hflat]
    exact mem_biUnion hvs hmem
  have hclosed : IsClosed (cover (L.flatMap segsOf)) :=
    Set.Finite.isClosed_biUnion (L.flatMap segsOf).finite_toSet fun P _ =>
      (isCompact_segment P.1 P.2).isClosed
  have heq : cover (L.flatMap segsOf) = ⋃ vs ∈ L, poly vs :=
    subset_antisymm hsub (subset_of_finite_diff hconn hclosed hdiff ha hb hab)
  have := exists_simple_poly_of_cover hnd (heq ▸ hconn) hab (heq ▸ ha) (heq ▸ hb)
  rwa [heq] at this

/-- A list of polygonal sets is a list of polygonal chains. -/
theorem exists_lists_of_isPolygonal : ∀ {L : List (Set Plane)}, (∀ A ∈ L, IsPolygonal A) →
    ∃ M : List (List Plane), (⋃ vs ∈ M, poly vs) = ⋃ A ∈ L, A
  | [], _ => ⟨[], by simp⟩
  | A :: L, h => by
    obtain ⟨vs, rfl⟩ := h A (List.mem_cons_self ..)
    obtain ⟨M, hM⟩ := exists_lists_of_isPolygonal fun B hB => h B (List.mem_cons_of_mem _ hB)
    refine ⟨vs :: M, ?_⟩
    rw [biUnion_list_cons (fun ws : List Plane => poly ws),
      biUnion_list_cons (fun B : Set Plane => B), hM]

/-- **Lemma 1.2 (finite polygonal unions)**, at the level of sets: if a connected set is the
union of finitely many polygonal sets, any two of its distinct points are joined in it by a
simple polygonal arc. -/
theorem exists_simple_poly_of_union {L : List (Set Plane)} (hL : ∀ A ∈ L, IsPolygonal A)
    (hconn : IsPreconnected (⋃ A ∈ L, A)) (hab : a ≠ b)
    (ha : a ∈ ⋃ A ∈ L, A) (hb : b ∈ ⋃ A ∈ L, A) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ A ∈ L, A) ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨M, hM⟩ := exists_lists_of_isPolygonal hL
  have := exists_simple_poly_of_biUnion (L := M) (hM ▸ hconn) hab (hM ▸ ha) (hM ▸ hb)
  rwa [hM] at this

/-- **Lemma 1.1 (polygonal connectedness), in full.** Any two distinct points of a region are
joined in it by a *simple* polygonal arc.

`Schoenflies.exists_poly_of_isPreconnected` supplies a polygonal path; Lemma 1.2 extracts a
simple arc from its carrier. -/
theorem exists_simple_poly_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = x ∧ vs.getLast h = y ∧
      poly vs ⊆ Ω ∧ IsArcBetween (poly vs) x y := by
  obtain ⟨us, hus, hsub, hhead, hlast⟩ := exists_poly_of_isPreconnected hΩ hconn hx hy
  have hxu : x ∈ poly us := hhead ▸ head_mem_poly hus
  have hyu : y ∈ poly us := hlast ▸ getLast_mem_poly hus
  obtain ⟨vs, hvs, h1, h2, h3, h4⟩ :=
    exists_simple_poly_of_poly (isConnected_poly hus).2 hxy hxu hyu
  exact ⟨vs, hvs, h1, h2, h3.trans hsub, h4⟩

/-- **Lemma 1.1**, in set form: a simple polygonal arc inside the region between any two of
its points. -/
theorem exists_simple_arc_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ A ⊆ Ω, IsPolygonal A ∧ IsArcBetween A x y := by
  obtain ⟨vs, -, -, -, hsub, harc⟩ := exists_simple_poly_of_isPreconnected hΩ hconn hx hy hxy
  exact ⟨poly vs, hsub, ⟨vs, rfl⟩, harc⟩

end Schoenflies
