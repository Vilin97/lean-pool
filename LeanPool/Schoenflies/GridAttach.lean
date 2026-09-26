/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.LocalGrid
public import LeanPool.Schoenflies.Graph.Ear
public import LeanPool.Schoenflies.Line
public import LeanPool.Schoenflies.PolygonalCarrier

/-!
# Attaching a local source grid — `prop:local-grid-attachment`

`Schoenflies/LocalGrid.lean` built the grid `K` itself and its quantitative clause 3. This
module is the *rest* of the proposition: the overlay of `K` with the polygonal nonboundary
skeleton of `Γ`, the three cases of the union argument, and the component-joining loop.

## Blueprint

* `lem:polygonal-overlay`, with the convention of `rem:polygonal-overlay-convention` —
  `Schoenflies.attachPoints`, `Schoenflies.attachGraph`, `Schoenflies.attachGraph_isDrawing`,
  `Schoenflies.attachGraph_pointSet`.
* `lem:subdivision-ear-preserve` — `Graph.SameLinks` and
  `Schoenflies.overlayGraph_isTwoConnected`, the bridge that lets the raw-subdivision
  2-connectivity of `Schoenflies/SquareMeshFixed.lean` reach an overlay graph at all (see the
  next section); `Schoenflies.pieceListGraph_append_crosscut`, the single-ear step.
* `lem:union-two-connected` — `Schoenflies.overlayGraph_append_isTwoConnected` and
  `Schoenflies.attachGraph_isTwoConnected`, the blueprint's three cases in one statement.
* the auxiliary crosscut `E` of the two degenerate cases — `Schoenflies.exists_crosscut`,
  `Schoenflies.frontier_face_subset_pointSet`, `Schoenflies.seg_subset_crosscut`
  ("since `E` contains `J`") and `Schoenflies.two_common_of_crosscut`.
* the component-joining loop — `Schoenflies.isConnected_union_joins` and its cover form
  `Schoenflies.isConnected_cover_diff_of_joins`.
* `prop:local-grid-attachment` itself — `Schoenflies.gridAttachPieces`,
  `Schoenflies.gridAttachGraph`, with clause 1 `gridAttachGraph_isConnected_diff`, clause 2
  `localGrid_subset_gridAttachGraph`, clause 3 `attachGraph_localGridCell_diam`, and
  2-connectivity `gridAttachGraph_isTwoConnected`.

## The bridge that was missing: 2-connectivity of an overlay graph

`Schoenflies/SquareMeshFixed.lean` proves `pieceListGraph_subdivide_isTwoConnected`: the graph
of a **raw** subdivided piece list is 2-connected. `Schoenflies/OverlayGraph.lean` builds the
overlay as `overlayGraph pieces points`, whose edges are the subdivided pieces *oriented and
deduplicated*. Nothing on `main` connects the two, so no overlay graph anywhere in the
development was known to be 2-connected — including `Schoenflies.squareMesh`, whose clause 5
is the subject of the first half of `LocalGrid.lean`.

Orienting renames an edge `(a, b)` to `(b, a)` and deduplication drops repeats, so the two
graphs are not equal and are not isomorphic by an identity on edges. But 2-connectivity does
not see edge *names*: it is a statement about which pairs of vertices are joined. That is what
`Graph.SameLinks` isolates — same vertex set, same joined pairs — and it transfers `Connected`,
`deleteVerts`, and hence `IsTwoConnected` in both directions.

## What is a hypothesis here, and why

Three things the blueprint's proof uses are hypotheses of the assembled theorems rather than
lemmas of this module, and all three are statements about `Γ`, never about the grid.

* `hΓ` of `gridAttachGraph_isTwoConnected` — the skeleton of `Γ`, with the case's crosscut and
  the loop's joining arcs appended and everything subdivided at the crossing points, is still
  2-connected. `Γ` itself is 2-connected by hypothesis of the proposition; the subdivision is
  `lem:subdivision-ear-preserve` (a), which is `pieceListGraph_subdivide_isTwoConnected` for the
  polygonal part and `Graph.IsTwoConnected.replace_edge_by_path` for the arcs of `C`; the ears
  are `lem:subdivision-ear-preserve` (b), which is `Graph.IsTwoConnected.ear`, and
  `pieceListGraph_append_crosscut` is that step for one straight crosscut. It is not proved here
  because this module never sees `Γ`'s drawing — `C` is not drawn by segments, so `Γ` is not a
  `pieceListGraph` and the union argument has to stay combinatorial.
* `hcov` of `gridAttachGraph_isConnected_diff` — that finitely many representatives meet every
  component of `|L| ∖ C`. This is the blueprint's *"since there are only finitely many
  components"*, and it is where the loop's termination lives. Nothing on `main` proves finiteness
  of a component count for a plane set.
* the joining arcs themselves — supplied to `gridAttachGraph_isConnected_diff` as the family
  `Jarc`, with the four properties `lem:polygonal-connected` gives them
  (`Schoenflies.exists_simple_poly_of_isPreconnected` in `Schoenflies/PolygonalCarrier.lean`
  produces a polygonal path inside the open connected `D`, and `D ∩ C = ∅` gives `hJC`).


Neither is a restatement of a goal of this module, and both are true.
-/

public section

open Metric Set
open scoped Graph

/-! ## Graphs that join the same pairs

2-connectivity is invariant under renaming edges, merging parallel edges, and dropping an edge
that duplicates another — none of which a `Graph` isomorphism captures, since the edge type is
fixed. `SameLinks` is the equivalence that does capture them, and it is exactly what the
overlay's orient-and-dedup step needs.

This is general graph theory and belongs in `Schoenflies/Graph/Walk.lean` beside `IsWalk.mono`;
it is here only because it was needed here first. -/

namespace Graph

variable {α β : Type*} {G H : Graph α β} {u v x y : α} {e : β} {X : Set α}

/-- Two graphs with the same vertices which join the same pairs of vertices. Edge names,
multiplicities and parallel edges are all invisible to it. -/
def SameLinks (G H : Graph α β) : Prop :=
  V(G) = V(H) ∧ ∀ x y, (∃ e, G.IsLink e x y) ↔ (∃ e, H.IsLink e x y)

namespace SameLinks

@[refl] theorem refl (G : Graph α β) : SameLinks G G := ⟨rfl, fun _ _ => Iff.rfl⟩

theorem symm (h : SameLinks G H) : SameLinks H G := ⟨h.1.symm, fun x y => (h.2 x y).symm⟩

theorem vertexSet (h : SameLinks G H) : V(G) = V(H) := h.1

/-- Deleting the same vertices from both sides preserves the relation: the deleted graph's
links are the old links between surviving vertices. -/
theorem deleteVerts (h : SameLinks G H) (X : Set α) :
    SameLinks (G.deleteVerts X) (H.deleteVerts X) := by
  refine ⟨by rw [vertexSet_deleteVerts, vertexSet_deleteVerts, h.1], fun x y => ?_⟩
  constructor
  · rintro ⟨e, he⟩
    rw [deleteVerts_isLink _ _] at he
    obtain ⟨f, hf⟩ := (h.2 x y).1 ⟨e, he.1⟩
    exact ⟨f, (deleteVerts_isLink _ _).2 ⟨hf, he.2.1, he.2.2⟩⟩
  · rintro ⟨e, he⟩
    rw [deleteVerts_isLink _ _] at he
    obtain ⟨f, hf⟩ := (h.2 x y).2 ⟨e, he.1⟩
    exact ⟨f, (deleteVerts_isLink _ _).2 ⟨hf, he.2.1, he.2.2⟩⟩

end SameLinks

/-- Reachability only sees which pairs are joined. -/
theorem Reaches.sameLinks (h : SameLinks G H) (hr : G.Reaches u v) : H.Reaches u v := by
  obtain ⟨W, hW⟩ := hr
  induction hW with
  | nil hz => exact Reaches.refl (h.1 ▸ hz)
  | @cons p w q g R hl _ ih =>
    obtain ⟨f, hf⟩ := (h.2 p w).1 ⟨g, hl⟩
    exact (Reaches.of_isLink hf).trans ih

theorem Connected.sameLinks (h : SameLinks G H) (hG : G.Connected) : H.Connected := by
  obtain ⟨z, hz⟩ := hG.nonempty
  exact Connected.of_hub (h.1 ▸ hz) fun w hw =>
    (hG.reaches hz (h.1 ▸ hw : w ∈ V(G))).sameLinks h

theorem HasThreeVertices.sameLinks (h : SameLinks G H) (hG : G.HasThreeVertices) :
    H.HasThreeVertices := hG.mono (le_of_eq h.1)

/-- **2-connectivity does not see edge names.** -/
theorem IsTwoConnected.sameLinks (h : SameLinks G H) (hG : G.IsTwoConnected) :
    H.IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.sameLinks h
  connected := hG.connected.sameLinks h
  deleteVerts_connected := fun z _ =>
    (hG.deleteVerts_connected' z).sameLinks (h.deleteVerts {z})

end Graph

namespace Schoenflies

/-! ## The overlay graph is a piece-list graph

`overlayGraph pieces points` and `pieceListGraph (overlayPieces pieces points)` are the same
structure with the same fields, so the equation is `rfl`. Saying it once lets every lemma of
`Schoenflies/SquareMeshConnected.lean` about `pieceListGraph` — in particular
`pieceListGraph_union`, which turns "glue on another family of segments" into a list append —
apply to overlays. -/

/-- The overlay graph is the piece-list graph of its own edges. -/
theorem overlayGraph_eq_pieceListGraph (pieces : List Piece) (points : List Plane) :
    overlayGraph pieces points = pieceListGraph (overlayPieces pieces points) := rfl

/-! ### Orienting and deduplicating do not change which pairs are joined -/

/-- The two ends of a piece, as an unordered pair, are what a link records. -/
theorem orientPiece_link_iff (P : Piece) (x y : Plane) :
    ((x = (orientPiece P).1 ∧ y = (orientPiece P).2) ∨
        (x = (orientPiece P).2 ∧ y = (orientPiece P).1)) ↔
      ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact or_comm

/-- **The subdivided list and the overlay's edge list join the same pairs.** This is the bridge
between `pieceListGraph_subdivide_isTwoConnected`, which knows about the raw subdivision, and
`overlayGraph`, which is what every plane consumer holds. -/
theorem sameLinks_overlayGraph (pieces : List Piece) (points : List Plane) :
    Graph.SameLinks (pieceListGraph (subdivide pieces points)) (overlayGraph pieces points) := by
  constructor
  · ext v
    simp only [pieceListGraph_vertexSet, overlayGraph_vertexSet, endSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨P, hP, hv⟩
      exact ⟨orientPiece P, mem_overlayPieces.2 ⟨P, hP, rfl⟩, (orientPiece_ends P v).2 hv⟩
    · rintro ⟨P, hP, hv⟩
      obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
      exact ⟨Q, hQ, (orientPiece_ends Q v).1 hv⟩
  · intro x y
    simp only [pieceListGraph_isLink, overlayGraph_isLink]
    constructor
    · rintro ⟨P, hP, hxy⟩
      exact ⟨orientPiece P, mem_overlayPieces.2 ⟨P, hP, rfl⟩,
        (orientPiece_link_iff P x y).2 hxy⟩
    · rintro ⟨P, hP, hxy⟩
      obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
      exact ⟨Q, hQ, (orientPiece_link_iff Q x y).1 hxy⟩

/-- **`lem:subdivision-ear-preserve` for an overlay.** If the raw subdivision of the piece list
has a 2-connected graph, so does the overlay graph built from it.

Without this the development had no 2-connected overlay at all: every 2-connectivity result
about segment families is stated for `pieceListGraph`, and every plane result — drawing, faces,
outer face — is stated for `overlayGraph`. -/
theorem overlayGraph_isTwoConnected {pieces : List Piece} {points : List Plane}
    (h : (pieceListGraph (subdivide pieces points)).IsTwoConnected) :
    (overlayGraph pieces points).IsTwoConnected :=
  h.sameLinks (sameLinks_overlayGraph pieces points)

/-- The same, from the hypotheses `pieceListGraph_subdivide_isTwoConnected` actually needs. -/
theorem overlayGraph_isTwoConnected_of_cleanCut {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hclean : ∀ q ∈ points, CleanCut pieces q)
    (h : (pieceListGraph pieces).IsTwoConnected) :
    (overlayGraph pieces points).IsTwoConnected :=
  overlayGraph_isTwoConnected (pieceListGraph_subdivide_isTwoConnected points pieces hnd hclean h)

/-! ## Subdividing an append

The blueprint's `Γ ∪ K` is, at the level of segment lists, a list append, and
`pieceListGraph_union` turns the graph union into that append. Subdivision has to commute with
it, which it does because a subdivision is a `flatMap`. -/

theorem splitAllAt_append (q : Plane) (l l' : List Piece) :
    splitAllAt q (l ++ l') = splitAllAt q l ++ splitAllAt q l' := by
  simp [splitAllAt, List.flatMap_append]

theorem subdivide_append (points : List Plane) : ∀ l l' : List Piece,
    subdivide (l ++ l') points = subdivide l points ++ subdivide l' points := by
  induction points with
  | nil => intro l l'; rfl
  | cons q qs ih => intro l l'; rw [subdivide_cons, splitAllAt_append, ih, subdivide_cons,
      subdivide_cons]

theorem endSet_subset_append_left {l l' : List Piece} : endSet l ⊆ endSet (l ++ l') := by
  rintro v ⟨P, hP, hv⟩
  exact ⟨P, List.mem_append_left _ hP, hv⟩

/-! ### A cut point on the drawing is a vertex

`Schoenflies/SimpleArc.lean` proves this for `overlayGraph`; the union argument runs on the raw
subdivision, where the same two facts — `subdivide_cover` and `subdivide_avoids` — give it. -/

/-- **A cut point lying on the pieces is an end of some subpiece.** -/
theorem mem_endSet_subdivide_of_mem_cover {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) {x : Plane} (hxp : x ∈ points) (hx : x ∈ cover pieces) :
    x ∈ endSet (subdivide pieces points) := by
  rw [← subdivide_cover pieces points] at hx
  obtain ⟨P, hP, hxP⟩ := mem_cover_iff.1 hx
  refine ⟨P, hP, ?_⟩
  by_contra hcon
  push Not at hcon
  exact subdivide_avoids points hnd x hxp P hP
    (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

/-! ## The union: the case "at least two common vertices"

`lem:union-two-connected`, in the form `prop:local-grid-attachment` uses it. The two families of
segments are overlaid together — one list append, one list of cut points — and the two distinct
common points are supplied as points that lie on *both* families and are cut. -/

/-- **`prop:local-grid-attachment`, the main case.** Two families of segments, each of which is
2-connected after subdivision, overlay to a 2-connected graph as soon as two distinct cut points
lie on both families.

This is `lem:union-two-connected` composed with `lem:subdivision-ear-preserve` and with the
orient-and-dedup bridge: the conclusion is about `overlayGraph`, which is what the plane layer
(drawing, faces, outer face) is stated for. -/
theorem overlayGraph_append_isTwoConnected {l l' : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ l, P.Nondeg) (hnd' : ∀ P ∈ l', P.Nondeg)
    (hl : (pieceListGraph (subdivide l points)).IsTwoConnected)
    (hl' : (pieceListGraph (subdivide l' points)).IsTwoConnected)
    {a b : Plane} (hab : a ≠ b) (ha : a ∈ points) (hb : b ∈ points)
    (hal : a ∈ cover l) (hbl : b ∈ cover l) (hal' : a ∈ cover l') (hbl' : b ∈ cover l') :
    (overlayGraph (l ++ l') points).IsTwoConnected := by
  refine overlayGraph_isTwoConnected ?_
  rw [subdivide_append, ← pieceListGraph_union]
  exact hl.union (pieceListGraph_compatible _ _) hl' hab
    (mem_endSet_subdivide_of_mem_cover hnd ha hal)
    (mem_endSet_subdivide_of_mem_cover hnd' ha hal')
    (mem_endSet_subdivide_of_mem_cover hnd hb hbl)
    (mem_endSet_subdivide_of_mem_cover hnd' hb hbl')

/-! ## The crosscut of a face

The two degenerate cases of `prop:local-grid-attachment` — no common vertex, and exactly one —
both build an auxiliary crosscut `E` of a face `F` of `Γ`: *"the component of `ℓ ∩ F` containing
the relative interior of `J` is a bounded open interval in `ℓ`; its closure `E` is a line segment
with two distinct endpoints on `∂F` and interior in `F`. Hence `E` is an ear for `Γ`."*

`Schoenflies.Plane.exists_openSegment_eq_connectedComponentIn` is exactly that component, with
its two endpoints already placed on `frontier F`. What is added here is the clause the blueprint
needs next — *"since `E` contains `J`"* — in the form that makes it usable: **every** connected
piece of `ℓ ∩ F` through the chosen point is swallowed by the crosscut, because a connected
subset of a set lies inside one component of it. -/

variable {F : Set Plane} {a b y : Plane}

/-- **The crosscut of a face along a line.** A face `F` (open, bounded) met by a line `ℓ` at `y`
supplies a segment `[q₀, q₁]` with distinct ends on `∂F`, open part inside `F`, containing `y` —
and containing every connected subset of `ℓ ∩ F` through `y`, which is how the blueprint's chosen
grid edge `J` ends up inside the crosscut. -/
theorem exists_crosscut (hab : a ≠ b) (hFopen : IsOpen F) (hFbdd : Bornology.IsBounded F)
    (hy : y ∈ Plane.line a b ∩ F) :
    ∃ q₀ q₁ : Plane, q₀ ≠ q₁ ∧ q₀ ∈ frontier F ∧ q₁ ∈ frontier F ∧
      openSegment ℝ q₀ q₁ ⊆ F ∧ y ∈ openSegment ℝ q₀ q₁ ∧
      ∀ S : Set Plane, IsPreconnected S → S ⊆ Plane.line a b ∩ F → y ∈ S →
        S ⊆ openSegment ℝ q₀ q₁ := by
  obtain ⟨q₀, q₁, hne, -, -, hcomp, -, h0, h1⟩ :=
    Plane.exists_openSegment_eq_connectedComponentIn hab hFopen hFbdd hy
  refine ⟨q₀, q₁, hne, h0, h1, ?_, ?_, ?_⟩
  · rw [← hcomp]
    exact fun z hz => (connectedComponentIn_subset _ _ hz).2
  · rw [← hcomp]
    exact mem_connectedComponentIn hy
  · intro S hS hSsub hyS
    rw [← hcomp]
    exact hS.subset_connectedComponentIn hyS hSsub

/-- The frontier of a face lies on the graph — which is what makes the crosscut's two endpoints
points of `Γ`, and hence (after subdivision) vertices of it. -/
theorem frontier_face_subset_pointSet {β : Type*} {G : Graph Plane β} [G.Finite]
    {drawing : β → ℝ → Plane} (h : Graph.IsDrawing G drawing) (base : Plane) :
    frontier (Graph.face G drawing base) ⊆ Graph.pointSet G drawing :=
  Plane.frontier_connectedComponentIn_compl_subset h.isClosed_pointSet base

/-! ## Attaching the crosscut as an ear

`lem:subdivision-ear-preserve` (b) with the ear a single straight edge: once the crosscut's two
endpoints are vertices — which they are, being cut points of the overlay lying on `Γ` — the
segment joining them is a path graph of length one. -/

/-- A single nondegenerate segment is a path graph between its two ends. -/
theorem isPathGraph_single {q₀ q₁ : Plane} (hne : q₀ ≠ q₁) :
    (pieceListGraph [(q₀, q₁)]).IsPathGraph q₀ [(q₀, q₁)] q₁ where
  isPath := .single (pieceListGraph_isLink_self (by simp)) hne
  edgeSet_eq := rfl
  vertexSet_eq := by
    have hmem : ((q₀, q₁) : Piece) ∈ [((q₀, q₁) : Piece)] := List.mem_singleton_self _
    ext x
    constructor
    · rintro ⟨P, hP, hx⟩
      rw [List.mem_singleton] at hP
      subst hP
      simp only [Graph.walkVertices, mem_insert_iff, Graph.coveredVertices, Set.mem_ofPred_eq]
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨(q₀, q₁), hmem, pieceListGraph_inc hmem (Or.inr h)⟩
    · intro hx
      simp only [Graph.walkVertices, mem_insert_iff, Graph.coveredVertices, Set.mem_ofPred_eq] at hx
      rcases hx with h | ⟨e, he, hinc⟩
      · exact ⟨(q₀, q₁), hmem, Or.inl h⟩
      · rw [List.mem_singleton] at he
        subst he
        obtain ⟨-, hx'⟩ := pieceListGraph_inc_iff.1 hinc
        exact ⟨(q₀, q₁), hmem, hx'⟩

/-- **A crosscut is an ear.** Adding to a 2-connected family of segments one further segment
whose two ends are already ends of the family keeps it 2-connected. -/
theorem pieceListGraph_append_crosscut {l : List Piece} {q₀ q₁ : Plane}
    (hl : (pieceListGraph l).IsTwoConnected) (hne : q₀ ≠ q₁)
    (h0 : q₀ ∈ endSet l) (h1 : q₁ ∈ endSet l) :
    (pieceListGraph (l ++ [(q₀, q₁)])).IsTwoConnected := by
  rw [← pieceListGraph_union]
  exact hl.ear (pieceListGraph_compatible _ _) (isPathGraph_single hne) hne h0 h1

/-! ## The component-joining loop

*"If `|L| ∖ C` has more than one component, choose points in two of its components and join them
by a simple polygonal arc in `D` … Each round therefore strictly decreases the number of
components. Since there are only finitely many components, finitely many repetitions produce a
2-connected graph `H_n` for which `|H_n| ∖ C` is connected."*

Counting components and decrementing is one way to run that loop; picking one representative per
component and joining each to a fixed one is another, and it is the one that survives
formalisation, because it replaces "strictly decreases" by a single induction-free statement. The
finiteness the blueprint spends is what supplies the finite list `reps`. -/

/-- **The joining loop.** If every point of `A` is joined inside `A` to one of finitely many
representatives, and each representative is joined to a fixed `r₀ ∈ A` by a connected set `T r`,
then `A` together with all the `T r` is connected.

The `T r` are the blueprint's joining arcs; nothing is assumed about how they meet `A` beyond
containing their two ends, so an arc that crosses `A` many times is no harder than one that does
not. -/
theorem isConnected_union_joins {A : Set Plane} {r₀ : Plane} (hr₀ : r₀ ∈ A)
    {reps : List Plane} {T : Plane → Set Plane}
    (hTconn : ∀ r ∈ reps, IsPreconnected (T r))
    (hThub : ∀ r ∈ reps, r₀ ∈ T r) (hTrep : ∀ r ∈ reps, r ∈ T r)
    (hcover : ∀ z ∈ A, ∃ r ∈ reps, ∃ S : Set Plane,
      S ⊆ A ∧ IsPreconnected S ∧ z ∈ S ∧ r ∈ S) :
    IsConnected (A ∪ ⋃ r ∈ reps, T r) := by
  have hmem : r₀ ∈ A ∪ ⋃ r ∈ reps, T r := Or.inl hr₀
  refine ⟨⟨r₀, hmem⟩, isPreconnected_of_forall r₀ ?_⟩
  rintro z (hz | hz)
  · -- inside `A`: walk to a representative, then along its joining set to the hub
    obtain ⟨r, hr, S, hSA, hSconn, hzS, hrS⟩ := hcover z hz
    refine ⟨S ∪ T r, ?_, Or.inr (hThub r hr), Or.inl hzS,
      hSconn.union' ⟨r, hrS, hTrep r hr⟩ (hTconn r hr)⟩
    exact union_subset (hSA.trans subset_union_left)
      (fun w hw => Or.inr (mem_biUnion hr hw))
  · -- on a joining set: it already contains the hub
    simp only [mem_iUnion, exists_prop] at hz
    obtain ⟨r, hr, hzT⟩ := hz
    exact ⟨T r, fun w hw => Or.inr (mem_biUnion hr hw), hThub r hr, hzT, hTconn r hr⟩

/-! ## The construction

`prop:local-grid-attachment` is an existence statement, but its consumer —
`thm:finite-transfer`(a) — reads the graph, its drawing and its 2-connectivity by name. So the
graph is a `def` and every clause is a theorem about it. -/

/-- Cut points for a family of segments, together with prescribed extra points that are to
become vertices whatever else happens. Enlarging the list produced by `exists_cut_points` is
harmless (`EndsAreCut.mono`, `MeetsAreCut.mono`) and is what makes the two common vertices of
`lem:union-two-connected` available. -/
noncomputable def attachPoints (pieces : List Piece) (extra : List Plane) : List Plane :=
  extra ++ (exists_cut_points pieces).choose

theorem mem_attachPoints_of_mem {pieces : List Piece} {extra : List Plane} {x : Plane}
    (hx : x ∈ extra) : x ∈ attachPoints pieces extra := List.mem_append_left _ hx

theorem attachPoints_endsAreCut (pieces : List Piece) (extra : List Plane) :
    EndsAreCut pieces (attachPoints pieces extra) :=
  (exists_cut_points pieces).choose_spec.1.mono (List.subset_append_right _ _)

theorem attachPoints_meetsAreCut (pieces : List Piece) (extra : List Plane) :
    MeetsAreCut pieces (attachPoints pieces extra) :=
  (exists_cut_points pieces).choose_spec.2.mono (List.subset_append_right _ _)

/-- **The overlay of `lem:polygonal-overlay`, with the convention of
`rem:polygonal-overlay-convention`**: every intersection of the listed segments is a vertex, and
so is every prescribed extra point. -/
noncomputable def attachGraph (pieces : List Piece) (extra : List Plane) : Graph Plane Piece :=
  overlayGraph pieces (attachPoints pieces extra)

instance attachGraph_finite (pieces : List Piece) (extra : List Plane) :
    Graph.Finite (attachGraph pieces extra) := overlayGraph_finite _ _

theorem attachGraph_isDrawing {pieces : List Piece} (hnd : ∀ P ∈ pieces, P.Nondeg)
    (extra : List Plane) : Graph.IsDrawing (attachGraph pieces extra) segmentDrawing :=
  overlayGraph_isDrawing _ _ hnd (attachPoints_endsAreCut _ _) (attachPoints_meetsAreCut _ _)

@[simp] theorem attachGraph_pointSet (pieces : List Piece) (extra : List Plane) :
    Graph.pointSet (attachGraph pieces extra) segmentDrawing = cover pieces :=
  overlayGraph_pointSet _ _

/-- **The three cases of `prop:local-grid-attachment`, in one statement.** The `Γ`-side list `l`
carries whatever the case needed — the bare skeleton in the main case, the skeleton together with
the auxiliary crosscut in the two degenerate ones — and the two distinct common points `a`, `b`
are the ones that case produced. -/
theorem attachGraph_isTwoConnected {l l' : List Piece} {extra : List Plane}
    (hnd : ∀ P ∈ l, P.Nondeg) (hnd' : ∀ P ∈ l', P.Nondeg)
    (hl : (pieceListGraph (subdivide l (attachPoints (l ++ l') extra))).IsTwoConnected)
    (hl' : (pieceListGraph (subdivide l' (attachPoints (l ++ l') extra))).IsTwoConnected)
    {a b : Plane} (hab : a ≠ b) (ha : a ∈ extra) (hb : b ∈ extra)
    (hal : a ∈ cover l) (hbl : b ∈ cover l) (hal' : a ∈ cover l') (hbl' : b ∈ cover l') :
    (attachGraph (l ++ l') extra).IsTwoConnected :=
  overlayGraph_append_isTwoConnected hnd hnd' hl hl' hab
    (mem_attachPoints_of_mem ha) (mem_attachPoints_of_mem hb) hal hbl hal' hbl'

/-! ### Clause 1: the open nonboundary part is connected

The joining loop, transported from sets to the graph. What the graph occupies is
`cover pieces` (`attachGraph_pointSet`), so the whole statement is about covers. -/

/-- **`prop:local-grid-attachment` clause 1.** Adding to a family of segments the joining arcs
of the loop makes what it occupies, minus `C`, connected. Each joining arc must miss `C` — the
blueprint's *"because the joining arc lies in `D`"* — and that is the only thing asked of it. -/
theorem isConnected_cover_diff_of_joins {l : List Piece} {C : Set Plane} {r₀ : Plane}
    {reps : List Plane} {J : Plane → List Piece} (hr₀ : r₀ ∈ cover l \ C)
    (hJconn : ∀ r ∈ reps, IsPreconnected (cover (J r)))
    (hJhub : ∀ r ∈ reps, r₀ ∈ cover (J r)) (hJrep : ∀ r ∈ reps, r ∈ cover (J r))
    (hJC : ∀ r ∈ reps, ∀ z ∈ cover (J r), z ∉ C)
    (hcov : ∀ z ∈ cover l \ C, ∃ r ∈ reps, ∃ S : Set Plane,
      S ⊆ cover l \ C ∧ IsPreconnected S ∧ z ∈ S ∧ r ∈ S) :
    IsConnected (cover (l ++ reps.flatMap J) \ C) := by
  have hEq : cover (l ++ reps.flatMap J) \ C = (cover l \ C) ∪ ⋃ r ∈ reps, cover (J r) := by
    rw [cover_append, cover_flatMap']
    ext z
    simp only [Set.mem_sdiff, mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz | ⟨r, hr, hz⟩, hzC⟩
      · exact Or.inl ⟨hz, hzC⟩
      · exact Or.inr ⟨r, hr, hz⟩
    · rintro (⟨hz, hzC⟩ | ⟨r, hr, hz⟩)
      · exact ⟨Or.inl hz, hzC⟩
      · exact ⟨Or.inr ⟨r, hr, hz⟩, hJC r hr z hz⟩
  rw [hEq]
  exact isConnected_union_joins hr₀ hJconn hJhub hJrep hcov

/-! ### Clause 2: the graph contains the grid, and clause 3: the grid is fine -/

theorem localGridEdges_nondeg {p : Plane} {s : ℝ} {k : ℕ} (hs : 0 < s) (hk : 1 ≤ k) :
    ∀ P ∈ localGridEdges p s k, P.Nondeg := fun _ hP =>
  gridEdges_nondeg ((localGridX_strictMono hs hk).strictMonoOn _)
    ((localGridY_strictMono hs hk).strictMonoOn _) hk hk hP

/-- **`prop:local-grid-attachment` clause 2.** The assembled graph contains the whole local
grid: overlaying only cuts, it never removes. -/
theorem localGrid_subset_attachGraph_pointSet {p : Plane} {s : ℝ} {k : ℕ} (l : List Piece)
    (extra : List Plane) :
    cover (localGridEdges p s k) ⊆
      Graph.pointSet (attachGraph (l ++ localGridEdges p s k) extra) segmentDrawing := by
  rw [attachGraph_pointSet, cover_append]
  exact subset_union_right

/-- **`prop:local-grid-attachment` clause 3**, restated for the assembled graph: at the mesh
`localGridCount s ε` every closed grid rectangle has diameter `< ε`. -/
theorem attachGraph_localGridCell_diam {p : Plane} {s ε : ℝ} (hε : 0 < ε) (i j : ℕ)
    {x y : Plane} (hx : x ∈ localGridCell p s (localGridCount s ε) i j)
    (hy : y ∈ localGridCell p s (localGridCount s ε) i j) : dist x y < ε :=
  lt_of_le_of_lt (dist_le_of_mem_localGridCell hx hy) (localGridCount_spec hε)

/-! ### From the crosscut to two common vertices

*"Since `E` contains `J`, after subdivision `Γ ∪ E` and `K` have at least two common
vertices."* — the step that turns each degenerate case into the main one. Its content is the
swallowing clause of `exists_crosscut`: the grid edge's relative interior is a connected subset
of `ℓ ∩ F` through the chosen point, hence lies inside the crosscut's open part, hence the whole
closed grid edge lies inside the closed crosscut. -/

/-- **The crosscut contains the chosen grid edge.** -/
theorem seg_subset_crosscut {q₀ q₁ : Plane} {J : Piece}
    (hswallow : ∀ S : Set Plane, IsPreconnected S → S ⊆ Plane.line a b ∩ F → y ∈ S →
      S ⊆ openSegment ℝ q₀ q₁)
    (hJline : J.interior ⊆ Plane.line a b ∩ F) (hy : y ∈ J.interior) :
    J.seg ⊆ segment ℝ q₀ q₁ := by
  have h1 : J.interior ⊆ openSegment ℝ q₀ q₁ :=
    hswallow _ (convex_openSegment _ _).isPreconnected hJline hy
  calc J.seg = closure J.interior := (closure_openSegment _ _).symm
    _ ⊆ closure (openSegment ℝ q₀ q₁) := closure_mono h1
    _ = segment ℝ q₀ q₁ := closure_openSegment _ _

/-- A point of the crosscut lies on the `Γ`-side family once the crosscut has been appended
to it. -/
theorem mem_cover_append_crosscut {l : List Piece} {q₀ q₁ z : Plane}
    (hz : z ∈ segment ℝ q₀ q₁) : z ∈ cover (l ++ [(q₀, q₁)]) := by
  rw [cover_append]
  exact Or.inr (mem_cover_iff.2 ⟨(q₀, q₁), List.mem_singleton_self _, hz⟩)

/-- An end of a listed piece lies on what the list covers. -/
theorem left_mem_cover {l : List Piece} {P : Piece} (hP : P ∈ l) : P.1 ∈ cover l :=
  mem_cover_iff.2 ⟨P, hP, left_mem_segment ℝ _ _⟩

theorem right_mem_cover {l : List Piece} {P : Piece} (hP : P ∈ l) : P.2 ∈ cover l :=
  mem_cover_iff.2 ⟨P, hP, right_mem_segment ℝ _ _⟩

/-- **The degenerate cases, reduced to the main one.** With the crosscut `(q₀, q₁)` appended to
the `Γ`-side family, the two ends of the chosen grid edge `J` are two distinct points lying on
both families — which is exactly what `attachGraph_isTwoConnected` asks for.

Note what is *not* assumed: nothing about how many vertices `Γ` and `K` had in common. The case
split of the blueprint is a device for choosing `J` and the line `ℓ`; once they are chosen, the
three cases run the same argument. -/
theorem two_common_of_crosscut {l l' : List Piece} {q₀ q₁ : Plane} {J : Piece}
    (hJ : J ∈ l') (hJnd : J.Nondeg)
    (hswallow : ∀ S : Set Plane, IsPreconnected S → S ⊆ Plane.line a b ∩ F → y ∈ S →
      S ⊆ openSegment ℝ q₀ q₁)
    (hJline : J.interior ⊆ Plane.line a b ∩ F) (hy : y ∈ J.interior) :
    J.1 ≠ J.2 ∧ J.1 ∈ cover (l ++ [(q₀, q₁)]) ∧ J.2 ∈ cover (l ++ [(q₀, q₁)]) ∧
      J.1 ∈ cover l' ∧ J.2 ∈ cover l' := by
  have hsub := seg_subset_crosscut hswallow hJline hy
  exact ⟨hJnd, mem_cover_append_crosscut (hsub (left_mem_segment ℝ _ _)),
    mem_cover_append_crosscut (hsub (right_mem_segment ℝ _ _)),
    left_mem_cover hJ, right_mem_cover hJ⟩

/-! ## `prop:local-grid-attachment`, assembled

One graph, and each clause of the proposition a theorem about it. The graph is a `def` and not
an existential: `thm:finite-transfer`(a) takes `H` as an input and reads its drawing, its
2-connectivity and its point set separately. -/

theorem cover_swap (l₁ l₂ l₃ : List Piece) :
    cover ((l₁ ++ l₂) ++ l₃) = cover ((l₁ ++ l₃) ++ l₂) := by
  simp only [cover_append]
  ac_rfl

/-- The segments of the assembled extension: the polygonal nonboundary skeleton of `Γ` — with
whatever auxiliary crosscut the case needed already appended to it — then the joining arcs of the
loop, then the local grid on `W`. -/
noncomputable def gridAttachPieces (gsegs : List Piece) (reps : List Plane)
    (Jarc : Plane → List Piece) (p : Plane) (s ε : ℝ) : List Piece :=
  (gsegs ++ reps.flatMap Jarc) ++ localGridEdges p s (localGridCount s ε)

/-- **The extension `H_n` of `prop:local-grid-attachment`.** -/
noncomputable def gridAttachGraph (gsegs : List Piece) (reps : List Plane)
    (Jarc : Plane → List Piece) (p : Plane) (s ε : ℝ) (extra : List Plane) : Graph Plane Piece :=
  attachGraph (gridAttachPieces gsegs reps Jarc p s ε) extra

variable {gsegs : List Piece} {reps : List Plane} {Jarc : Plane → List Piece} {p : Plane}
  {s ε : ℝ} {extra : List Plane} {C : Set Plane} {r₀ : Plane}

instance gridAttachGraph_finite (gsegs : List Piece) (reps : List Plane)
    (Jarc : Plane → List Piece) (p : Plane) (s ε : ℝ) (extra : List Plane) :
    Graph.Finite (gridAttachGraph gsegs reps Jarc p s ε extra) := attachGraph_finite _ _

/-- The nondegeneracy of every segment in play, which is what `lem:polygonal-overlay` needs. -/
theorem gridAttachPieces_nondeg (hs : 0 < s)
    (hg : ∀ P ∈ gsegs, P.Nondeg) (hj : ∀ P ∈ reps.flatMap Jarc, P.Nondeg) :
    ∀ P ∈ gridAttachPieces gsegs reps Jarc p s ε, P.Nondeg := by
  intro P hP
  rcases List.mem_append.1 hP with hP' | hP'
  · rcases List.mem_append.1 hP' with hP'' | hP''
    exacts [hg P hP'', hj P hP'']
  · exact localGridEdges_nondeg hs (one_le_localGridCount s ε) P hP'

/-- **The extension is a plane graph**, drawn with straight edges — `lem:polygonal-overlay`. -/
theorem gridAttachGraph_isDrawing (hs : 0 < s)
    (hg : ∀ P ∈ gsegs, P.Nondeg) (hj : ∀ P ∈ reps.flatMap Jarc, P.Nondeg) :
    Graph.IsDrawing (gridAttachGraph gsegs reps Jarc p s ε extra) segmentDrawing :=
  attachGraph_isDrawing (gridAttachPieces_nondeg hs hg hj) extra

@[simp] theorem gridAttachGraph_pointSet :
    Graph.pointSet (gridAttachGraph gsegs reps Jarc p s ε extra) segmentDrawing =
      cover (gridAttachPieces gsegs reps Jarc p s ε) := attachGraph_pointSet _ _

/-- **Clause 2.** The extension contains the whole local grid on `W`. -/
theorem localGrid_subset_gridAttachGraph :
    cover (localGridEdges p s (localGridCount s ε)) ⊆
      Graph.pointSet (gridAttachGraph gsegs reps Jarc p s ε extra) segmentDrawing := by
  rw [gridAttachGraph_pointSet, gridAttachPieces, cover_append]
  exact subset_union_right

/-- **The extension is 2-connected** — the three cases of the blueprint, all of which end in
`lem:union-two-connected` applied to two distinct points lying on both families.

`hΓ` is the `Γ`-side hypothesis this module cannot discharge: the skeleton of `Γ`, with the
crosscut and the joining arcs appended and everything subdivided at the crossing points, is still
2-connected. For the polygonal part it is `pieceListGraph_subdivide_isTwoConnected`; for the arcs
of `C` and for the ears it is `Graph.IsTwoConnected.replace_edge_by_path` and
`Graph.IsTwoConnected.ear` iterated (`pieceListGraph_append_crosscut` above is the single ear
step, for a straight crosscut). -/
theorem gridAttachGraph_isTwoConnected (hs : 0 < s)
    (hg : ∀ P ∈ gsegs, P.Nondeg) (hj : ∀ P ∈ reps.flatMap Jarc, P.Nondeg)
    (hΓ : (pieceListGraph (subdivide (gsegs ++ reps.flatMap Jarc)
      (attachPoints (gridAttachPieces gsegs reps Jarc p s ε) extra))).IsTwoConnected)
    (hK : (pieceListGraph (subdivide (localGridEdges p s (localGridCount s ε))
      (attachPoints (gridAttachPieces gsegs reps Jarc p s ε) extra))).IsTwoConnected)
    {a b : Plane} (hab : a ≠ b) (ha : a ∈ extra) (hb : b ∈ extra)
    (haΓ : a ∈ cover (gsegs ++ reps.flatMap Jarc))
    (hbΓ : b ∈ cover (gsegs ++ reps.flatMap Jarc))
    (haK : a ∈ cover (localGridEdges p s (localGridCount s ε)))
    (hbK : b ∈ cover (localGridEdges p s (localGridCount s ε))) :
    (gridAttachGraph gsegs reps Jarc p s ε extra).IsTwoConnected := by
  refine attachGraph_isTwoConnected (fun P hP => ?_)
    (localGridEdges_nondeg hs (one_le_localGridCount s ε)) hΓ hK hab ha hb haΓ hbΓ haK hbK
  rcases List.mem_append.1 hP with hP' | hP'
  exacts [hg P hP', hj P hP']

/-- **Clause 1.** `|H| ∖ C` is connected — the component-joining loop, run once for each
representative. Nothing is asked of a joining arc except that it be connected, run from the hub
`r₀` to its representative, and miss `C`; the blueprint's *"because the joining arc lies in `D`"*
is the last of these. -/
theorem gridAttachGraph_isConnected_diff
    (hr₀ : r₀ ∈ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C)
    (hJconn : ∀ r ∈ reps, IsPreconnected (cover (Jarc r)))
    (hJhub : ∀ r ∈ reps, r₀ ∈ cover (Jarc r)) (hJrep : ∀ r ∈ reps, r ∈ cover (Jarc r))
    (hJC : ∀ r ∈ reps, ∀ z ∈ cover (Jarc r), z ∉ C)
    (hcov : ∀ z ∈ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C,
      ∃ r ∈ reps, ∃ S : Set Plane, S ⊆ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C
        ∧ IsPreconnected S ∧ z ∈ S ∧ r ∈ S) :
    IsConnected
      (Graph.pointSet (gridAttachGraph gsegs reps Jarc p s ε extra) segmentDrawing \ C) := by
  rw [gridAttachGraph_pointSet, gridAttachPieces, cover_swap]
  exact isConnected_cover_diff_of_joins hr₀ hJconn hJhub hJrep hJC hcov

end Schoenflies
