/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.Graph.K33
import LeanPool.Schoenflies.Graph.Redrawing
import LeanPool.Schoenflies.AlternatingCrosscuts

/-!
# Lemma 3.10: the utility graph is not planar, and Corollary 3.11 for its subdivisions

`Schoenflies/Graph/K33.lean` built the whole configuration: the six-cycle of a drawn `K(3,3)`
is a Jordan curve, each of the three remaining edges is a crosscut of it, two of the three lie
on the same side, their endpoints alternate, and any two of them are disjoint. This module
wires those five facts to `Schoenflies.alternating_crosscuts` and derives the contradiction; it
then does the blueprint's reduction of `cor:k33-subdivision` to `lem:k33`.

**One hypothesis is assumed and not proved: `Graph.IsHexRealization`. See "The gap" below.**
The remaining results use only the hypotheses in their statements.

## Blueprint

* `Graph.IsHexCrosscut` — the six-cycle, together with one of the three remaining edges, in the
  vocabulary `Schoenflies.IsPolygonalCrosscut` speaks: a `Schoenflies.ClosedPolygon`, its two
  arcs, the crosscut, and a reference point.
* `Graph.IsK33Config.endpoints_subset_arcA`, `…_arcB`, `…exists_reference_point`,
  `…isHexCrosscut` — the four *topological* clauses of `Schoenflies.IsPolygonalCrosscut`,
  discharged from the drawing, so that only the combinatorial realization has to be assumed.
* `Graph.IsHexRealization` — that combinatorial realization, and the one thing assumed here.
* `Graph.IsK33Config.exists_two_chords_same_region` — `lem:k33`, "two of the three lie on the
  same side", with the side named as a region of the complement rather than as one of a pair
  of open sets, which is the form the crosscut corollary consumes.
* `Graph.IsK33Config.false_of_isHexCrosscut` — the contradiction at a *fixed* pair of remaining
  edges: `cor:alternating-crosscuts` makes them meet, `chords_disjoint` says they do not.
* `Graph.IsK33Config.false_of_hexCrosscuts`, `…false_of_hexRealizations` — `lem:k33` for a
  drawing that is already polygonal.
* `Graph.IsK33Config.not_isDrawing` — `lem:k33`: a graph carrying a copy of `K(3,3)` has no
  plane drawing at all. `lem:polygonal-redrawing` reduces the general drawing to a polygonal
  one, which is the only place polygonality is used.
* `Graph.IsArcK33`, `Graph.k33Graph`, `Graph.IsArcK33.arcDrawing`, `…isDrawing`,
  `…isK33Config`, `…false_of_realization` — `cor:k33-subdivision`, first half: nine arcs in the
  plane meeting only where a `K(3,3)` forces them to already *are* a plane drawing of `K(3,3)`,
  on an abstract graph built here for the purpose.
* `Graph.IsK33Subdivision`, `…isArcK33`, `…false_of_realization` — `cor:k33-subdivision`: in a
  plane drawing of a subdivision, the branch paths draw nine such arcs.

## The gap: realizing the six-cycle as a `ClosedPolygon`

Every statement of `Schoenflies/PolygonalJordan.lean`, `Schoenflies/PolygonalCrosscut.lean` and
`Schoenflies/AlternatingCrosscuts.lean` is about a `Schoenflies.ClosedPolygon m` — a cyclic
*vertex list* with `vertex_inj`, `edges_meet` and `corner`. The six-cycle of a polygonally
drawn `K(3,3)` is a polygonal Jordan curve as a **point set**, and nothing in the development
turns a point set into a `ClosedPolygon`: there is no declaration anywhere whose conclusion is
`∃ m (C : ClosedPolygon m), C.carrier = _`. The only closed polygons that exist are the
hand-built `Schoenflies.triangle` and `Schoenflies.unitTriangle`.

`IsHexRealization` is exactly that missing step, stated for the one curve this argument needs
it for and pared down to its combinatorial core: four closed polygons and four equations
identifying their carriers and edge lists with the drawing. No topological side condition
survives in it — the reference point of Theorem 2.8 and the three "meets" clauses are proved
here from the drawing. It is *not proved here*, and every theorem below that mentions it is
therefore requires that realization as a hypothesis.

**Why the realization is allowed to change the drawing.** `IsHexRealization` asks for
`C.arc a k = arcA e s`, which pins the two ends of that arc — the vertices `x s` and
`y (s+1)` — to be *vertices* of `C`. A `Schoenflies.ClosedPolygon` has no straight vertices
(its `corner` field), so this is possible only if the six-cycle actually turns at `x s` and at
`y (s+1)`. A polygonal drawing need not do that: two of the three polygonal edges at a vertex
may leave it in exactly opposite directions, and then no closed polygon with that carrier has
that point as a vertex. A realization must therefore be free to bend the drawing at the six
vertices first, and `Graph.IsK33Config.not_isDrawing` gives it that freedom: it hands the
realization a polygonal drawing and accepts *any* drawing back. This restriction comes from
`Schoenflies.IsPolygonalCrosscut`, not from anything here; the alternative is a crosscut
interface that lets the two cut points be interior to edges of `C`.
-/

open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s t : Fin 3} {R : Set Plane}

/-! ### The missing realization, isolated

The six-cycle of a polygonally drawn `K(3,3)`, cut by the remaining edge `e s (s+1)`, presented
in the vocabulary of `Schoenflies.IsPolygonalCrosscut`: a `ClosedPolygon` whose carrier is the
six-cycle, whose two arcs from the cut are the two halves `arcA e s` and `arcB e s`, and whose
crosscut occupies exactly the remaining edge's arc. -/

/-- **The six-cycle and one remaining edge, realized as a polygonal crosscut.** `C` is the
six-cycle as a `Schoenflies.ClosedPolygon`, cut at the vertices `a` and `a + k` — which are the
two ends `x s` and `y (s+1)` of the remaining edge indexed by `s` — into the two arcs
`arcA e s` and `arcB e s`; `K` is the remaining edge, and `J₁`, `J₂` the two closed polygons it
forms with the two arcs.

This is the *only* thing the argument below assumes, and it is exactly what a bridge from
polygonal Jordan curves to `Schoenflies.ClosedPolygon` would supply. -/
def IsHexCrosscut (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁) (J₂ : ClosedPolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (yref : Plane),
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      IsPolygonalCrosscut C J₁ J₂ K a k yref

/-- The six-cycle separates the plane: it is the carrier of a closed polygon, and
`thm:polygonal-jordan` applies to that. -/
theorem isSeparating_hexSet (h : IsHexCrosscut drawing e s) :
    IsSeparating (hexSet drawing e) := by
  obtain ⟨_, _, _, C, _, _, _, _, _, _, hcar, _⟩ := h
  exact hcar ▸ C.isSeparating_carrier

namespace IsK33Config

/-! ### The alternation, with the two arcs named

`Graph.IsK33Config.chords_alternate` returns the two arcs existentially. The crosscut corollary
has to be handed *those particular sets*, since the realization has to reproduce them, so the
two membership clauses are restated here with the arcs written out. -/

/-- The near end of the next remaining edge is interior to the first arc. -/
theorem x_succ_mem_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    x (s + 1) ∈ edgesCover drawing (arcA e s) \ ({x s, y (s + 1)} : Set Plane) := by
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  refine ⟨mem_arcA_iff.2 ⟨(s + 1, s), by simp [arcAPairs],
    (hd.edge_isArcBetween (h.isLink (s + 1) s)).left_mem⟩, ?_⟩
  rintro (hc | hc)
  exacts [h.x_ne_x (hs1 s) hc, h.x_ne_y _ _ hc]

/-- The far end of the next remaining edge is interior to the second arc. -/
theorem y_succ_mem_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    y (s + 1 + 1) ∈ edgesCover drawing (arcB e s) \ ({x s, y (s + 1)} : Set Plane) := by
  have hsucc : ∀ s : Fin 3, s + 1 + 1 = s + 2 := by decide
  have hs2 : ∀ s : Fin 3, s + 2 ≠ s + 1 := by decide
  rw [hsucc s]
  refine ⟨mem_arcB_iff.2 ⟨(s + 2, s + 2), by simp [arcBPairs],
    (hd.edge_isArcBetween (h.isLink (s + 2) (s + 2))).right_mem⟩, ?_⟩
  rintro (hc | hc)
  exacts [h.y_ne_x _ _ hc, h.y_ne_y (hs2 s) hc]

/-! ### Two of the three remaining edges lie in one region -/

/-- A remaining edge's interior lies inside the edge's arc. -/
theorem chord_openArc_subset_edgeArc (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : openArc (drawing (e s (s + 1))) ⊆ edgeArc drawing (e s (s + 1)) := by
  rw [h.chord_openArc_eq hd s]; exact Set.sdiff_subset

/-- **Two of the three remaining edges lie in one and the same region of the complement of the
six-cycle.** This is `Graph.IsK33Config.exists_two_chords_same_side` with the two sides read as
the two regions `Int` and `Ext` of the polygonal Jordan curve theorem, which is the form the
crosscut corollary consumes. -/
theorem exists_two_chords_same_region (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hsep : IsSeparating (hexSet drawing e)) :
    ∃ s t : Fin 3, s ≠ t ∧ ∃ R : Set Plane, IsRegionOf (hexSet drawing e) R ∧
      openArc (drawing (e s (s + 1))) ⊆ R ∧ openArc (drawing (e t (t + 1))) ⊆ R := by
  obtain ⟨s, t, hst, hcase⟩ := h.exists_two_chords_same_side hd hsep.isOpen_inside
    hsep.isOpen_outside disjoint_inside_outside (inside_union_outside _).ge
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨s, t, hst, _, IsRegionOf.inside _, h1, h2⟩
  · exact ⟨s, t, hst, _, IsRegionOf.outside _, h1, h2⟩

/-! ### The topological side conditions of the crosscut, discharged

`Schoenflies.IsPolygonalCrosscut` asks for four things beyond the edge lists: that the crosscut
meets the polygon only in points of each arc, and a reference point off the polygon in the
region the crosscut does not enter. All four are properties of the *drawing*, and are proved
here, so that what has to be assumed from outside is only the combinatorial realization
(`Graph.IsHexRealization`). -/

/-- The two ends of the remaining edge lie on the first arc of the cut. -/
theorem endpoints_subset_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ({x s, y (s + 1)} : Set Plane) ⊆ edgesCover drawing (arcA e s) := by
  rintro p (rfl | rfl)
  · exact mem_arcA_iff.2 ⟨(s, s), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink s s)).left_mem⟩
  · exact mem_arcA_iff.2 ⟨(s + 1, s + 1), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1))).right_mem⟩

/-- The two ends of the remaining edge lie on the second arc of the cut. -/
theorem endpoints_subset_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ({x s, y (s + 1)} : Set Plane) ⊆ edgesCover drawing (arcB e s) := by
  rintro p (rfl | rfl)
  · exact mem_arcB_iff.2 ⟨(s, s + 2), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink s (s + 2))).left_mem⟩
  · exact mem_arcB_iff.2 ⟨(s + 2, s + 1), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink (s + 2) (s + 1))).right_mem⟩

/-- **The reference point of Theorem 2.8, for a remaining edge.** The interior of the remaining
edge lies in one region of the complement of the six-cycle; any point of the *other* region is a
legitimate reference point, and the other region is nonempty because it is a region. -/
theorem exists_reference_point (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hsep : IsSeparating (hexSet drawing e)) (s : Fin 3) :
    ∃ yref : Plane, yref ∉ hexSet drawing e ∧
      Disjoint (edgeArc drawing (e s (s + 1)))
        (connectedComponentIn (hexSet drawing e)ᶜ yref) := by
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzC : z ∉ hexSet drawing e := h.chord_openArc_subset_compl hd s hz
  -- The region of `z` and the region on the far side of it are the two regions.
  have hpair := hsep.isRegionPair_farRegion hzC
  obtain ⟨yref, hyref⟩ := (hpair.right.isConnected hsep).nonempty
  refine ⟨yref, hpair.right.subset_compl hyref, ?_⟩
  rw [hpair.right.connectedComponentIn_eq hsep hyref, Set.disjoint_left]
  intro p hp hpfar
  by_cases hpin : p ∈ ({x s, y (s + 1)} : Set Plane)
  · refine hpfar.1 ?_
    rcases hpin with rfl | rfl
    exacts [h.x_mem_hexSet hd s, h.y_mem_hexSet hd (s + 1)]
  · refine hpfar.2 (h.chord_openArc_subset_connectedComponentIn hd s hz ?_)
    rw [h.chord_openArc_eq hd s]
    exact ⟨hp, hpin⟩

end IsK33Config

/-! ### What must still be assumed: the combinatorial realization

Everything above is proved. What is not is that the six-cycle, its two arcs, and the two closed
curves the remaining edge forms with them are *closed polygons at all* — that a polygonal Jordan
curve given as a point set carries a cyclic vertex list. `IsHexRealization` says exactly that,
and nothing more: no reference point, no meeting condition, only the four `ClosedPolygon`s and
the four equations identifying their carriers and edge lists with the drawing. -/

/-- **The six-cycle and one remaining edge, realized combinatorially.** The six-cycle is a
`Schoenflies.ClosedPolygon` `C` whose two arcs from the cut at `a`, `a + k` are the two halves
`arcA e s`, `arcB e s` of the six-cycle; the remaining edge occupies the segments `K`; and the
two closed curves it forms with the two arcs are closed polygons `J₁`, `J₂` carrying exactly
those segments.

This is the one thing this module assumes and does not prove. See "The gap" in the module
docstring. -/
def IsHexRealization (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁) (J₂ : ClosedPolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ),
      k ≤ m + 3 ∧
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      SameEdges J₁.pieces (C.arcPieces a k ++ K) ∧
      SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K)

namespace IsK33Config

/-- **The realization is enough.** The four topological clauses of
`Schoenflies.IsPolygonalCrosscut` come from the drawing: the remaining edge meets the six-cycle
exactly in its own two ends (`chord_inter_hexSet`), which lie on both arcs, and the reference
point is `exists_reference_point`. -/
theorem isHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hr : IsHexRealization drawing e s) : IsHexCrosscut drawing e s := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, hk, hcar, hA, hB, hK, hE₁, hE₂⟩ := hr
  have hsep : IsSeparating (hexSet drawing e) := hcar ▸ C.isSeparating_carrier
  obtain ⟨yref, hyref, hdisj⟩ := h.exists_reference_point hd hsep s
  refine ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK,
    ⟨hk, hE₁, hE₂, ?_, ?_, ?_, ?_⟩⟩
  · rw [hK, hcar, hA, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcA hd s
  · rw [hK, hcar, hB, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcB hd s
  · rw [hcar]; exact hyref
  · rw [hK, hcar]; exact hdisj

/-! ### The contradiction -/

/-- **The two remaining edges indexed by `s` and `s + 1` cannot lie in one region.** Their four
ends alternate around the six-cycle (`chords_alternate`), so `cor:alternating-crosscuts` makes
them meet; but distinct edges of a plane graph meet only at shared vertices, and these two share
none (`chords_disjoint`). -/
theorem false_of_isHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : IsHexCrosscut drawing e s) (hsep : IsSeparating (hexSet drawing e))
    (hR : IsRegionOf (hexSet drawing e) R)
    (h1 : openArc (drawing (e s (s + 1))) ⊆ R)
    (h2 : openArc (drawing (e (s + 1) (s + 1 + 1))) ⊆ R) : False := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK, hcc⟩ := hcross
  -- A point of the first remaining edge, off the six-cycle: it pins down the region.
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzK : z ∈ cover K := by rw [hK]; exact h.chord_openArc_subset_edgeArc hd s hz
  have hzC : z ∉ C.carrier := by rw [hcar]; exact h.chord_openArc_subset_compl hd s hz
  have hzR : z ∈ R := h1 hz
  -- The second remaining edge's interior lies in the component of `z`.
  have hside : edgeArc drawing (e (s + 1) (s + 1 + 1)) \ ({x (s + 1), y (s + 1 + 1)} : Set Plane)
      ⊆ connectedComponentIn C.carrierᶜ z := by
    rw [hcar, hR.connectedComponentIn_eq hsep hzR, ← h.chord_openArc_eq hd (s + 1)]
    exact h2
  -- `cor:alternating-crosscuts`.
  obtain ⟨w, hw₁, hw₂⟩ := hcc.alternating_inter_nonempty_of_same_side hzK hzC hA hB
    (h.arcs_inter hd s) (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1 + 1))) hside
    (h.x_succ_mem_arcA hd s) (h.y_succ_mem_arcB hd s)
  -- … against the disjointness of two remaining edges.
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  have := h.chords_disjoint hd (hs1 s)
  rw [Set.eq_empty_iff_forall_notMem] at this
  exact this w ⟨hw₁, by rwa [hK] at hw₂⟩

/-- **`lem:k33` for a drawing that is already polygonal.** Three remaining edges, two sides:
two of them lie in one region (`exists_two_chords_same_region`); every pair of remaining edges
is indexed by `s` and `s + 1` for some `s`, so `false_of_isHexCrosscut` applies. -/
theorem false_of_hexCrosscuts (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : ∀ s : Fin 3, IsHexCrosscut drawing e s) : False := by
  have hsep : IsSeparating (hexSet drawing e) := isSeparating_hexSet (hcross 0)
  obtain ⟨s, t, hst, R, hR, h1, h2⟩ := h.exists_two_chords_same_region hd hsep
  -- In `Fin 3` two distinct indices are consecutive one way or the other.
  have hpair : ∀ s t : Fin 3, s ≠ t → t = s + 1 ∨ s = t + 1 := by decide
  rcases hpair s t hst with rfl | rfl
  · exact h.false_of_isHexCrosscut hd (hcross s) hsep hR h1 h2
  · exact h.false_of_isHexCrosscut hd (hcross t) hsep hR h2 h1

/-- **`lem:k33` for a polygonal drawing, from the combinatorial realization alone.** -/
theorem false_of_hexRealizations (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hr : ∀ s : Fin 3, IsHexRealization drawing e s) : False :=
  h.false_of_hexCrosscuts hd fun s => h.isHexCrosscut hd (hr s)

/-- **Lemma 3.10 (nonplanarity of `K(3,3)`).** A finite graph carrying a copy of `K(3,3)` has no
plane drawing.

`lem:polygonal-redrawing` replaces an arbitrary drawing by a polygonal one on the same graph and
the same vertices, which is the only use polygonality is put to; the contradiction itself is
`false_of_hexRealizations`. The realization hypothesis is therefore consulted only about
drawings that are already polygonal — and it is allowed to *change* the drawing again, which it
must be: see "The gap" in the module docstring. -/
theorem not_isDrawing [G.Finite] (h : IsK33Config G x y e)
    (hreal : ∀ dr : β → ℝ → Plane, IsDrawing G dr → (∀ f ∈ E(G), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : β → ℝ → Plane, IsDrawing G dr' ∧ ∀ s : Fin 3, IsHexRealization dr' e s) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly⟩ := polygonal_redrawing G dr hdr
  obtain ⟨dr'', hdr'', hr⟩ := hreal dr' hdr' hpoly
  exact h.false_of_hexRealizations hdr'' hr

end IsK33Config

/-! ## Corollary 3.11: no subdivision of `K(3,3)` has a plane drawing

The blueprint's proof replaces each branch path of a subdivision by the simple arc it draws and
then treats that arc as a single edge. Both halves are done here, in that order: first the
*abstract* statement that nine arcs meeting only where they must already carry a drawn
`K(3,3)` (`Graph.IsArcK33`), then the reduction of a drawn subdivision to nine such arcs. -/

/-- **Nine arcs in the plane, meeting only where they must.** This is what a plane drawing of a
subdivision of `K(3,3)` leaves once each branch path has been replaced by the arc it draws: six
distinct points, and for each pair `(i, j)` an arc from `x i` to `y j`, with two distinct arcs
meeting only in a point that is an endpoint of both.

Nothing here mentions a graph. The abstract `K(3,3)` that carries these arcs is built below. -/
structure IsArcK33 (x y : Fin 3 → Plane) (P : Fin 3 → Fin 3 → Set Plane) : Prop where
  /-- The `(i, j)`-th arc runs from `x i` to `y j`. -/
  arc : ∀ i j, IsArcBetween (P i j) (x i) (y j)
  /-- The three points of the first side are distinct. -/
  x_injective : Function.Injective x
  /-- The three points of the second side are distinct. -/
  y_injective : Function.Injective y
  /-- The two sides are disjoint. -/
  ne : ∀ i j, x i ≠ y j
  /-- Two distinct arcs meet only in a common endpoint. -/
  meet : ∀ i j k l, (i, j) ≠ (k, l) →
    P i j ∩ P k l ⊆ ({x i, y j} : Set Plane) ∩ ({x k, y l} : Set Plane)

/-- **The abstract `K(3,3)` on six named points of the plane.** Its edges are index pairs, and
`(i, j)` links `x i` to `y j`. The edge set is all of `Fin 3 × Fin 3`, so no membership side
condition ever has to be discharged. -/
def k33Graph (x y : Fin 3 → Plane) : Graph Plane (Fin 3 × Fin 3) where
  vertexSet := Set.range x ∪ Set.range y
  edgeSet := Set.univ
  IsLink p u v := (u = x p.1 ∧ v = y p.2) ∨ (u = y p.2 ∧ v = x p.1)
  isLink_symm := by
    rintro ⟨i, j⟩ -
    constructor
    rintro u v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩]
  eq_or_eq_of_isLink_of_isLink := by
    rintro ⟨i, j⟩ u v a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  edge_mem_iff_exists_isLink := by
    rintro ⟨i, j⟩
    exact ⟨fun _ => ⟨x i, y j, Or.inl ⟨rfl, rfl⟩⟩, fun _ => Set.mem_univ _⟩
  left_mem_of_isLink := by
    rintro ⟨i, j⟩ u v (⟨rfl, -⟩ | ⟨rfl, -⟩)
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩]

@[simp] theorem k33Graph_vertexSet (x y : Fin 3 → Plane) :
    V(k33Graph x y) = Set.range x ∪ Set.range y := rfl

@[simp] theorem k33Graph_edgeSet (x y : Fin 3 → Plane) :
    E(k33Graph x y) = (Set.univ : Set (Fin 3 × Fin 3)) := rfl

theorem k33Graph_isLink (x y : Fin 3 → Plane) (i j : Fin 3) :
    (k33Graph x y).IsLink (i, j) (x i) (y j) := Or.inl ⟨rfl, rfl⟩

/-- An endpoint of an edge of the abstract `K(3,3)` is incident with it. -/
theorem k33Graph_inc {x y : Fin 3 → Plane} {i j : Fin 3} {p : Plane}
    (hp : p ∈ ({x i, y j} : Set Plane)) : (k33Graph x y).Inc (i, j) p := by
  rcases hp with rfl | rfl
  · exact ⟨y j, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨x i, Or.inr ⟨rfl, rfl⟩⟩

instance (x y : Fin 3 → Plane) : (k33Graph x y).Finite where
  finite_vertexSet := (Set.finite_range x).union (Set.finite_range y)
  finite_edgeSet := Set.finite_univ

namespace IsArcK33

variable {x y : Fin 3 → Plane} {P : Fin 3 → Fin 3 → Set Plane}

/-- The nine arcs, parametrized: a drawing of `k33Graph`. The parametrizations are the ones the
arcs come with, so the point set of an edge is the arc it was built from
(`IsArcK33.edgeArc_eq`). -/
noncomputable def arcDrawing (h : IsArcK33 x y P) : Fin 3 × Fin 3 → ℝ → Plane :=
  fun p => (h.arc p.1 p.2).choose

theorem edgeArc_eq (h : IsArcK33 x y P) (i j : Fin 3) :
    edgeArc h.arcDrawing (i, j) = P i j := (h.arc i j).choose_spec.2.2.1

theorem arcDrawing_zero (h : IsArcK33 x y P) (i j : Fin 3) : h.arcDrawing (i, j) 0 = x i :=
  (h.arc i j).choose_spec.2.2.2.1

theorem arcDrawing_one (h : IsArcK33 x y P) (i j : Fin 3) : h.arcDrawing (i, j) 1 = y j :=
  (h.arc i j).choose_spec.2.2.2.2

/-- An arc carries none of the six points except its own two ends: a third point `x k` lies on
the arc `P k l` for every `l`, and two distinct arcs meet only in a common end. -/
theorem mem_arc_elim (h : IsArcK33 x y P) {i j : Fin 3} {p : Plane}
    (hpV : p ∈ Set.range x ∪ Set.range y) (hp : p ∈ P i j) :
    p ∈ ({x i, y j} : Set Plane) := by
  have hsucc : ∀ i : Fin 3, i + 1 ≠ i := by decide
  rcases hpV with ⟨k, rfl⟩ | ⟨l, rfl⟩
  · -- `x k` lies on `P k (j+1)`, an arc with a different index pair.
    exact (h.meet i j k (j + 1) (fun hc => hsucc j (congrArg Prod.snd hc).symm)
      ⟨hp, (h.arc k (j + 1)).left_mem⟩).1
  · -- `y l` lies on `P (i+1) l`.
    exact (h.meet i j (i + 1) l (fun hc => hsucc i (congrArg Prod.fst hc).symm)
      ⟨hp, (h.arc (i + 1) l).right_mem⟩).1

/-- **The nine arcs draw the abstract `K(3,3)` in the plane.** -/
theorem isDrawing (h : IsArcK33 x y P) : IsDrawing (k33Graph x y) h.arcDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, j⟩ -
    obtain ⟨hc, hi, -, -, -⟩ := (h.arc i j).choose_spec
    refine ⟨hc, hi, ?_⟩
    rw [show h.arcDrawing (i, j) 0 = x i from h.arcDrawing_zero i j,
      show h.arcDrawing (i, j) 1 = y j from h.arcDrawing_one i j]
    exact k33Graph_isLink x y i j
  · rintro ⟨i, j⟩ u v w hl hwV hw
    have hmem : w ∈ ({x i, y j} : Set Plane) :=
      h.mem_arc_elim hwV (by rwa [h.edgeArc_eq i j] at hw)
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem
    · exact hmem.symm
  · rintro ⟨i, j⟩ ⟨k, l⟩ - - hne p hp hq
    rw [h.edgeArc_eq i j] at hp
    rw [h.edgeArc_eq k l] at hq
    obtain ⟨hij, hkl⟩ := h.meet i j k l hne ⟨hp, hq⟩
    refine ⟨?_, k33Graph_inc hij, k33Graph_inc hkl⟩
    rcases hij with rfl | rfl
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩]

/-- The nine arcs carry a copy of `K(3,3)`, on the graph they draw. -/
theorem isK33Config (h : IsArcK33 x y P) :
    IsK33Config (k33Graph x y) x y (fun i j => (i, j)) where
  isLink := k33Graph_isLink x y
  x_injective := h.x_injective
  y_injective := h.y_injective
  ne := h.ne

/-- **`lem:k33` for nine arcs**: no nine arcs in the plane meet only where a `K(3,3)` forces
them to. This assumes the realization, exactly as `Graph.IsK33Config.not_isDrawing` does. -/
theorem false_of_realization (h : IsArcK33 x y P)
    (hreal : ∀ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr →
      (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr' ∧
        ∀ s : Fin 3, IsHexRealization dr' (fun i j => (i, j)) s) : False :=
  h.isK33Config.not_isDrawing hreal ⟨h.arcDrawing, h.isDrawing⟩

end IsArcK33

/-! ### From a drawn subdivision to nine arcs -/

variable {H : Graph Plane β} {W : Fin 3 → Fin 3 → List β}

/-- **A subdivision of `K(3,3)` inside a graph.** Six distinct branch vertices and nine branch
paths, the `(i, j)`-th running from `x i` to `y j`; distinct branch paths share no edge and meet
only in vertices that are branch vertices of both.

Both clauses are combinatorial: no drawing appears. That distinct branch paths meet only in
common branch vertices is the blueprint's own phrasing of what a subdivision is. -/
structure IsK33Subdivision (H : Graph Plane β) (x y : Fin 3 → Plane)
    (W : Fin 3 → Fin 3 → List β) : Prop where
  /-- The `(i, j)`-th branch path runs from `x i` to `y j`. -/
  isPath : ∀ i j, H.IsPath (x i) (W i j) (y j)
  /-- The three branch vertices of the first side are distinct. -/
  x_injective : Function.Injective x
  /-- The three branch vertices of the second side are distinct. -/
  y_injective : Function.Injective y
  /-- The two sides are disjoint. -/
  ne : ∀ i j, x i ≠ y j
  /-- Distinct branch paths share no edge. -/
  edge_ne : ∀ i j k l, (i, j) ≠ (k, l) → ∀ f ∈ W i j, f ∉ W k l
  /-- Distinct branch paths meet only in vertices that are branch vertices of both. -/
  vertex_meet : ∀ i j k l, (i, j) ≠ (k, l) → ∀ v ∈ H.walkVertices (x i) (W i j),
    v ∈ H.walkVertices (x k) (W k l) → v ∈ ({x i, y j} : Set Plane) ∩ ({x k, y l} : Set Plane)

namespace IsK33Subdivision

variable {x y : Fin 3 → Plane}

/-- A branch path has at least one edge: an empty one would identify its two ends. -/
theorem ne_nil (h : IsK33Subdivision H x y W) (i j : Fin 3) : W i j ≠ [] := by
  intro hnil
  have hp := h.isPath i j
  rw [hnil] at hp
  exact h.ne i j hp.isWalk.eq_of_nil

/-- **The branch paths of a drawn subdivision are nine arcs meeting only where they must.**
A point on two branch paths lies on an edge of each; the two edges are distinct, so a plane
drawing puts the point at a vertex incident with both, and a vertex on two branch paths is a
branch vertex of both. -/
theorem isArcK33 {drawing : β → ℝ → Plane} (hd : IsDrawing H drawing)
    (h : IsK33Subdivision H x y W) : IsArcK33 x y fun i j => edgesCover drawing (W i j) := by
  refine ⟨fun i j => hd.path_isArcBetween (h.isPath i j) (h.ne_nil i j), h.x_injective,
    h.y_injective, h.ne, ?_⟩
  rintro i j k l hne p ⟨hp1, hp2⟩
  obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hp1
  obtain ⟨g, hg, hpg⟩ := mem_edgesCover_iff.1 hp2
  have hfg : f ≠ g := fun hEq => h.edge_ne i j k l hne f hf (hEq ▸ hg)
  obtain ⟨-, hincf, hincg⟩ := hd.edge_inter ((h.isPath i j).edge_mem hf)
    ((h.isPath k l).edge_mem hg) hfg hpf hpg
  exact h.vertex_meet i j k l hne p (mem_walkVertices_of_mem_covered ⟨f, hf, hincf⟩)
    (mem_walkVertices_of_mem_covered ⟨g, hg, hincg⟩)

/-- **Corollary 3.11 (subdivisions of `K(3,3)`).** No subdivision of `K(3,3)` has a plane
drawing. This assumes the realization, exactly as `Graph.IsK33Config.not_isDrawing` does, and
the realization is needed only for the *contracted* graph `k33Graph x y`, whose nine edges are
the branch paths. -/
theorem false_of_realization {drawing : β → ℝ → Plane} (hd : IsDrawing H drawing)
    (h : IsK33Subdivision H x y W)
    (hreal : ∀ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr →
      (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr' ∧
        ∀ s : Fin 3, IsHexRealization dr' (fun i j => (i, j)) s) : False :=
  (h.isArcK33 hd).false_of_realization hreal

end IsK33Subdivision

end Graph
