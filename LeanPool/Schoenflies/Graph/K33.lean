/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Graph.CycleJordan
public import LeanPool.Schoenflies.Subarc

/-!
# The utility graph `K(3,3)` inside a plane graph

The blueprint's proof of `lem:k33` is four sentences: regard `K(3,3)` as the six-cycle
`x₀y₀x₁y₁x₂y₂x₀` together with the three remaining edges `x₀y₁, x₁y₂, x₂y₀`; the six-cycle is
a Jordan curve; each remaining edge lies wholly on one side of it; two of the three lie on the
same side, and their endpoints alternate on the six-cycle, contrary to
`cor:alternating-crosscuts`.

**Everything in that proof except the last two citations is established here.** What is left is
the polygonal Jordan curve theorem — which supplies "the two sides" — and the alternating
crosscut corollary itself; neither exists yet, so `lem:k33` is not stated. See the note at the
end of this docstring for exactly how the last step will read.

## `K(3,3)` is a configuration, not a graph

There is no `K33 : Graph α β`. A copy of `K(3,3)` inside `G` is `Graph.IsK33Config G x y e`:
six vertices `x 0, x 1, x 2, y 0, y 1, y 2`, all distinct, and nine edge names `e i j` with
`e i j` linking `x i` to `y j`. Nothing says `G` has no other vertex or edge.

This is the shape the theorem is used in — one always *finds* a `K(3,3)` inside a graph one
already has, never constructs the abstract one — and it is also what makes the drawing
hypothesis land correctly: `Graph.IsDrawing G drawing` is a hypothesis about all of `G`, so
taking `G` larger only strengthens it.

Two economies follow from stating the configuration this way. The nine edge names are
automatically distinct (`Graph.IsK33Config.eq_of_e_eq`): an edge has only two ends, so two
names coinciding would force the index pairs to agree. And no looplessness clause is needed:
`x i ≠ y j` is one of the four fields.

## The indexing is arithmetic in `Fin 3`, so that `decide` can do the bookkeeping

The six-cycle uses the edges `e i i` and `e (i+1) i`; the three remaining edges are
`e s (s+1)` for `s : Fin 3`. Every combinatorial side condition below — that a remaining edge
is not a cycle edge, that the two arcs of the cut cycle cover it and meet only at the cut
points — is a statement about index pairs quantified over `Fin 3`, and is discharged by
`decide`. The edges themselves never have to be compared.

The two arcs into which the ends of the remaining edge `e s (s+1)` cut the six-cycle are named
by their index pairs as well (`Graph.arcAPairs`, `Graph.arcBPairs`); `Graph.arcA` and
`Graph.arcB` are the corresponding edge lists, `rfl`-equal to the mapped pair lists so that
both presentations are available with no conversion lemma.

## Blueprint

* `Graph.IsK33Config` — a copy of the utility graph.
* `Graph.IsK33Config.hexagon_isCycleThrough` — §"Plane graphs and the utility graph": "regard
  `K(3,3)` as the six-cycle `x₁y₁x₂y₂x₃y₃x₁` together with the three remaining edges".
* `Graph.IsK33Config.hexagon_isJordanCurve` — `lem:k33`, "the six-cycle is a polygonal Jordan
  curve". Polygonality plays no part; it is needed only where the *polygonal* Jordan curve
  theorem is applied to the result.
* `Graph.IsK33Config.chord_inter_hexSet`, `Graph.IsK33Config.chord_openArc_eq`,
  `Graph.IsK33Config.chord_openArc_subset_connectedComponentIn` — `lem:k33`, "each remaining
  edge lies wholly on one side": a remaining edge meets the six-cycle in exactly its own two
  ends, so its interior is a connected subset of the complement, hence lies in one component.
  This is also the crosscut hypothesis of `thm:polygonal-crosscut` and
  `cor:alternating-crosscuts`.
* `Graph.IsK33Config.exists_two_chords_same_side` — `lem:k33`, "two of the three lie on the
  same side". The two sides arrive as an arbitrary pair of disjoint open sets covering the
  complement, which is the form `thm:polygonal-jordan` will supply them in.
* `Graph.IsK33Config.chords_alternate` — `lem:k33`, "their endpoints alternate on the
  six-cycle", in the form `cor:alternating-crosscuts` consumes: the ends of one remaining edge
  cut the cycle into two arcs meeting only at those ends, and the two ends of another remaining
  edge lie one interior to each. Every pair of remaining edges is of the form `(s, s+1)`, so
  the single index `s` covers all three pairs.
* `Graph.IsK33Config.chords_disjoint` — the disjointness that `cor:alternating-crosscuts`
  contradicts: two remaining edges have four distinct ends, and distinct edges of a plane graph
  meet only at a shared end.

**How `lem:k33` will close.** Given a plane drawing of a graph with a `K(3,3)` configuration,
make it polygonal (`Graph.polygonal_redrawing`, `lem:polygonal-redrawing`); the six-cycle is
then a polygonal Jordan curve, and `thm:polygonal-jordan` gives the two disjoint open sides
that `exists_two_chords_same_side` wants. It returns two remaining edges on the same side;
`chords_alternate` says their ends alternate, so `cor:alternating-crosscuts` makes them meet,
and `chords_disjoint` says they do not.
-/

@[expose] public section

open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {α β : Type*} {G : Graph α β} {x y : Fin 3 → α} {e : Fin 3 → Fin 3 → β}
variable {i j k l s t : Fin 3} {z : α}

/-- A copy of the utility graph `K(3,3)` inside `G`. -/
structure IsK33Config (G : Graph α β) (x y : Fin 3 → α) (e : Fin 3 → Fin 3 → β) : Prop where
  /-- `e i j` joins the `i`-th vertex of one side to the `j`-th vertex of the other. -/
  isLink : ∀ i j, G.IsLink (e i j) (x i) (y j)
  /-- The three vertices of the first side are distinct. -/
  x_injective : Function.Injective x
  /-- The three vertices of the second side are distinct. -/
  y_injective : Function.Injective y
  /-- The two sides are disjoint. -/
  ne : ∀ i j, x i ≠ y j

namespace IsK33Config

theorem x_ne_x (h : IsK33Config G x y e) (hik : i ≠ k) : x i ≠ x k :=
  fun he ↦ hik (h.x_injective he)

theorem y_ne_y (h : IsK33Config G x y e) (hjl : j ≠ l) : y j ≠ y l :=
  fun he ↦ hjl (h.y_injective he)

theorem x_ne_y (h : IsK33Config G x y e) (i j : Fin 3) : x i ≠ y j := h.ne i j

theorem y_ne_x (h : IsK33Config G x y e) (j i : Fin 3) : y j ≠ x i := (h.ne i j).symm

/-- **The nine edges carry nine different names.** This is not an axiom of the configuration:
an edge has only two ends, so two of the nine names being equal would force the two index
pairs to agree. -/
theorem eq_of_e_eq (h : IsK33Config G x y e) (heq : e i j = e k l) : i = k ∧ j = l := by
  have h' : G.IsLink (e i j) (x k) (y l) := by rw [heq]; exact h.isLink k l
  rcases (h.isLink i j).eq_and_eq_or_eq_and_eq h' with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨h.x_injective h1, h.y_injective h2⟩
  · exact absurd h1 (h.ne i l)

theorem e_ne (h : IsK33Config G x y e) (hne : ¬ (i = k ∧ j = l)) : e i j ≠ e k l :=
  fun heq ↦ hne (h.eq_of_e_eq heq)

/-- A vertex on one of the nine edges is one of that edge's two ends. -/
theorem inc_elim (h : IsK33Config G x y e) (hz : G.Inc (e i j) z) : z = x i ∨ z = y j :=
  hz.eq_or_eq_of_isLink (h.isLink i j)

/-- **Freshness, in the form the path constructor asks for.** A vertex which is neither the
source of the rest of the walk nor an end of any of its edges is not among the vertices that
rest visits. -/
theorem notMem_walkVertices (h : IsK33Config G x y e) {W : List β} {w : α} (hzw : z ≠ w)
    (hW : ∀ f ∈ W, ∃ i j, f = e i j ∧ z ≠ x i ∧ z ≠ y j) :
    z ∉ G.walkVertices w W := by
  intro hz
  rcases mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, hinc⟩
  · exact hzw rfl
  obtain ⟨i, j, rfl, hxi, hyj⟩ := hW f hf
  rcases h.inc_elim hinc with hh | hh
  exacts [hxi hh, hyj hh]

end IsK33Config

/-! ### The six-cycle

The blueprint reads `K(3,3)` as the six-cycle `x₀y₀x₁y₁x₂y₂x₀` together with the three
remaining edges. The cycle is presented as `Schoenflies/Graph/Cycle.lean` presents one:
through the edge `e 0 0`, with a detour path running the other way round. -/

/-- The index pairs of the six edges of the six-cycle, in the order the cycle is traversed
starting from `e 0 0`. Kept as index pairs, not as edges, because every question about which
edges the cycle uses is then decidable. -/
def hexPairs : List (Fin 3 × Fin 3) := [(0, 0), (0, 2), (2, 2), (2, 1), (1, 1), (1, 0)]

/-- The five edges of the detour of the six-cycle: the path
`x₀ → y₂ → x₂ → y₁ → x₁ → y₀` that returns to the other end of `e 0 0`. -/
def hexDetour (e : Fin 3 → Fin 3 → β) : List β := [e 0 2, e 2 2, e 2 1, e 1 1, e 1 0]

/-- The six edges of the six-cycle. -/
def hexList (e : Fin 3 → Fin 3 → β) : List β := e 0 0 :: hexDetour e

theorem hexList_eq_map (e : Fin 3 → Fin 3 → β) :
    hexList e = hexPairs.map fun p ↦ e p.1 p.2 := rfl

theorem mem_hexList_iff {f : β} : f ∈ hexList e ↔ ∃ p ∈ hexPairs, f = e p.1 p.2 := by
  rw [hexList_eq_map]
  simp only [List.mem_map, eq_comm]

namespace IsK33Config

/-- The detour of the six-cycle is a path. Each freshness clause says that the vertex a step
departs from is none of the six vertices the rest of the detour meets. -/
theorem hexDetour_isPath (h : IsK33Config G x y e) : G.IsPath (x 0) (hexDetour e) (y 0) := by
  have h5 : G.IsPath (x 1) [e 1 0] (y 0) := .single (h.isLink 1 0) (h.x_ne_y 1 0)
  have h4 : G.IsPath (y 1) [e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 1 1).symm h5 (h.notMem_walkVertices (h.y_ne_x 1 1) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨1, 0, rfl, h.y_ne_x 1 1, h.y_ne_y (by decide)⟩
  have h3 : G.IsPath (x 2) [e 2 1, e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 2 1) h4 (h.notMem_walkVertices (h.x_ne_y 2 1) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨1, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 2 1⟩
    · exact ⟨1, 0, rfl, h.x_ne_x (by decide), h.x_ne_y 2 0⟩
  have h2 : G.IsPath (y 2) [e 2 2, e 2 1, e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 2 2).symm h3 (h.notMem_walkVertices (h.y_ne_x 2 2) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact ⟨2, 1, rfl, h.y_ne_x 2 2, h.y_ne_y (by decide)⟩
    · exact ⟨1, 1, rfl, h.y_ne_x 2 1, h.y_ne_y (by decide)⟩
    · exact ⟨1, 0, rfl, h.y_ne_x 2 1, h.y_ne_y (by decide)⟩
  refine .cons (h.isLink 0 2) h2 (h.notMem_walkVertices (h.x_ne_y 0 2) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨2, 2, rfl, h.x_ne_x (by decide), h.x_ne_y 0 2⟩
  · exact ⟨2, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 0 1⟩
  · exact ⟨1, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 0 1⟩
  · exact ⟨1, 0, rfl, h.x_ne_x (by decide), h.x_ne_y 0 0⟩

/-- **The six-cycle is a cycle**, presented through the edge `e 0 0`. -/
theorem hexagon_isCycleThrough (h : IsK33Config G x y e) :
    G.IsCycleThrough (e 0 0) (x 0) (y 0) (hexDetour e) := by
  refine ⟨h.isLink 0 0, h.hexDetour_isPath, ?_⟩
  simp only [hexDetour, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.e_ne (by decide), h.e_ne (by decide), h.e_ne (by decide), h.e_ne (by decide),
    h.e_ne (by decide)⟩

/-! ### The three remaining edges

`e s (s+1)`, for `s : Fin 3`, are the three edges of `K(3,3)` that the six-cycle leaves out. -/

/-- The three remaining edges are not edges of the six-cycle. -/
theorem chord_notMem_hexList (h : IsK33Config G x y e) (s : Fin 3) : e s (s + 1) ∉ hexList e := by
  intro hmem
  obtain ⟨p, hp, heq⟩ := mem_hexList_iff.1 hmem
  have key : ∀ (s : Fin 3) (p : Fin 3 × Fin 3), p ∈ hexPairs → ¬ (s = p.1 ∧ s + 1 = p.2) := by
    decide
  exact key s p hp (h.eq_of_e_eq heq)

/-- Two distinct remaining edges carry distinct names, and share no end. -/
theorem chord_ne (h : IsK33Config G x y e) (hst : s ≠ t) : e s (s + 1) ≠ e t (t + 1) :=
  h.e_ne (fun hc ↦ hst hc.1)

/-- The edges of the six-cycle are edges of the graph. -/
theorem hexList_edge_mem (h : IsK33Config G x y e) {f : β} (hf : f ∈ hexList e) : f ∈ E(G) := by
  obtain ⟨p, -, rfl⟩ := mem_hexList_iff.1 hf
  exact (h.isLink p.1 p.2).edge_mem

end IsK33Config

theorem mem_hexList (e : Fin 3 → Fin 3 → β) {p : Fin 3 × Fin 3} (hp : p ∈ hexPairs) :
    e p.1 p.2 ∈ hexList e :=
  mem_hexList_iff.2 ⟨p, hp, rfl⟩

/-! ### The six-cycle cut at the ends of one remaining edge

The two ends of the remaining edge `e s (s+1)` are `x s` and `y (s+1)`, and they cut the
six-cycle into two paths: `x s → y s → x (s+1) → y (s+1)` and
`x s → y (s+2) → x (s+2) → y (s+1)`. The other two remaining edges each have one end interior
to the first and one end interior to the second — this is the blueprint's "their endpoints
alternate on the six-cycle". -/

/-- Index pairs of the first of the two paths the ends of `e s (s+1)` cut the six-cycle into. -/
def arcAPairs (s : Fin 3) : List (Fin 3 × Fin 3) := [(s, s), (s + 1, s), (s + 1, s + 1)]

/-- Index pairs of the second of the two paths. -/
def arcBPairs (s : Fin 3) : List (Fin 3 × Fin 3) := [(s, s + 2), (s + 2, s + 2), (s + 2, s + 1)]

/-- The edges of the first path. -/
def arcA (e : Fin 3 → Fin 3 → β) (s : Fin 3) : List β := [e s s, e (s + 1) s, e (s + 1) (s + 1)]

/-- The edges of the second path. -/
def arcB (e : Fin 3 → Fin 3 → β) (s : Fin 3) : List β :=
  [e s (s + 2), e (s + 2) (s + 2), e (s + 2) (s + 1)]

theorem arcA_eq_map (e : Fin 3 → Fin 3 → β) (s : Fin 3) :
    arcA e s = (arcAPairs s).map fun p ↦ e p.1 p.2 := rfl

theorem arcB_eq_map (e : Fin 3 → Fin 3 → β) (s : Fin 3) :
    arcB e s = (arcBPairs s).map fun p ↦ e p.1 p.2 := rfl

namespace IsK33Config

/-- The first of the two paths is a path. -/
theorem arcA_isPath (h : IsK33Config G x y e) (s : Fin 3) :
    G.IsPath (x s) (arcA e s) (y (s + 1)) := by
  have hab : s ≠ s + 1 := by revert s; decide
  have p3 : G.IsPath (x (s + 1)) [e (s + 1) (s + 1)] (y (s + 1)) :=
    .single (h.isLink (s + 1) (s + 1)) (h.x_ne_y _ _)
  have p2 : G.IsPath (y s) [e (s + 1) s, e (s + 1) (s + 1)] (y (s + 1)) := by
    refine .cons (h.isLink (s + 1) s).symm p3 (h.notMem_walkVertices (h.y_ne_x _ _) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨s + 1, s + 1, rfl, h.y_ne_x _ _, h.y_ne_y hab⟩
  refine .cons (h.isLink s s) p2 (h.notMem_walkVertices (h.x_ne_y _ _) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨s + 1, s, rfl, h.x_ne_x hab, h.x_ne_y _ _⟩
  · exact ⟨s + 1, s + 1, rfl, h.x_ne_x hab, h.x_ne_y _ _⟩

/-- The second of the two paths is a path. -/
theorem arcB_isPath (h : IsK33Config G x y e) (s : Fin 3) :
    G.IsPath (x s) (arcB e s) (y (s + 1)) := by
  have hac : s ≠ s + 2 := by revert s; decide
  have hcb : s + 2 ≠ s + 1 := by revert s; decide
  have q3 : G.IsPath (x (s + 2)) [e (s + 2) (s + 1)] (y (s + 1)) :=
    .single (h.isLink (s + 2) (s + 1)) (h.x_ne_y _ _)
  have q2 : G.IsPath (y (s + 2)) [e (s + 2) (s + 2), e (s + 2) (s + 1)] (y (s + 1)) := by
    refine .cons (h.isLink (s + 2) (s + 2)).symm q3 (h.notMem_walkVertices (h.y_ne_x _ _) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨s + 2, s + 1, rfl, h.y_ne_x _ _, h.y_ne_y hcb⟩
  refine .cons (h.isLink s (s + 2)) q2 (h.notMem_walkVertices (h.x_ne_y _ _) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨s + 2, s + 2, rfl, h.x_ne_x hac, h.x_ne_y _ _⟩
  · exact ⟨s + 2, s + 1, rfl, h.x_ne_x hac, h.x_ne_y _ _⟩

end IsK33Config

end Graph

/-! ## The six-cycle drawn in the plane

Everything from here on is about a *drawing* of the configuration. Nothing in this section
uses more geometry than the three clauses of `Graph.IsDrawing`. -/

namespace Graph

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s t : Fin 3}

/-- The point set of the six-cycle of a drawn `K(3,3)`. -/
def hexSet (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) : Set Plane :=
  edgesCover drawing (hexList e)

theorem mem_edgesCover_map_iff {L : List (Fin 3 × Fin 3)} {p : Plane} :
    p ∈ edgesCover drawing (L.map fun q ↦ e q.1 q.2) ↔
      ∃ q ∈ L, p ∈ edgeArc drawing (e q.1 q.2) := by
  constructor
  · intro hp
    obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hf
    exact ⟨q, hq, hpf⟩
  · rintro ⟨q, hq, hpq⟩
    exact mem_edgesCover (List.mem_map_of_mem hq) hpq

theorem mem_hexSet_iff {p : Plane} :
    p ∈ hexSet drawing e ↔ ∃ q ∈ hexPairs, p ∈ edgeArc drawing (e q.1 q.2) := by
  rw [hexSet, hexList_eq_map]; exact mem_edgesCover_map_iff

theorem mem_arcA_iff {p : Plane} :
    p ∈ edgesCover drawing (arcA e s) ↔ ∃ q ∈ arcAPairs s, p ∈ edgeArc drawing (e q.1 q.2) := by
  rw [arcA_eq_map]; exact mem_edgesCover_map_iff

theorem mem_arcB_iff {p : Plane} :
    p ∈ edgesCover drawing (arcB e s) ↔ ∃ q ∈ arcBPairs s, p ∈ edgeArc drawing (e q.1 q.2) := by
  rw [arcB_eq_map]; exact mem_edgesCover_map_iff

namespace IsK33Config

/-- **The six-cycle of a drawn `K(3,3)` is a Jordan curve.** This is the blueprint's "the
six-cycle is a polygonal Jordan curve"; polygonality plays no part in it, and is needed only
where the *polygonal* Jordan curve theorem is applied to the result. -/
theorem hexagon_isJordanCurve (h : IsK33Config G x y e) (hd : IsDrawing G drawing) :
    IsJordanCurve (hexSet drawing e) :=
  hd.cycle_isJordanCurve h.hexagon_isCycleThrough

/-- The `i`-th vertex of the first side lies on the six-cycle. -/
theorem x_mem_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (i : Fin 3) :
    x i ∈ hexSet drawing e := by
  have hp : ∀ i : Fin 3, ((i, i) : Fin 3 × Fin 3) ∈ hexPairs := by decide
  exact mem_edgesCover (mem_hexList e (hp i)) (hd.edge_isArcBetween (h.isLink i i)).left_mem

/-- The `j`-th vertex of the second side lies on the six-cycle. -/
theorem y_mem_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (j : Fin 3) :
    y j ∈ hexSet drawing e := by
  have hp : ∀ j : Fin 3, ((j, j) : Fin 3 × Fin 3) ∈ hexPairs := by decide
  exact mem_edgesCover (mem_hexList e (hp j)) (hd.edge_isArcBetween (h.isLink j j)).right_mem

/-- **Each of the three remaining edges is a crosscut of the six-cycle**: its arc meets the
cycle in exactly its own two ends. -/
theorem chord_inter_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgeArc drawing (e s (s + 1)) ∩ hexSet drawing e = {x s, y (s + 1)} := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p ⟨hpe, hph⟩
    obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hph
    have hne : e s (s + 1) ≠ f := fun hc ↦ h.chord_notMem_hexList s (hc ▸ hf)
    obtain ⟨-, hinc, -⟩ :=
      hd.edge_inter (h.isLink s (s + 1)).edge_mem (h.hexList_edge_mem hf) hne hpe hpf
    exact h.inc_elim hinc
  · rintro p (rfl | rfl)
    · exact ⟨(hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem, h.x_mem_hexSet hd s⟩
    · exact ⟨(hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem, h.y_mem_hexSet hd (s + 1)⟩

/-- The interior of a remaining edge, as the blueprint reads it: its arc without its two
ends. -/
theorem chord_openArc_eq (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    openArc (drawing (e s (s + 1))) = edgeArc drawing (e s (s + 1)) \ {x s, y (s + 1)} := by
  obtain ⟨-, hi, hlink⟩ := hd.edge_param (h.isLink s (s + 1)).edge_mem
  have hpair : ({drawing (e s (s + 1)) 0, drawing (e s (s + 1)) 1} : Set Plane)
      = {x s, y (s + 1)} := by
    rcases hlink.eq_and_eq_or_eq_and_eq (h.isLink s (s + 1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
  rw [openArc_eq_diff hi, hpair]
  rfl

/-- **A remaining edge lies wholly off the six-cycle except at its ends.** -/
theorem chord_openArc_subset_compl (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : openArc (drawing (e s (s + 1))) ⊆ (hexSet drawing e)ᶜ := by
  rw [h.chord_openArc_eq hd s]
  rintro p ⟨hpe, hpn⟩ hph
  exact hpn ((h.chord_inter_hexSet hd s).subset ⟨hpe, hph⟩)

theorem chord_openArc_isPreconnected (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : IsPreconnected (openArc (drawing (e s (s + 1)))) :=
  isPreconnected_Ioo.image _
    ((hd.edge_param (h.isLink s (s + 1)).edge_mem).1.mono Ioo_subset_I)

theorem chord_openArc_nonempty (s : Fin 3) :
    (openArc (drawing (e s (s + 1)))).Nonempty :=
  ⟨drawing (e s (s + 1)) (1 / 2), 1 / 2, by norm_num, rfl⟩

/-- **Each of the three remaining edges lies wholly on one side of the six-cycle**: its
interior, being connected and disjoint from the cycle, lies in a single connected component of
the complement. -/
theorem chord_openArc_subset_connectedComponentIn (h : IsK33Config G x y e)
    (hd : IsDrawing G drawing) (s : Fin 3) {p : Plane}
    (hp : p ∈ openArc (drawing (e s (s + 1)))) :
    openArc (drawing (e s (s + 1))) ⊆ connectedComponentIn (hexSet drawing e)ᶜ p :=
  (h.chord_openArc_isPreconnected hd s).subset_connectedComponentIn hp
    (h.chord_openArc_subset_compl hd s)

/-- **Two distinct remaining edges are disjoint.** Their four ends are distinct, and two
distinct edges of a plane graph meet only at a shared end. -/
theorem chords_disjoint (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (hst : s ≠ t) :
    edgeArc drawing (e s (s + 1)) ∩ edgeArc drawing (e t (t + 1)) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hps, hpt⟩ ↦ ?_
  obtain ⟨-, hincs, hinct⟩ := hd.edge_inter (h.isLink s (s + 1)).edge_mem
    (h.isLink t (t + 1)).edge_mem (h.chord_ne hst) hps hpt
  have hne1 : s ≠ t := hst
  have hne2 : s + 1 ≠ t + 1 := fun hc ↦ hst (by simpa using hc)
  rcases h.inc_elim hincs with rfl | rfl <;> rcases h.inc_elim hinct with hh | hh
  · exact (h.x_ne_x hne1) hh
  · exact (h.x_ne_y s (t + 1)) hh
  · exact (h.y_ne_x (s + 1) t) hh
  · exact (h.y_ne_y hne2) hh

/-! ### The two arcs the ends of a remaining edge cut the six-cycle into -/

theorem arcA_isArcBetween (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    IsArcBetween (edgesCover drawing (arcA e s)) (x s) (y (s + 1)) :=
  hd.path_isArcBetween (h.arcA_isPath s) (by simp [arcA])

theorem arcB_isArcBetween (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    IsArcBetween (edgesCover drawing (arcB e s)) (x s) (y (s + 1)) :=
  hd.path_isArcBetween (h.arcB_isPath s) (by simp [arcB])

/-- **The two arcs make up the six-cycle.** -/
theorem arcs_union (s : Fin 3) :
    edgesCover drawing (arcA e s) ∪ edgesCover drawing (arcB e s) = hexSet drawing e := by
  have hA : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, q ∈ hexPairs := by decide
  have hB : ∀ s : Fin 3, ∀ q ∈ arcBPairs s, q ∈ hexPairs := by decide
  have hC : ∀ s : Fin 3, ∀ q ∈ hexPairs, q ∈ arcAPairs s ∨ q ∈ arcBPairs s := by decide
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p (hp | hp)
    · obtain ⟨q, hq, hpq⟩ := mem_arcA_iff.1 hp
      exact mem_hexSet_iff.2 ⟨q, hA s q hq, hpq⟩
    · obtain ⟨q, hq, hpq⟩ := mem_arcB_iff.1 hp
      exact mem_hexSet_iff.2 ⟨q, hB s q hq, hpq⟩
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_hexSet_iff.1 hp
    rcases hC s q hq with hq' | hq'
    exacts [Or.inl (mem_arcA_iff.2 ⟨q, hq', hpq⟩), Or.inr (mem_arcB_iff.2 ⟨q, hq', hpq⟩)]

/-- **The two arcs meet exactly in the two ends of the remaining edge that cuts the cycle.** -/
theorem arcs_inter (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgesCover drawing (arcA e s) ∩ edgesCover drawing (arcB e s) = {x s, y (s + 1)} := by
  have hne : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, ∀ r ∈ arcBPairs s, ¬ (q.1 = r.1 ∧ q.2 = r.2) := by
    decide
  have h1 : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, ∀ r ∈ arcBPairs s, q.1 = r.1 → q.1 = s := by decide
  have h2 : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, ∀ r ∈ arcBPairs s, q.2 = r.2 → q.2 = s + 1 := by
    decide
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p ⟨hpA, hpB⟩
    obtain ⟨q, hq, hpq⟩ := mem_arcA_iff.1 hpA
    obtain ⟨r, hr, hpr⟩ := mem_arcB_iff.1 hpB
    obtain ⟨-, hincq, hincr⟩ := hd.edge_inter (h.isLink q.1 q.2).edge_mem
      (h.isLink r.1 r.2).edge_mem (h.e_ne (hne s q hq r hr)) hpq hpr
    rcases h.inc_elim hincq with hh | hh <;> rcases h.inc_elim hincr with hh' | hh'
    · exact Or.inl (hh.trans (by rw [h1 s q hq r hr (h.x_injective (hh.symm.trans hh'))]))
    · exact absurd (hh.symm.trans hh') (h.x_ne_y _ _)
    · exact absurd (hh.symm.trans hh') (h.y_ne_x _ _)
    · exact Or.inr (hh.trans (by rw [h2 s q hq r hr (h.y_injective (hh.symm.trans hh'))]))
  · rintro p (rfl | rfl)
    · exact ⟨mem_arcA_iff.2 ⟨(s, s), by simp [arcAPairs],
        (hd.edge_isArcBetween (h.isLink s s)).left_mem⟩,
        mem_arcB_iff.2 ⟨(s, s + 2), by simp [arcBPairs],
          (hd.edge_isArcBetween (h.isLink s (s + 2))).left_mem⟩⟩
    · exact ⟨mem_arcA_iff.2 ⟨(s + 1, s + 1), by simp [arcAPairs],
        (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1))).right_mem⟩,
        mem_arcB_iff.2 ⟨(s + 2, s + 1), by simp [arcBPairs],
          (hd.edge_isArcBetween (h.isLink (s + 2) (s + 1))).right_mem⟩⟩

/-- **The endpoints of two of the three remaining edges alternate on the six-cycle.**

The remaining edge indexed by `s` has ends `x s` and `y (s+1)`; they cut the six-cycle into
two arcs `A` and `B` meeting only in those two points. The remaining edge indexed by `s+1`
has ends `x (s+1)` and `y (s+1+1)`, and this says one of them is interior to `A` and the other
interior to `B`. Since the three remaining edges are indexed by `Fin 3`, every *pair* of them
is of this form, which is what the blueprint's "their endpoints alternate on the six-cycle"
asserts. -/
theorem chords_alternate (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ∃ A B : Set Plane,
      IsArcBetween A (x s) (y (s + 1)) ∧ IsArcBetween B (x s) (y (s + 1)) ∧
        A ∪ B = hexSet drawing e ∧ A ∩ B = {x s, y (s + 1)} ∧
        x (s + 1) ∈ A \ ({x s, y (s + 1)} : Set Plane) ∧
        y (s + 1 + 1) ∈ B \ ({x s, y (s + 1)} : Set Plane) := by
  have hsucc : s + 1 + 1 = s + 2 := by revert s; decide
  have hs1 : s + 1 ≠ s := by revert s; decide
  have hs2 : s + 2 ≠ s + 1 := by revert s; decide
  refine ⟨_, _, h.arcA_isArcBetween hd s, h.arcB_isArcBetween hd s, arcs_union s,
    h.arcs_inter hd s, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact mem_arcA_iff.2 ⟨(s + 1, s), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink (s + 1) s)).left_mem⟩
  · rintro (hc | hc)
    exacts [h.x_ne_x hs1 hc, h.x_ne_y _ _ hc]
  · rw [hsucc]
    exact mem_arcB_iff.2 ⟨(s + 2, s + 2), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink (s + 2) (s + 2))).right_mem⟩
  · rw [hsucc]
    rintro (hc | hc)
    exacts [h.y_ne_x _ _ hc, h.y_ne_y hs2 hc]

/-! ### Two of the three remaining edges lie on the same side -/

/-- A remaining edge lies wholly in one of two disjoint open sets covering the complement of
the six-cycle: its interior is connected and misses the cycle. -/
theorem chord_subset_or (h : IsK33Config G x y e) (hd : IsDrawing G drawing) {U V : Set Plane}
    (hUo : IsOpen U) (hVo : IsOpen V) (hUV : Disjoint U V)
    (hcover : (hexSet drawing e)ᶜ ⊆ U ∪ V) (s : Fin 3) :
    openArc (drawing (e s (s + 1))) ⊆ U ∨ openArc (drawing (e s (s + 1))) ⊆ V := by
  have hsub : openArc (drawing (e s (s + 1))) ⊆ U ∪ V :=
    (h.chord_openArc_subset_compl hd s).trans hcover
  obtain ⟨p, hp⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  rcases hsub hp with hpU | hpV
  · exact Or.inl ((h.chord_openArc_isPreconnected hd s).subset_left_of_subset_union
      hUo hVo hUV hsub ⟨p, hp, hpU⟩)
  · refine Or.inr ((h.chord_openArc_isPreconnected hd s).subset_left_of_subset_union
      hVo hUo hUV.symm (hsub.trans (by rw [Set.union_comm])) ⟨p, hp, hpV⟩)

/-- **Two of the three remaining edges lie on the same side of the six-cycle.** The blueprint's
"two of the three lie on the same side": three edges, two sides. The two sides arrive here as
an arbitrary pair of disjoint open sets covering the complement of the cycle, which is the form
the polygonal Jordan curve theorem supplies them in. -/
theorem exists_two_chords_same_side (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    {U V : Set Plane} (hUo : IsOpen U) (hVo : IsOpen V) (hUV : Disjoint U V)
    (hcover : (hexSet drawing e)ᶜ ⊆ U ∪ V) :
    ∃ s t : Fin 3, s ≠ t ∧
      ((openArc (drawing (e s (s + 1))) ⊆ U ∧ openArc (drawing (e t (t + 1))) ⊆ U) ∨
        (openArc (drawing (e s (s + 1))) ⊆ V ∧ openArc (drawing (e t (t + 1))) ⊆ V)) := by
  have key := fun s ↦ h.chord_subset_or hd hUo hVo hUV hcover s
  rcases key 0 with h0 | h0 <;> rcases key 1 with h1 | h1 <;> rcases key 2 with h2 | h2
  exacts [⟨0, 1, by decide, Or.inl ⟨h0, h1⟩⟩, ⟨0, 1, by decide, Or.inl ⟨h0, h1⟩⟩,
    ⟨0, 2, by decide, Or.inl ⟨h0, h2⟩⟩, ⟨1, 2, by decide, Or.inr ⟨h1, h2⟩⟩,
    ⟨1, 2, by decide, Or.inl ⟨h1, h2⟩⟩, ⟨0, 2, by decide, Or.inr ⟨h0, h2⟩⟩,
    ⟨0, 1, by decide, Or.inr ⟨h0, h1⟩⟩, ⟨0, 1, by decide, Or.inr ⟨h0, h1⟩⟩]

end IsK33Config

end Graph
