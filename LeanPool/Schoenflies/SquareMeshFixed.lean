/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.SquareMeshConnected
public import LeanPool.Schoenflies.Graph.Ear

/-!
# The anchored square mesh: the three gaps an audit found

`Schoenflies/SquareMesh.lean` and `Schoenflies/SquareMeshConnected.lean` deliver
`prop:anchored-square-mesh` between them. An adversarial audit of the second found three real
gaps; this module closes what can be closed and states, as explicit hypotheses, what cannot.

## Gap 3 — the dropped subdivision step

The blueprint proves the inner grid 2-connected "by the same ear construction used for `K`,
together with `lem:subdivision-ear-preserve`". `SquareMeshConnected.gridGraph_isTwoConnected`
supplies the ear half (as a chain of `Graph.IsTwoConnected.union`s) and **drops the
subdivision half entirely** — yet the mesh subdivides the grid, at the four corners of the
inner square, at every point `λ zᵢ`, and at every crossing the overlay finds. A grid that is
2-connected before subdivision and unproved after it is of no use to the proposition.

`pieceListGraph_subdivide_isTwoConnected` is the missing half, in the vocabulary of
`Schoenflies/Subdivide.lean`: subdividing a list of segments whose graph is 2-connected, at
any list of points that cut it *cleanly* (`CleanCut`: each point interior to at most one
segment, and interior to none once it is an end of one), leaves the graph 2-connected. It is
`Graph.IsTwoConnected.replace_edge_by_path` — `lem:subdivision-ear-preserve` (a) — iterated,
with the two-edge replacement path built by `isPathGraph_pair`.

For a grid the cleanliness hypothesis is **free**: two distinct grid edges meet only at a grid
point, and a grid point interior to a grid edge does not exist. So
`gridGraph_subdivide_isTwoConnected` has no hypothesis on the points at all.

## Gap 2 — the outer cycle was instantiated at the wrong square

`SquareMeshConnected.edgesCover_gridBoundary_modelCurve` pins the grid to `xc 0 = -1`,
`xc m = 1`, `yc 0 = -1`, `yc n = 1`: a grid spanning **all** of `Q`, whose boundary cycle is
`S`. The audit says such a grid cannot be the mesh, and it is right. The obstruction is
`gridGraph_full_square_aligned_ends` below: for `0 < i < m` the two grid points `(xc i, -1)`
and `(xc i, 1)` both lie on `S` and both carry an internal edge — the vertical edges at the
bottom and top of the column `i` — neither of which lies on `S`. Clause 3 of the proposition
then demands that *both* be fresh points of `u(𝒜)`, and clause 2 demands a grid line through
every old boundary vertex, which manufactures such a pair on the opposite side. Nothing about
`u(𝒜)` supplies pairs of points with a common coordinate: it is merely dense. The theorem is
true; the *instantiation* is wrong.

The blueprint's grid fills the **inner** square `λQ`, `λ < 1`, which touches `S` nowhere;
`edgesCover_gridBoundary_ringSet` is the corrected statement — the boundary cycle of a grid on
`[-r, r]²` occupies `ringSet r` — and `gridGraph_inner_cycle` packages it with the
disjointness from `S` that makes the freshness clauses vacuous for the grid.

## Gap 1 — nothing was proved about `squareMesh` itself

`squareMesh δ fresh anchors` is `overlayGraph` applied to the mesh segments and to a list of
cut points obtained from `exists_cut_points` **by choice**. Its edges are the pieces of a
subdivision nobody can enumerate, so no clause about *its* combinatorics follows from the grid
results, which are about a different graph.

One general fact about `overlayGraph` is missing, and it is stated here as the explicit
hypothesis `SubdividesToPath`: *the overlay edges lying inside a source segment are exactly the
edges of a path of the overlay from one end of that segment to the other.* That is a statement
about `Schoenflies.overlayGraph` and `Schoenflies.subdivide` alone — believed, and
dischargeable, since the pieces of the subdivision of a segment have pairwise disjoint interiors
and cover it, so the distance from one end orders them into a chain. It is not a restatement of
any goal here: the whole content below is the *assembly*, which the hypothesis does not contain.

From it:

* `meshGraph_outer_cycle` / `squareMesh_outer_cycle_of_subdividesToPath` — clause 3 **as a
  cycle**, for the mesh
  itself. The four sides of the outer ring are four overlay paths; three concatenations
  (`Graph.IsPath.append_of_disjoint`) glue them into one path once round `S`, and the first step
  of the *reversed* fourth side is peeled off to close the cycle. The result is a
  `Graph.IsLongCycle` of the mesh whose edges occupy exactly `modelCurve`.
* `squareMesh_outer_cycleGraph_isTwoConnected_of_subdividesToPath` — hence the outer ring is a
  2-connected subgraph
  of the mesh, which is the first step of the blueprint's assembly of clause 5.

**Full 2-connectivity of `squareMesh` is NOT proved here, and is not assumed either.** What
remains is the rest of that assembly: the inner rings as cycles (the same argument, with
`ringPieces r` in place of `ringPieces 1`), the crossing points `r • z` as vertices (which needs
the `MeetsAreCut` clause of `meshPoints`), and then each spoke segment between consecutive rings
attached as an ear — for which one also needs the two arcs of an already-built cycle between two
of its vertices. None of that is short.

The degeneracy the audit asked about is settled, with a proof rather than an assertion:
`not_isTwoConnected_squareMesh_of_fresh_nil`. With no fresh point the mesh is
`meshCount δ ≥ 2` disjoint concentric frames and is not even connected, so clause 5 is **false**
as stated for `squareMesh δ [] anchors`. With exactly one fresh point it is connected but every
interior vertex of the single spoke is a cut vertex; that case is discussed in the section
docstring and not formalised. Every statement of clause 5 for the mesh must therefore carry a
hypothesis giving two distinct fresh points.

## Blueprint

* `lem:subdivision-ear-preserve` — `isPathGraph_pair`, `pieceListGraph_splitAllAt_eq`,
  `pieceListGraph_splitAllAt_isTwoConnected`, `pieceListGraph_subdivide_isTwoConnected`.
* `prop:anchored-square-mesh`, clause 5 for the inner grid, **after** subdivision —
  `gridGraph_subdivide_isTwoConnected`.
* `prop:anchored-square-mesh`, clause 3 for the inner grid at the right radius —
  `edgesCover_gridBoundary_ringSet`, `gridGraph_inner_cycle`.
* `prop:anchored-square-mesh`, clauses 3 and 4, the obstruction to a grid on all of `Q` —
  `gridGraph_full_square_aligned_ends`.
* `prop:anchored-square-mesh`, clause 3 as a cycle, for the mesh — `SubdividesToPath`,
  `meshGraph_outer_cycle`, `squareMesh_outer_cycle_of_subdividesToPath`.
* `prop:anchored-square-mesh`, clause 5, the first step for the mesh and the degenerate case —
  `squareMesh_outer_cycleGraph_isTwoConnected_of_subdividesToPath`,
  `not_isTwoConnected_squareMesh_of_fresh_nil`.
* `lem:union-two-connected` is *not* used here; the assembly that would use it is the part left
  open.
-/

public section

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### A two-edge path graph

The replacement path of a single subdivision: one new vertex `q` between the two ends of the
segment being cut. `Graph.IsTwoConnected.replace_edge_by_path` takes a path of any length, so
this is the only shape needed. -/

theorem pieceListGraph_inc_iff {l : List Piece} {P : Piece} {v : Plane} :
    (pieceListGraph l).Inc P v ↔ P ∈ l ∧ (v = P.1 ∨ v = P.2) := by
  constructor
  · rintro ⟨y, hP, h⟩
    exact ⟨hP, by tauto⟩
  · rintro ⟨hP, h⟩
    exact pieceListGraph_inc hP h

theorem endSet_pair (a q b : Plane) : endSet [((a, q) : Piece), (q, b)] = {a, q, b} := by
  ext x
  simp only [endSet, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro ⟨P, hP, hx⟩
    rcases hP with rfl | rfl <;> simp only [] at hx <;> tauto
  · intro hx
    rcases hx with hx | hx | hx
    exacts [⟨(a, q), Or.inl rfl, Or.inl hx⟩, ⟨(a, q), Or.inl rfl, Or.inr hx⟩,
      ⟨(q, b), Or.inr rfl, Or.inr hx⟩]

theorem coveredVertices_pair (a q b : Plane) :
    (pieceListGraph [((a, q) : Piece), (q, b)]).coveredVertices [((a, q) : Piece), (q, b)]
      = {a, q, b} := by
  ext x
  simp only [Graph.mem_coveredVertices_iff, List.mem_cons, List.not_mem_nil, or_false,
    mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨e, he, hinc⟩
    obtain ⟨-, hx⟩ := pieceListGraph_inc_iff.1 hinc
    rcases he with rfl | rfl <;> simp only [] at hx <;> tauto
  · intro hx
    have h₁ : ((a, q) : Piece) ∈ [((a, q) : Piece), (q, b)] := by simp
    have h₂ : ((q, b) : Piece) ∈ [((a, q) : Piece), (q, b)] := by simp
    rcases hx with hx | hx | hx
    exacts [⟨(a, q), Or.inl rfl, pieceListGraph_inc h₁ (Or.inl hx)⟩,
      ⟨(a, q), Or.inl rfl, pieceListGraph_inc h₁ (Or.inr hx)⟩,
      ⟨(q, b), Or.inr rfl, pieceListGraph_inc h₂ (Or.inr hx)⟩]

/-- **The two halves of a cut segment form a path graph.** -/
theorem isPathGraph_pair {a q b : Plane} (haq : a ≠ q) (hqb : q ≠ b) (hab : a ≠ b) :
    (pieceListGraph [(a, q), (q, b)]).IsPathGraph a [(a, q), (q, b)] b := by
  have h₁ : ((a, q) : Piece) ∈ [((a, q) : Piece), (q, b)] := by simp
  have h₂ : ((q, b) : Piece) ∈ [((a, q) : Piece), (q, b)] := by simp
  have hlink₁ := pieceListGraph_isLink_self h₁
  have hlink₂ := pieceListGraph_isLink_self h₂
  -- the vertices the second step visits are exactly `q` and `b`
  have hcov : (pieceListGraph [((a, q) : Piece), (q, b)]).coveredVertices [((q, b) : Piece)]
      = {q, b} := by
    ext x
    simp only [Graph.mem_coveredVertices_iff, List.mem_singleton, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨e, rfl, hinc⟩
      obtain ⟨-, hx⟩ := pieceListGraph_inc_iff.1 hinc
      simpa only [] using hx
    · intro hx
      rcases hx with hx | hx
      exacts [⟨(q, b), rfl, pieceListGraph_inc h₂ (Or.inl hx)⟩,
        ⟨(q, b), rfl, pieceListGraph_inc h₂ (Or.inr hx)⟩]
  have hpath : (pieceListGraph [((a, q) : Piece), (q, b)]).IsPath a [(a, q), (q, b)] b := by
    refine Graph.IsPath.cons hlink₁ (Graph.IsPath.single hlink₂ hqb) ?_
    rw [Graph.walkVertices, hcov]
    simp only [mem_insert_iff, mem_singleton_iff]
    push Not
    exact ⟨haq, haq, hab⟩
  refine ⟨hpath, rfl, ?_⟩
  rw [pieceListGraph_vertexSet, endSet_pair, Graph.walkVertices, coveredVertices_pair]
  simp

/-! ### Cutting a list of segments cleanly

`splitAllAt q l` cuts **every** piece of `l` that has `q` in its interior. To read the result
as one subdivision of one edge — which is what `lem:subdivision-ear-preserve` is about — the
point must be interior to at most one piece; and to keep the replacement path's middle vertex
new, the point must not already be an end. A point that is interior to no piece cuts nothing
at all, and is harmless. -/

/-- `q` cuts the list `l` cleanly: it is interior to at most one piece, and either it is
interior to none or it is an end of none.

Both branches of the disjunction occur in the intended use: a point of the cut list that has
already been cut out is interior to nothing, and a point not yet used is an end of nothing. -/
def CleanCut (l : List Piece) (q : Plane) : Prop :=
  (∀ R ∈ l, ∀ S ∈ l, q ∈ R.interior → q ∈ S.interior → R = S) ∧
    ((∀ R ∈ l, q ∉ R.interior) ∨ q ∉ endSet l)

theorem CleanCut.of_no_interior {l : List Piece} {q : Plane} (h : ∀ R ∈ l, q ∉ R.interior) :
    CleanCut l q :=
  ⟨fun R hR _ _ hq _ => absurd hq (h R hR), Or.inl h⟩

/-- **The two halves of a cut segment have disjoint interiors.** The distance from the left
end is a faithful coordinate along the segment (`Schoenflies/SegmentOrder.lean`), and it is
`< dist a p` on one half and `> dist a p` on the other. -/
theorem openSegment_halves_disjoint {a b p x : Plane} (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) (h₁ : x ∈ openSegment ℝ a p) (h₂ : x ∈ openSegment ℝ p b) :
    False := by
  have hpseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ _ _ hp
  have hap : a ≠ p := by
    rintro rfl
    exact hab (left_mem_openSegment_iff.1 hp)
  have hpb : p ≠ b := by
    rintro rfl
    exact hab (right_mem_openSegment_iff.1 hp)
  have hle : dist a p ≤ dist a b :=
    (dist_le_of_mem_segment hab (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
      (by simp) hpseg).2
  have hlt₁ := dist_lt_of_mem_openSegment hab (left_mem_segment ℝ a b) hpseg hap (by simp) h₁
  have hlt₂ :=
    dist_lt_of_mem_openSegment hab hpseg (right_mem_segment ℝ a b) hpb hle h₂
  linarith [hlt₁.2, hlt₂.1]

/-- Splitting at a point that is interior to nothing changes the list not at all. -/
theorem splitAllAt_eq_self {l : List Piece} {q : Plane} (h : ∀ R ∈ l, q ∉ R.interior) :
    splitAllAt q l = l := by
  induction l with
  | nil => rfl
  | cons R l ih =>
    rw [splitAllAt, List.flatMap_cons, splitAt, ite_eq_right (h R (List.mem_cons_self ..))]
    rw [show l.flatMap (splitAt q) = splitAllAt q l from rfl,
      ih fun S hS => h S (List.mem_cons_of_mem _ hS)]
    rfl

/-- The members of a split list: everything but the cut piece, and the cut piece's two
halves. -/
theorem mem_splitAllAt_iff {l : List Piece} {P R : Piece} {q : Plane} (hP : P ∈ l)
    (hq : q ∈ P.interior) (huniq : ∀ S ∈ l, q ∈ S.interior → S = P) :
    R ∈ splitAllAt q l ↔ (R ∈ l ∧ R ≠ P) ∨ R ∈ [((P.1, q) : Piece), (q, P.2)] := by
  classical
  constructor
  · intro hR
    obtain ⟨S, hS, hRS⟩ := List.mem_flatMap.1 hR
    by_cases hqS : q ∈ S.interior
    · obtain rfl := huniq S hS hqS
      rw [splitAt, ite_eq_left hqS] at hRS
      exact Or.inr hRS
    · rw [splitAt, ite_eq_right hqS] at hRS
      obtain rfl : R = S := List.mem_singleton.1 hRS
      exact Or.inl ⟨hS, fun h => hqS (h ▸ hq)⟩
  · rintro (⟨hR, hRP⟩ | hR)
    · have hqR : q ∉ R.interior := fun h => hRP (huniq R hR h)
      exact List.mem_flatMap.2 ⟨R, hR, by rw [splitAt, ite_eq_right hqR]; simp⟩
    · exact List.mem_flatMap.2 ⟨P, hP, by rw [splitAt, ite_eq_left hq]; exact hR⟩

/-- The ends of a split list: the old ends and the cut point. -/
theorem endSet_splitAllAt {l : List Piece} {P : Piece} {q : Plane} (hP : P ∈ l)
    (hq : q ∈ P.interior) (huniq : ∀ S ∈ l, q ∈ S.interior → S = P) :
    endSet (splitAllAt q l) = endSet l ∪ {q} := by
  ext v
  simp only [endSet, Set.mem_ofPred_eq, mem_union, mem_singleton_iff]
  constructor
  · rintro ⟨R, hR, hv⟩
    rcases (mem_splitAllAt_iff hP hq huniq).1 hR with ⟨hRl, -⟩ | hR2
    · exact Or.inl ⟨R, hRl, hv⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR2
      rcases hR2 with rfl | rfl <;> rcases hv with rfl | rfl
      exacts [Or.inl ⟨P, hP, Or.inl rfl⟩, Or.inr rfl, Or.inr rfl, Or.inl ⟨P, hP, Or.inr rfl⟩]
  · have hleft : ((P.1, q) : Piece) ∈ splitAllAt q l :=
      (mem_splitAllAt_iff hP hq huniq).2 (Or.inr (by simp))
    have hright : ((q, P.2) : Piece) ∈ splitAllAt q l :=
      (mem_splitAllAt_iff hP hq huniq).2 (Or.inr (by simp))
    rintro (⟨R, hR, hv⟩ | hvq)
    · by_cases hRP : R = P
      · subst hRP
        rcases hv with rfl | rfl
        exacts [⟨(R.1, q), hleft, Or.inl rfl⟩, ⟨(q, R.2), hright, Or.inr rfl⟩]
      · exact ⟨R, (mem_splitAllAt_iff hP hq huniq).2 (Or.inl ⟨hR, hRP⟩), hv⟩
    · exact ⟨(P.1, q), hleft, Or.inr hvq⟩

/-- **One cut, as a replacement of one edge by a two-edge path.** -/
theorem pieceListGraph_splitAllAt_eq {l : List Piece} {P : Piece} {q : Plane} (hP : P ∈ l)
    (hq : q ∈ P.interior) (huniq : ∀ S ∈ l, q ∈ S.interior → S = P) :
    pieceListGraph (splitAllAt q l)
      = ((pieceListGraph l).deleteEdges {P}).union (pieceListGraph [(P.1, q), (q, P.2)]) := by
  have hVsplit : endSet (splitAllAt q l) = endSet l ∪ {q} := endSet_splitAllAt hP hq huniq
  have hqmem : q ∈ endSet (splitAllAt q l) := by rw [hVsplit]; exact Or.inr rfl
  refine (Graph.eq_of_le_of_subset_subset (Graph.union_le ?_ ?_) ?_ ?_).symm
  · -- the untouched edges
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [Graph.vertexSet_deleteEdges, pieceListGraph_vertexSet] at hv
      rw [pieceListGraph_vertexSet, hVsplit]
      exact mem_union_left _ hv
    · intro R x y hlink
      obtain ⟨⟨hRl, hends⟩, hRP⟩ :
          ((R ∈ l ∧ ((x = R.1 ∧ y = R.2) ∨ (x = R.2 ∧ y = R.1))) ∧ R ∉ ({P} : Set Piece)) := hlink
      exact ⟨(mem_splitAllAt_iff hP hq huniq).2
        (Or.inl ⟨hRl, by simpa using hRP⟩), hends⟩
  · exact pieceListGraph_mono fun R hR => (mem_splitAllAt_iff hP hq huniq).2 (Or.inr hR)
  · intro v hv
    rw [pieceListGraph_vertexSet, hVsplit] at hv
    rw [Graph.vertexSet_union, Graph.vertexSet_deleteEdges, pieceListGraph_vertexSet,
      pieceListGraph_vertexSet]
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr ⟨(P.1, q), by simp, Or.inr hv⟩
  · intro R hR
    rw [pieceListGraph_mem_edgeSet] at hR
    rcases (mem_splitAllAt_iff hP hq huniq).1 hR with ⟨hRl, hRP⟩ | hR2
    · exact Or.inl (Graph.mem_edgeSet_deleteEdges_iff.2 ⟨hRl, by simpa using hRP⟩)
    · exact Or.inr hR2

/-- **`lem:subdivision-ear-preserve`, one cut.** Cutting one segment of a 2-connected list of
segments at an interior point that is interior to no other segment and is an end of none
leaves the graph 2-connected. -/
theorem pieceListGraph_splitAllAt_isTwoConnected {l : List Piece} {P : Piece} {q : Plane}
    (hP : P ∈ l) (hnd : P.Nondeg) (hq : q ∈ P.interior)
    (huniq : ∀ S ∈ l, q ∈ S.interior → S = P) (hnew : q ∉ endSet l)
    (h2 : (pieceListGraph l).IsTwoConnected) :
    (pieceListGraph (splitAllAt q l)).IsTwoConnected := by
  have h1q : P.1 ≠ q := by
    intro h
    rw [← h] at hq
    exact hnd (left_mem_openSegment_iff.1 hq)
  have hq2 : q ≠ P.2 := by
    intro h
    rw [h] at hq
    exact hnd (right_mem_openSegment_iff.1 hq)
  rw [pieceListGraph_splitAllAt_eq hP hq huniq]
  refine h2.replace_edge_by_path (pieceListGraph_isLink_self hP) hnd ?_
    (isPathGraph_pair h1q hq2 hnd) ?_
  · -- no edge is shared: a half of `P` has `q` as an end, and `q` is an end of nothing in `l`
    intro R hR hR' x y
    exfalso
    simp only [pieceListGraph_mem_edgeSet, List.mem_cons, List.not_mem_nil, or_false] at hR'
    rw [Graph.mem_edgeSet_deleteEdges_iff, pieceListGraph_mem_edgeSet] at hR
    rcases hR' with rfl | rfl
    exacts [hnew ⟨_, hR.1, Or.inr rfl⟩, hnew ⟨_, hR.1, Or.inl rfl⟩]
  · rintro x ⟨R, hR, hx⟩ hx1 hx2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl <;> rcases hx with rfl | rfl
    exacts [absurd rfl hx1, hnew, hnew, absurd rfl hx2]

/-- Cleanliness survives a cut: interiors only shrink, and the only new end is the cut
point — which, after its own cut, is interior to nothing. -/
theorem CleanCut.splitAllAt {l : List Piece} {q q' : Plane} (hnd : ∀ R ∈ l, R.Nondeg)
    (hq : CleanCut l q) (hq' : CleanCut l q') : CleanCut (splitAllAt q' l) q := by
  classical
  by_cases hsame : q = q'
  · subst hsame
    exact CleanCut.of_no_interior (Schoenflies.splitAllAt_avoids q hnd)
  refine ⟨?_, ?_⟩
  · -- two pieces of the split list with `q` inside come from one piece of `l` …
    intro R hR S hS hqR hqS
    obtain ⟨R₀, hR₀, hRR₀⟩ := List.mem_flatMap.1 hR
    obtain ⟨S₀, hS₀, hSS₀⟩ := List.mem_flatMap.1 hS
    obtain rfl : R₀ = S₀ :=
      hq.1 R₀ hR₀ S₀ hS₀ (splitAt_interior_subset q' R₀ R hRR₀ hqR)
        (splitAt_interior_subset q' S₀ S hSS₀ hqS)
    -- … and the two halves of one piece have disjoint interiors
    by_cases hq'R : q' ∈ R₀.interior
    · rw [splitAt, ite_eq_left hq'R] at hRR₀ hSS₀
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRR₀ hSS₀
      have hnd₀ : R₀.Nondeg := hnd R₀ hR₀
      rcases hRR₀ with rfl | rfl <;> rcases hSS₀ with rfl | rfl
      · rfl
      · exact absurd (openSegment_halves_disjoint hnd₀ hq'R hqR hqS) not_false
      · exact absurd (openSegment_halves_disjoint hnd₀ hq'R hqS hqR) not_false
      · rfl
    · rw [splitAt, ite_eq_right hq'R] at hRR₀ hSS₀
      rw [List.mem_singleton.1 hRR₀, List.mem_singleton.1 hSS₀]
  · rcases hq.2 with hnone | hend
    · exact Or.inl fun R hR => by
        obtain ⟨R₀, hR₀, hRR₀⟩ := List.mem_flatMap.1 hR
        exact fun hmem => hnone R₀ hR₀ (splitAt_interior_subset q' R₀ R hRR₀ hmem)
    · refine Or.inr fun hmem => ?_
      obtain ⟨R, hR, hv⟩ := hmem
      obtain ⟨R₀, hR₀, hRR₀⟩ := List.mem_flatMap.1 hR
      rcases splitAt_ends q' R₀ R hRR₀ q hv with h | h
      exacts [hsame h, hend ⟨R₀, hR₀, h⟩]

/-- **`lem:subdivision-ear-preserve`, the whole subdivision.** A list of segments whose graph
is 2-connected, subdivided at any list of points that cut it cleanly, still has a 2-connected
graph.

This is the half of the blueprint's inner-grid argument that `Schoenflies/SquareMeshConnected.lean`
dropped. -/
theorem pieceListGraph_subdivide_isTwoConnected : ∀ (points : List Plane) (l : List Piece),
    (∀ P ∈ l, P.Nondeg) → (∀ q ∈ points, CleanCut l q) →
      (pieceListGraph l).IsTwoConnected →
      (pieceListGraph (subdivide l points)).IsTwoConnected := by
  classical
  intro points
  induction points with
  | nil => exact fun l _ _ h2 => h2
  | cons q qs ih =>
    intro l hnd hclean h2
    rw [subdivide_cons]
    refine ih (splitAllAt q l) (splitAllAt_ne q hnd) ?_ ?_
    · exact fun q' hq' => (hclean q' (List.mem_cons_of_mem _ hq')).splitAllAt hnd
        (hclean q (List.mem_cons_self ..))
    · obtain ⟨huniq, hor⟩ := hclean q (List.mem_cons_self ..)
      rcases hor with hnone | hend
      · rw [splitAllAt_eq_self hnone]; exact h2
      · by_cases hex : ∃ P ∈ l, q ∈ P.interior
        · obtain ⟨P, hP, hqP⟩ := hex
          exact pieceListGraph_splitAllAt_isTwoConnected hP (hnd P hP) hqP
            (fun S hS hqS => huniq S hS P hP hqS hqP) hend h2
        · push Not at hex
          rw [splitAllAt_eq_self hex]; exact h2

/-! ### The inner grid, subdivided

For a grid the cleanliness hypothesis costs nothing. Two distinct grid edges meet only at a
grid point (`gridPt_of_mem_two_edges`), a grid point on a grid edge is an end of it
(`end_of_gridPt_mem_seg`), and an end of a nondegenerate segment is not interior to it. So
*every* point cuts the grid cleanly, and the subdivision theorem applies with no hypothesis on
the cut points at all. -/

/-- An end of a nondegenerate segment is not interior to it. -/
theorem notMem_interior_of_end {R : Piece} (hnd : R.Nondeg) {q : Plane} (h : q = R.1 ∨ q = R.2) :
    q ∉ R.interior := by
  rcases h with rfl | rfl
  · exact fun hmem => hnd (left_mem_openSegment_iff.1 hmem)
  · exact fun hmem => hnd (right_mem_openSegment_iff.1 hmem)

variable {xc yc : ℕ → ℝ} {m n : ℕ}

/-- **Every point cuts the grid cleanly.** -/
theorem cleanCut_gridEdges (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) (q : Plane) :
    CleanCut (gridEdges xc yc m n) q := by
  have hnd : ∀ P ∈ gridEdges xc yc m n, P.Nondeg :=
    fun P hP => gridEdges_nondeg hxs hys hm hn hP
  -- a point interior to a grid edge is not a grid point
  have hgrid : ∀ R ∈ gridEdges xc yc m n, q ∈ R.interior →
      ∀ a ≤ m, ∀ b ≤ n, q ≠ gridPt xc yc a b := by
    intro R hR hqR a ha b hb hab
    refine notMem_interior_of_end (hnd R hR) ?_ hqR
    rw [hab]
    exact end_of_gridPt_mem_seg hxs hys hm hn hR ha hb
      (hab ▸ openSegment_subset_segment ℝ _ _ hqR)
  refine ⟨fun R hR S hS hqR hqS => ?_, ?_⟩
  · by_contra hRS
    obtain ⟨a, ha, b, hb, hq⟩ := gridPt_of_mem_two_edges hxs hys hm hn hR hS hRS
      (openSegment_subset_segment ℝ _ _ hqR) (openSegment_subset_segment ℝ _ _ hqS)
    exact hgrid R hR hqR a ha b hb hq
  · by_cases hq : q ∈ endSet (gridEdges xc yc m n)
    · refine Or.inl fun R hR hqR => ?_
      obtain ⟨a, ha, b, hb, hab⟩ := (mem_vertexSet_gridGraph_iff hm hn).1 hq
      exact hgrid R hR hqR a ha b hb hab
    · exact Or.inr hq

/-- **`prop:anchored-square-mesh`, clause 5 for the inner grid, after subdivision.** This is
the half of the blueprint's argument — `lem:subdivision-ear-preserve` — that
`Schoenflies/SquareMeshConnected.lean` dropped. It needs nothing of the cut points: the grid is
in general position with itself, so any list of points cuts it cleanly. -/
theorem gridGraph_subdivide_isTwoConnected (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) (points : List Plane) :
    (pieceListGraph (subdivide (gridEdges xc yc m n) points)).IsTwoConnected := by
  refine pieceListGraph_subdivide_isTwoConnected points _
    (fun P hP => gridEdges_nondeg hxs hys hm hn hP)
    (fun q _ => cleanCut_gridEdges hxs hys hm hn q) ?_
  exact gridGraph_isTwoConnected hm hn
    (fun i hi => ne_of_lt (hxs (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)))
    (fun j hj => ne_of_lt (hys (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)))

/-! ### The outer cycle of the inner grid, at the right radius

`SquareMeshConnected.edgesCover_gridBoundary_modelCurve` is the `r = 1` case of the theorem
below, and `r = 1` is exactly the case the mesh cannot use. See the module docstring, and
`gridGraph_full_square_aligned_ends` for the obstruction made explicit. -/

/-- **What the grid's outer cycle occupies, at any radius.** For a grid on `[-r, r]²` the
boundary cycle occupies the frame `ringSet r`. The blueprint's inner grid is the case
`r = λ < 1`, and then the cycle misses `S` entirely. -/
theorem edgesCover_gridBoundary_ringSet {r : ℝ} (hr : 0 ≤ r) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hxmono : ∀ i, i < m → xc i ≤ xc (i + 1)) (hymono : ∀ j, j < n → yc j ≤ yc (j + 1))
    (hx0 : xc 0 = -r) (hxm : xc m = r) (hy0 : yc 0 = -r) (hyn : yc n = r) :
    Graph.edgesCover segmentDrawing
        (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n) = ringSet r := by
  rw [edgesCover_gridBoundary hm hn hxmono hymono, ← cover_ringPieces hr]
  simp only [ringPieces, cover_cons, cover_nil, Set.union_empty, Piece.seg, gridPt, hx0, hxm,
    hy0, hyn]
  rw [segment_symm ℝ (Plane.mk r r) (Plane.mk (-r) r),
    segment_symm ℝ (Plane.mk (-r) r) (Plane.mk (-r) (-r))]
  ext z
  simp only [Set.mem_union]
  tauto

/-- **The distinguished cycle of the blueprint's inner grid.** The grid fills `λQ` for some
`0 ≤ λ < 1`; its boundary is a cycle of the grid graph, occupies the frame of `λQ`, and misses
`S`. The last clause is why the inner grid is exempt from the mesh's freshness clauses 3 and 4:
no edge of it reaches `S` at all. -/
theorem gridGraph_inner_cycle {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≠ 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hxs : StrictMonoOn xc (Set.Iic m)) (hys : StrictMonoOn yc (Set.Iic n))
    (hx0 : xc 0 = -r) (hxm : xc m = r) (hy0 : yc 0 = -r) (hyn : yc n = r) :
    (gridGraph xc yc m n).IsCycleThrough (gridBoundaryLast xc yc m n)
        (gridBoundaryPt xc yc m n 0) (gridBoundaryPt xc yc m n (2 * m + 2 * n - 1))
        (gridBoundaryDetour xc yc m n) ∧
      Graph.edgesCover segmentDrawing
          (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n) = ringSet r ∧
      Graph.edgesCover segmentDrawing
          (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n) ∩ modelCurve = ∅ := by
  have hcov := edgesCover_gridBoundary_ringSet (xc := xc) (yc := yc) hr hm hn
    (fun i hi => (coord_le_of_idx_le hxs (by omega) (by omega) (by omega)))
    (fun j hj => (coord_le_of_idx_le hys (by omega) (by omega) (by omega))) hx0 hxm hy0 hyn
  exact ⟨gridGraph_isCycleThrough_boundary hm hn hxs.injOn hys.injOn, hcov,
    by rw [hcov]; exact ringSet_disjoint_modelCurve hr1⟩

/-! ### Why the grid may not span all of `Q`

The audit's second finding, made explicit. -/

theorem mem_modelCurve_of_supNorm {z : Plane} (h : Plane.supNorm z = 1) : z ∈ modelCurve := h

theorem supNorm_mk (a b : ℝ) : Plane.supNorm (Plane.mk a b) = max |a| |b| := rfl

/-- A vertical grid edge inside the open strip `|x| < 1` and inside `|y| ≤ 1` does not lie on
`S`: its midpoint has sup norm `< 1`. -/
theorem gridVEdge_not_subset_modelCurve {i j : ℕ} (hxi : |xc i| < 1) (h1 : -1 ≤ yc j)
    (h2 : yc (j + 1) ≤ 1) (hlt : yc j < yc (j + 1)) :
    ¬ (gridVEdge xc yc i j).seg ⊆ modelCurve := by
  intro hsub
  set t : ℝ := (yc j + yc (j + 1)) / 2 with ht
  have hmem : Plane.mk (xc i) t ∈ (gridVEdge xc yc i j).seg := by
    refine mem_gridVEdge_seg_iff.2 ⟨Plane.mk_zero _ _, ?_⟩
    rw [Plane.mk_one, segment_eq_Icc hlt.le]
    constructor <;> (rw [ht]; linarith)
  have hone : Plane.supNorm (Plane.mk (xc i) t) = 1 := hsub hmem
  rw [supNorm_mk] at hone
  have habs : |t| < 1 := by
    rw [abs_lt]
    constructor <;> (rw [ht]; linarith)
  rcases max_cases |xc i| |t| with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hone <;> linarith

/-- **The obstruction to a grid spanning all of `Q`.** For a strictly increasing grid on
`[-1,1]²` and any interior column `0 < i < m`, the two grid points `(xc i, -1)` and
`(xc i, 1)` both lie on `S`, they share their first coordinate, and each is an end of a grid
edge that does *not* lie on `S`.

Clause 3 of `prop:anchored-square-mesh` says every internal edge meeting `S` ends at a fresh
point of `u(𝒜)`. Applied to such a grid it therefore demands that `u(𝒜)` contain **both**
points of a vertically aligned pair, for every interior column — and, by the same argument on
rows, for every interior row. Density of `u(𝒜)` in `S` supplies no aligned pair, and clause 2
makes the demand unavoidable: an old boundary vertex on the bottom side forces a coordinate
`xc i`, and that coordinate forces the point `(xc i, 1)` opposite it.

The blueprint's grid therefore fills the *inner* square `λQ` with `λ < 1`, where the clauses
are vacuous by `gridGraph_inner_cycle`; the collar between `λQ` and `S`, not the grid, carries
the fresh points and their single spokes. -/
theorem gridGraph_full_square_aligned_ends (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hxs : StrictMonoOn xc (Set.Iic m)) (hys : StrictMonoOn yc (Set.Iic n))
    (hx0 : xc 0 = -1) (hxm : xc m = 1) (hy0 : yc 0 = -1) (hyn : yc n = 1)
    {i : ℕ} (hi0 : 0 < i) (him : i < m) :
    gridPt xc yc i 0 ∈ modelCurve ∧ gridPt xc yc i n ∈ modelCurve ∧
      gridPt xc yc i 0 0 = gridPt xc yc i n 0 ∧
      (∃ P ∈ E(gridGraph xc yc m n),
        (gridPt xc yc i 0 = P.1 ∨ gridPt xc yc i 0 = P.2) ∧ ¬ P.seg ⊆ modelCurve) ∧
      (∃ P ∈ E(gridGraph xc yc m n),
        (gridPt xc yc i n = P.1 ∨ gridPt xc yc i n = P.2) ∧ ¬ P.seg ⊆ modelCurve) := by
  have hxi_lo : -1 < xc i := by
    rw [← hx0]; exact hxs (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)
  have hxi_hi : xc i < 1 := by
    rw [← hxm]; exact hxs (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)
  have hxi : |xc i| < 1 := abs_lt.2 ⟨hxi_lo, hxi_hi⟩
  have hymono : ∀ a b : ℕ, a ≤ b → b ≤ n → yc a ≤ yc b := fun a b hab hb =>
    coord_le_of_idx_le hys (by omega) (Set.mem_Iic.2 hb) hab
  -- the two boundary points, on `S`
  have hbot : gridPt xc yc i 0 ∈ modelCurve := by
    refine mem_modelCurve_of_supNorm ?_
    rw [gridPt, supNorm_mk, hy0]
    simp only [abs_neg, abs_one]
    exact max_eq_right hxi.le
  have htop : gridPt xc yc i n ∈ modelCurve := by
    refine mem_modelCurve_of_supNorm ?_
    rw [gridPt, supNorm_mk, hyn, abs_one]
    exact max_eq_right hxi.le
  refine ⟨hbot, htop, by simp only [gridPt, Plane.mk_zero], ?_, ?_⟩
  · -- the bottom of column `i`
    refine ⟨gridVEdge xc yc i 0, gridVEdge_mem_gridEdges (by omega) (by omega) hm,
      Or.inl rfl, ?_⟩
    refine gridVEdge_not_subset_modelCurve hxi (by rw [hy0]) ?_ ?_
    · rw [← hyn]; exact hymono 1 n (by omega) le_rfl
    · exact hys (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)
  · -- the top of column `i`
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine ⟨gridVEdge xc yc i k, gridVEdge_mem_gridEdges (by omega) (by omega) hm,
      Or.inr rfl, ?_⟩
    refine gridVEdge_not_subset_modelCurve hxi ?_ (by rw [hyn]) ?_
    · rw [← hy0]; exact hymono 0 k (by omega) (by omega)
    · exact hys (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)

/-! ### The mesh needs at least two fresh points

The audit asks whether the plan for clause 5 is false when the fresh set is small. It is, and
this section proves the extreme case rather than asserting it: with no fresh point there is no
spoke, the mesh is `meshCount δ ≥ 2` pairwise disjoint concentric frames, and the graph is not
even connected.

The invariant is the sup norm. Every mesh segment other than a spoke lies on one ring, so with
`fresh = []` both ends of every edge have the same sup norm and a walk cannot change it. The
corner of the outer ring has sup norm `1`, the corner of the innermost ring has `N⁻¹ ≠ 1`.

**With exactly one fresh point `z` the mesh is connected but still not 2-connected**: the spoke
at `z` is the only thing joining the rings, so each of its interior vertices — the crossing
points `(k/N) • z` for `0 < k < N` — is a cut vertex, separating the rings inside it from the
rings outside. That case is *not* formalised here; it needs the crossing points to be vertices,
which needs the `MeetsAreCut` clause of the mesh's cut points, and then a separation argument.
It is recorded so that no consumer states clause 5 for `squareMesh` without a hypothesis
guaranteeing two distinct fresh points. -/

/-- An end of a source segment of the mesh is a vertex of the mesh graph. -/
theorem end_mem_vertexSet_meshGraph {N : ℕ} {fresh anchors : List Plane} {R : Piece}
    (hR : R ∈ meshSegments N fresh) {z : Plane} (hz : z = R.1 ∨ z = R.2) :
    z ∈ V(meshGraph N fresh anchors) := by
  obtain ⟨Q, hQ, -, hend⟩ :=
    subdivide_preserves_end (meshPoints N fresh anchors) ⟨R, hR, subset_rfl, hz⟩
  exact ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, (orientPiece_ends Q z).2 hend⟩

/-- With no spoke, every edge of the mesh keeps the sup norm: it is a subsegment of a side of
one ring. -/
theorem supNorm_eq_of_isLink_of_fresh_nil {N : ℕ} (hN : 2 ≤ N) {anchors : List Plane}
    {P : Piece} {x y : Plane} (h : (meshGraph N [] anchors).IsLink P x y) :
    Plane.supNorm x = Plane.supNorm y := by
  obtain ⟨R, hR, hsub⟩ := meshGraph_edge_source h.1
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨z, hz, -⟩
  · have hring : P.seg ⊆ ringSet r :=
      hsub.trans (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr)
    have h1 : Plane.supNorm P.1 = r := hring (left_mem_segment ℝ _ _)
    have h2 : Plane.supNorm P.2 = r := hring (right_mem_segment ℝ _ _)
    rcases h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [h1.trans h2.symm, h2.trans h1.symm]
  · exact absurd hz (by simp)

/-- **With no fresh point the mesh is disconnected.** -/
theorem not_connected_meshGraph_of_fresh_nil {N : ℕ} (hN : 2 ≤ N) (anchors : List Plane) :
    ¬ (meshGraph N [] anchors).Connected := by
  intro hconn
  have hinv : ∀ {u v : Plane}, (meshGraph N [] anchors).Reaches u v →
      Plane.supNorm u = Plane.supNorm v := by
    rintro u v ⟨W, hW⟩
    induction hW with
    | nil => rfl
    | cons hl _ ih => exact (supNorm_eq_of_isLink_of_fresh_nil hN hl).trans ih
  -- the outer corner and the innermost corner, at sup norms `1` and `N⁻¹`
  have houter : (Plane.mk 1 1 : Plane) ∈ V(meshGraph N [] anchors) :=
    end_mem_vertexSet_meshGraph (R := (Plane.mk 1 1, Plane.mk (-1) 1))
      (outer_ringPieces_mem hN (by simp [ringPieces])) (Or.inl rfl)
  have hinner : (Plane.mk ((N : ℝ)⁻¹) ((N : ℝ)⁻¹) : Plane) ∈ V(meshGraph N [] anchors) :=
    end_mem_vertexSet_meshGraph
      (R := (Plane.mk ((N : ℝ)⁻¹) ((N : ℝ)⁻¹), Plane.mk (-(N : ℝ)⁻¹) ((N : ℝ)⁻¹)))
      (mem_meshSegments.2 (Or.inl ⟨(N : ℝ)⁻¹, inv_mem_meshRadii hN, by simp [ringPieces]⟩))
      (Or.inl rfl)
  have heq := hinv (hconn.reaches houter hinner)
  rw [supNorm_mk, supNorm_mk, abs_one, max_self, abs_of_nonneg (inv_cast_pos hN).le,
    max_self] at heq
  exact absurd heq.symm (ne_of_lt (inv_cast_lt_one hN))

/-- **`prop:anchored-square-mesh` clause 5 is false for a mesh with no fresh point.** Every
statement of 2-connectivity for `squareMesh` must therefore carry a hypothesis on `fresh`; see
the section docstring for the one-fresh-point case, which is connected but has a cut vertex. -/
theorem not_isTwoConnected_squareMesh_of_fresh_nil (δ : ℝ) (anchors : List Plane) :
    ¬ (squareMesh δ [] anchors).IsTwoConnected := fun h =>
  not_connected_meshGraph_of_fresh_nil (two_le_meshCount δ) anchors h.connected

end Schoenflies

/-! ### Concatenating two paths

`Schoenflies/Graph/Walk.lean` has `Graph.IsWalk.append` and no path analogue, because nothing
before this needed one. The general lemma is here; the integrator should hoist it. -/

namespace Graph

variable {α β : Type*} {G : Graph α β}

/-- **Two paths that meet only at the vertex they share concatenate to a path.** -/
theorem IsPath.append_of_disjoint : ∀ {u v : α} {W₁ : List β}, G.IsPath u W₁ v →
    ∀ {w : α} {W₂ : List β}, G.IsPath v W₂ w →
      (∀ x ∈ G.walkVertices u W₁, x ∈ G.walkVertices v W₂ → x = v) →
      G.IsPath u (W₁ ++ W₂) w := by
  intro u v W₁ h₁
  induction h₁ with
  | nil hx => intro w W₂ h₂ _; simpa using h₂
  | @cons u₀ w₀ v₀ e W hl hW hfresh ih =>
    intro w W₂ h₂ hdisj
    refine IsPath.cons hl (ih h₂ fun x hx hx2 =>
      hdisj x (mem_walkVertices_cons_of_mem hl hx) hx2) ?_
    intro hmem
    rw [walkVertices] at hmem
    simp only [List.append_eq, coveredVertices_append, Set.mem_insert_iff,
      Set.mem_union] at hmem
    rcases hmem with hu | hcov
    · exact hfresh (hu ▸ mem_walkVertices_self)
    rcases hcov with hcov | hcov
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · -- the second path returns to the source of the first, so the first path is closed
      have : u₀ = v₀ :=
        hdisj u₀ mem_walkVertices_self (mem_walkVertices_of_mem_covered hcov)
      exact absurd (IsPath.eq_nil_of_eq (this ▸ IsPath.cons hl hW hfresh)) (by simp)

/-- Reading a path off its first step. `cases` on `Graph.IsPath` needs the edge list to be a
literal cons before it can discard the `nil` constructor; this packages that. -/
theorem IsPath.cons_cases {u v : α} {e : β} {W : List β} (h : G.IsPath u (e :: W) v) :
    ∃ w, G.IsLink e u w ∧ G.IsPath w W v ∧ u ∉ G.walkVertices w W := by
  cases h with
  | cons hl hW hfresh => exact ⟨_, hl, hW, hfresh⟩

end Graph

namespace Schoenflies

/-! ### The subdivision hypothesis

The one general fact about `overlayGraph` that `Schoenflies/SquareMeshConnected.lean` names as
missing, stated as a `Prop` so that the axiom audit stays a real guarantee and the defect shows
up at the consumer. It is *believed*: the pieces of the subdivision of a nondegenerate segment
have pairwise disjoint interiors and cover it, so the distance from `P.1` orders them into a
chain running from `P.1` to `P.2`. Nothing about the mesh appears in it. -/

/-- **The overlay subdivides each source segment into a path.** For each nondegenerate source
segment `P` there is an ordering `W` of *exactly* the overlay edges lying inside `P` which is a
path of the overlay from `P.1` to `P.2`. -/
def SubdividesToPath (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, P.Nondeg → ∃ W : List Piece,
    (overlayGraph pieces points).IsPath P.1 W P.2 ∧
      ∀ Q, Q ∈ W ↔ (Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ P.seg)

/-- A vertex an overlay walk visits lies wherever its source and its edges lie. -/
theorem walkVertices_subset_of_edges {pieces : List Piece} {points : List Plane}
    {A : Set Plane} {u : Plane} {W : List Piece} (hu : u ∈ A) (hW : ∀ Q ∈ W, Q.seg ⊆ A)
    {x : Plane} (hx : x ∈ (overlayGraph pieces points).walkVertices u W) : x ∈ A := by
  rcases Graph.mem_walkVertices_iff.1 hx with rfl | ⟨Q, hQ, hinc⟩
  · exact hu
  · obtain ⟨y, -, hends⟩ := hinc
    rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [hW Q hQ (left_mem_segment ℝ _ _), hW Q hQ (right_mem_segment ℝ _ _)]

/-- The edges of an overlay path along `P` occupy all of `P`. -/
theorem edgesCover_eq_seg {pieces : List Piece} {points : List Plane} {P : Piece}
    (hP : P ∈ pieces) {W : List Piece}
    (hW : ∀ Q, Q ∈ W ↔ (Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ P.seg)) :
    Graph.edgesCover segmentDrawing W = P.seg := by
  refine subset_antisymm ?_ ?_
  · intro z hz
    obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
    rw [edgeArc_segmentDrawing] at hzQ
    exact ((hW Q).1 hQ).2 hzQ
  · intro z hz
    obtain ⟨Q, hQ, hzQ, hsub⟩ := subdivide_covers_source points pieces P hP z hz
    refine Graph.mem_edgesCover ((hW (orientPiece Q)).2
      ⟨mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, by rwa [orientPiece_seg]⟩) ?_
    rw [edgeArc_segmentDrawing, orientPiece_seg]
    exact hzQ

/-! ### The four sides of the outer ring

Names for the four sides of `ringPieces 1` and the six pairwise intersections. Two opposite
sides are disjoint; two adjacent ones meet in their common corner. Everything is
`mem_segment_horiz` / `mem_segment_vert` and `plane_eq_of_coords`. -/

/-- The top side of `S`, from the north-east corner to the north-west one. -/
@[expose] def sideT : Piece := (Plane.mk 1 1, Plane.mk (-1) 1)

/-- The left side of `S`. -/
def sideL : Piece := (Plane.mk (-1) 1, Plane.mk (-1) (-1))

/-- The bottom side of `S`. -/
@[expose] def sideB : Piece := (Plane.mk (-1) (-1), Plane.mk 1 (-1))

/-- The right side of `S`, from the south-east corner back to the north-east one. -/
def sideR : Piece := (Plane.mk 1 (-1), Plane.mk 1 1)

theorem sideT_mem_ringPieces : sideT ∈ ringPieces 1 := by simp [ringPieces, sideT]
theorem sideL_mem_ringPieces : sideL ∈ ringPieces 1 := by simp [ringPieces, sideL]
theorem sideB_mem_ringPieces : sideB ∈ ringPieces 1 := by simp [ringPieces, sideB]
theorem sideR_mem_ringPieces : sideR ∈ ringPieces 1 := by simp [ringPieces, sideR]

theorem mem_sideT {x : Plane} (h : x ∈ sideT.seg) : x 1 = 1 := (mem_segment_horiz.1 h).1
theorem mem_sideB {x : Plane} (h : x ∈ sideB.seg) : x 1 = -1 := (mem_segment_horiz.1 h).1
theorem mem_sideL {x : Plane} (h : x ∈ sideL.seg) : x 0 = -1 := (mem_segment_vert.1 h).1
theorem mem_sideR {x : Plane} (h : x ∈ sideR.seg) : x 0 = 1 := (mem_segment_vert.1 h).1

theorem sideT_inter_sideL {x : Plane} (h : x ∈ sideT.seg) (h' : x ∈ sideL.seg) :
    x = Plane.mk (-1) 1 :=
  plane_eq_of_coords (by rw [mem_sideL h', Plane.mk_zero]) (by rw [mem_sideT h, Plane.mk_one])

theorem sideL_inter_sideB {x : Plane} (h : x ∈ sideL.seg) (h' : x ∈ sideB.seg) :
    x = Plane.mk (-1) (-1) :=
  plane_eq_of_coords (by rw [mem_sideL h, Plane.mk_zero]) (by rw [mem_sideB h', Plane.mk_one])

theorem sideB_inter_sideR {x : Plane} (h : x ∈ sideB.seg) (h' : x ∈ sideR.seg) :
    x = Plane.mk 1 (-1) :=
  plane_eq_of_coords (by rw [mem_sideR h', Plane.mk_zero]) (by rw [mem_sideB h, Plane.mk_one])

theorem sideT_inter_sideR {x : Plane} (h : x ∈ sideT.seg) (h' : x ∈ sideR.seg) :
    x = Plane.mk 1 1 :=
  plane_eq_of_coords (by rw [mem_sideR h', Plane.mk_zero]) (by rw [mem_sideT h, Plane.mk_one])

theorem sideT_disjoint_sideB {x : Plane} (h : x ∈ sideT.seg) (h' : x ∈ sideB.seg) : False := by
  have := (mem_sideT h).symm.trans (mem_sideB h'); norm_num at this

theorem sideL_disjoint_sideR {x : Plane} (h : x ∈ sideL.seg) (h' : x ∈ sideR.seg) : False := by
  have := (mem_sideL h).symm.trans (mem_sideR h'); norm_num at this

/-- The four sides occupy `S`. -/
theorem sides_cover : sideT.seg ∪ sideL.seg ∪ sideB.seg ∪ sideR.seg = modelCurve := by
  rw [← ringSet_one, ← cover_ringPieces zero_le_one]
  simp only [ringPieces, cover_cons, cover_nil, Set.union_empty, sideT, sideL, sideB, sideR]
  ext z
  simp only [Set.mem_union]
  tauto

theorem side_seg_subset_modelCurve {P : Piece}
    (h : P = sideT ∨ P = sideL ∨ P = sideB ∨ P = sideR) : P.seg ⊆ modelCurve := by
  rw [← sides_cover]
  rcases h with rfl | rfl | rfl | rfl
  exacts [fun x hx => Or.inl (Or.inl (Or.inl hx)), fun x hx => Or.inl (Or.inl (Or.inr hx)),
    fun x hx => Or.inl (Or.inr hx), fun x hx => Or.inr hx]

/-! ### The outer cycle of the mesh

The four sides of the outer ring are four overlay paths; three concatenations glue them into
one path once round `S`, and the last edge of the fourth is peeled off to close the cycle.
Peeling is why the fourth side is reversed: `Graph.IsPath` is built at the *source* end, so its
first step is the one that can be split off, and the first step of the reversed side is the
last edge of the side. -/

/-- **`prop:anchored-square-mesh`, clause 3 as a cycle, for the mesh graph itself.** The edges
of the mesh lying on `S` form a cycle of the mesh graph, and they occupy exactly `S`.

`Schoenflies.cover_outerEdges` proves only the point-set half of this, and
`SquareMeshConnected.gridGraph_outer_cycle` proves the cycle for a *different* graph. This is
the statement for `Schoenflies.meshGraph`.

The conclusion is existential because the hypothesis `SubdividesToPath` is: nothing here can
name the edge list of a side without choosing it. Once that hypothesis is discharged by a
theorem exporting the chain as a `def`, this should be restated with the cycle as data. -/
theorem meshGraph_outer_cycle {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane)
    (hsub : SubdividesToPath (meshSegments N fresh) (meshPoints N fresh anchors)) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (meshGraph N fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve := by
  have hmemT := outer_ringPieces_mem (fresh := fresh) hN sideT_mem_ringPieces
  have hmemL := outer_ringPieces_mem (fresh := fresh) hN sideL_mem_ringPieces
  have hmemB := outer_ringPieces_mem (fresh := fresh) hN sideB_mem_ringPieces
  have hmemR := outer_ringPieces_mem (fresh := fresh) hN sideR_mem_ringPieces
  obtain ⟨WT, hpT, hcT⟩ := hsub _ hmemT (ringPieces_nondeg one_pos _ sideT_mem_ringPieces)
  obtain ⟨WL, hpL, hcL⟩ := hsub _ hmemL (ringPieces_nondeg one_pos _ sideL_mem_ringPieces)
  obtain ⟨WB, hpB, hcB⟩ := hsub _ hmemB (ringPieces_nondeg one_pos _ sideB_mem_ringPieces)
  obtain ⟨WR, hpR, hcR⟩ := hsub _ hmemR (ringPieces_nondeg one_pos _ sideR_mem_ringPieces)
  have hsegT : ∀ Q ∈ WT, Q.seg ⊆ sideT.seg := fun Q hQ => ((hcT Q).1 hQ).2
  have hsegL : ∀ Q ∈ WL, Q.seg ⊆ sideL.seg := fun Q hQ => ((hcL Q).1 hQ).2
  have hsegB : ∀ Q ∈ WB, Q.seg ⊆ sideB.seg := fun Q hQ => ((hcB Q).1 hQ).2
  have hsegR : ∀ Q ∈ WR, Q.seg ⊆ sideR.seg := fun Q hQ => ((hcR Q).1 hQ).2
  -- the vertices each side path visits stay on that side
  have hVT : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices sideT.1 WT, x ∈ sideT.seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegT hx
  have hVL : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices sideL.1 WL, x ∈ sideL.seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegL hx
  have hVB : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices sideB.1 WB, x ∈ sideB.seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegB hx
  -- top, then left
  have hp1 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      sideT.1 (WT ++ WL) sideL.2 :=
    hpT.append_of_disjoint hpL fun x hx hx2 => sideT_inter_sideL (hVT x hx) (hVL x hx2)
  have hV1 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      sideT.1 (WT ++ WL), x ∈ sideT.seg ∪ sideL.seg := by
    refine fun x hx => walkVertices_subset_of_edges (Or.inl (left_mem_segment ℝ _ _))
      (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    exacts [(hsegT Q h).trans Set.subset_union_left, (hsegL Q h).trans Set.subset_union_right]
  -- … then the bottom
  have hp2 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      sideT.1 ((WT ++ WL) ++ WB) sideB.2 := by
    refine hp1.append_of_disjoint hpB fun x hx hx2 => ?_
    rcases hV1 x hx with h | h
    · exact absurd (sideT_disjoint_sideB h (hVB x hx2)) not_false
    · exact sideL_inter_sideB h (hVB x hx2)
  have hV2 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      sideT.1 ((WT ++ WL) ++ WB), x ∈ sideT.seg ∪ sideL.seg ∪ sideB.seg := by
    refine fun x hx => walkVertices_subset_of_edges
      (Or.inl (Or.inl (left_mem_segment ℝ _ _))) (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    · rcases List.mem_append.1 h with h' | h'
      exacts [(hsegT Q h').trans (Set.subset_union_left.trans Set.subset_union_left),
        (hsegL Q h').trans (Set.subset_union_right.trans Set.subset_union_left)]
    · exact (hsegB Q h).trans Set.subset_union_right
  -- the right side, read backwards, so that its last edge is its first step
  have hRne : sideR.1 ≠ sideR.2 := ringPieces_nondeg one_pos _ sideR_mem_ringPieces
  have hWRne : WR ≠ [] := by
    rintro rfl
    exact hRne hpR.isWalk.eq_of_nil
  obtain ⟨eR, L, hL⟩ := List.exists_cons_of_ne_nil
    (show WR.reverse ≠ [] by simpa using hWRne)
  have hpRrev := hpR.reverse
  rw [hL] at hpRrev
  obtain ⟨w, hlink, htail, hfr⟩ := hpRrev.cons_cases
  have heRmem : eR ∈ WR := by
    rw [← List.mem_reverse, hL]; exact List.mem_cons_self ..
  have hLmem : ∀ Q ∈ L, Q ∈ WR := fun Q hQ => by
    rw [← List.mem_reverse, hL]; exact List.mem_cons_of_mem _ hQ
  have hwR : w ∈ sideR.seg := by
    rcases hlink.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [hsegR eR heRmem (right_mem_segment ℝ _ _),
      hsegR eR heRmem (left_mem_segment ℝ _ _)]
  have hVRtail : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices w L, x ∈ sideR.seg := fun x hx =>
    walkVertices_subset_of_edges hwR (fun Q hQ => hsegR Q (hLmem Q hQ)) hx
  have hrevV : (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices sideB.2 L.reverse
      = (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices w L :=
    htail.isWalk.reverse_walkVertices
  -- the fourth append: what is left of the right side, from the south-east corner
  have hp3 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      sideT.1 (((WT ++ WL) ++ WB) ++ L.reverse) w := by
    refine hp2.append_of_disjoint htail.reverse fun x hx hx2 => ?_
    rw [hrevV] at hx2
    have hxR : x ∈ sideR.seg := hVRtail x hx2
    rcases hV2 x hx with (h | h) | h
    · refine absurd (show sideR.2 ∈ (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices w L from ?_) hfr
      rwa [show sideR.2 = x from (sideT_inter_sideR h hxR).symm]
    · exact absurd (sideL_disjoint_sideR h hxR) not_false
    · exact sideB_inter_sideR h hxR
  -- the closing edge is not one of the others
  have hnondegR : eR.Nondeg :=
    meshGraph_edge_nondeg (anchors := anchors) hN hfresh ((hcR eR).1 heRmem).1
  have hnotT : eR ∉ WT := fun hmem => hnondegR (by
    have h1 := sideT_inter_sideR (hsegT eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := sideT_inter_sideR (hsegT eR hmem (right_mem_segment ℝ _ _))
      (hsegR eR heRmem (right_mem_segment ℝ _ _))
    exact h1.trans h2.symm)
  have hnotL : eR ∉ WL := fun hmem =>
    sideL_disjoint_sideR (hsegL eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
  have hnotB : eR ∉ WB := fun hmem => hnondegR (by
    have h1 := sideB_inter_sideR (hsegB eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := sideB_inter_sideR (hsegB eR hmem (right_mem_segment ℝ _ _))
      (hsegR eR heRmem (right_mem_segment ℝ _ _))
    exact h1.trans h2.symm)
  have hnotLrev : eR ∉ L.reverse := by
    have hnodup : (eR :: L).Nodup := hL ▸ hpR.reverse.nodup
    rw [List.mem_reverse]
    exact (List.nodup_cons.1 hnodup).1
  have hnotD : eR ∉ ((WT ++ WL) ++ WB) ++ L.reverse := by
    intro hmem
    rcases List.mem_append.1 hmem with h | h
    · rcases List.mem_append.1 h with h' | h'
      · rcases List.mem_append.1 h' with h'' | h''
        exacts [hnotT h'', hnotL h'']
      · exact hnotB h'
    · exact hnotLrev h
  -- every edge of the cycle lies on `S`
  have hmT : sideT.seg ⊆ modelCurve := side_seg_subset_modelCurve (Or.inl rfl)
  have hmL : sideL.seg ⊆ modelCurve := side_seg_subset_modelCurve (Or.inr (Or.inl rfl))
  have hmB : sideB.seg ⊆ modelCurve := side_seg_subset_modelCurve (Or.inr (Or.inr (Or.inl rfl)))
  have hmR : sideR.seg ⊆ modelCurve := side_seg_subset_modelCurve (Or.inr (Or.inr (Or.inr rfl)))
  have hsegsAll : ∀ Q ∈ eR :: (((WT ++ WL) ++ WB) ++ L.reverse), Q.seg ⊆ modelCurve := by
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | h
    · exact (hsegR Q heRmem).trans hmR
    rcases List.mem_append.1 h with h' | h'
    · rcases List.mem_append.1 h' with h'' | h''
      · rcases List.mem_append.1 h'' with h3 | h3
        exacts [(hsegT Q h3).trans hmT, (hsegL Q h3).trans hmL]
      · exact (hsegB Q h'').trans hmB
    · exact (hsegR Q (hLmem Q (List.mem_reverse.1 h'))).trans hmR
  -- a third vertex on the cycle: the north-west corner, where the top side meets the left one
  have hthird : sideT.2 ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices sideT.1 (((WT ++ WL) ++ WB) ++ L.reverse) :=
    Graph.walkVertices_mono
      (List.Subset.trans (List.subset_append_left _ _)
        (List.Subset.trans (List.subset_append_left _ _) (List.subset_append_left _ _)))
      hpT.isWalk.target_mem_walkVertices
  have hne₁ : sideT.2 ≠ sideT.1 := mk_ne_mk_of_fst (by norm_num)
  have hne₂ : sideT.2 ≠ w := by
    intro h
    have := mem_sideR (h ▸ hwR)
    rw [sideT, Plane.mk_zero] at this
    norm_num at this
  refine ⟨eR, sideT.1, w, sideT.2, ((WT ++ WL) ++ WB) ++ L.reverse,
    ⟨⟨hlink, hp3, hnotD⟩, hthird, hne₁, hne₂⟩, hsegsAll, ?_⟩
  have hcovT : Graph.edgesCover segmentDrawing WT = sideT.seg := edgesCover_eq_seg hmemT hcT
  have hcovL : Graph.edgesCover segmentDrawing WL = sideL.seg := edgesCover_eq_seg hmemL hcL
  have hcovB : Graph.edgesCover segmentDrawing WB = sideB.seg := edgesCover_eq_seg hmemB hcB
  have hcovR : Graph.edgesCover segmentDrawing WR = sideR.seg := edgesCover_eq_seg hmemR hcR
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
    rw [edgeArc_segmentDrawing] at hzQ
    exact hsegsAll Q hQ hzQ
  · rw [← sides_cover] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · rw [← hcovT] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      exact Graph.mem_edgesCover (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hQ)))) hzQ
    · rw [← hcovL] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      exact Graph.mem_edgesCover (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hQ)))) hzQ
    · rw [← hcovB] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      exact Graph.mem_edgesCover (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_right _ hQ))) hzQ
    · rw [← hcovR] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      rw [← List.mem_reverse, hL] at hQ
      rcases List.mem_cons.1 hQ with rfl | hQ'
      · exact Graph.mem_edgesCover List.mem_cons_self hzQ
      · exact Graph.mem_edgesCover (List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_reverse.2 hQ'))) hzQ

/-- **`prop:anchored-square-mesh`, clause 3 as a cycle, for `squareMesh`.** -/
theorem squareMesh_outer_cycle_of_subdividesToPath {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane)
    (hsub : SubdividesToPath (meshSegments (meshCount δ) fresh)
      (meshPoints (meshCount δ) fresh anchors)) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (squareMesh δ fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  meshGraph_outer_cycle (two_le_meshCount δ) hfresh anchors hsub


/-- **The outer ring of the mesh is a 2-connected subgraph of the mesh.** The first step of the
blueprint's assembly of clause 5, for `squareMesh` itself: the cycle carrying `S` is 2-connected
by `lem:face-cycles`'s `Graph.IsLongCycle.isTwoConnected`. What is still missing is the rest of
the assembly — the inner rings as cycles, and the spokes attached as ears at their crossings
with each ring. -/
theorem squareMesh_outer_cycleGraph_isTwoConnected_of_subdividesToPath {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane)
    (hsub : SubdividesToPath (meshSegments (meshCount δ) fresh)
      (meshPoints (meshCount δ) fresh anchors)) :
    ∃ (e : Piece) (u : Plane) (D : List Piece),
      ((squareMesh δ fresh anchors).cycleGraph u e D).IsTwoConnected ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve := by
  obtain ⟨e, u, v, x, D, hlc, -, hcov⟩ :=
    squareMesh_outer_cycle_of_subdividesToPath hfresh δ anchors hsub
  exact ⟨e, u, D, Graph.IsLongCycle.isTwoConnected hlc, hcov⟩

end Schoenflies
