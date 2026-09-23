/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.ArcComplementPrep
public import LeanPool.Schoenflies.CombinatorialInvariance
public import LeanPool.Schoenflies.Graph.VertexSquares
public import LeanPool.Schoenflies.OuterChainClosed
public import LeanPool.Schoenflies.AccessibleJoin

/-!
# A simple arc does not separate the plane

`thm:arc-complement`.  Two points off a simple arc `A` are covered by a chain of small
axis-parallel squares strung along `A`; the two points lie in the outer face of every
consecutive pair of links, hence — by `lem:outer-chain` — in the outer face of the whole chain,
which is an open connected set missing `A`.  `lem:polygonal-connected` then joins them there.

## The single-ambient-graph obligation, and how it is met

`Graph.IsPlaneChain` requires every link `Γ i` to be a subgraph of **one** ambient plane graph
with **one** drawing.  A link built as the polygonal overlay of its own squares would *not*
qualify: the total overlay cuts those same segments at the crossings with the squares of other
links as well, so a sub-overlay has edges the total overlay has subdivided further.

The construction is therefore inverted.  `familyPieces c N r` is **one** list holding the four
sides of every small square; `familyOverlay c N r` is the one overlay of that list; and a link
is carved out of it by restricting the *edge set*:

* `segGraph S` — the plane graph spanned by a set `S` of straight edges, with the ends of those
  edges as vertices.  `overlayGraph pieces points = segGraph {Q | Q ∈ overlayPieces pieces
  points}` holds by `rfl`, so `segGraph_mono` turns a subset of the overlay's edges into a
  subgraph of the overlay with nothing to prove.
* `squareGraph pieces points c r` — the edges of the overlay lying on the boundary of the square
  of radius `r` about `c`, spanned.  It occupies exactly that boundary
  (`pointSet_squareGraph`), and every cut point on the boundary is one of its vertices
  (`mem_vertexSet_squareGraph`), which is what `Graph.IsTwoConnected.union` needs.
* `familyChain c N m r i` — the `i`-th link: `Graph.chainUnion` of the `m + 1` square graphs of
  the `i`-th coarse subarc.  Consecutive links share the square at the sample they have in
  common; nonconsecutive links are disjoint.

`isPlaneChain_familyChain` is the theorem that this family is a `Graph.IsPlaneChain`, stated for
an arbitrary family of centres `c : ℕ → Plane` with two geometric hypotheses — consecutive
centres closer than one radius, nonconsecutive-block centres further apart than two radii.  The
arc enters only in `exists_face_of_notMem_arc`, where `c j = α(j/N)`.

## What is assumed

Three hypotheses, all named in the statements that carry them.

* `SquaresTwoConnected` — **the part of a polygonal overlay lying on the boundary of one of its
  squares is 2-connected.**  That part is the subdivided boundary cycle of an axis-parallel
  square: four sides, cut at finitely many interior points, every cut point a vertex, the four
  corners among the vertices.  It is a cycle, so `Graph.IsLongCycle.isTwoConnected` finishes;
  what a discharger must build is the cyclic order of the cut points along the four sides, for
  which `Schoenflies/SegmentOrder.lean` is the tool.  Nothing about the arc, the chain or the
  outer face enters the statement.
* `Graph.CrosscutExists` and `Graph.CrosscutEncloses` — the two halves of the descent step of
  `lem:outer-chain`, quoted from `Schoenflies/OuterChain.lean` unchanged.  Because the chain is
  built from choices made inside the proof of `exists_face_of_notMem_arc`, they appear there in
  ∀-form: `CrosscutExists` conditioned on `Graph.IsPlaneChain` (which is how a discharger will
  state it) and `CrosscutEncloses` for every point.

## Blueprint

* `segGraph`, `squareGraph`, `familyPieces`, `familyOverlay`, `familySquare`, `familyChain` —
  the construction of the proof of `thm:arc-complement`: "around every sample draw the boundary
  of the axis-parallel square of `ℓ^∞`-radius `δ/4`, and let `Γ_i` be the polygonal overlay
  (`lem:polygonal-overlay`) of the square boundaries associated with `A_i`".
* `familyChain_isTwoConnected` — "it follows inductively from `lem:union-two-connected` that
  `Γ_i` is 2-connected".
* `isPlaneChain_familyChain` — "consecutive graphs `Γ_i, Γ_{i+1}` share the square at their
  common sample.  If `|i-j| ≥ 2`, then `Γ_i` and `Γ_j` are disjoint".
* `outer_of_notMem_closedSquare`, `outerOnPairs_familyChain` — "the graph `Γ_i ∪ Γ_{i+1}` is
  contained in the `ℓ^∞`-square of radius `3d` centered at `a_i` … both `p` and `q` lie outside
  this containing square and hence in the outer face of the pair".
* `notMem_face_of_mem_openSquare` — "if it lies inside, the boundary cycle of that square
  separates it from the outer face of `G`".
* `exists_face_of_notMem_arc` — the whole proof of `thm:arc-complement` up to the last sentence.
* `isConnected_compl_arc`, `exists_simple_poly_compl_arc` — **`thm:arc-complement`**: the
  complement of a simple arc is connected, and any two of its points are joined in it by a
  simple polygonal arc.
-/

@[expose] public section

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## Part 1: the subgraph of the plane spanned by a set of straight edges -/

/-- **The plane graph spanned by a set of straight edges.**  Its vertices are the ends of
those edges and an edge links its two ends in either order — the shape of
`Schoenflies.overlayGraph`, with the edge list replaced by an arbitrary set.

This exists so that a *part* of one overlay can be spoken about as a graph in its own right
while remaining a subgraph of the whole overlay (`segGraph_mono`).  Building the part as an
overlay of its own source segments would not do: the total overlay cuts those segments at more
points, so a sub-overlay is not a subgraph of it. -/
def segGraph (S : Set Piece) : Graph Plane Piece where
  vertexSet := {v | ∃ P ∈ S, v = P.1 ∨ v = P.2}
  IsLink P x y := P ∈ S ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1))
  edgeSet := S
  isLink_symm := fun _ _ => ⟨fun _ _ h => ⟨h.1, by tauto⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro P x y v w ⟨-, hxy⟩ ⟨-, hvw⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro P
    exact ⟨fun hP => ⟨P.1, P.2, hP, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hP, _⟩ => hP⟩
  left_mem_of_isLink := by
    rintro P x y ⟨hP, h⟩
    exact ⟨P, hP, by tauto⟩

variable {S T : Set Piece} {P : Piece} {x y v : Plane}

@[simp] theorem segGraph_vertexSet (S : Set Piece) :
    V(segGraph S) = {v | ∃ P ∈ S, v = P.1 ∨ v = P.2} := rfl

@[simp] theorem segGraph_edgeSet (S : Set Piece) : E(segGraph S) = S := rfl

@[simp] theorem segGraph_isLink :
    (segGraph S).IsLink P x y ↔ P ∈ S ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := Iff.rfl

theorem mem_vertexSet_segGraph : v ∈ V(segGraph S) ↔ ∃ P ∈ S, v = P.1 ∨ v = P.2 := Iff.rfl

/-- An end of an edge is a vertex. -/
theorem mem_vertexSet_segGraph_of_end (hP : P ∈ S) (h : v = P.1 ∨ v = P.2) :
    v ∈ V(segGraph S) := ⟨P, hP, h⟩

/-- **More edges, larger graph.**  This is the whole point of `segGraph`: the pieces of the
chain are subgraphs of one ambient overlay by construction. -/
theorem segGraph_mono (h : S ⊆ T) : segGraph S ≤ segGraph T where
  vertexSet_mono := by rintro v ⟨P, hP, hv⟩; exact ⟨P, h hP, hv⟩
  isLink_mono := by rintro P a b ⟨hP, hab⟩; exact ⟨h hP, hab⟩

theorem segGraph_finite (hS : S.Finite) : Graph.Finite (segGraph S) where
  finite_vertexSet := by
    refine Set.Finite.subset ((hS.image (fun P : Piece => P.1)).union
      (hS.image (fun P : Piece => P.2))) ?_
    rintro v ⟨P, hP, rfl | rfl⟩
    exacts [Or.inl ⟨P, hP, rfl⟩, Or.inr ⟨P, hP, rfl⟩]
  finite_edgeSet := hS

/-- **The overlay graph is the graph spanned by its own edge list.**  Definitional, so that a
subset of the overlay pieces spans a subgraph of the overlay with nothing to prove. -/
theorem overlayGraph_eq_segGraph (pieces : List Piece) (points : List Plane) :
    overlayGraph pieces points = segGraph {Q | Q ∈ overlayPieces pieces points} := rfl

/-- What a spanned graph occupies is the union of its segments: every vertex is an end of an
edge, so the vertices add nothing. -/
theorem pointSet_segGraph (S : Set Piece) :
    Graph.pointSet (segGraph S) segmentDrawing = ⋃ P ∈ S, P.seg := by
  ext z
  simp only [Graph.pointSet, mem_union, mem_iUnion, exists_prop, segGraph_vertexSet,
    Set.mem_ofPred_eq, segGraph_edgeSet, edgeArc_segmentDrawing]
  constructor
  · rintro (⟨P, hP, hzP⟩ | ⟨P, hP, hzP⟩)
    · refine ⟨P, hP, ?_⟩
      rcases hzP with rfl | rfl
      exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
    · exact ⟨P, hP, hzP⟩
  · rintro ⟨P, hP, hzP⟩
    exact Or.inr ⟨P, hP, hzP⟩

/-! ## Part 2: the part of an overlay lying on one square

The chain graphs are assembled out of these.  Each is the set of overlay edges whose segment
lies on one small square boundary, spanned by `segGraph` — so it is a subgraph of the *total*
overlay, not an overlay of the four sides of that square alone. -/

/-- **Every point of a source segment lies on an overlay edge inside that source segment.**
`Schoenflies.exists_overlayPiece_end_subset` is the same statement for a *cut* point, with the
edge pinned so as to have that point among its ends; this is the plain covering form, and it is
what makes the part of the overlay on a square occupy the whole of that square's boundary. -/
theorem exists_overlayPiece_mem_subset {pieces : List Piece} {points : List Plane}
    {x : Plane} {P₀ : Piece} (hP₀ : P₀ ∈ pieces) (hx : x ∈ P₀.seg) :
    ∃ Q ∈ overlayPieces pieces points, x ∈ Q.seg ∧ Q.seg ⊆ P₀.seg := by
  -- The pieces of the subdivision of `[P₀]` alone already cover `P₀.seg`.
  have hcov : x ∈ cover (subdivide [P₀] points) := by
    rw [subdivide_cover, cover_cons, cover_nil, union_empty]
    exact hx
  simp only [cover, mem_iUnion, exists_prop] at hcov
  obtain ⟨Q, hQ, hxQ⟩ := hcov
  have hQpieces : Q ∈ subdivide pieces points :=
    subdivide_mono points (by simpa using hP₀) Q hQ
  have hQsub : Q.seg ⊆ P₀.seg := by
    obtain ⟨R, hR, hseg, -⟩ := subdivide_subset [P₀] points Q hQ
    rw [List.mem_singleton] at hR
    exact hR ▸ hseg
  exact ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQpieces, rfl⟩, by rwa [orientPiece_seg],
    by rw [orientPiece_seg]; exact hQsub⟩

variable {pieces : List Piece} {points : List Plane} {c c₁ c₂ : Plane} {r : ℝ}

/-- The edges of an overlay whose segment lies on the boundary of the square of `ℓ^∞`-radius
`r` about `c`. -/
def squareEdges (pieces : List Piece) (points : List Plane) (c : Plane) (r : ℝ) : Set Piece :=
  {Q | Q ∈ overlayPieces pieces points ∧ Q.seg ⊆ frontier (Plane.closedSquare c r)}

/-- **The part of one overlay lying on one square boundary.**  A subgraph of that overlay by
construction (`squareGraph_le`), which is the single-ambient-graph obligation of
`Graph.IsPlaneChain` discharged at the bottom of the tower. -/
def squareGraph (pieces : List Piece) (points : List Plane) (c : Plane) (r : ℝ) :
    Graph Plane Piece :=
  segGraph (squareEdges pieces points c r)

theorem squareEdges_finite : (squareEdges pieces points c r).Finite :=
  (overlayPieces pieces points).finite_toSet.subset fun _ hQ => hQ.1

theorem squareGraph_le : squareGraph pieces points c r ≤ overlayGraph pieces points :=
  segGraph_mono fun _ hQ => hQ.1

instance squareGraph_finite : Graph.Finite (squareGraph pieces points c r) :=
  segGraph_finite squareEdges_finite

theorem pointSet_squareGraph_subset :
    Graph.pointSet (squareGraph pieces points c r) segmentDrawing ⊆
      frontier (Plane.closedSquare c r) := by
  rw [squareGraph, pointSet_segGraph]
  exact iUnion₂_subset fun _ hQ => hQ.2

/-- **The part of the overlay on a square occupies the whole square boundary.**  Every point of
the boundary lies on one of the four sides, and the overlay subdivides that side into pieces
that stay inside it. -/
theorem pointSet_squareGraph (hr : 0 ≤ r) (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) :
    Graph.pointSet (squareGraph pieces points c r) segmentDrawing =
      frontier (Plane.closedSquare c r) := by
  refine subset_antisymm pointSet_squareGraph_subset fun z hz => ?_
  rw [← cover_squarePieces c hr] at hz
  simp only [cover, mem_iUnion, exists_prop] at hz
  obtain ⟨P₀, hP₀, hzP₀⟩ := hz
  obtain ⟨Q, hQ, hzQ, hQsub⟩ := exists_overlayPiece_mem_subset (points := points) (hsub P₀ hP₀) hzP₀
  have hQfr : Q.seg ⊆ frontier (Plane.closedSquare c r) := by
    rw [← cover_squarePieces c hr]
    exact hQsub.trans fun w hw => mem_iUnion₂.2 ⟨P₀, hP₀, hw⟩
  rw [squareGraph, pointSet_segGraph]
  exact mem_iUnion₂.2 ⟨Q, ⟨hQ, hQfr⟩, hzQ⟩

/-- A cut point on a square boundary is a **vertex** of the part of the overlay on that
square.  This is what turns "two nearby squares meet in two points" into the two common
*vertices* that `Graph.IsTwoConnected.union` consumes. -/
theorem mem_vertexSet_squareGraph (hnd : ∀ P ∈ pieces, P.Nondeg) (hr : 0 ≤ r)
    (hsub : ∀ P ∈ squarePieces c r, P ∈ pieces) {z : Plane} (hz : z ∈ points)
    (hzf : z ∈ frontier (Plane.closedSquare c r)) :
    z ∈ V(squareGraph pieces points c r) := by
  rw [← cover_squarePieces c hr] at hzf
  simp only [cover, mem_iUnion, exists_prop] at hzf
  obtain ⟨P₀, hP₀, hzP₀⟩ := hzf
  obtain ⟨Q, hQ, hend, hQsub⟩ :=
    exists_overlayPiece_end_subset (points := points) hnd hz (hsub P₀ hP₀) hzP₀
  have hQfr : Q.seg ⊆ frontier (Plane.closedSquare c r) := by
    rw [← cover_squarePieces c hr]
    exact hQsub.trans fun w hw => mem_iUnion₂.2 ⟨P₀, hP₀, hw⟩
  exact mem_vertexSet_segGraph_of_end ⟨hQ, hQfr⟩ hend

/-- **Two nearby congruent squares contribute two common vertices**, each a vertex of the part
of the overlay lying on its own square.  With equal centres this produces two vertices of one
square, which is how consecutive links of the chain are shown to meet. -/
theorem exists_two_vertices_squareGraph (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hMeets : MeetsAreCut pieces points) (hr : 0 < r) (hd : Plane.supDist c₁ c₂ < r)
    (h₁ : ∀ P ∈ squarePieces c₁ r, P ∈ pieces) (h₂ : ∀ P ∈ squarePieces c₂ r, P ∈ pieces) :
    ∃ a b : Plane, a ≠ b ∧
      a ∈ V(squareGraph pieces points c₁ r) ∧ a ∈ V(squareGraph pieces points c₂ r) ∧
      b ∈ V(squareGraph pieces points c₁ r) ∧ b ∈ V(squareGraph pieces points c₂ r) := by
  obtain ⟨a, b, hab, ha, hb, haf, hbf⟩ :=
    exists_two_cut_points (points := points) hnd hMeets hr hd h₁ h₂
  exact ⟨a, b, hab,
    mem_vertexSet_squareGraph hnd hr.le h₁ ha haf.1,
    mem_vertexSet_squareGraph hnd hr.le h₂ ha haf.2,
    mem_vertexSet_squareGraph hnd hr.le h₁ hb hbf.1,
    mem_vertexSet_squareGraph hnd hr.le h₂ hb hbf.2⟩

/-! ## Part 3: the chain of square boundaries

Everything here is about a family of centres `c : ℕ → Plane` and one radius `r`; the arc enters
only in Part 5, where `c j = α (j / N)`.  Separating the two keeps the single-ambient-graph
bookkeeping free of parametrisation arithmetic. -/

/-- **The one list of source segments**: the four sides of the square of `ℓ^∞`-radius `r`
about each of the centres `c 0, …, c N`.

The whole proof rests on this being *one* list.  A chain link built as the overlay of its own
squares would not be a subgraph of the total overlay, because the total overlay cuts those
segments at the crossings with squares of other links as well. -/
noncomputable def familyPieces (c : ℕ → Plane) (N : ℕ) (r : ℝ) : List Piece :=
  (List.range (N + 1)).flatMap fun j => squarePieces (c j) r

variable {c : ℕ → Plane} {N m i j : ℕ}

theorem mem_familyPieces {P : Piece} :
    P ∈ familyPieces c N r ↔ ∃ j ≤ N, P ∈ squarePieces (c j) r := by
  simp only [familyPieces, List.mem_flatMap, List.mem_range]
  exact ⟨fun ⟨j, hj, hP⟩ => ⟨j, by omega, hP⟩, fun ⟨j, hj, hP⟩ => ⟨j, by omega, hP⟩⟩

theorem squarePieces_subset_familyPieces (hj : j ≤ N) :
    ∀ P ∈ squarePieces (c j) r, P ∈ familyPieces c N r :=
  fun _ hP => mem_familyPieces.2 ⟨j, hj, hP⟩

theorem familyPieces_nondeg (hr : 0 < r) : ∀ P ∈ familyPieces c N r, P.Nondeg := by
  intro P hP
  obtain ⟨j, -, hPj⟩ := mem_familyPieces.1 hP
  exact squarePieces_nondeg (c j) hr P hPj

/-- The cut points of that list, chosen once and for all.  `Schoenflies.exists_cut_points`
produces them existentially; naming them here is what lets every chain link be a subgraph of
*the same* overlay. -/
noncomputable def familyPoints (c : ℕ → Plane) (N : ℕ) (r : ℝ) : List Plane :=
  (exists_cut_points (familyPieces c N r)).choose

theorem familyPoints_endsAreCut : EndsAreCut (familyPieces c N r) (familyPoints c N r) :=
  (exists_cut_points (familyPieces c N r)).choose_spec.1

theorem familyPoints_meetsAreCut : MeetsAreCut (familyPieces c N r) (familyPoints c N r) :=
  (exists_cut_points (familyPieces c N r)).choose_spec.2

/-- **The single ambient plane graph of the whole proof**: the polygonal overlay of every small
square at once (`lem:polygonal-overlay`). -/
noncomputable def familyOverlay (c : ℕ → Plane) (N : ℕ) (r : ℝ) : Graph Plane Piece :=
  overlayGraph (familyPieces c N r) (familyPoints c N r)

/-- The part of the ambient overlay lying on the `j`-th small square. -/
noncomputable def familySquare (c : ℕ → Plane) (N : ℕ) (r : ℝ) (j : ℕ) : Graph Plane Piece :=
  squareGraph (familyPieces c N r) (familyPoints c N r) (c j) r

/-- **The `i`-th link of the chain, `Γ_i`**: the squares at the `m + 1` fine samples
`i·m, …, i·m + m` of the `i`-th coarse subarc.  Consecutive links share the square at the
sample they have in common. -/
noncomputable def familyChain (c : ℕ → Plane) (N m : ℕ) (r : ℝ) (i : ℕ) : Graph Plane Piece :=
  Graph.chainUnion (familySquare c N r) (i * m) m

theorem familySquare_le : familySquare c N r j ≤ familyOverlay c N r := squareGraph_le

instance familySquare_finite : Graph.Finite (familySquare c N r j) := squareGraph_finite

theorem familyChain_le : familyChain c N m r i ≤ familyOverlay c N r :=
  Graph.chainUnion_le fun _ _ _ => familySquare_le

theorem familyChain_finite : (familyChain c N m r i).Finite :=
  Graph.chainUnion_finite fun _ _ _ => familySquare_finite

/-- The drawing of the ambient overlay: every edge is a straight segment. -/
theorem familyOverlay_isDrawing (hr : 0 < r) :
    Graph.IsDrawing (familyOverlay c N r) segmentDrawing :=
  overlayGraph_isDrawing _ _ (familyPieces_nondeg hr) familyPoints_endsAreCut
    familyPoints_meetsAreCut

theorem pointSet_familySquare (hr : 0 < r) (hj : j ≤ N) :
    Graph.pointSet (familySquare c N r j) segmentDrawing =
      frontier (Plane.closedSquare (c j) r) :=
  pointSet_squareGraph hr.le (squarePieces_subset_familyPieces hj)

/-- A point of a chain link lies on one of that link's squares. -/
theorem exists_mem_frontier_of_mem_pointSet_familyChain {z : Plane}
    (hz : z ∈ Graph.pointSet (familyChain c N m r i) segmentDrawing) :
    ∃ j, i * m ≤ j ∧ j ≤ i * m + m ∧ z ∈ frontier (Plane.closedSquare (c j) r) := by
  obtain ⟨p, hp, hp', hzp⟩ := Graph.IsPlaneChain.mem_pointSet_block hz
  exact ⟨p, hp, hp', pointSet_squareGraph_subset hzp⟩

/-- **Assumed**: the part of a polygonal overlay lying on the boundary of one of its squares is
2-connected.

It is the subdivided boundary of an axis-parallel square — four sides, cut at finitely many
points, each cut point a vertex — so it is a cycle, and `Graph.IsLongCycle.isTwoConnected`
finishes.  What a discharging module must build is the cyclic order of the cut points along the
four sides; `Schoenflies/SegmentOrder.lean` is the tool.  Nothing about the arc, the chain or
the outer face enters the statement. -/
def SquaresTwoConnected : Prop :=
  ∀ (pieces : List Piece) (points : List Plane), (∀ P ∈ pieces, P.Nondeg) →
    EndsAreCut pieces points → MeetsAreCut pieces points →
    ∀ (c : Plane) (r : ℝ), 0 < r → (∀ P ∈ squarePieces c r, P ∈ pieces) →
      (squareGraph pieces points c r).IsTwoConnected

theorem familySquare_isTwoConnected (h2c : SquaresTwoConnected) (hr : 0 < r) (hj : j ≤ N) :
    (familySquare c N r j).IsTwoConnected :=
  h2c _ _ (familyPieces_nondeg hr) familyPoints_endsAreCut familyPoints_meetsAreCut _ r hr
    (squarePieces_subset_familyPieces hj)

/-- Two squares whose centres are within one radius contribute two common vertices to the two
parts of the overlay lying on them.  With equal centres this gives two vertices of one square,
which is how consecutive links of the chain are shown to meet. -/
theorem exists_two_vertices_familySquare (hr : 0 < r) {j j' : ℕ} (hj : j ≤ N) (hj' : j' ≤ N)
    (hd : Plane.supDist (c j) (c j') < r) :
    ∃ a b : Plane, a ≠ b ∧ a ∈ V(familySquare c N r j) ∧ a ∈ V(familySquare c N r j') ∧
      b ∈ V(familySquare c N r j) ∧ b ∈ V(familySquare c N r j') :=
  exists_two_vertices_squareGraph (familyPieces_nondeg hr) familyPoints_meetsAreCut hr hd
    (squarePieces_subset_familyPieces hj) (squarePieces_subset_familyPieces hj')

/-- Each link of the chain is 2-connected: consecutive squares in it share two vertices, so
`lem:union-two-connected` applies all the way along. -/
theorem familyChain_isTwoConnected (h2c : SquaresTwoConnected) (hr : 0 < r)
    (hi : i * m + m ≤ N) (hstep : ∀ q < N, Plane.supDist (c q) (c (q + 1)) < r) :
    (familyChain c N m r i).IsTwoConnected :=
  Graph.chainUnion_isTwoConnected (G := familyOverlay c N r)
    (fun _ _ _ => familySquare_le)
    (fun q _ hq' => familySquare_isTwoConnected h2c hr (by omega))
    fun q _ hq' => exists_two_vertices_familySquare hr (by omega) (by omega)
      (hstep q (by omega))

/-! ## Part 4: the chain satisfies `Graph.IsPlaneChain`

This is the obligation `Schoenflies/OuterChain.lean` flagged: every link must be a subgraph of
**one** ambient plane graph with **one** drawing.  It is discharged by construction — every link
is a `Graph.chainUnion` of `familySquare`s, and every `familySquare` is a `segGraph` on a subset
of the edges of the one overlay `familyOverlay c N r`. -/

/-- **The chain of square boundaries is a plane chain.**

The two geometric hypotheses are the blueprint's: consecutive centres are closer than one square
radius (`hstep`), and centres belonging to nonconsecutive links are more than two radii apart
(`hfar`).  Everything else — one ambient graph, one drawing, finiteness, polygonality — is
discharged by the construction. -/
theorem isPlaneChain_familyChain {n : ℕ} (h2c : SquaresTwoConnected) (hr : 0 < r)
    (hn : 2 ≤ n) (hN : n * m + m ≤ N)
    (hstep : ∀ q < N, Plane.supDist (c q) (c (q + 1)) < r)
    (hfar : ∀ p q, p ≤ n → q ≤ n → p + 1 < q →
      ∀ j, p * m ≤ j → j ≤ p * m + m → ∀ j', q * m ≤ j' → j' ≤ q * m + m →
        2 * r < Plane.supDist (c j) (c j')) :
    Graph.IsPlaneChain (familyChain c N m r) segmentDrawing (familyOverlay c N r) n := by
  -- Every index the chain uses is one of the `N + 1` centres.
  have hblock : ∀ p ≤ n, p * m + m ≤ N := by
    intro p hp
    have : p * m ≤ n * m := Nat.mul_le_mul_right _ hp
    omega
  refine ⟨hn, fun _ _ => familyChain_le, familyOverlay_isDrawing hr, ?_,
    fun _ _ => familyChain_finite, ?_, ?_, ?_⟩
  · -- Every edge of the overlay is drawn as a straight segment.
    intro g _
    rw [edgeArc_segmentDrawing]
    exact isPolygonal_segment g.1 g.2
  · exact fun p hp => familyChain_isTwoConnected h2c hr (hblock p hp) hstep
  · -- Consecutive links share the square at the sample they have in common.
    intro p hp
    have hpm : (p + 1) * m = p * m + m := by ring
    have hjN : p * m + m ≤ N := hblock p (by omega)
    obtain ⟨a, b, hab, ha, -, hb, -⟩ :=
      exists_two_vertices_familySquare (c := c) hr hjN hjN
        (by rw [Plane.supDist_self]; exact hr)
    -- The shared square is a member of both blocks.
    have hle₁ : familySquare c N r (p * m + m) ≤ familyChain c N m r p :=
      Graph.le_chainUnion (G := familyOverlay c N r) (fun _ _ _ => familySquare_le)
        (by omega) (by omega)
    have hle₂ : familySquare c N r (p * m + m) ≤ familyChain c N m r (p + 1) :=
      Graph.le_chainUnion (G := familyOverlay c N r) (fun _ _ _ => familySquare_le)
        (by omega) (by omega)
    exact ⟨a, b, hab, hle₁.vertexSet_mono ha, hle₂.vertexSet_mono ha,
      hle₁.vertexSet_mono hb, hle₂.vertexSet_mono hb⟩
  · -- Nonconsecutive links are disjoint: a common point would put two far-apart centres within
    -- two radii of each other.
    intro p q hp hq hpq
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨j, hj, hj', hzj⟩ := exists_mem_frontier_of_mem_pointSet_familyChain hz
    obtain ⟨k, hk, hk', hzk⟩ := exists_mem_frontier_of_mem_pointSet_familyChain hz'
    rw [Plane.frontier_closedSquare, Set.mem_ofPred_eq] at hzj hzk
    have htri := Plane.supDist_triangle (c j) z (c k)
    rw [Plane.supDist_comm (c j) z] at htri
    exact absurd (hfar p q hp hq hpq j hj hj' k hk hk') (by rw [hzj, hzk] at htri; linarith)

/-! ## Part 5: the outer face of the chain

Two plane facts, both general, and then the hypothesis of `lem:outer-chain` on consecutive
pairs. -/

/-- **The outside of a square containing the whole drawing lies in one unbounded face.**
`Graph.beyondSquare_subset_face` is this statement for a square centred at the origin; the
chain argument needs it about a square centred at a sample of the arc, and the connectedness of
the outside of an arbitrary square is `Plane.isConnected_compl_closedSquare`. -/
theorem outer_of_notMem_closedSquare {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {c₀ : Plane} {R : ℝ} (hsub : Graph.pointSet G drawing ⊆ Plane.closedSquare c₀ R)
    {base : Plane} (hbase : base ∉ Plane.closedSquare c₀ R) :
    base ∈ Graph.exterior G drawing ∧ ¬ Bornology.IsBounded (Graph.face G drawing base) := by
  refine ⟨fun h => hbase (hsub h), fun hb => ?_⟩
  have hsub' : (Plane.closedSquare c₀ R)ᶜ ⊆ Graph.face G drawing base :=
    (Plane.isConnected_compl_closedSquare c₀ R).isPreconnected.subset_connectedComponentIn
      hbase (compl_subset_compl.2 hsub)
  exact Plane.not_isBounded_compl_closedSquare c₀ R (hb.subset hsub')

/-- The complement of a square's boundary has the open square as one whole component. -/
theorem connectedComponentIn_compl_frontier_closedSquare {c₀ : Plane} {R : ℝ} {z : Plane}
    (hz : z ∈ Plane.openSquare c₀ R) :
    connectedComponentIn (frontier (Plane.closedSquare c₀ R))ᶜ z = Plane.openSquare c₀ R :=
  Plane.connectedComponentIn_eq_of_frontier_disjoint (Plane.isOpen_openSquare c₀ R)
    (Plane.convex_openSquare c₀ R).isPreconnected
    (by rw [Plane.compl_frontier_closedSquare]; exact subset_union_left)
    (by
      rw [eq_empty_iff_forall_notMem]
      exact fun w hw => hw.2 (Plane.frontier_openSquare_subset c₀ R hw.1))
    hz

/-- **"If it lies inside, the boundary cycle of that square separates it from the outer
face."**  A point strictly inside a square whose boundary the drawing carries is not in any
unbounded face: the face would be a connected subset of the complement of that boundary meeting
the inside, hence inside, hence bounded. -/
theorem notMem_face_of_mem_openSquare {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {c₀ : Plane} {R : ℝ} (hfr : frontier (Plane.closedSquare c₀ R) ⊆ Graph.pointSet G drawing)
    {base z : Plane} (hb : ¬ Bornology.IsBounded (Graph.face G drawing base))
    (hz : z ∈ Plane.openSquare c₀ R) : z ∉ Graph.face G drawing base := by
  intro hmem
  have hsub : Graph.face G drawing base ⊆ (frontier (Plane.closedSquare c₀ R))ᶜ :=
    fun w hw hw' => Graph.face_subset_exterior _ _ _ hw (hfr hw')
  have hcomp : Graph.face G drawing base ⊆
      connectedComponentIn (frontier (Plane.closedSquare c₀ R))ᶜ z :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn hmem hsub
  rw [connectedComponentIn_compl_frontier_closedSquare hz] at hcomp
  exact hb ((Plane.isBounded_closedSquare c₀ R).subset
    (hcomp.trans fun w hw => show Plane.supDist w c₀ ≤ R from le_of_lt hw))

/-- **The hypothesis of `lem:outer-chain` on consecutive pairs.**  Every consecutive pair of
links is contained in one square of radius `R` about the pair's first centre, and `x` is outside
that square. -/
theorem outerOnPairs_familyChain {n : ℕ} {R : ℝ} {x : Plane}
    (hcontain : ∀ p, p + 1 ≤ n → ∀ j, p * m ≤ j → j ≤ p * m + m + m →
      Plane.supDist (c j) (c (p * m)) + r ≤ R)
    (hx : ∀ p, p + 1 ≤ n → R < Plane.supDist x (c (p * m))) :
    Graph.OuterOnPairs (familyChain c N m r) segmentDrawing n x := by
  intro p hp
  refine outer_of_notMem_closedSquare (c₀ := c (p * m)) (R := R) ?_ ?_
  · -- Every point of either link is within `r` of one of the centres of the pair.
    intro z hz
    rw [Graph.chainUnion_one, Graph.pointSet_union] at hz
    have key : ∀ i, p ≤ i → i ≤ p + 1 →
        z ∈ Graph.pointSet (familyChain c N m r i) segmentDrawing →
        z ∈ Plane.closedSquare (c (p * m)) R := by
      intro i hi hi' hzi
      obtain ⟨j, hj, hj', hzj⟩ := exists_mem_frontier_of_mem_pointSet_familyChain hzi
      rw [Plane.frontier_closedSquare, Set.mem_ofPred_eq] at hzj
      have hjlo : p * m ≤ j := le_trans (Nat.mul_le_mul_right _ hi) hj
      have hjhi : j ≤ p * m + m + m := by
        have : i * m ≤ (p + 1) * m := Nat.mul_le_mul_right _ hi'
        have hpm : (p + 1) * m = p * m + m := by ring
        omega
      have htri := Plane.supDist_triangle z (c j) (c (p * m))
      have := hcontain p hp j hjlo hjhi
      exact show Plane.supDist z (c (p * m)) ≤ R by rw [hzj] at htri; linarith
    rcases hz with hz | hz
    · exact key p le_rfl (by omega) hz
    · exact key (p + 1) (by omega) le_rfl hz
  · exact fun hmem => absurd (hx p hp) (not_lt.2 hmem)

/-- **`lem:outer-chain`, applied to the chain of squares.**  Stated with the two halves of the
descent step exactly as `Schoenflies/OuterChain.lean` defines them and for *this* chain, so that
a discharger's terms substitute here with nothing to adapt. -/
theorem outer_face_familyChain {n : ℕ} {x : Plane}
    (hchain : Graph.IsPlaneChain (familyChain c N m r) segmentDrawing (familyOverlay c N r) n)
    (hout : Graph.OuterOnPairs (familyChain c N m r) segmentDrawing n x) :
    x ∈ Graph.exterior (Graph.chainUnion (familyChain c N m r) 0 n) segmentDrawing ∧
      ¬ Bornology.IsBounded
        (Graph.face (Graph.chainUnion (familyChain c N m r) 0 n) segmentDrawing x) :=
  hchain.outer_chain' hout

/-! ## Part 6: from the Euclidean distance to the sup distance

The only place the two metrics have to be compared. `‖·‖ ≤ √2‖·‖∞` and `√2 < 2`, so half the
Euclidean distance is a *strict* lower bound for the sup distance — which is what turns the
blueprint's separation constants into square radii. -/

theorem lt_supDist_of_le_dist {x y : Plane} {t : ℝ} (ht : 0 < t) (h : t ≤ dist x y) :
    t / 2 < Plane.supDist x y := by
  have h2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hs0 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hle : dist x y ≤ Real.sqrt 2 * Plane.supDist x y := by
    rw [dist_eq_norm]
    exact Plane.norm_le_sqrt_two_mul_supNorm _
  have hsd : 0 < Plane.supDist x y := by nlinarith
  nlinarith

/-- The block of fine samples belonging to one coarse cell lies in that coarse cell. -/
theorem sample_mem_Icc_of_block {K m j p : ℕ} (hm : 0 < m) (h₁ : p * m ≤ j)
    (h₂ : j ≤ (p + 1) * m) : sample (K * m) j ∈ Icc (sample K p) (sample K (p + 1)) := by
  refine ⟨?_, ?_⟩
  · rw [← sample_mul (k := K) (i := p) hm]; exact sample_mono h₁
  · rw [← sample_mul (k := K) (i := p + 1) hm]; exact sample_mono h₂

/-- Every index below `(n+1)·m` belongs to one of the `n + 1` blocks of length `m`. -/
theorem exists_block_index {j m n : ℕ} (hj : j ≤ (n + 1) * m) :
    ∃ i ≤ n, i * m ≤ j ∧ j ≤ i * m + m := by
  induction n with
  | zero => exact ⟨0, le_rfl, by simp, by simpa using hj⟩
  | succ n ih =>
    by_cases h : j ≤ (n + 1) * m
    · obtain ⟨i, hi, h₁, h₂⟩ := ih h
      exact ⟨i, Nat.le_succ_of_le hi, h₁, h₂⟩
    · exact ⟨n + 1, le_rfl, (not_le.1 h).le,
        le_trans hj (le_of_eq (by ring))⟩

/-! ## Part 7: `thm:arc-complement`

The blueprint's proof, in its own order.  The two hypotheses `hce` and `hcen` are the two halves
of the descent step of `lem:outer-chain`, quoted verbatim from `Schoenflies/OuterChain.lean`;
`h2c` is the 2-connectivity of one subdivided square, discussed at `SquaresTwoConnected`. -/

/-- **The heart of `thm:arc-complement`**: two points off a simple arc lie in a common open
connected set missing the arc — the outer face of the chain of small squares along the arc. -/
theorem exists_face_of_notMem_arc {A : Set Plane} (hA : IsArc A) (h2c : SquaresTwoConnected)
    {u w : Plane} (hu : u ∉ A) (hw : w ∉ A) :
    ∃ F : Set Plane, IsOpen F ∧ IsConnected F ∧ u ∈ F ∧ w ∈ F ∧ Disjoint F A := by
  obtain ⟨α, hα, hinj, rfl⟩ := hA
  have hAc : IsCompact (α '' I) := isCompact_image_of_subset_I hα subset_rfl isCompact_I.isClosed
  -- **Step 1.** `d > 0` with both points at sup-distance more than `4d` from the arc.
  have hpair : IsCompact ({u, w} : Set Plane) :=
    ((Set.finite_singleton w).insert u).isCompact
  have hdisj : Disjoint ({u, w} : Set Plane) (α '' I) := by
    rw [Set.disjoint_left]
    intro z hz hzA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    exacts [hu hzA, hw hzA]
  obtain ⟨ρ, hρ, hbound⟩ := Plane.exists_dist_pos hpair hAc hdisj
  set d : ℝ := ρ / 8 with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  have hfar4 : ∀ z ∈ ({u, w} : Set Plane), ∀ y ∈ α '' I, 4 * d < Plane.supDist z y := by
    intro z hz y hy
    have hlt := lt_supDist_of_le_dist hρ (hbound z hz y hy)
    rw [hd_def]; linarith
  -- **Step 2.** The coarse partition, into `K = 3·m₁ ≥ 3` cells of diameter less than `d`.
  obtain ⟨m₁, hm₁, hmesh₁⟩ := exists_mesh hα hd 3 (by norm_num)
  obtain ⟨n, hK⟩ : ∃ n, 3 * m₁ = n + 1 := ⟨3 * m₁ - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  rw [hK] at hmesh₁
  -- **Step 3.** `δ = min(d, d')`, the second the separation of nonadjacent coarse subarcs.
  obtain ⟨ρ', hρ', hsep⟩ := exists_pos_dist_nonadjacent hα hinj (n := n + 1)
  set δ : ℝ := min d ρ' with hδ_def
  have hδ : 0 < δ := lt_min hd hρ'
  have hδd : δ ≤ d := min_le_left _ _
  have hδρ : δ ≤ ρ' := min_le_right _ _
  -- **Step 4.** The fine partition, refining the coarse one, of mesh less than `δ/4`.
  obtain ⟨m, hm, hmesh₂⟩ := exists_mesh hα (by linarith : (0 : ℝ) < δ / 4) (n + 1) (by omega)
  -- **Step 5.** The squares of radius `δ/4` about the fine samples, overlaid all at once.
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Plane, ∀ j, c j = α (sample ((n + 1) * m) j) := ⟨_, fun _ => rfl⟩
  set r : ℝ := δ / 4 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  -- Consecutive centres are closer than one radius.
  have hstep : ∀ q < (n + 1) * m, Plane.supDist (c q) (c (q + 1)) < r := by
    intro q hq
    have hmem : sample ((n + 1) * m) (q + 1) ∈
        Icc (sample ((n + 1) * m) q) (sample ((n + 1) * m) (q + 1)) :=
      ⟨sample_mono (Nat.le_succ q), le_rfl⟩
    have hlt := hmesh₂ q hq _ hmem
    rw [Plane.supDist_comm, hc, hc]
    exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) hlt
  -- A fine sample of the `p`-th block lies on the `p`-th coarse subarc.
  have hcell : ∀ p j, p * m ≤ j → j ≤ p * m + m → c j ∈ subarcCell α (n + 1) p := by
    intro p j h₁ h₂
    refine ⟨sample ((n + 1) * m) j, sample_mem_Icc_of_block hm h₁ ?_, (hc j).symm⟩
    calc j ≤ p * m + m := h₂
      _ = (p + 1) * m := by ring
  -- Centres of nonconsecutive links are more than two radii apart.
  have hfarblock : ∀ p q, p ≤ n → q ≤ n → p + 1 < q →
      ∀ j, p * m ≤ j → j ≤ p * m + m → ∀ j', q * m ≤ j' → j' ≤ q * m + m →
        2 * r < Plane.supDist (c j) (c j') := by
    intro p q hp hq hpq j hj hj' k hk hk'
    have hdist := hsep p (by omega) q (by omega) (by omega) _ (hcell p j hj hj')
      _ (hcell q k hk hk')
    have hlt := lt_supDist_of_le_dist hρ' hdist
    rw [hr_def]; linarith
  -- **Step 6.** The chain is a plane chain.
  have hchain := isPlaneChain_familyChain (c := c) (N := (n + 1) * m) (m := m) (r := r) (n := n)
    h2c hr hn (le_of_eq (by ring)) hstep hfarblock
  -- **Step 7.** Each consecutive pair sits in the square of radius `3d` about its first centre.
  have hcpm : ∀ p, c (p * m) = α (sample (n + 1) p) := fun p => by
    rw [hc, sample_mul (k := n + 1) hm]
  have hnear : ∀ p, p + 1 ≤ n → ∀ j, p * m ≤ j → j ≤ p * m + m + m →
      Plane.supDist (c j) (c (p * m)) < 2 * d := by
    intro p hp j h₁ h₂
    -- Membership of a fine sample in a coarse cell, as a distance bound from its base point.
    have base : ∀ q, q < n + 1 → ∀ k, q * m ≤ k → k ≤ q * m + m →
        Plane.supDist (c k) (α (sample (n + 1) q)) < d := by
      intro q hq k hk hk'
      have hmem : sample ((n + 1) * m) k ∈ Icc (sample (n + 1) q) (sample (n + 1) (q + 1)) :=
        sample_mem_Icc_of_block hm hk (by calc k ≤ q * m + m := hk'
          _ = (q + 1) * m := by ring)
      have hlt := hmesh₁ q hq _ hmem
      rw [hc]
      exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) hlt
    by_cases hcase : j ≤ p * m + m
    · have := base p (by omega) j h₁ hcase
      rw [hcpm]; linarith
    · -- `j` is in the next block: go through the shared sample `α(t_{p+1})`.
      have h₁' : (p + 1) * m ≤ j := by
        have : (p + 1) * m = p * m + m := by ring
        omega
      have h₂' : j ≤ (p + 1) * m + m := by
        have : (p + 1) * m = p * m + m := by ring
        omega
      have hA' := base (p + 1) (by omega) j h₁' h₂'
      -- The two consecutive coarse samples are themselves within `d`.
      have hB' : Plane.supDist (α (sample (n + 1) (p + 1))) (α (sample (n + 1) p)) < d := by
        have hmem : sample (n + 1) (p + 1) ∈
            Icc (sample (n + 1) p) (sample (n + 1) (p + 1)) :=
          ⟨sample_mono (Nat.le_succ p), le_rfl⟩
        exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) (hmesh₁ p (by omega) _ hmem)
      have htri := Plane.supDist_triangle (c j) (α (sample (n + 1) (p + 1))) (c (p * m))
      rw [hcpm] at htri ⊢
      linarith
  have hcontain : ∀ p, p + 1 ≤ n → ∀ j, p * m ≤ j → j ≤ p * m + m + m →
      Plane.supDist (c j) (c (p * m)) + r ≤ 3 * d := by
    intro p hp j h₁ h₂
    have := hnear p hp j h₁ h₂
    rw [hr_def]; linarith
  have hxfar : ∀ z ∈ ({u, w} : Set Plane), ∀ p, p + 1 ≤ n →
      3 * d < Plane.supDist z (c (p * m)) := by
    intro z hz p hp
    have hmemA : c (p * m) ∈ α '' I :=
      ⟨sample (n + 1) p, sample_mem_I (by omega), (hcpm p).symm⟩
    have := hfar4 z hz _ hmemA
    linarith
  -- **Step 8.** `lem:outer-chain`.
  have hmemu : u ∈ ({u, w} : Set Plane) := Or.inl rfl
  have hmemw : w ∈ ({u, w} : Set Plane) := Or.inr rfl
  have houtu := outer_face_familyChain hchain
    (outerOnPairs_familyChain hcontain (hxfar u hmemu))
  have houtw := outer_face_familyChain hchain
    (outerOnPairs_familyChain hcontain (hxfar w hmemw))
  let _ : (Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n).Finite :=
    hchain.block_finite (i := 0) (m := n) (by omega)
  have hdraw : Graph.IsDrawing (Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n)
      segmentDrawing := hchain.block_isDrawing (by omega)
  have hface := Graph.unbounded_face_unique hdraw houtw.2 houtu.2
  -- **Step 9.** The outer face misses the arc.
  have hmiss : Disjoint (Graph.face (Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n)
      segmentDrawing u) (α '' I) := by
    rw [Set.disjoint_right]
    intro z hz hzF
    obtain ⟨j, hjr, hzj⟩ := Set.mem_iUnion₂.1
      (image_subset_iUnion_closedSquare (α := α) (n := (n + 1) * m) (by positivity) hmesh₂ hz)
    rw [Finset.mem_range] at hjr
    -- The `j`-th square belongs to one link of the chain, hence to the whole chain.
    obtain ⟨i, hi, h₁, h₂⟩ := exists_block_index (j := j) (n := n) (m := m) (by omega)
    have hle₁ : familySquare c ((n + 1) * m) r j ≤ familyChain c ((n + 1) * m) m r i :=
      Graph.le_chainUnion (G := familyOverlay c ((n + 1) * m) r)
        (fun _ _ _ => familySquare_le) h₁ h₂
    have hle₂ : familyChain c ((n + 1) * m) m r i ≤
        Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n :=
      Graph.le_chainUnion (G := familyOverlay c ((n + 1) * m) r)
        (fun _ _ _ => familyChain_le) (Nat.zero_le _) (by omega)
    have hfrsub : frontier (Plane.closedSquare (c j) r) ⊆
        Graph.pointSet (Graph.chainUnion (familyChain c ((n + 1) * m) m r) 0 n) segmentDrawing := by
      rw [← pointSet_familySquare (c := c) hr (le_of_lt hjr)]
      exact Graph.pointSet_mono (hle₁.trans hle₂)
    have hzj' : Plane.supDist z (c j) ≤ r := by rw [hc]; exact hzj
    rcases lt_or_eq_of_le hzj' with hlt | heq
    · exact notMem_face_of_mem_openSquare hfrsub houtu.2 hlt hzF
    · exact (Graph.face_subset_exterior _ _ _ hzF)
        (hfrsub (by rw [Plane.frontier_closedSquare]; exact heq))
  exact ⟨_, hdraw.isOpen_face u, Graph.isConnected_face houtu.1, Graph.mem_face houtu.1,
    hface ▸ Graph.mem_face houtw.1, hmiss⟩

/-- **`thm:arc-complement`, the polygonal half.**  Two distinct points off a simple arc are
joined, off the arc, by a *simple polygonal* arc.  This is the form `lem:accessible-dense`
consumes; the joining is `lem:polygonal-connected` inside the outer face. -/
theorem exists_simple_poly_compl_arc {A : Set Plane} (hA : IsArc A) (h2c : SquaresTwoConnected)
    {u w : Plane} (huw : u ≠ w) (hu : u ∉ A) (hw : w ∉ A) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P u w ∧ P ⊆ Aᶜ := by
  obtain ⟨F, hFopen, hFconn, huF, hwF, hFA⟩ := exists_face_of_notMem_arc hA h2c hu hw
  obtain ⟨P, hPpoly, hParc, hPsub⟩ :=
    exists_simple_arc_of_polyAccessible hFopen hFconn.isPreconnected huw
      (polyAccessible_of_mem huF) (polyAccessible_of_mem hwF)
  refine ⟨P, hPpoly, hParc, fun z hz => ?_⟩
  by_cases hzuw : z = u ∨ z = w
  · rcases hzuw with rfl | rfl
    exacts [hu, hw]
  · exact Set.disjoint_left.1 hFA (hPsub ⟨hz, by simpa using hzuw⟩)

/-- **`thm:arc-complement`.**  The complement of a simple arc in the plane is connected. -/
theorem isConnected_compl_arc {A : Set Plane} (hA : IsArc A) (h2c : SquaresTwoConnected) :
    IsConnected Aᶜ := by
  refine ⟨?_, isPreconnected_of_forall_pair fun z hz y hy => ?_⟩
  · -- An arc is compact, so it misses the outside of a large square.
    obtain ⟨s, -, hs⟩ := Plane.exists_closedSquare_of_isBounded hA.isCompact.isBounded
    obtain ⟨t, ht⟩ := (Plane.isConnected_beyondSquare s).nonempty
    rw [Plane.beyondSquare_eq_compl] at ht
    exact ⟨t, fun htA => ht (hs htA)⟩
  · obtain ⟨F, -, hFconn, hzF, hyF, hFA⟩ := exists_face_of_notMem_arc hA h2c hz hy
    exact ⟨F, fun v hv => Set.disjoint_left.1 hFA hv, hzF, hyF, hFconn.isPreconnected⟩

end Schoenflies
