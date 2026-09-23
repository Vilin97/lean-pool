/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.GridAttach
public import LeanPool.Schoenflies.SquareCycle

/-!
# The anchored square mesh, closed

`Schoenflies/SquareMesh.lean` builds `Schoenflies.squareMesh δ fresh anchors` and proves the
geometric clauses of `prop:anchored-square-mesh`; `Schoenflies/SquareMeshConnected.lean`,
`Schoenflies/SquareMeshFixed.lean` and `Schoenflies/LocalGrid.lean` add the grid combinatorics,
the outer cycle from an explicit path-subdivision hypothesis, and the degenerate cases. This
module proves that path-subdivision hypothesis for the mesh.

## The hypothesis that is discharged here

`Schoenflies.SubdividesToPath pieces points` says: *the overlay edges lying inside a source
segment are exactly the edges of a path of the overlay from one end of that segment to the
other.* `SquareMeshFixed.lean` states it as an explicit hypothesis, and its docstring says the
theorem does not exist on `main`.

It does exist. `Schoenflies.exists_incWalk_insideEdges` in `Schoenflies/SquareCycle.lean` is
exactly that statement in the vocabulary of `Graph.IsIncWalk` — a walk along which
`dist P.1 ·` strictly increases — and `Graph.IsIncWalk.isPath` turns it into a path. The two
modules were simply never in one import chain: `SquareCycle.lean` was imported only by
`Schoenflies/JordanClosed.lean`. `Schoenflies.subdividesToPath_of_overlay` is the four-line
bridge, allowing the results of `SquareMeshFixed.lean` to be applied directly to the mesh.

## The outer cycle, as data

`Schoenflies.meshGraph_outer_cycle` is existential — its own docstring says *"once that
hypothesis is discharged by a theorem exporting the chain as a `def`, this should be restated
with the cycle as data"*. That is done here: `outerCycleEdge`, `outerCycleStart`,
`outerCycleEnd`, `outerCycleThird` and `outerCycleDetour` are `def`s, and the three clauses
are separate lemmas about them. A consumer needing the outer cycle of the mesh takes these
five names, not an `∃` it has to destructure at every use.

## Clause 5, and the hypothesis that is actually true

Clause 5 — *the skeleton of `T` is 2-connected* — was absent from every earlier module, and for
a good reason: it is **false** for `Schoenflies.squareMesh δ fresh anchors` when `fresh` has
fewer than two distinct points (`Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton`),
and `Schoenflies.FreshDense fresh δ` alone does not repair it
(`Schoenflies.freshDense_not_isTwoConnected`). What repairs it is `FreshDense fresh δ` together
with `δ < 4`, which forces two distinct fresh points
(`Schoenflies.exists_two_distinct_fresh_of_freshDense`). The blueprint's caller uses
`δ = ε_n = 2⁻ⁿ`, far below `4`, so the hypothesis is free at the only call site.

The assembly is the blueprint's, with one correction. The blueprint says *"adding these finitely
many cycles one at a time"*, but the **first** addition cannot be a cycle: distinct rings of the
mesh are disjoint, so no two of them share the two vertices `lem:union-two-connected` needs. The
first addition is an **ear** — down the spoke at `z`, round the inner ring, back up the spoke at
`w` — and that is precisely where the two distinct fresh points are spent. After it, every
further ring shares the crossing points `r • z ≠ r • w` with the spokes and goes in by
`lem:union-two-connected`, and every further spoke is an ear between the outer and inner rings.
`Graph.IsTwoConnected.of_le_of_vertexSet_subset` then transfers 2-connectivity from the assembly
to the mesh, since every mesh vertex lies on a ring or on a spoke.

## The proposition, clause by clause

`prop:anchored-square-mesh` is exported as **data with its clauses as separate lemmas**: the
object is the `def` `Schoenflies.squareMesh δ fresh anchors`, and nothing is `∃`-packaged.

1. every 2-cell has diameter `< δ` — `Schoenflies.squareMesh_face_small`;
2. every anchor on `S` is a boundary vertex — `Schoenflies.squareMesh_anchor_mem_vertexSet`;
3. every new internal edge meeting `S` ends at a fresh point —
   `Schoenflies.squareMesh_inner_edge_at_fresh`;
4. exactly one such edge at each fresh point — `Schoenflies.squareMesh_unique_inner_edge`;
5. the skeleton is 2-connected — **`Schoenflies.squareMesh_isTwoConnected`** (this module);
6. `|T| ∖ S` is connected — `Schoenflies.squareMesh_isConnected_diff`.

and the outer cycle, which `def:admissible-graph` and every downstream consumer need as a
genuine cycle rather than a point set — `Schoenflies.squareMesh_isLongCycle_outerCycle`,
`Schoenflies.squareMesh_outerCycle_edgesCover` (this module).

## Blueprint

* `subdividesToPath_of_overlay`, `meshSubdividesToPath` — `lem:polygonal-overlay`: the
  subdivision of one source segment is a path of the overlay. This discharges
  `Schoenflies.SubdividesToPath`.
* `meshGraph_outer_cycle_of_mem_modelCurve`, `squareMesh_outer_cycle` —
  `prop:anchored-square-mesh` clause 3 as a **cycle**, with no hypothesis beyond `fresh ⊆ S`.
* `outerCycleEdge`, `outerCycleStart`, `outerCycleEnd`, `outerCycleThird`, `outerCycleDetour`,
  `squareMesh_isLongCycle_outerCycle`, `squareMesh_outerCycle_subset_modelCurve`,
  `squareMesh_outerCycle_edgesCover` — the same cycle as data with its clauses as lemmas.
* `rsideT`/`rsideL`/`rsideB`/`rsideR` and `meshGraph_ring_cycle` — the outer-cycle argument at
  every radius: each ring of the mesh is a long cycle occupying exactly that ring.
* `ringGraph`, `ringGraph_isTwoConnected`, `mem_vertexSet_ringGraph` — each ring as a named
  2-connected subgraph, via `Schoenflies.squareGraph` at centre `0`.
* `spokePiece_inter_ringSet`, `smul_mem_meshPoints`, `smul_mem_vertexSet_ringGraph` —
  the crossing points `r • z` as vertices, from the `MeetsAreCut` clause of `meshPoints`.
* `spokeWalk`, `spokeGraph` — each spoke as a path of the mesh.
* `meshEar`, `meshEar_isPath`, `meshCore_isTwoConnected` — `lem:subdivision-ear-preserve` (b):
  the ear that joins the outer ring to the inner one.
* `attachRings`, `attachSpokes` and their 2-connectivity — `lem:union-two-connected` and
  `lem:subdivision-ear-preserve` iterated, the blueprint's *"adding these finitely many cycles
  one at a time"*.
* `meshGraph_isTwoConnected`, `squareMesh_isTwoConnected` — `prop:anchored-square-mesh`
  clause 5.
-/

@[expose] public section

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### `SubdividesToPath` is a theorem

The membership clause of `Schoenflies.SubdividesToPath` and the membership clause of
`Schoenflies.insideEdges` are the same statement: `Q ∈ E(overlayGraph pieces points)` unfolds
to `Q ∈ overlayPieces pieces points` by `Iff.rfl`. So the only work is to turn the increasing
walk into a path, which `Graph.IsIncWalk.isPath` does. -/

/-- **The subdivision of a source segment is a path of the overlay.** This is
`Schoenflies.SubdividesToPath`, the hypothesis `Schoenflies/SquareMeshFixed.lean` carries
through all of its results, proved from `Schoenflies.exists_incWalk_insideEdges`. -/
theorem subdividesToPath_of_overlay {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) : SubdividesToPath pieces points := by
  intro P hP hPnd
  obtain ⟨W, hW, hinc⟩ := exists_incWalk_insideEdges hnd hEnds hMeets hP hPnd
  exact ⟨W, hinc.isPath, hW⟩

/-- The mesh's own instance of `Schoenflies.SubdividesToPath`. -/
theorem meshSubdividesToPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    SubdividesToPath (meshSegments N fresh) (meshPoints N fresh anchors) :=
  subdividesToPath_of_overlay (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)

/-! ### The outer cycle, with no hypothesis -/

/-- **Clause 3 as a cycle**, for `meshGraph`. -/
theorem meshGraph_outer_cycle_of_mem_modelCurve {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (meshGraph N fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  meshGraph_outer_cycle hN hfresh anchors (meshSubdividesToPath hN hfresh anchors)

/-- **Clause 3 as a cycle**, for `squareMesh`. -/
theorem squareMesh_outer_cycle {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (squareMesh δ fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  squareMesh_outer_cycle_of_subdividesToPath hfresh δ anchors
    (meshSubdividesToPath (two_le_meshCount δ) hfresh anchors)

/-- The mesh has a 2-connected outer-cycle subgraph. -/
theorem exists_squareMesh_outerCycleGraph_isTwoConnected {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ∃ (e : Piece) (u : Plane) (D : List Piece),
      ((squareMesh δ fresh anchors).cycleGraph u e D).IsTwoConnected ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  squareMesh_outer_cycleGraph_isTwoConnected_of_subdividesToPath hfresh δ anchors
    (meshSubdividesToPath (two_le_meshCount δ) hfresh anchors)

/-! ### The outer cycle as data

Five `def`s and three lemmas, replacing the five-fold existential above. The `dite` is what
makes the definition total: the hypothesis `fresh ⊆ S` is not available inside a `def`, so the
data is junk when it fails and the lemmas carry the hypothesis. -/

open scoped Classical in
/-- The outer cycle of the mesh, as a tuple `(e, u, v, w, D)`: the distinguished edge, its two
ends, the third vertex, and the detour. Junk when `fresh ⊄ S`. -/
noncomputable def outerCycleData (δ : ℝ) (fresh anchors : List Plane) :
    Piece × Plane × Plane × Plane × List Piece :=
  if h : ∃ t : Piece × Plane × Plane × Plane × List Piece,
      (squareMesh δ fresh anchors).IsLongCycle t.1 t.2.1 t.2.2.1 t.2.2.2.2 t.2.2.2.1 ∧
        (∀ Q ∈ t.1 :: t.2.2.2.2, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (t.1 :: t.2.2.2.2) = modelCurve
    then h.choose else ((0, 0), 0, 0, 0, [])

/-- The distinguished edge of the outer cycle. -/
noncomputable def outerCycleEdge (δ : ℝ) (fresh anchors : List Plane) : Piece :=
  (outerCycleData δ fresh anchors).1

/-- The vertex the outer cycle starts at: one end of `outerCycleEdge`. -/
noncomputable def outerCycleStart (δ : ℝ) (fresh anchors : List Plane) : Plane :=
  (outerCycleData δ fresh anchors).2.1

/-- The other end of `outerCycleEdge`, where the detour ends. -/
noncomputable def outerCycleEnd (δ : ℝ) (fresh anchors : List Plane) : Plane :=
  (outerCycleData δ fresh anchors).2.2.1

/-- A third vertex of the outer cycle, distinct from its two named ones: this is what makes the
cycle *long*, hence 2-connected. -/
noncomputable def outerCycleThird (δ : ℝ) (fresh anchors : List Plane) : Plane :=
  (outerCycleData δ fresh anchors).2.2.2.1

/-- The detour of the outer cycle: the path from `outerCycleStart` to `outerCycleEnd` avoiding
`outerCycleEdge`. -/
noncomputable def outerCycleDetour (δ : ℝ) (fresh anchors : List Plane) : List Piece :=
  (outerCycleData δ fresh anchors).2.2.2.2

theorem outerCycleData_spec {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane) :
    (squareMesh δ fresh anchors).IsLongCycle (outerCycleEdge δ fresh anchors)
        (outerCycleStart δ fresh anchors) (outerCycleEnd δ fresh anchors)
        (outerCycleDetour δ fresh anchors) (outerCycleThird δ fresh anchors) ∧
      (∀ Q ∈ outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors,
        Q.seg ⊆ modelCurve) ∧
      Graph.edgesCover segmentDrawing
        (outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors) = modelCurve := by
  classical
  have h : ∃ t : Piece × Plane × Plane × Plane × List Piece,
      (squareMesh δ fresh anchors).IsLongCycle t.1 t.2.1 t.2.2.1 t.2.2.2.2 t.2.2.2.1 ∧
        (∀ Q ∈ t.1 :: t.2.2.2.2, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (t.1 :: t.2.2.2.2) = modelCurve := by
    obtain ⟨e, u, v, x, D, h₁, h₂, h₃⟩ := squareMesh_outer_cycle hfresh δ anchors
    exact ⟨(e, u, v, x, D), h₁, h₂, h₃⟩
  have hd : outerCycleData δ fresh anchors = h.choose := dite_eq_left h
  simpa [outerCycleEdge, outerCycleStart, outerCycleEnd, outerCycleThird, outerCycleDetour, hd]
    using h.choose_spec

/-- **Clause 3, as data.** The edge, the two ends, the third vertex and the detour form a long
cycle of the mesh. -/
theorem squareMesh_isLongCycle_outerCycle {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    (squareMesh δ fresh anchors).IsLongCycle (outerCycleEdge δ fresh anchors)
      (outerCycleStart δ fresh anchors) (outerCycleEnd δ fresh anchors)
      (outerCycleDetour δ fresh anchors) (outerCycleThird δ fresh anchors) :=
  (outerCycleData_spec hfresh δ anchors).1

/-- Every edge of the outer cycle lies on `S`. -/
theorem squareMesh_outerCycle_subset_modelCurve {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ∀ Q ∈ outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors,
      Q.seg ⊆ modelCurve :=
  (outerCycleData_spec hfresh δ anchors).2.1

/-- The outer cycle occupies exactly `S`. -/
theorem squareMesh_outerCycle_edgesCover {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    Graph.edgesCover segmentDrawing
      (outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors) = modelCurve :=
  (outerCycleData_spec hfresh δ anchors).2.2

/-- The outer cycle, as a subgraph, is 2-connected. -/
theorem squareMesh_outerCycleGraph_isTwoConnected {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ((squareMesh δ fresh anchors).cycleGraph (outerCycleStart δ fresh anchors)
      (outerCycleEdge δ fresh anchors) (outerCycleDetour δ fresh anchors)).IsTwoConnected :=
  (squareMesh_isLongCycle_outerCycle hfresh δ anchors).isTwoConnected

/-! ### The four sides of a ring of arbitrary radius

`Schoenflies/SquareMeshFixed.lean` names the four sides of the *outer* ring — `sideT`, `sideL`,
`sideB`, `sideR` — and proves the handful of coordinate facts that the outer-cycle argument
runs on. Every inner ring needs the same facts, so they are restated here with the radius as a
parameter; `rsideT 1 = sideT` and so on, definitionally. -/

/-- The top side of the ring of radius `r`, from the north-east corner to the north-west one. -/
def rsideT (r : ℝ) : Piece := (Plane.mk r r, Plane.mk (-r) r)

/-- The left side of the ring of radius `r`, from north-west to south-west. -/
def rsideL (r : ℝ) : Piece := (Plane.mk (-r) r, Plane.mk (-r) (-r))

/-- The bottom side of the ring of radius `r`, from south-west to south-east. -/
def rsideB (r : ℝ) : Piece := (Plane.mk (-r) (-r), Plane.mk r (-r))

/-- The right side of the ring of radius `r`, from south-east back to north-east. -/
def rsideR (r : ℝ) : Piece := (Plane.mk r (-r), Plane.mk r r)

theorem rsideT_one : rsideT 1 = sideT := rfl
theorem rsideL_one : rsideL 1 = sideL := rfl
theorem rsideB_one : rsideB 1 = sideB := rfl
theorem rsideR_one : rsideR 1 = sideR := rfl

theorem rsideT_mem_ringPieces (r : ℝ) : rsideT r ∈ ringPieces r := by
  simp [ringPieces, rsideT]

theorem rsideL_mem_ringPieces (r : ℝ) : rsideL r ∈ ringPieces r := by
  simp [ringPieces, rsideL]

theorem rsideB_mem_ringPieces (r : ℝ) : rsideB r ∈ ringPieces r := by
  simp [ringPieces, rsideB]

theorem rsideR_mem_ringPieces (r : ℝ) : rsideR r ∈ ringPieces r := by
  simp [ringPieces, rsideR]

theorem mem_rsideT {r : ℝ} {x : Plane} (h : x ∈ (rsideT r).seg) : x 1 = r :=
  (mem_segment_horiz.1 h).1

theorem mem_rsideB {r : ℝ} {x : Plane} (h : x ∈ (rsideB r).seg) : x 1 = -r :=
  (mem_segment_horiz.1 h).1

theorem mem_rsideL {r : ℝ} {x : Plane} (h : x ∈ (rsideL r).seg) : x 0 = -r :=
  (mem_segment_vert.1 h).1

theorem mem_rsideR {r : ℝ} {x : Plane} (h : x ∈ (rsideR r).seg) : x 0 = r :=
  (mem_segment_vert.1 h).1

theorem rsideT_inter_rsideL {r : ℝ} {x : Plane} (h : x ∈ (rsideT r).seg)
    (h' : x ∈ (rsideL r).seg) : x = Plane.mk (-r) r :=
  plane_eq_of_coords (by rw [mem_rsideL h', Plane.mk_zero]) (by rw [mem_rsideT h, Plane.mk_one])

theorem rsideL_inter_rsideB {r : ℝ} {x : Plane} (h : x ∈ (rsideL r).seg)
    (h' : x ∈ (rsideB r).seg) : x = Plane.mk (-r) (-r) :=
  plane_eq_of_coords (by rw [mem_rsideL h, Plane.mk_zero]) (by rw [mem_rsideB h', Plane.mk_one])

theorem rsideB_inter_rsideR {r : ℝ} {x : Plane} (h : x ∈ (rsideB r).seg)
    (h' : x ∈ (rsideR r).seg) : x = Plane.mk r (-r) :=
  plane_eq_of_coords (by rw [mem_rsideR h', Plane.mk_zero]) (by rw [mem_rsideB h, Plane.mk_one])

theorem rsideT_inter_rsideR {r : ℝ} {x : Plane} (h : x ∈ (rsideT r).seg)
    (h' : x ∈ (rsideR r).seg) : x = Plane.mk r r :=
  plane_eq_of_coords (by rw [mem_rsideR h', Plane.mk_zero]) (by rw [mem_rsideT h, Plane.mk_one])

theorem rsideT_disjoint_rsideB {r : ℝ} (hr : 0 < r) {x : Plane} (h : x ∈ (rsideT r).seg)
    (h' : x ∈ (rsideB r).seg) : False := by
  have := (mem_rsideT h).symm.trans (mem_rsideB h'); linarith

theorem rsideL_disjoint_rsideR {r : ℝ} (hr : 0 < r) {x : Plane} (h : x ∈ (rsideL r).seg)
    (h' : x ∈ (rsideR r).seg) : False := by
  have := (mem_rsideL h).symm.trans (mem_rsideR h'); linarith

/-- The four sides of the ring of radius `r` occupy that ring. -/
theorem rsides_cover {r : ℝ} (hr : 0 ≤ r) :
    (rsideT r).seg ∪ (rsideL r).seg ∪ (rsideB r).seg ∪ (rsideR r).seg = ringSet r := by
  rw [← cover_ringPieces hr]
  simp only [ringPieces, cover_cons, cover_nil, Set.union_empty, rsideT, rsideL, rsideB, rsideR]
  ext z
  simp only [Set.mem_union]
  tauto

theorem rside_seg_subset_ringSet {r : ℝ} (hr : 0 ≤ r) {P : Piece}
    (h : P = rsideT r ∨ P = rsideL r ∨ P = rsideB r ∨ P = rsideR r) : P.seg ⊆ ringSet r := by
  rw [← rsides_cover hr]
  rcases h with rfl | rfl | rfl | rfl
  exacts [fun x hx => Or.inl (Or.inl (Or.inl hx)), fun x hx => Or.inl (Or.inl (Or.inr hx)),
    fun x hx => Or.inl (Or.inr hx), fun x hx => Or.inr hx]

/-- Every side of every ring of the mesh is a mesh segment. -/
theorem ring_ringPieces_mem {N : ℕ} {fresh : List Plane} {r : ℝ} (hr : r ∈ meshRadii N)
    {R : Piece} (hR : R ∈ ringPieces r) : R ∈ meshSegments N fresh :=
  mem_meshSegments.2 (Or.inl ⟨r, hr, hR⟩)

/-! ### Every ring of the mesh is a cycle

`Schoenflies.meshGraph_outer_cycle` proves this for the outer ring, `r = 1`, and every step of
its proof is about the four sides of that ring and nothing else. With the sides of a ring of
arbitrary radius now available, the same argument runs verbatim at every radius: the four sides
are four overlay paths, three concatenations glue them into one path once round the ring, and
the last edge of the fourth is peeled off to close the cycle.

This is the theorem the blueprint's *"adding these finitely many cycles one at a time"* needs
for the inner rings, and which `Schoenflies/SquareMeshFixed.lean` names as missing. -/

/-- **Every ring of the mesh is a long cycle of the mesh graph**, and its edges occupy exactly
that ring.

For `r = 1` this is `Schoenflies.meshGraph_outer_cycle`; the content added here is that the
statement holds at every radius of `Schoenflies.meshRadii`, which is what the assembly of
clause 5 of `prop:anchored-square-mesh` consumes. -/
theorem meshGraph_ring_cycle {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) {r : ℝ}
    (hr : r ∈ meshRadii N) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (meshGraph N fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ ringSet r) ∧
        Graph.edgesCover segmentDrawing (e :: D) = ringSet r := by
  have hrpos : 0 < r := meshRadii_pos hN hr
  have hsub : SubdividesToPath (meshSegments N fresh) (meshPoints N fresh anchors) :=
    meshSubdividesToPath hN hfresh anchors
  have hmemT := ring_ringPieces_mem (fresh := fresh) hr (rsideT_mem_ringPieces r)
  have hmemL := ring_ringPieces_mem (fresh := fresh) hr (rsideL_mem_ringPieces r)
  have hmemB := ring_ringPieces_mem (fresh := fresh) hr (rsideB_mem_ringPieces r)
  have hmemR := ring_ringPieces_mem (fresh := fresh) hr (rsideR_mem_ringPieces r)
  obtain ⟨WT, hpT, hcT⟩ := hsub _ hmemT (ringPieces_nondeg hrpos _ (rsideT_mem_ringPieces r))
  obtain ⟨WL, hpL, hcL⟩ := hsub _ hmemL (ringPieces_nondeg hrpos _ (rsideL_mem_ringPieces r))
  obtain ⟨WB, hpB, hcB⟩ := hsub _ hmemB (ringPieces_nondeg hrpos _ (rsideB_mem_ringPieces r))
  obtain ⟨WR, hpR, hcR⟩ := hsub _ hmemR (ringPieces_nondeg hrpos _ (rsideR_mem_ringPieces r))
  have hsegT : ∀ Q ∈ WT, Q.seg ⊆ (rsideT r).seg := fun Q hQ => ((hcT Q).1 hQ).2
  have hsegL : ∀ Q ∈ WL, Q.seg ⊆ (rsideL r).seg := fun Q hQ => ((hcL Q).1 hQ).2
  have hsegB : ∀ Q ∈ WB, Q.seg ⊆ (rsideB r).seg := fun Q hQ => ((hcB Q).1 hQ).2
  have hsegR : ∀ Q ∈ WR, Q.seg ⊆ (rsideR r).seg := fun Q hQ => ((hcR Q).1 hQ).2
  -- the vertices each side path visits stay on that side
  have hVT : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideT r).1 WT,
      x ∈ (rsideT r).seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegT hx
  have hVL : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideL r).1 WL,
      x ∈ (rsideL r).seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegL hx
  have hVB : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideB r).1 WB,
      x ∈ (rsideB r).seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegB hx
  -- top, then left
  have hp1 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      (rsideT r).1 (WT ++ WL) (rsideL r).2 :=
    hpT.append_of_disjoint hpL fun x hx hx2 => rsideT_inter_rsideL (hVT x hx) (hVL x hx2)
  have hV1 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      (rsideT r).1 (WT ++ WL), x ∈ (rsideT r).seg ∪ (rsideL r).seg := by
    refine fun x hx => walkVertices_subset_of_edges (Or.inl (left_mem_segment ℝ _ _))
      (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    exacts [(hsegT Q h).trans Set.subset_union_left, (hsegL Q h).trans Set.subset_union_right]
  -- … then the bottom
  have hp2 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      (rsideT r).1 ((WT ++ WL) ++ WB) (rsideB r).2 := by
    refine hp1.append_of_disjoint hpB fun x hx hx2 => ?_
    rcases hV1 x hx with h | h
    · exact absurd (rsideT_disjoint_rsideB hrpos h (hVB x hx2)) not_false
    · exact rsideL_inter_rsideB h (hVB x hx2)
  have hV2 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      (rsideT r).1 ((WT ++ WL) ++ WB),
      x ∈ (rsideT r).seg ∪ (rsideL r).seg ∪ (rsideB r).seg := by
    refine fun x hx => walkVertices_subset_of_edges
      (Or.inl (Or.inl (left_mem_segment ℝ _ _))) (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    · rcases List.mem_append.1 h with h' | h'
      exacts [(hsegT Q h').trans (Set.subset_union_left.trans Set.subset_union_left),
        (hsegL Q h').trans (Set.subset_union_right.trans Set.subset_union_left)]
    · exact (hsegB Q h).trans Set.subset_union_right
  -- the right side, read backwards, so that its last edge is its first step
  have hRne : (rsideR r).1 ≠ (rsideR r).2 := ringPieces_nondeg hrpos _ (rsideR_mem_ringPieces r)
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
  have hwR : w ∈ (rsideR r).seg := by
    rcases hlink.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [hsegR eR heRmem (right_mem_segment ℝ _ _),
      hsegR eR heRmem (left_mem_segment ℝ _ _)]
  have hVRtail : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices w L, x ∈ (rsideR r).seg := fun x hx =>
    walkVertices_subset_of_edges hwR (fun Q hQ => hsegR Q (hLmem Q hQ)) hx
  have hrevV : (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices (rsideB r).2 L.reverse
      = (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices w L :=
    htail.isWalk.reverse_walkVertices
  -- the fourth append: what is left of the right side, from the south-east corner
  have hp3 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      (rsideT r).1 (((WT ++ WL) ++ WB) ++ L.reverse) w := by
    refine hp2.append_of_disjoint htail.reverse fun x hx hx2 => ?_
    rw [hrevV] at hx2
    have hxR : x ∈ (rsideR r).seg := hVRtail x hx2
    rcases hV2 x hx with (h | h) | h
    · refine absurd (show (rsideR r).2 ∈ (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices w L from ?_) hfr
      rwa [show (rsideR r).2 = x from (rsideT_inter_rsideR h hxR).symm]
    · exact absurd (rsideL_disjoint_rsideR hrpos h hxR) not_false
    · exact rsideB_inter_rsideR h hxR
  -- the closing edge is not one of the others
  have hnondegR : eR.Nondeg :=
    meshGraph_edge_nondeg (anchors := anchors) hN hfresh ((hcR eR).1 heRmem).1
  have hnotT : eR ∉ WT := fun hmem => hnondegR (by
    have h1 := rsideT_inter_rsideR (hsegT eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := rsideT_inter_rsideR (hsegT eR hmem (right_mem_segment ℝ _ _))
      (hsegR eR heRmem (right_mem_segment ℝ _ _))
    exact h1.trans h2.symm)
  have hnotL : eR ∉ WL := fun hmem =>
    rsideL_disjoint_rsideR hrpos (hsegL eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
  have hnotB : eR ∉ WB := fun hmem => hnondegR (by
    have h1 := rsideB_inter_rsideR (hsegB eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := rsideB_inter_rsideR (hsegB eR hmem (right_mem_segment ℝ _ _))
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
  -- every edge of the cycle lies on the ring
  have hmT : (rsideT r).seg ⊆ ringSet r := rside_seg_subset_ringSet hrpos.le (Or.inl rfl)
  have hmL : (rsideL r).seg ⊆ ringSet r :=
    rside_seg_subset_ringSet hrpos.le (Or.inr (Or.inl rfl))
  have hmB : (rsideB r).seg ⊆ ringSet r :=
    rside_seg_subset_ringSet hrpos.le (Or.inr (Or.inr (Or.inl rfl)))
  have hmR : (rsideR r).seg ⊆ ringSet r :=
    rside_seg_subset_ringSet hrpos.le (Or.inr (Or.inr (Or.inr rfl)))
  have hsegsAll : ∀ Q ∈ eR :: (((WT ++ WL) ++ WB) ++ L.reverse), Q.seg ⊆ ringSet r := by
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
  have hthird : (rsideT r).2 ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideT r).1
        (((WT ++ WL) ++ WB) ++ L.reverse) :=
    Graph.walkVertices_mono
      (List.Subset.trans (List.subset_append_left _ _)
        (List.Subset.trans (List.subset_append_left _ _) (List.subset_append_left _ _)))
      hpT.isWalk.target_mem_walkVertices
  have hne₁ : (rsideT r).2 ≠ (rsideT r).1 :=
    mk_ne_mk_of_fst (by intro h; linarith)
  have hne₂ : (rsideT r).2 ≠ w := by
    intro h
    have hw := mem_rsideR (h ▸ hwR)
    rw [rsideT, Plane.mk_zero] at hw
    linarith
  refine ⟨eR, (rsideT r).1, w, (rsideT r).2, ((WT ++ WL) ++ WB) ++ L.reverse,
    ⟨⟨hlink, hp3, hnotD⟩, hthird, hne₁, hne₂⟩, hsegsAll, ?_⟩
  have hcovT : Graph.edgesCover segmentDrawing WT = (rsideT r).seg := edgesCover_eq_seg hmemT hcT
  have hcovL : Graph.edgesCover segmentDrawing WL = (rsideL r).seg := edgesCover_eq_seg hmemL hcL
  have hcovB : Graph.edgesCover segmentDrawing WB = (rsideB r).seg := edgesCover_eq_seg hmemB hcB
  have hcovR : Graph.edgesCover segmentDrawing WR = (rsideR r).seg := edgesCover_eq_seg hmemR hcR
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
    rw [edgeArc_segmentDrawing] at hzQ
    exact hsegsAll Q hQ hzQ
  · rw [← rsides_cover hrpos.le] at hz
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


/-! ### Each ring of the mesh, as a named 2-connected subgraph

`Schoenflies/SquareCycle.lean` proves that the part of *any* polygonal overlay lying on the
boundary of a square whose four sides are among the overlay's source segments is a long cycle,
and is 2-connected — at any centre and any positive radius. The rings of the mesh are exactly
that, at centre `0`: `squarePieces 0 r` and `ringPieces r` are the same list. So each ring comes
with a name, `ringGraph`, a 2-connectivity proof, and the two membership lemmas the assembly of
clause 5 needs, at no cost. -/

/-- The four sides of the square of radius `r` about the origin are the four sides of the ring
of radius `r`: the two lists are equal, entry for entry. -/
theorem squarePieces_zero (r : ℝ) : squarePieces 0 r = ringPieces r := by
  simp [squarePieces, ringPieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE]

/-- The frontier of the closed square of radius `r` about the origin is the ring of radius
`r`. -/
theorem frontier_closedSquare_zero {r : ℝ} (hr : 0 ≤ r) :
    frontier (Plane.closedSquare 0 r) = ringSet r := by
  rw [← cover_squarePieces 0 hr, squarePieces_zero, cover_ringPieces hr]

/-- **The ring of radius `r` of the mesh, as a subgraph**: the mesh edges lying on that ring. -/
noncomputable def ringGraph (N : ℕ) (fresh anchors : List Plane) (r : ℝ) : Graph Plane Piece :=
  squareGraph (meshSegments N fresh) (meshPoints N fresh anchors) 0 r

theorem ringGraph_le (N : ℕ) (fresh anchors : List Plane) (r : ℝ) :
    ringGraph N fresh anchors r ≤ meshGraph N fresh anchors :=
  squareGraph_le

/-- The sides of the ring of radius `r` are mesh segments, for every radius the mesh uses. -/
theorem squarePieces_zero_subset_meshSegments {N : ℕ} {fresh : List Plane} {r : ℝ}
    (hr : r ∈ meshRadii N) : ∀ P ∈ squarePieces 0 r, P ∈ meshSegments N fresh := by
  rw [squarePieces_zero]
  exact fun P hP => ring_ringPieces_mem hr hP

/-- **Every ring of the mesh is a 2-connected subgraph.** -/
theorem ringGraph_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) {r : ℝ}
    (hr : r ∈ meshRadii N) : (ringGraph N fresh anchors r).IsTwoConnected :=
  squareGraph_isTwoConnected (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)
    (meshRadii_pos hN hr) (squarePieces_zero_subset_meshSegments hr)

/-- **A cut point of the mesh lying on a ring is a vertex of that ring.** This is what makes the
crossing points of the spokes with the rings usable as the shared vertices of
`lem:union-two-connected`. -/
theorem mem_vertexSet_ringGraph {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {r : ℝ}
    (hr : r ∈ meshRadii N) {y : Plane} (hy : y ∈ meshPoints N fresh anchors)
    (hyr : y ∈ ringSet r) : y ∈ V(ringGraph N fresh anchors r) :=
  mem_vertexSet_squareGraph (meshSegments_nondeg hN hfresh) (meshRadii_pos hN hr).le
    (squarePieces_zero_subset_meshSegments hr) hy
    (by rw [frontier_closedSquare_zero (meshRadii_pos hN hr).le]; exact hyr)


/-! ### Where a spoke crosses a ring

`Schoenflies/SquareMeshFixed.lean` records the crossing points `r • z` as the thing its
assembly of clause 5 lacked: *"the crossing points `r • z` as vertices (which needs the
`MeetsAreCut` clause of `meshPoints`)"*. That is what this section supplies. The sup norm is a
faithful coordinate along a spoke (`Schoenflies.supNorm_smul_of_mem_modelCurve`), so a spoke
meets the ring of radius `r` in the single point `r • z`; a singleton meet forces both ends of
the `MeetsAreCut` segment to be that point; and `mem_vertexSet_ringGraph` then makes it a
vertex of the ring. -/

theorem inv_le_of_mem_meshRadii {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ meshRadii N) :
    ((N : ℝ)⁻¹) ≤ r := by
  obtain ⟨j, -, rfl⟩ := mem_meshRadii.1 hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  rw [inv_eq_one_div, div_le_div_iff_of_pos_right hN0]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

/-- **A spoke meets a ring in exactly one point.** -/
theorem spokePiece_inter_ringSet {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve)
    {r : ℝ} (hr : r ∈ meshRadii N) : (spokePiece N z).seg ∩ ringSet r = {r • z} := by
  have hrpos : 0 < r := meshRadii_pos hN hr
  ext x
  rw [spokePiece_seg hN]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hx⟩
    have : t = r := by
      rw [← supNorm_smul_of_mem_modelCurve (le_trans (inv_cast_pos hN).le ht.1) hz]
      exact hx
    simp [this]
  · rintro rfl
    exact ⟨⟨r, ⟨inv_le_of_mem_meshRadii hN hr, meshRadii_le_one hN hr⟩, rfl⟩,
      supNorm_smul_of_mem_modelCurve hrpos.le hz⟩

theorem smul_mem_ringSet {r : ℝ} (hr : 0 ≤ r) {z : Plane} (hz : z ∈ modelCurve) :
    r • z ∈ ringSet r := supNorm_smul_of_mem_modelCurve hr hz

/-- **Every crossing point of a spoke with a ring is a cut point of the mesh.** The meet of the
spoke with the side of the ring through the crossing point is the single point `r • z`, and
`MeetsAreCut` returns a segment with both ends among the cut points; a segment equal to a
singleton has both ends there. -/
theorem smul_mem_meshPoints {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) : r • z ∈ meshPoints N fresh anchors := by
  have hzm : z ∈ modelCurve := hfresh z hz
  have hrpos : 0 < r := meshRadii_pos hN hr
  -- the side of the ring through the crossing point
  have hmemring : r • z ∈ cover (ringPieces r) := by
    rw [cover_ringPieces hrpos.le]; exact smul_mem_ringSet hrpos.le hzm
  obtain ⟨Q, hQ, hxQ⟩ := mem_cover_iff.1 hmemring
  set P : Piece := spokePiece N z with hP
  have hPmem : P ∈ meshSegments N fresh := spokePiece_mem_meshSegments hz
  have hQmem : Q ∈ meshSegments N fresh := ring_ringPieces_mem hr hQ
  have hQring : Q.seg ⊆ ringSet r := ringPieces_seg_subset hrpos.le hQ
  -- the spoke is not a ring side: its two ends have different sup norms
  have hPQ : P ≠ Q := by
    intro h
    have h1 : Plane.supNorm z = r := hQring (h ▸ left_mem_segment ℝ P.1 P.2)
    have h2 : Plane.supNorm (((N : ℝ)⁻¹) • z) = r := hQring (h ▸ right_mem_segment ℝ P.1 P.2)
    rw [supNorm_smul_of_mem_modelCurve (inv_cast_pos hN).le hzm] at h2
    rw [show Plane.supNorm z = 1 from hzm] at h1
    exact absurd (h2.trans h1.symm) (ne_of_lt (inv_cast_lt_one hN))
  -- the meet is the crossing point, and nothing else
  have hmeetsub : meetOf P Q ⊆ {r • z} := by
    rw [← spokePiece_inter_ringSet hN hzm hr]
    exact fun x hx => ⟨hx.1, hQring hx.2⟩
  have hmeetmem : r • z ∈ meetOf P Q :=
    ⟨((spokePiece_inter_ringSet hN hzm hr).symm ▸ rfl : r • z ∈ (spokePiece N z).seg ∩ ringSet r).1,
      hxQ⟩
  obtain ⟨u, v, huv, hu, -⟩ :=
    meshPoints_meetsAreCut N fresh anchors P hPmem Q hQmem hPQ ⟨_, hmeetmem⟩
  have : u = r • z := hmeetsub (huv ▸ left_mem_segment ℝ u v)
  exact this ▸ hu

/-- **The crossing point is a vertex of the ring it lies on.** -/
theorem smul_mem_vertexSet_ringGraph {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) : r • z ∈ V(ringGraph N fresh anchors r) :=
  mem_vertexSet_ringGraph hN hfresh hr (smul_mem_meshPoints hN hfresh anchors hz hr)
    (smul_mem_ringSet (meshRadii_pos hN hr).le (hfresh z hz))

/-- Two distinct fresh points have distinct crossing points on every ring. -/
theorem smul_ne_smul {r : ℝ} (hr : r ≠ 0) {z w : Plane} (hzw : z ≠ w) : r • z ≠ r • w := by
  intro h
  exact hzw (smul_right_injective Plane hr h)


/-! ### The spokes, as paths of the mesh

`Schoenflies.SubdividesToPath` — now a theorem — turns each spoke into a path of the mesh from
its outer end `z` to its inner end `N⁻¹ • z`. The path is exported as data, `spokeWalk`, so
that the assembly can name it; and the crossing points are shown to be among the vertices it
visits, which is what makes each ring attachable at two of them. -/

/-- **A cut point lying on a source segment is a vertex of the path that subdivides it.** The
edges of the path cover the segment, and a cut point is interior to no edge of an overlay, so
it is an *end* of one of them. -/
theorem mem_walkVertices_of_mem_points {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) {P : Piece} (hP : P ∈ pieces) {W : List Piece}
    (hW : ∀ Q, Q ∈ W ↔ (Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ P.seg))
    {q : Plane} (hq : q ∈ points) (hqP : q ∈ P.seg) :
    q ∈ (overlayGraph pieces points).walkVertices P.1 W := by
  have hcov : Graph.edgesCover segmentDrawing W = P.seg := edgesCover_eq_seg hP hW
  rw [← hcov] at hqP
  obtain ⟨Q, hQ, hqQ⟩ := Graph.mem_edgesCover_iff.1 hqP
  rw [edgeArc_segmentDrawing] at hqQ
  have hQmem : Q ∈ overlayPieces pieces points := ((hW Q).1 hQ).1
  have hint : q ∉ Q.interior := overlayPieces_avoids hnd q hq Q hQmem
  have hend : q = Q.1 ∨ q = Q.2 := by
    by_contra hcon
    push Not at hcon
    exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hqQ)
  exact Graph.mem_walkVertices_of_mem_covered
    (Graph.mem_coveredVertices hQ (overlayGraph_inc hQmem hend))

open scoped Classical in
/-- **The subdivision of the spoke at a fresh point, as data**: the list of mesh edges lying
inside `spokePiece N z`, in order from `z` inwards. Junk when `z` is not a fresh point of the
model curve. -/
noncomputable def spokeWalk (N : ℕ) (fresh anchors : List Plane) (z : Plane) : List Piece :=
  if h : ∃ W : List Piece,
      (meshGraph N fresh anchors).IsPath z W (((N : ℝ)⁻¹) • z) ∧
        ∀ Q, Q ∈ W ↔ (Q ∈ E(meshGraph N fresh anchors) ∧ Q.seg ⊆ (spokePiece N z).seg)
    then h.choose else []

theorem spokeWalk_spec {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    (meshGraph N fresh anchors).IsPath z (spokeWalk N fresh anchors z) (((N : ℝ)⁻¹) • z) ∧
      ∀ Q, Q ∈ spokeWalk N fresh anchors z ↔
        (Q ∈ E(meshGraph N fresh anchors) ∧ Q.seg ⊆ (spokePiece N z).seg) := by
  classical
  have h : ∃ W : List Piece,
      (meshGraph N fresh anchors).IsPath z W (((N : ℝ)⁻¹) • z) ∧
        ∀ Q, Q ∈ W ↔ (Q ∈ E(meshGraph N fresh anchors) ∧ Q.seg ⊆ (spokePiece N z).seg) :=
    meshSubdividesToPath hN hfresh anchors _ (spokePiece_mem_meshSegments hz)
      (spokePiece_nondeg hN (hfresh z hz))
  rw [spokeWalk, dite_eq_left h]
  exact h.choose_spec

theorem spokeWalk_isPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    (meshGraph N fresh anchors).IsPath z (spokeWalk N fresh anchors z) (((N : ℝ)⁻¹) • z) :=
  (spokeWalk_spec hN hfresh anchors hz).1

theorem spokeWalk_seg_subset {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {Q : Piece} (hQ : Q ∈ spokeWalk N fresh anchors z) : Q.seg ⊆ (spokePiece N z).seg :=
  (((spokeWalk_spec hN hfresh anchors hz).2 Q).1 hQ).2

/-- **Every crossing point on a spoke is a vertex the spoke's path visits.** -/
theorem smul_mem_walkVertices_spokeWalk {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) :
    r • z ∈ (meshGraph N fresh anchors).walkVertices z (spokeWalk N fresh anchors z) := by
  have hmem : r • z ∈ (spokePiece N z).seg :=
    ((spokePiece_inter_ringSet hN (hfresh z hz) hr).symm.subset rfl).1
  exact mem_walkVertices_of_mem_points (meshSegments_nondeg hN hfresh)
    (spokePiece_mem_meshSegments hz) (spokeWalk_spec hN hfresh anchors hz).2
    (smul_mem_meshPoints hN hfresh anchors hz hr) hmem

/-- Every vertex the spoke's path visits lies on the spoke. -/
theorem walkVertices_spokeWalk_subset {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {x : Plane}
    (hx : x ∈ (meshGraph N fresh anchors).walkVertices z (spokeWalk N fresh anchors z)) :
    x ∈ (spokePiece N z).seg :=
  walkVertices_subset_of_edges (left_mem_segment ℝ _ _)
    (fun _ hQ => spokeWalk_seg_subset hN hfresh anchors hz hQ) hx


/-! ### The core: outer ring, two spokes, inner ring

The blueprint assembles clause 5 by *"adding these finitely many cycles one at a time"*, but
the first addition cannot be a cycle: distinct rings of the mesh are disjoint, so no two of
them share the two vertices `lem:union-two-connected` asks for. What joins them is an **ear** —
a path with both ends on the outer ring — and the only such path runs down one spoke, round
part of the inner ring, and back up another spoke. That is why clause 5 needs **two distinct
fresh points**, and why it is false with fewer
(`Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton`).

Once that ear is in place the inner ring shares the two crossing points `N⁻¹ • z` and
`N⁻¹ • w` with it, and `Graph.IsTwoConnected.union` applies; from then on every further ring
shares `r • z` and `r • w`, and every further spoke is an ear between the outer and inner
rings. -/

/-- **Distinct spokes are disjoint** — the blueprint's *"two radial segments in the annulus can
meet only if they lie on the same ray, and then their endpoints on `S` are equal"*. -/
theorem spokePiece_disjoint {N : ℕ} (hN : 2 ≤ N) {z w : Plane} (hz : z ∈ modelCurve)
    (hw : w ∈ modelCurve) (hzw : z ≠ w) {x : Plane} (hxz : x ∈ (spokePiece N z).seg)
    (hxw : x ∈ (spokePiece N w).seg) : False := by
  rw [spokePiece_seg hN] at hxz hxw
  obtain ⟨t, ht, hxt⟩ := hxz
  obtain ⟨s, hs, hxs⟩ := hxw
  have hxt' : t • z = x := hxt
  have hxs' : s • w = x := hxs
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (inv_cast_pos hN) ht.1
  have hspos : (0 : ℝ) ≤ s := le_trans (inv_cast_pos hN).le hs.1
  have h1 : Plane.supNorm x = t := by
    rw [← hxt']; exact supNorm_smul_of_mem_modelCurve htpos.le hz
  have h2 : Plane.supNorm x = s := by
    rw [← hxs']; exact supNorm_smul_of_mem_modelCurve hspos hw
  rw [show s = t from by rw [← h2, h1]] at hxs'
  exact hzw (smul_right_injective Plane (ne_of_gt htpos) (hxt'.trans hxs'.symm))

theorem ringGraph_edge_seg_subset {N : ℕ} {fresh anchors : List Plane} {r : ℝ} (hr : 0 ≤ r)
    {Q : Piece} (hQ : Q ∈ E(ringGraph N fresh anchors r)) : Q.seg ⊆ ringSet r := by
  rw [← frontier_closedSquare_zero hr]
  exact (mem_edgeSet_squareGraph_iff.1 hQ).2

open scoped Classical in
/-- An arc of the ring of radius `r` between two of its vertices, as data. The ring is
2-connected, hence connected, so such a path exists; *which* of the two arcs is chosen does not
matter — only that it is a path inside the ring. -/
noncomputable def ringArc (N : ℕ) (fresh anchors : List Plane) (r : ℝ) (a b : Plane) :
    List Piece :=
  if h : ∃ P : List Piece, (ringGraph N fresh anchors r).IsPath a P b then h.choose else []

theorem ringArc_isPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {r : ℝ}
    (hr : r ∈ meshRadii N) {a b : Plane} (ha : a ∈ V(ringGraph N fresh anchors r))
    (hb : b ∈ V(ringGraph N fresh anchors r)) :
    (ringGraph N fresh anchors r).IsPath a (ringArc N fresh anchors r a b) b := by
  classical
  have h : ∃ P : List Piece, (ringGraph N fresh anchors r).IsPath a P b :=
    (ringGraph_isTwoConnected hN hfresh anchors hr).connected.exists_isPath ha hb
  rw [ringArc, dite_eq_left h]
  exact h.choose_spec

/-- **The ear**: down the spoke at `z`, round the inner ring, and back up the spoke at `w`. -/
noncomputable def meshEar (N : ℕ) (fresh anchors : List Plane) (z w : Plane) : List Piece :=
  spokeWalk N fresh anchors z ++
    ringArc N fresh anchors ((N : ℝ)⁻¹) (((N : ℝ)⁻¹) • z) (((N : ℝ)⁻¹) • w) ++
    (spokeWalk N fresh anchors w).reverse

theorem meshEar_isPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshGraph N fresh anchors).IsPath z (meshEar N fresh anchors z w) w := by
  set G := meshGraph N fresh anchors with hG
  set rmin : ℝ := ((N : ℝ)⁻¹) with hrmin
  have hrm : rmin ∈ meshRadii N := inv_mem_meshRadii hN
  have hrmpos : 0 < rmin := inv_cast_pos hN
  have hzm : z ∈ modelCurve := hfresh z hz
  have hwm : w ∈ modelCurve := hfresh w hw
  -- the three pieces
  have hP1 : G.IsPath z (spokeWalk N fresh anchors z) (rmin • z) :=
    spokeWalk_isPath hN hfresh anchors hz
  have hP3 : G.IsPath (rmin • w) (spokeWalk N fresh anchors w).reverse w :=
    (spokeWalk_isPath hN hfresh anchors hw).reverse
  have harc := ringArc_isPath hN hfresh anchors hrm
    (smul_mem_vertexSet_ringGraph hN hfresh anchors hz hrm)
    (smul_mem_vertexSet_ringGraph hN hfresh anchors hw hrm)
  have hP2 : G.IsPath (rmin • z) (ringArc N fresh anchors rmin (rmin • z) (rmin • w))
      (rmin • w) := harc.mono (ringGraph_le N fresh anchors rmin)
  -- where each piece's vertices live
  have harcseg : ∀ Q ∈ ringArc N fresh anchors rmin (rmin • z) (rmin • w), Q.seg ⊆ ringSet rmin :=
    fun Q hQ => ringGraph_edge_seg_subset hrmpos.le (harc.isWalk.edgeSet_subset Q hQ)
  have hV2 : ∀ x ∈ G.walkVertices (rmin • z)
      (ringArc N fresh anchors rmin (rmin • z) (rmin • w)), x ∈ ringSet rmin :=
    fun x hx => walkVertices_subset_of_edges (smul_mem_ringSet hrmpos.le hzm) harcseg hx
  have hV3 : ∀ x ∈ G.walkVertices (rmin • w) (spokeWalk N fresh anchors w).reverse,
      x ∈ (spokePiece N w).seg := by
    refine fun x hx => walkVertices_subset_of_edges ?_ (fun Q hQ =>
      spokeWalk_seg_subset hN hfresh anchors hw (List.mem_reverse.1 hQ)) hx
    exact ((spokePiece_inter_ringSet hN hwm hrm).symm.subset rfl).1
  -- first append: the spoke at `z`, then the inner arc, meeting only at `rmin • z`
  have hp1 : G.IsPath z (spokeWalk N fresh anchors z ++
      ringArc N fresh anchors rmin (rmin • z) (rmin • w)) (rmin • w) := by
    refine hP1.append_of_disjoint hP2 fun x hx hx2 => ?_
    have hxs : x ∈ (spokePiece N z).seg :=
      walkVertices_spokeWalk_subset hN hfresh anchors hz hx
    have := (spokePiece_inter_ringSet hN hzm hrm).subset ⟨hxs, hV2 x hx2⟩
    exact this
  have hV1 : ∀ x ∈ G.walkVertices z (spokeWalk N fresh anchors z ++
      ringArc N fresh anchors rmin (rmin • z) (rmin • w)),
      x ∈ (spokePiece N z).seg ∪ ringSet rmin := by
    refine fun x hx => walkVertices_subset_of_edges (Or.inl (left_mem_segment ℝ _ _))
      (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    · exact (spokeWalk_seg_subset hN hfresh anchors hz h).trans Set.subset_union_left
    · exact (harcseg Q h).trans Set.subset_union_right
  -- second append: back up the spoke at `w`, meeting only at `rmin • w`
  refine hp1.append_of_disjoint hP3 fun x hx hx2 => ?_
  have hxw : x ∈ (spokePiece N w).seg := hV3 x hx2
  rcases hV1 x hx with h | h
  · exact absurd (spokePiece_disjoint hN hzm hwm hzw h hxw) not_false
  · exact (spokePiece_inter_ringSet hN hwm hrm).subset ⟨hxw, h⟩


/-! ### The assembly

`meshCore` is the outer ring, the ear, and the inner ring. `attachRings` then adds every ring
by `lem:union-two-connected` at the two crossing points `r • z ≠ r • w`, and `attachSpokes`
adds every remaining spoke by `lem:subdivision-ear-preserve` (b) — its two ends are `u` on the
outer ring and `N⁻¹ • u` on the inner one, both already present. Finally every vertex of the
mesh lies on a ring or on a spoke, so the assembled graph spans the mesh and
`Graph.IsTwoConnected.of_le_of_vertexSet_subset` transfers 2-connectivity to the mesh itself. -/

/-- The spoke at `u`, as a subgraph of the mesh. -/
noncomputable def spokeGraph (N : ℕ) (fresh anchors : List Plane) (u : Plane) :
    Graph Plane Piece :=
  (meshGraph N fresh anchors).pathGraphOf u (spokeWalk N fresh anchors u)

theorem spokeGraph_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {u : Plane} (hu : u ∈ fresh) :
    spokeGraph N fresh anchors u ≤ meshGraph N fresh anchors :=
  Graph.pathGraphOf_le (spokeWalk_isPath hN hfresh anchors hu).isWalk

/-- A crossing point on a ring other than the outer one is not the fresh point itself. -/
theorem smul_ne_self {N : ℕ} (hN : 2 ≤ N) {u : Plane} (hu : u ∈ modelCurve) {r : ℝ}
    (hr : r ∈ meshRadii N) (hr1 : r ≠ 1) : r • u ≠ u := by
  intro h
  have h1 : Plane.supNorm (r • u) = r :=
    supNorm_smul_of_mem_modelCurve (meshRadii_pos hN hr).le hu
  rw [h, show Plane.supNorm u = 1 from hu] at h1
  exact hr1 h1.symm

/-- An inner crossing point is *covered* by the spoke's path — it is an end of one of its
edges, not merely its source. -/
theorem smul_mem_coveredVertices_spokeWalk {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {u : Plane} (hu : u ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) (hr1 : r ≠ 1) :
    r • u ∈ (meshGraph N fresh anchors).coveredVertices (spokeWalk N fresh anchors u) := by
  rcases Graph.mem_walkVertices_iff.1
    (smul_mem_walkVertices_spokeWalk hN hfresh anchors hu hr) with h | h
  · exact absurd h (smul_ne_self hN (hfresh u hu) hr hr1)
  · exact h

/-- **The core**: outer ring, ear, inner ring. -/
noncomputable def meshCore (N : ℕ) (fresh anchors : List Plane) (z w : Plane) :
    Graph Plane Piece :=
  ((ringGraph N fresh anchors 1).union
      ((meshGraph N fresh anchors).pathGraphOf z (meshEar N fresh anchors z w))).union
    (ringGraph N fresh anchors ((N : ℝ)⁻¹))

theorem meshCore_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    meshCore N fresh anchors z w ≤ meshGraph N fresh anchors :=
  Graph.union_le
    (Graph.union_le (ringGraph_le N fresh anchors 1)
      (Graph.pathGraphOf_le (meshEar_isPath hN hfresh anchors hz hw hzw).isWalk))
    (ringGraph_le N fresh anchors _)

/-- A fresh point is a vertex of the outer ring. -/
theorem mem_vertexSet_ringGraph_one {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {u : Plane} (hu : u ∈ fresh) :
    u ∈ V(ringGraph N fresh anchors 1) := by
  have := smul_mem_vertexSet_ringGraph hN hfresh anchors hu (one_mem_meshRadii hN)
  rwa [one_smul] at this

/-- **The core is 2-connected.** -/
theorem meshCore_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshCore N fresh anchors z w).IsTwoConnected := by
  set G := meshGraph N fresh anchors with hG
  set rmin : ℝ := ((N : ℝ)⁻¹) with hrmin
  have hrm : rmin ∈ meshRadii N := inv_mem_meshRadii hN
  have hear := meshEar_isPath hN hfresh anchors hz hw hzw
  have hearle : G.pathGraphOf z (meshEar N fresh anchors z w) ≤ G :=
    Graph.pathGraphOf_le hear.isWalk
  -- the ear, attached to the outer ring
  have h1 : ((ringGraph N fresh anchors 1).union
      (G.pathGraphOf z (meshEar N fresh anchors z w))).IsTwoConnected :=
    (ringGraph_isTwoConnected hN hfresh anchors (one_mem_meshRadii hN)).ear
      (Graph.Compatible.of_le_le (ringGraph_le N fresh anchors 1) hearle)
      hear.isPathGraph_pathGraphOf hzw
      (mem_vertexSet_ringGraph_one hN hfresh anchors hz)
      (mem_vertexSet_ringGraph_one hN hfresh anchors hw)
  -- the crossing points, which the ear visits
  have hrne : rmin ≠ 1 := (inv_cast_lt_one hN).ne
  have hmemz : rmin • z ∈ V(G.pathGraphOf z (meshEar N fresh anchors z w)) :=
    Graph.mem_walkVertices_of_mem_covered (Graph.coveredVertices_mono
      (fun _ hQ => List.mem_append_left _ (List.mem_append_left _ hQ))
      (smul_mem_coveredVertices_spokeWalk hN hfresh anchors hz hrm hrne))
  have hmemw : rmin • w ∈ V(G.pathGraphOf z (meshEar N fresh anchors z w)) :=
    Graph.mem_walkVertices_of_mem_covered (Graph.coveredVertices_mono
      (fun _ hQ => List.mem_append_right _ (List.mem_reverse.2 hQ))
      (smul_mem_coveredVertices_spokeWalk hN hfresh anchors hw hrm hrne))
  exact h1.union (Graph.Compatible.of_le_le
      (Graph.union_le (ringGraph_le N fresh anchors 1) hearle) (ringGraph_le N fresh anchors rmin))
    (ringGraph_isTwoConnected hN hfresh anchors hrm)
    (smul_ne_smul (ne_of_gt (inv_cast_pos hN)) hzw)
    (Or.inr hmemz) (smul_mem_vertexSet_ringGraph hN hfresh anchors hz hrm)
    (Or.inr hmemw) (smul_mem_vertexSet_ringGraph hN hfresh anchors hw hrm)


/-! ### Adding every ring and every spoke -/

/-- Both crossing points of a spoke lie on the ear, whichever ring they belong to. -/
theorem smul_mem_walkVertices_meshEar {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) {r : ℝ} (hr : r ∈ meshRadii N) :
    r • z ∈ (meshGraph N fresh anchors).walkVertices z (meshEar N fresh anchors z w) ∧
      r • w ∈ (meshGraph N fresh anchors).walkVertices z (meshEar N fresh anchors z w) := by
  have hear := meshEar_isPath hN hfresh anchors hz hw hzw
  constructor
  · exact Graph.walkVertices_mono
      (fun _ hQ => List.mem_append_left _ (List.mem_append_left _ hQ))
      (smul_mem_walkVertices_spokeWalk hN hfresh anchors hz hr)
  · by_cases h1 : r = 1
    · rw [h1, one_smul]; exact hear.isWalk.target_mem_walkVertices
    · exact Graph.mem_walkVertices_of_mem_covered (Graph.coveredVertices_mono
        (fun _ hQ => List.mem_append_right _ (List.mem_reverse.2 hQ))
        (smul_mem_coveredVertices_spokeWalk hN hfresh anchors hw hr h1))

/-- The rings of the mesh, attached one at a time — `lem:union-two-connected` iterated. -/
noncomputable def attachRings (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece) :
    List ℝ → Graph Plane Piece
  | [] => K
  | r :: rs => (attachRings N fresh anchors K rs).union (ringGraph N fresh anchors r)

/-- The spokes of the mesh, attached one at a time — `lem:subdivision-ear-preserve` (b)
iterated. -/
noncomputable def attachSpokes (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece) :
    List Plane → Graph Plane Piece
  | [] => K
  | u :: us => (attachSpokes N fresh anchors K us).union (spokeGraph N fresh anchors u)

theorem le_attachRings (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece)
    (l : List ℝ) : K ≤ attachRings N fresh anchors K l := by
  induction l with
  | nil => exact le_refl K
  | cons r rs ih => exact ih.trans (Graph.left_le_union _ _)

theorem le_attachSpokes (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece)
    (l : List Plane) : K ≤ attachSpokes N fresh anchors K l := by
  induction l with
  | nil => exact le_refl K
  | cons u us ih => exact ih.trans (Graph.left_le_union _ _)

theorem attachRings_le {N : ℕ} {fresh anchors : List Plane} {K : Graph Plane Piece}
    (hK : K ≤ meshGraph N fresh anchors) (l : List ℝ) :
    attachRings N fresh anchors K l ≤ meshGraph N fresh anchors := by
  induction l with
  | nil => exact hK
  | cons r rs ih => exact Graph.union_le ih (ringGraph_le _ _ _ _)

theorem attachSpokes_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) {anchors : List Plane} {K : Graph Plane Piece}
    (hK : K ≤ meshGraph N fresh anchors) {l : List Plane} (hl : ∀ u ∈ l, u ∈ fresh) :
    attachSpokes N fresh anchors K l ≤ meshGraph N fresh anchors := by
  induction l with
  | nil => exact hK
  | cons u us ih =>
    exact Graph.union_le (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (spokeGraph_le hN hfresh anchors (hl u List.mem_cons_self))

theorem ringGraph_le_attachRings {N : ℕ} {fresh anchors : List Plane} {K : Graph Plane Piece}
    (hK : K ≤ meshGraph N fresh anchors) {l : List ℝ} {r : ℝ} (hr : r ∈ l) :
    ringGraph N fresh anchors r ≤ attachRings N fresh anchors K l := by
  induction l with
  | nil => exact absurd hr (List.not_mem_nil)
  | cons r' rs ih =>
    rcases List.mem_cons.1 hr with rfl | h
    · exact (Graph.Compatible.of_le_le (attachRings_le hK rs)
        (ringGraph_le N fresh anchors r)).right_le_union
    · exact (ih h).trans (Graph.left_le_union _ _)

theorem spokeGraph_le_attachSpokes {N : ℕ} {fresh anchors : List Plane}
    {K : Graph Plane Piece} (hK : K ≤ meshGraph N fresh anchors) {l : List Plane} {u : Plane}
    (hN : 2 ≤ N) (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (hl : ∀ x ∈ l, x ∈ fresh)
    (hu : u ∈ l) : spokeGraph N fresh anchors u ≤ attachSpokes N fresh anchors K l := by
  induction l with
  | nil => exact absurd hu (List.not_mem_nil)
  | cons u' us ih =>
    rcases List.mem_cons.1 hu with rfl | h
    · exact (Graph.Compatible.of_le_le
        (attachSpokes_le hN hfresh hK fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (spokeGraph_le hN hfresh anchors (hl u List.mem_cons_self))).right_le_union
    · exact (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h).trans (Graph.left_le_union _ _)

theorem attachRings_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) {anchors : List Plane} {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) {K : Graph Plane Piece}
    (hK : K.IsTwoConnected) (hKle : K ≤ meshGraph N fresh anchors)
    (hzK : ∀ r ∈ meshRadii N, r • z ∈ V(K)) (hwK : ∀ r ∈ meshRadii N, r • w ∈ V(K))
    {l : List ℝ} (hl : ∀ r ∈ l, r ∈ meshRadii N) :
    (attachRings N fresh anchors K l).IsTwoConnected := by
  induction l with
  | nil => exact hK
  | cons r rs ih =>
    have hrm : r ∈ meshRadii N := hl r List.mem_cons_self
    have hacc := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hmono := (le_attachRings N fresh anchors K rs).vertexSet_mono
    exact hacc.union (Graph.Compatible.of_le_le
        (attachRings_le hKle rs) (ringGraph_le N fresh anchors r))
      (ringGraph_isTwoConnected hN hfresh anchors hrm)
      (smul_ne_smul (ne_of_gt (meshRadii_pos hN hrm)) hzw)
      (hmono (hzK r hrm)) (smul_mem_vertexSet_ringGraph hN hfresh anchors hz hrm)
      (hmono (hwK r hrm)) (smul_mem_vertexSet_ringGraph hN hfresh anchors hw hrm)

theorem attachSpokes_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) {anchors : List Plane} {K : Graph Plane Piece}
    (hK : K.IsTwoConnected) (hKle : K ≤ meshGraph N fresh anchors)
    (houter : ∀ u ∈ fresh, u ∈ V(K)) (hinner : ∀ u ∈ fresh, ((N : ℝ)⁻¹) • u ∈ V(K))
    {l : List Plane} (hl : ∀ u ∈ l, u ∈ fresh) :
    (attachSpokes N fresh anchors K l).IsTwoConnected := by
  induction l with
  | nil => exact hK
  | cons u us ih =>
    have hu : u ∈ fresh := hl u List.mem_cons_self
    have hacc := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hmono := (le_attachSpokes N fresh anchors K us).vertexSet_mono
    refine hacc.ear (Graph.Compatible.of_le_le
        (attachSpokes_le hN hfresh hKle fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (spokeGraph_le hN hfresh anchors hu))
      (spokeWalk_isPath hN hfresh anchors hu).isPathGraph_pathGraphOf ?_
      (hmono (houter u hu)) (hmono (hinner u hu))
    exact fun h => smul_ne_self hN (hfresh u hu) (inv_mem_meshRadii hN)
      (inv_cast_lt_one hN).ne h.symm


/-! ### Clause 5: the skeleton of the mesh is 2-connected -/

/-- **The whole mesh, assembled**: the core, then every ring, then every spoke. -/
noncomputable def meshAssembly (N : ℕ) (fresh anchors : List Plane) (z w : Plane) :
    Graph Plane Piece :=
  attachSpokes N fresh anchors
    (attachRings N fresh anchors (meshCore N fresh anchors z w) (meshRadii N)) fresh

theorem meshAssembly_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    meshAssembly N fresh anchors z w ≤ meshGraph N fresh anchors :=
  attachSpokes_le hN hfresh
    (attachRings_le (meshCore_le hN hfresh anchors hz hw hzw) (meshRadii N)) fun _ hx => hx

theorem meshAssembly_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshAssembly N fresh anchors z w).IsTwoConnected := by
  have hcore := meshCore_isTwoConnected hN hfresh anchors hz hw hzw
  have hcorele := meshCore_le hN hfresh anchors hz hw hzw
  -- both crossing points of every ring lie on the ear, hence in the core
  have hzK : ∀ r ∈ meshRadii N, r • z ∈ V(meshCore N fresh anchors z w) := fun r hr =>
    Or.inl (Or.inr (smul_mem_walkVertices_meshEar hN hfresh anchors hz hw hzw hr).1)
  have hwK : ∀ r ∈ meshRadii N, r • w ∈ V(meshCore N fresh anchors z w) := fun r hr =>
    Or.inl (Or.inr (smul_mem_walkVertices_meshEar hN hfresh anchors hz hw hzw hr).2)
  have hrings := attachRings_isTwoConnected hN hfresh hz hw hzw hcore hcorele hzK hwK
    (l := meshRadii N) fun _ hx => hx
  refine attachSpokes_isTwoConnected hN hfresh hrings
    (attachRings_le hcorele (meshRadii N)) ?_ ?_ fun _ hx => hx
  · exact fun u hu => (le_attachRings N fresh anchors _ (meshRadii N)).vertexSet_mono
      (Or.inl (Or.inl (mem_vertexSet_ringGraph_one hN hfresh anchors hu)))
  · exact fun u hu => (le_attachRings N fresh anchors _ (meshRadii N)).vertexSet_mono
      (Or.inr (smul_mem_vertexSet_ringGraph hN hfresh anchors hu (inv_mem_meshRadii hN)))

/-- **The assembly spans the mesh.** Every vertex of the mesh is an end of an edge, every edge
lies inside a mesh segment, and a mesh segment is either a ring side — putting the vertex on
that ring — or a spoke, putting it on that spoke's path. -/
theorem vertexSet_meshGraph_subset_meshAssembly {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    V(meshGraph N fresh anchors) ⊆ V(meshAssembly N fresh anchors z w) := by
  have hcorele := meshCore_le hN hfresh anchors hz hw hzw
  intro v hv
  obtain ⟨Q, hQ, hvQ⟩ := meshGraph_mem_vertexSet.1 hv
  obtain ⟨R, hR, hsub⟩ := meshGraph_edge_source hQ
  have hvseg : v ∈ Q.seg := by
    rcases hvQ with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  have hvR : v ∈ R.seg := hsub hvseg
  have hvp : v ∈ meshPoints N fresh anchors :=
    overlayPieces_ends_cut (meshPoints_endsAreCut N fresh anchors) Q hQ v hvQ
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨u, hu, rfl⟩
  · -- `v` lies on the ring of radius `r`
    have hvring : v ∈ V(ringGraph N fresh anchors r) :=
      mem_vertexSet_ringGraph hN hfresh hr hvp
        (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr hvR)
    exact (le_attachSpokes N fresh anchors _ fresh).vertexSet_mono
      ((ringGraph_le_attachRings hcorele hr).vertexSet_mono hvring)
  · -- `v` lies on the spoke at `u`
    have hvwalk : v ∈ (meshGraph N fresh anchors).walkVertices u (spokeWalk N fresh anchors u) :=
      mem_walkVertices_of_mem_points (meshSegments_nondeg hN hfresh)
        (spokePiece_mem_meshSegments hu) (spokeWalk_spec hN hfresh anchors hu).2 hvp hvR
    exact (spokeGraph_le_attachSpokes (l := fresh)
      (attachRings_le hcorele (meshRadii N)) hN hfresh (fun _ hx => hx) hu).vertexSet_mono hvwalk

/-- **`prop:anchored-square-mesh`, clause 5, for `meshGraph`: the skeleton is 2-connected.**

The hypothesis is *two distinct fresh points*, and it is exactly right:
`Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton` shows the conclusion is
**false** with fewer. -/
theorem meshGraph_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshGraph N fresh anchors).IsTwoConnected :=
  (meshAssembly_isTwoConnected hN hfresh anchors hz hw hzw).of_le_of_vertexSet_subset
    (meshAssembly_le hN hfresh anchors hz hw hzw)
    (vertexSet_meshGraph_subset_meshAssembly hN hfresh anchors hz hw hzw)

/-- **`prop:anchored-square-mesh`, clause 5, for `squareMesh`.**

`Schoenflies.FreshDense fresh δ` alone does **not** suffice — `freshDense_not_isTwoConnected`
is the counterexample — but `FreshDense` together with `δ < 4` does, because it forces two
distinct fresh points (`Schoenflies.exists_two_distinct_fresh_of_freshDense`). The blueprint's
caller uses `δ = ε_n = 2⁻ⁿ`, far below `4`. -/
theorem squareMesh_isTwoConnected {fresh : List Plane} (hfresh : ∀ x ∈ fresh, x ∈ modelCurve)
    {δ : ℝ} (hdense : FreshDense fresh δ) (hδ : δ < 4) (anchors : List Plane) :
    (squareMesh δ fresh anchors).IsTwoConnected := by
  obtain ⟨z, hz, w, hw, hzw⟩ := exists_two_distinct_fresh_of_freshDense hdense hδ
  exact meshGraph_isTwoConnected (two_le_meshCount δ) hfresh anchors hz hw hzw

end Schoenflies
