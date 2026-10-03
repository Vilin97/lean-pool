/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.OverlayGraph
public import LeanPool.Schoenflies.Graph.OuterFace
public import LeanPool.Schoenflies.Graph.CycleJordan
public import LeanPool.Schoenflies.TwoArcs
public import LeanPool.Schoenflies.StripConstants
public import LeanPool.Schoenflies.StripConnected

/-!
# Composition checks

Each layer of this development was built against an interface rather than against its
consumer, so the interfaces can drift apart while every module still compiles on its own.
These are the checks that they actually fit: short theorems that use two or more layers
together and are worth nothing except as a tripwire.

The first one has already earned its place. `polygonal_overlay` originally concluded only
`IsDrawing G segmentDrawing ∧ pointSet G segmentDrawing = cover pieces`, with `G` bound by an
existential. Every statement about faces carries a `[G.Finite]` instance, and there is no way
to recover an instance for a graph hidden behind a binder — so the overlay could not be handed
to the face machinery at all, even though both halves compiled. The overlay now carries
`Graph.Finite` in its conclusion, and this file is what would have caught that.

## What is checked

* `overlay_has_outer_face` — Layer 6's overlay composes with Layer 6's outer face.
* `two_arcs_roundtrip` — Layer 4's cutting theorem composes with its gluing theorem.
* `polygonal_collar` — Lemma 1.8 (a), the three strip modules composed.
-/

public section

open Set
open scoped Graph

namespace Schoenflies

/-- The overlay of finitely many nondegenerate segments is a plane graph to which the
outer-face theorem applies. Uses `polygonal_overlay`, `Graph.Finite`, `IsDrawing`, `face` and
`exists_unbounded_face` together. -/
theorem overlay_has_outer_face (pieces : List Piece) (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∃ G : Graph Plane Piece, Graph.pointSet G segmentDrawing = cover pieces ∧
      ∃ base ∈ Graph.exterior G segmentDrawing,
        ¬ Bornology.IsBounded (Graph.face G segmentDrawing base) := by
  obtain ⟨G, hfin, hdraw, hpt⟩ := polygonal_overlay pieces hnd
  let _ := hfin
  exact ⟨G, hpt, Graph.exists_unbounded_face hdraw⟩

/-- Cutting a Jordan curve at two points and gluing the pieces back returns a Jordan curve —
`IsJordanCurve.two_arcs` composed with `IsJordanCurve.of_two_arcs`. The two are converse, and
this is what says so. -/
theorem two_arcs_roundtrip {C : Set Plane} (hC : IsJordanCurve C) {p q : Plane}
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A B, A ∪ B = C ∧ IsJordanCurve (A ∪ B) := by
  obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hC.two_arcs hp hq hpq
  exact ⟨A, B, hcov, IsJordanCurve.two_arcs_of_two_arcs hA hB hmeet⟩

/-- **Lemma 1.8 (a) (two-sided polygonal strips).** A simple closed polygonal curve has an open
neighbourhood `N`, inside any prescribed open set containing it, such that `N` minus the curve
is the disjoint union of two connected open sets.

This is `Strip.lean` (the apparatus, the germ argument and the disjointness),
`StripConstants.lean` (the constants exist) and `StripConnected.lean` (each side is connected,
and the collar minus the curve is exactly the two sides) composed. It is stated here rather
than in any one of them because no one of them can state it.

`IsOpen N` and `P.carrier ⊆ N` are not decoration: without them "neighbourhood" is not being
asserted at all, and the Jordan curve argument needs `N` to be a neighbourhood of the curve —
it has to land the final portion of a segment `[x, a)` inside `N`. An earlier version of this
statement omitted both and was correspondingly useless to its consumer.

`ClosedPolygon.exists_two_sided_collar` strengthens this further with the local clauses: every
point of the curve lies in the closure of *both* sides. -/
theorem polygonal_collar {m : ℕ} (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) :
    ∃ N L R : Set Plane, IsOpen N ∧ P.carrier ⊆ N ∧ N ⊆ U ∧ IsOpen L ∧ IsOpen R ∧
      N \ P.carrier = L ∪ R ∧ Disjoint L R ∧ IsConnected L ∧ IsConnected R := by
  obtain ⟨D, hDU⟩ := exists_stripData_subset P hU hPU
  exact ⟨D.nbhd, D.sideL, D.sideR, D.isOpen_nbhd, D.carrier_subset_nbhd, hDU,
    D.isOpen_sideL, D.isOpen_sideR, D.nbhd_diff_carrier, D.sideL_disjoint_sideR,
    D.isConnected_sideL, D.isConnected_sideR⟩

end Schoenflies
