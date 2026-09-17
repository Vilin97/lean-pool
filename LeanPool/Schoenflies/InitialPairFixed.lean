/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.InitialPair
import LeanPool.Schoenflies.JordanClosed
import LeanPool.Schoenflies.BoundaryCycles

/-!
# The complete construction of `prop:initial-pair`

`Schoenflies/InitialPair.lean` builds the initial matched pair but leaves three things that
`def:matched-pair` and `prop:initial-pair` actually assert:

1. **the anchor clause.** The blueprint chooses `a, b ∈ 𝒜`, the fixed countable dense set of
   *strongly accessible* points of `prop:countable-strong-access` (tex 1403–1418). `InitialData`
   records neither the anchor set nor the strong accessibility of `a` and `b`, so nothing
   downstream can build a further crosscut ending at them, and `lem:anchor-density` — which
   needs the anchors of every stage to be points of `𝒜` — has nothing to attach to.
   `Schoenflies.AnchorSet` is `𝒜` as data, `Schoenflies.AnchoredInitialData` is the initial pair
   with the clause recorded, and `Schoenflies.AnchoredInitialData.stronglyAccessible_a` /
   `.exists_access_segment_a` turn it back into the straight access segment `lem:tangent-cone`
   supplies.
2. **the matched labelling.** `InitialData.source_closure_cell_inter` labels the two source
   2-cells by the two boundary arcs `A₁, A₂` of `C`, and `.target_closure_cell_inter` labels the
   two target 2-cells by the two boundary arcs of `S` — independently. Nothing said the two
   labellings correspond, which is the whole content of a *matched* pair.
   `Schoenflies.InitialData.tgt_arcOf_eq_image` (`tgt.arcOf k = u '' src.arcOf k`),
   `.skeletonHomeo_image_arcOf` and `.closure_cell_face_link` supply the link.
3. **`def:admissible-graph` for the target**: "all its edges are polygonal".
   `Schoenflies.InitialData.isPolygonal_tgt_edgeArc` and
   `.isPolygonal_targetRealization_skeletonSet`.

It also carried two hypotheses, `harc` (`thm:arc-complement`) and `hcollars`
(`lem:crosscut-collars`), both of which are now theorems on `main`
(`Schoenflies.arc_complement`, `Schoenflies.IsCrosscut.hasArcCollars`). Every headline result is
restated here after supplying them; the primed names distinguish these strengthened statements.

Finally, `initBoundary` is a raw datum in `CellStructure`, and nothing checked that the two
lists it holds are closed walks of `initSkel` whose cells are exactly `faceCells`. They are:
`Schoenflies.isWalk_initBoundary_false`, `.._true`, and `Schoenflies.mem_faceCells_iff`.

## Blueprint

* `Schoenflies.AnchorSet`, `Schoenflies.nonempty_anchorSet`, `Schoenflies.anchorSet` —
  `prop:countable-strong-access` as the *fixed* set `𝒜` of tex 1418.
* `Schoenflies.AnchoredInitialData`, `Schoenflies.exists_anchoredInitialData`,
  `Schoenflies.anchoredInitialData`, `Schoenflies.initialData` — `prop:initial-pair` including
  the dropped clause "two further points `a, b ∈ 𝒜`", the last one with the canonical anchor
  set supplied.
* `Schoenflies.stronglyAccessible_initialData_a`, `.._b` — the strong accessibility of the two
  chosen points of the canonical pair, which is what the dropped clause was *for*.
* `Schoenflies.AnchoredInitialData.stronglyAccessible_a`, `.stronglyAccessible_b`,
  `.exists_access_segment_a`, `.exists_access_segment_b` — `lem:tangent-cone` at the two
  anchors, the form `lem:accessible-endpoints` consumes at every later stage.
* `Schoenflies.isWalk_initBoundary_false`, `Schoenflies.isWalk_initBoundary_true`,
  `Schoenflies.mem_faceCells_iff`, `Schoenflies.boundaryCycles_initialStructure` — the boundary
  datum of `def:matched-cellulation` really is the simple boundary cycle of each 2-cell and
  carries exactly its strict subcells.
* `Schoenflies.HexData.isPolygonal_arcOf`, `.isPolygonal_outerArcs`,
  `Schoenflies.isPolygonal_modelCurve`, `Schoenflies.InitialData.isPolygonal_tgt_edgeArc`,
  `.isPolygonal_targetRealization_skeletonSet` — the clause "all its edges are polygonal" of
  `def:admissible-graph` for the target realization.
* `Schoenflies.InitialData.src_arcOf_eq_image`, `.tgt_arcOf_eq_image`,
  `.skeletonHomeo_image_arcOf`, `.closure_cell_face_link`, `.closure_cell_face_link_homeo` —
  clause 1 of `def:matched-pair` ("the two distinguished outer cycles correspond") at the level
  of the two boundary arcs, and the correspondence of the two 2-cell labellings.
* `Schoenflies.InitialData.u_src_pos`, `.tgt_pos_corners`, `.u_a_mem_openTop`,
  `.u_b_mem_openBottom` — the geometric content of the `prop:initial-pair` sentence: `C` is
  subdivided at the `u`-preimages of the four corners, and `a, b` lie in two nonadjacent
  corner arcs.
* `Schoenflies.InitialData.source_cells_cover'`, `.source_cell_isComponent'`,
  `.source_closure_cell_inter'`, `.source_cells_ne'`, `.target_cells_cover'`,
  `.target_closure_cell_inter'`, `.target_cell_isComponent`, `.target_cells_ne` —
  `thm:general-crosscut` on both sides, with its hypotheses supplied.
* `Schoenflies.exists_initialData'`, `Schoenflies.initial_pair'` — `prop:initial-pair`, with the
  anchor clause and the matched labelling in the statement.
-/

open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

/-- **`thm:jordan` in the shape `thm:general-crosscut` consumes.** Every consumer below feeds
this to a lemma whose separating hypothesis is universally quantified over curves.
(`Schoenflies.isSeparating_of_isJordanCurve` is the *polygonal* statement of `Jordan.lean`, and
is a different hypothesis; this is the general one, now a theorem.) -/
theorem forall_isSeparating_of_isJordanCurve : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S :=
  fun _ h => jordan_curve_theorem h

/-! ### Two missing `HexData` facts

The two boundary arcs are part of the outer cycle, and both are polygonal as soon as the six
outer edges are. The second is the clause of `def:admissible-graph` that the target realization
has to satisfy and the source one does not. -/

namespace HexData

variable (H : HexData)

-- Deliberately *not* `@[simp]`: `HexData.arcOf_union`, `.arcOf_inter` and the two labelling
-- theorems are all stated about `arcOf`, and a global unfolding lemma would take `simp` apart
-- underneath them.
theorem arcOf_false :
    H.arcOf false = H.outer 1 '' I ∪ (H.outer 2 '' I ∪ H.outer 3 '' I) := rfl

theorem arcOf_true :
    H.arcOf true = H.outer 4 '' I ∪ (H.outer 5 '' I ∪ H.outer 0 '' I) := rfl

theorem arcOf_subset_outerArcs (k : Bool) : H.arcOf k ⊆ H.outerArcs := by
  rw [← H.arcOf_union]
  cases k
  exacts [Set.subset_union_left, Set.subset_union_right]

/-- The vertex an outer edge ends at, named. -/
theorem pos_mem_outer_of_succ {i j : Fin 6} (h : i + 1 = j) : H.pos j ∈ H.outer i '' I := by
  subst h; exact H.pos_succ_mem_outer i

/-- **Each boundary arc is polygonal when the outer edges are.** Three consecutive segments,
glued at the two vertices between them. -/
theorem isPolygonal_arcOf (hp : ∀ i, IsPolygonal (H.outer i '' I)) (k : Bool) :
    IsPolygonal (H.arcOf k) := by
  cases k
  · rw [H.arcOf_false]
    refine (hp 1).union ((hp 2).union (hp 3)
      ⟨H.pos 3, H.pos_mem_outer_of_succ (by decide), H.pos_mem_outer 3⟩) ?_
    exact ⟨H.pos 2, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 2)⟩
  · rw [H.arcOf_true]
    refine (hp 4).union ((hp 5).union (hp 0)
      ⟨H.pos 0, H.pos_mem_outer_of_succ (by decide), H.pos_mem_outer 0⟩) ?_
    exact ⟨H.pos 5, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 5)⟩

/-- **The whole outer cycle is polygonal when the six outer edges are.** -/
theorem isPolygonal_outerArcs (hp : ∀ i, IsPolygonal (H.outer i '' I)) :
    IsPolygonal H.outerArcs := by
  rw [H.outerArcs_eq]
  have h45 : IsPolygonal (H.outer 4 '' I ∪ H.outer 5 '' I) :=
    (hp 4).union (hp 5) ⟨H.pos 5, H.pos_mem_outer_of_succ (by decide), H.pos_mem_outer 5⟩
  have h345 := (hp 3).union h45
    ⟨H.pos 4, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 4)⟩
  have h2345 := (hp 2).union h345
    ⟨H.pos 3, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 3)⟩
  have h12345 := (hp 1).union h2345
    ⟨H.pos 2, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 2)⟩
  exact (hp 0).union h12345
    ⟨H.pos 1, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 1)⟩

end HexData

/-- **The model curve is polygonal.** Instantiate the target realization at `α = β = 0`: its
outer cycle is `S` and each of its six edges is a straight segment. -/
theorem isPolygonal_modelCurve : IsPolygonal modelCurve := by
  have h : |(0 : ℝ)| < 1 := by norm_num
  have hp : ∀ i, IsPolygonal ((targetHex h h).outer i '' I) := by
    intro i
    change IsPolygonal (tgtOuter 0 0 i '' I)
    rw [tgtOuter_image]
    exact isPolygonal_segment _ _
  have hpoly := (targetHex h h).isPolygonal_outerArcs hp
  rwa [targetHex_outerArcs h h] at hpoly

/-! ### `initBoundary` really is the boundary walk

`CellStructure.boundary` is documented as a raw datum: nothing in the record forces it to walk
anywhere. For `initialStructure` it does. Both lists are *closed* walks of `initSkel`, and the
cells they run through are exactly the `faceCells` that `initSub` declares to be subcells of the
corresponding 2-cell — so the base value of `≼_abs` is not an independent choice. -/

/-- An outer edge links its two consecutive vertices, with the second one named. -/
theorem initSkel_isLink_edge {i j : Fin 6} (h : i + 1 = j) :
    initSkel.IsLink (.edge i) (.vert i) (.vert j) := by
  subst h; exact initSkel_isLink_ends (InitialCell.edge_mem_edges i)

/-- The chord links `a` and `b`. -/
theorem initSkel_isLink_chord : initSkel.IsLink .chord (.vert 1) (.vert 4) :=
  initSkel_isLink_ends InitialCell.chord_mem_edges

/-- **`B₁ ∪ P` is a closed walk at `a`.** -/
theorem isWalk_initBoundary_false :
    initSkel.IsWalk (.vert 1) (initBoundary (.face false)) (.vert 1) := by
  change initSkel.IsWalk (.vert 1) [.edge 1, .edge 2, .edge 3, .chord] (.vert 1)
  exact .cons (initSkel_isLink_edge (by decide : (1 : Fin 6) + 1 = 2))
    (.cons (initSkel_isLink_edge (by decide : (2 : Fin 6) + 1 = 3))
      (.cons (initSkel_isLink_edge (by decide : (3 : Fin 6) + 1 = 4))
        (.cons initSkel_isLink_chord.symm (.nil (InitialCell.vert_mem_vertices 1)))))

/-- **`B₂ ∪ P` is a closed walk at `b`.** -/
theorem isWalk_initBoundary_true :
    initSkel.IsWalk (.vert 4) (initBoundary (.face true)) (.vert 4) := by
  change initSkel.IsWalk (.vert 4) [.edge 4, .edge 5, .edge 0, .chord] (.vert 4)
  exact .cons (initSkel_isLink_edge (by decide : (4 : Fin 6) + 1 = 5))
    (.cons (initSkel_isLink_edge (by decide : (5 : Fin 6) + 1 = 0))
      (.cons (initSkel_isLink_edge (by decide : (0 : Fin 6) + 1 = 1))
        (.cons initSkel_isLink_chord (.nil (InitialCell.vert_mem_vertices 4)))))

/-- Each 2-cell of the initial structure has a closed boundary walk. -/
theorem exists_isWalk_initBoundary (k : Bool) :
    ∃ v, initSkel.IsWalk v (initialStructure.boundary (.face k)) v := by
  cases k
  exacts [⟨_, isWalk_initBoundary_false⟩, ⟨_, isWalk_initBoundary_true⟩]

/-- Incidence in `initSkel` is membership among the two ends. -/
theorem initSkel_inc_iff {e x : InitialCell} :
    initSkel.Inc e x ↔ e ∈ InitialCell.edges ∧ (x = e.ends.1 ∨ x = e.ends.2) := by
  constructor
  · rintro ⟨y, hy⟩
    rw [initSkel_isLink] at hy
    rcases hy.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [⟨hy.1, Or.inl rfl⟩, ⟨hy.1, Or.inr rfl⟩]
  · rintro ⟨he, rfl | rfl⟩
    exacts [⟨_, initSkel_isLink_ends he⟩, ⟨_, (initSkel_isLink_ends he).symm⟩]

/-- **The cells of a 2-cell are the cells of its boundary walk.** The base value of `≼_abs`
declares `faceCells k` to be the subcells of `face k`; this says `faceCells k` is exactly the
set of edges the boundary walk takes together with the vertices it visits. -/
theorem mem_faceCells_iff {k : Bool} {c : InitialCell} :
    c ∈ faceCells k ↔
      c ∈ initBoundary (.face k) ∨ ∃ e ∈ initBoundary (.face k), initSkel.Inc e c := by
  have hedge : ∀ i j : Fin 6, i + 1 = j → ∀ x : InitialCell,
      initSkel.Inc (.edge i) x ↔ (x = .vert i ∨ x = .vert j) := by
    rintro i j rfl x
    rw [initSkel_inc_iff]
    exact ⟨fun h => h.2, fun h => ⟨InitialCell.edge_mem_edges i, h⟩⟩
  have hchord : ∀ x : InitialCell,
      initSkel.Inc .chord x ↔ (x = .vert 1 ∨ x = .vert 4) := by
    intro x
    rw [initSkel_inc_iff]
    exact ⟨fun h => h.2, fun h => ⟨InitialCell.chord_mem_edges, h⟩⟩
  cases k <;>
    simp only [faceCells, initBoundary, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left,
      hedge 1 2 (by decide), hedge 2 3 (by decide), hedge 3 4 (by decide),
      hedge 4 5 (by decide), hedge 5 0 (by decide), hedge 0 1 (by decide), hchord] <;>
    tauto

/-! ### The initial face-boundary cycles

The closed-walk facts above are strengthened here to the maintained data needed by
`thm:finite-transfer`: each boundary is a simple cycle of length at least three, and its cells
are exactly the strict subcells of the corresponding face. -/

/-- The complementary part of the first face boundary is a simple path. -/
theorem isPath_initBoundary_false_tail :
    initSkel.IsPath (.vert 2) [.edge 2, .edge 3, .chord] (.vert 1) := by
  refine .cons (initSkel_isLink_edge (by decide : (2 : Fin 6) + 1 = 3))
    (.cons (initSkel_isLink_edge (by decide : (3 : Fin 6) + 1 = 4))
      (Graph.IsPath.single initSkel_isLink_chord.symm (by simp)) ?_) ?_
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]

/-- The complementary part of the second face boundary is a simple path. -/
theorem isPath_initBoundary_true_tail :
    initSkel.IsPath (.vert 5) [.edge 5, .edge 0, .chord] (.vert 4) := by
  refine .cons (initSkel_isLink_edge (by decide : (5 : Fin 6) + 1 = 0))
    (.cons (initSkel_isLink_edge (by decide : (0 : Fin 6) + 1 = 1))
      (Graph.IsPath.single initSkel_isLink_chord (by simp)) ?_) ?_
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]

/-- The first declared boundary list presents a long simple cycle. -/
theorem isLongCycle_initBoundary_false :
    initSkel.IsLongCycle (.edge 1) (.vert 2) (.vert 1)
      [.edge 2, .edge 3, .chord] (.vert 3) where
  isCycle := ⟨(initSkel_isLink_edge (by decide : (1 : Fin 6) + 1 = 2)).symm,
    isPath_initBoundary_false_tail, by simp⟩
  mem := Graph.mem_walkVertices_cons_of_mem
    (initSkel_isLink_edge (by decide : (2 : Fin 6) + 1 = 3))
    Graph.mem_walkVertices_self
  ne_left := by simp
  ne_right := by simp

/-- The second declared boundary list presents a long simple cycle. -/
theorem isLongCycle_initBoundary_true :
    initSkel.IsLongCycle (.edge 4) (.vert 5) (.vert 4)
      [.edge 5, .edge 0, .chord] (.vert 0) where
  isCycle := ⟨(initSkel_isLink_edge (by decide : (4 : Fin 6) + 1 = 5)).symm,
    isPath_initBoundary_true_tail, by simp⟩
  mem := Graph.mem_walkVertices_cons_of_mem
    (initSkel_isLink_edge (by decide : (5 : Fin 6) + 1 = 0))
    Graph.mem_walkVertices_self
  ne_left := by simp
  ne_right := by simp

/-- Incidence below an initial face consists of the face itself and its declared boundary
cells. -/
theorem initSub_face_iff {k : Bool} {c : InitialCell} :
    initSub c (.face k) ↔ c = .face k ∨ c ∈ faceCells k := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨l, h, hc⟩)
    · exact Or.inl h
    · exact absurd h (by simp [InitialCell.edges])
    · cases h; exact Or.inr hc
  · rintro (rfl | hc)
    · exact initSub_refl (Or.inr ⟨k, rfl⟩)
    · exact initSub_face hc

/-- A declared initial boundary has exactly the cells recorded by `faceCells`, once its
starting vertex is known to occur on the boundary. -/
theorem mem_faceCells_iff_mem_pathCells {k : Bool} {u c : InitialCell}
    (hu : ∃ e ∈ initBoundary (.face k), initSkel.Inc e u) :
    c ∈ faceCells k ↔
      c ∈ initialStructure.pathCells u (initBoundary (.face k)) := by
  rw [mem_faceCells_iff]
  simp only [CellStructure.pathCells, Set.mem_union, Set.mem_ofPred_eq,
    Graph.mem_walkVertices_iff, Graph.mem_coveredVertices_iff]
  constructor
  · rintro (hc | hc)
    · exact Or.inl hc
    · exact Or.inr (Or.inr hc)
  · rintro (hc | rfl | hc)
    · exact Or.inl hc
    · exact Or.inr hu
    · exact Or.inr hc

/-- The two faces of the initial matched cellulation carry chosen simple boundary cycles. -/
theorem boundaryCycles_initialStructure : initialStructure.BoundaryCycles where
  cycle F hF := by
    obtain ⟨k, rfl⟩ := hF
    cases k
    · refine ⟨
        { face_mem := ⟨false, rfl⟩
          edge := .edge 1
          source := .vert 2
          target := .vert 1
          walk := [.edge 2, .edge 3, .chord]
          boundary_eq := rfl
          isCycle := isLongCycle_initBoundary_false.isCycle
          sub_face := fun {c} => ?_ }⟩
      rw [initialStructure_sub, initSub_face_iff]
      refine or_congr Iff.rfl (mem_faceCells_iff_mem_pathCells ?_)
      exact ⟨.edge 1, by simp [initBoundary],
        (initSkel_isLink_edge (by decide : (1 : Fin 6) + 1 = 2)).inc_left⟩
    · refine ⟨
        { face_mem := ⟨true, rfl⟩
          edge := .edge 4
          source := .vert 5
          target := .vert 4
          walk := [.edge 5, .edge 0, .chord]
          boundary_eq := rfl
          isCycle := isLongCycle_initBoundary_true.isCycle
          sub_face := fun {c} => ?_ }⟩
      rw [initialStructure_sub, initSub_face_iff]
      refine or_congr Iff.rfl (mem_faceCells_iff_mem_pathCells ?_)
      exact ⟨.edge 4, by simp [initBoundary],
        (initSkel_isLink_edge (by decide : (4 : Fin 6) + 1 = 5)).inc_left⟩

/-! ### The anchor set `𝒜`

`prop:countable-strong-access` produces a countable dense set of strongly accessible points of
`C`; the blueprint then *fixes* it for the whole construction (tex 1418) and every later stage
draws its new boundary vertices from it. Fixing it means it is data, so it is a structure, and
`prop:initial-pair` takes it as an argument rather than producing its own. -/

variable {C : Set Plane}

/-- **The anchor set `𝒜`** of tex 1403–1418: a countable dense subset of the Jordan curve `C`
every point of which is strongly accessible from the Jordan domain `D`. -/
structure AnchorSet (C : Set Plane) where
  /-- The points of `𝒜`. -/
  carrier : Set Plane
  /-- They lie on the curve. -/
  subset_curve : carrier ⊆ C
  /-- There are countably many. -/
  countable : carrier.Countable
  /-- Each is strongly accessible from the inside — `def:strong-accessibility`. -/
  stronglyAccessible : ∀ p ∈ carrier, StronglyAccessible (inside C) p
  /-- They are dense in the curve. -/
  dense : C ⊆ closure carrier

namespace AnchorSet

variable (A : AnchorSet C)

/-- An anchor is the endpoint of a straight access segment into `D` — `lem:tangent-cone`. -/
theorem exists_access_segment {p : Plane} (hp : p ∈ A.carrier) :
    ∃ z ∈ inside C, p ≠ z ∧ openSegment ℝ p z ⊆ inside C :=
  (A.stronglyAccessible p hp).openSegment_subset

/-- An anchor has a whole open cone of straight access segments, truncatable at any radius —
`lem:tangent-cone` in the form the later stages need, where the segment must also avoid a
compact set already drawn. -/
theorem exists_cone {p : Plane} (hp : p ∈ A.carrier) :
    ∃ v : Plane, ‖v‖ = 1 ∧ ∃ r > 0, ∀ s ≤ r, accessCone p v s ⊆ inside C :=
  (A.stronglyAccessible p hp).exists_cone

/-- An anchor is polygonally accessible, the hypothesis `lem:accessible-endpoints` consumes. -/
theorem polyAccessible {p : Plane} (hp : p ∈ A.carrier) : PolyAccessible (inside C) p :=
  (A.stronglyAccessible p hp).polyAccessible

end AnchorSet

/-- **`prop:countable-strong-access`, as the fixed set `𝒜`.** This uses the proved Jordan
curve theorem. -/
theorem nonempty_anchorSet (hC : IsJordanCurve C) : Nonempty (AnchorSet C) := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  -- `inside C` swallows the component in `Cᶜ` of each of its points, being a union of them
  have hDmax : ∀ q ∈ inside C, connectedComponentIn Cᶜ q ⊆ inside C := by
    intro q hq z hz
    refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
    rw [← connectedComponentIn_eq hz]
    exact hq.2
  have hCD : C ⊆ closure (inside C) := by
    intro x hx
    have hxf : x ∈ frontier (inside C) := by rw [hsep.frontier_inside]; exact hx
    exact hxf.1
  obtain ⟨A, hAC, hAcount, hAacc, hCA⟩ := exists_countable_dense_stronglyAccessible hC.isCompact
    hC.nonempty hsep.isOpen_inside inside_subset_compl hDmax hCD
  exact ⟨⟨A, hAC, hAcount, hAacc, hCA⟩⟩

open Classical in
/-- The fixed anchor set of a Jordan curve, as data. -/
noncomputable def anchorSet (hC : IsJordanCurve C) : AnchorSet C := (nonempty_anchorSet hC).some

/-! ### The initial matched pair, anchored

The clause of `prop:initial-pair` that `InitialData` drops. It is recorded as an extension
rather than as a side theorem so that a consumer holding an initial pair holds the anchoring
too; the integrator merging this file into `InitialPair.lean` should move the two fields into
`InitialData` itself. -/

/-- **The initial matched pair with the anchor clause of `prop:initial-pair`**: the two chosen
boundary points are points of the fixed set `𝒜`. -/
structure AnchoredInitialData (C : Set Plane) (A : AnchorSet C) extends InitialData C where
  /-- `a ∈ 𝒜`. -/
  a_mem_anchors : toInitialData.a ∈ A.carrier
  /-- `b ∈ 𝒜`. -/
  b_mem_anchors : toInitialData.b ∈ A.carrier

namespace AnchoredInitialData

variable {A : AnchorSet C} (D : AnchoredInitialData C A)

/-- **`a` is strongly accessible** — the clause `def:generated-structure` and
`thm:finite-transfer` need and `InitialData` does not record. -/
theorem stronglyAccessible_a : StronglyAccessible (inside C) D.toInitialData.a :=
  A.stronglyAccessible _ D.a_mem_anchors

/-- **`b` is strongly accessible.** -/
theorem stronglyAccessible_b : StronglyAccessible (inside C) D.toInitialData.b :=
  A.stronglyAccessible _ D.b_mem_anchors

/-- A straight access segment at `a` — `lem:tangent-cone`. -/
theorem exists_access_segment_a :
    ∃ z ∈ inside C, D.toInitialData.a ≠ z ∧ openSegment ℝ D.toInitialData.a z ⊆ inside C :=
  A.exists_access_segment D.a_mem_anchors

/-- A straight access segment at `b`. -/
theorem exists_access_segment_b :
    ∃ z ∈ inside C, D.toInitialData.b ≠ z ∧ openSegment ℝ D.toInitialData.b z ⊆ inside C :=
  A.exists_access_segment D.b_mem_anchors

/-- The access cone at `a`, truncatable — what a later crosscut ending at `a` is built from. -/
theorem exists_cone_a :
    ∃ v : Plane, ‖v‖ = 1 ∧ ∃ r > 0, ∀ s ≤ r, accessCone D.toInitialData.a v s ⊆ inside C :=
  A.exists_cone D.a_mem_anchors

/-- The access cone at `b`. -/
theorem exists_cone_b :
    ∃ v : Plane, ‖v‖ = 1 ∧ ∃ r > 0, ∀ s ≤ r, accessCone D.toInitialData.b v s ⊆ inside C :=
  A.exists_cone D.b_mem_anchors

end AnchoredInitialData

/-- **`prop:initial-pair` including the anchor clause.** The two chosen points
are points of the *given* anchor set `𝒜`; the blueprint fixes `𝒜` once and reuses it at every
later stage, so it must be an input, not an output.

The proof is that of `Schoenflies.exists_initialData` with the anchor set supplied rather than
manufactured: the two open corner arcs are relatively open and nonempty in `C`, `𝒜` is dense in
`C`, so `𝒜` meets both; `lem:tangent-cone` (through `StronglyAccessible.polyAccessible`) and
`lem:accessible-endpoints` then supply the polygonal crosscut. -/
theorem exists_anchoredInitialData_of_homeo (hC : IsJordanCurve C) (A : AnchorSet C)
    (u w : Plane → Plane) (hhom : IsSetHomeoOn u w C modelCurve) :
    ∃ D : AnchoredInitialData C A,
      D.toInitialData.u = u ∧ D.toInitialData.w = w := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  -- the two open corner arcs, relatively open in `C` and nonempty
  obtain ⟨W₁, hW₁, hW₁eq⟩ := hhom.symm.image_isRelOpen isOpen_topBand (U := openTop) rfl
  obtain ⟨W₂, hW₂, hW₂eq⟩ := hhom.symm.image_isRelOpen isOpen_bottomBand (U := openBottom) rfl
  obtain ⟨a₀, ha₀A, ha₀⟩ := exists_mem_inter_of_dense A.subset_curve A.dense hW₁ hW₁eq
    (openTop_nonempty.image w)
  obtain ⟨b₀, hb₀A, hb₀⟩ := exists_mem_inter_of_dense A.subset_curve A.dense hW₂ hW₂eq
    (openBottom_nonempty.image w)
  obtain ⟨q₁, hq₁, rfl⟩ := ha₀
  obtain ⟨q₂, hq₂, rfl⟩ := hb₀
  have hq₁m : q₁ ∈ modelCurve := hq₁.2
  have hq₂m : q₂ ∈ modelCurve := hq₂.2
  obtain ⟨hq₁1, hq₁0⟩ := mem_openTop.1 hq₁
  obtain ⟨hq₂1, hq₂0⟩ := mem_openBottom.1 hq₂
  set xa : ℝ := q₁ 0 with hxa
  set xb : ℝ := q₂ 0 with hxb
  have hq₁eq : q₁ = tgtPos xa xb 1 := Plane.eq_mk rfl hq₁1
  have hq₂eq : q₂ = tgtPos xa xb 4 := Plane.eq_mk rfl hq₂1
  have haC : w q₁ ∈ C := hhom.mapsTo_inv hq₁m
  have hbC : w q₂ ∈ C := hhom.mapsTo_inv hq₂m
  have hab : w q₁ ≠ w q₂ := by
    intro h
    have hr := hhom.rightInvOn hq₁m
    rw [h, hhom.rightInvOn hq₂m] at hr
    rw [← hr] at hq₁1
    rw [hq₂1] at hq₁1
    norm_num at hq₁1
  -- the polygonal crosscut, from the two access cones
  obtain ⟨ws, -, -, -, hwsin, hwsarc, -⟩ := exists_crosscut_of_polyAccessible
    hsep.isOpen_inside hsep.isConnected_inside.isPreconnected
    (Set.disjoint_left.2 fun x hx => inside_subset_compl hx) hab haC hbC
    (A.polyAccessible ha₀A) (A.polyAccessible hb₀A)
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hwsarc
  refine ⟨{ toInitialData :=
              { u := u, w := w, homeo := hhom, curve := hC, xa := xa, xb := xb
                abs_xa := hq₁0, abs_xb := hq₂0
                cross := f
                continuousOn_cross := hfc, injOn_cross := hfi
                cross_zero := by rw [hf0, hq₁eq]
                cross_one := by rw [hf1, hq₂eq]
                cross_inside := ?_
                polygonal_cross := ?_ }
            a_mem_anchors := ?_
            b_mem_anchors := ?_ }, rfl, rfl⟩
  · rw [hfim, ← hq₁eq, ← hq₂eq]
    intro z hz
    exact hwsin ⟨hz.1, by simpa [hf0, hf1] using hz.2⟩
  · rw [hfim]
    exact ⟨ws, rfl⟩
  · change w (tgtPos xa xb 1) ∈ A.carrier
    rw [← hq₁eq]
    exact ha₀A
  · change w (tgtPos xa xb 4) ∈ A.carrier
    rw [← hq₂eq]
    exact hb₀A

/-- The anchored initial pair with a boundary parametrization chosen internally. -/
theorem exists_anchoredInitialData (hC : IsJordanCurve C) (A : AnchorSet C) :
    Nonempty (AnchoredInitialData C A) := by
  obtain ⟨u, w, hhom⟩ := exists_isSetHomeoOn_modelCurve hC
  obtain ⟨D, -, -⟩ := exists_anchoredInitialData_of_homeo hC A u w hhom
  exact ⟨D⟩

open Classical in
/-- The initial matched pair over `C` anchored in `𝒜`, as data. `def:generated-structure`
builds every later stage from it, so it must be a `def`. -/
noncomputable def anchoredInitialData (hC : IsJordanCurve C) (A : AnchorSet C) :
    AnchoredInitialData C A := (exists_anchoredInitialData hC A).some

/-- **`prop:initial-pair`**, in the shape `Schoenflies.exists_initialData` should have had:
`harc` is supplied by `arc_complement` and the two chosen points are anchors. -/
theorem exists_initialData' (hC : IsJordanCurve C) (A : AnchorSet C) :
    ∃ d : InitialData C, d.a ∈ A.carrier ∧ d.b ∈ A.carrier := by
  obtain ⟨D⟩ := exists_anchoredInitialData hC A
  exact ⟨D.toInitialData, D.a_mem_anchors, D.b_mem_anchors⟩

/-! #### The canonical initial pair

`AnchorSet` is an input because the blueprint fixes `𝒜` once and every later stage draws from
the *same* set. A consumer that has no other constraint on `𝒜` can take `anchorSet hC`: it is a
function of `C` alone (`Nonempty (AnchorSet C)` is a `Prop`, so proof irrelevance makes the
choice independent of the proof supplied), so all its uses agree. -/

/-- The canonical initial matched pair over `C`, anchored in `Schoenflies.anchorSet hC`. -/
noncomputable def initialData (hC : IsJordanCurve C) : InitialData C :=
  (anchoredInitialData hC (anchorSet hC)).toInitialData

theorem initialData_a_mem_anchorSet (hC : IsJordanCurve C) :
    (initialData hC).a ∈ (anchorSet hC).carrier :=
  (anchoredInitialData hC (anchorSet hC)).a_mem_anchors

theorem initialData_b_mem_anchorSet (hC : IsJordanCurve C) :
    (initialData hC).b ∈ (anchorSet hC).carrier :=
  (anchoredInitialData hC (anchorSet hC)).b_mem_anchors

/-- **The first chosen point of the canonical initial pair is strongly accessible.** This is
the clause `prop:initial-pair` asserts, `InitialData` drops, and `def:generated-structure` and
`thm:finite-transfer` need in order to run a further crosscut into `a`. -/
theorem stronglyAccessible_initialData_a (hC : IsJordanCurve C) :
    StronglyAccessible (inside C) (initialData hC).a :=
  (anchoredInitialData hC (anchorSet hC)).stronglyAccessible_a

/-- **The second chosen point of the canonical initial pair is strongly accessible.** -/
theorem stronglyAccessible_initialData_b (hC : IsJordanCurve C) :
    StronglyAccessible (inside C) (initialData hC).b :=
  (anchoredInitialData hC (anchorSet hC)).stronglyAccessible_b

/-! ### The two crosscut theorems on the initial pair

`InitialPair.lean` carries `harc` (`thm:arc-complement`) and, on the source side, `hcollars`
(`lem:crosscut-collars`). Both are theorems on `main`: `Schoenflies.arc_complement` and
`Schoenflies.IsCrosscut.hasArcCollars`. Every consumer in Part II should use the primed forms
below and thread nothing. -/

namespace InitialData

variable (d : InitialData C)

/-- The collar hypothesis on the source side, discharged: the crosscut is polygonal. -/
theorem hasArcCollarsSource : HasArcCollars (inside C) d.crossSet :=
  d.isCrosscut.hasArcCollars

/-- **The two source 2-cells exhaust `D ∖ P`.** -/
theorem source_cells_cover' :
    inside C \ d.crossSet =
      d.sourceRealization.cell (.face false) ∪ d.sourceRealization.cell (.face true) :=
  d.source_cells_cover (fun _ hA => arc_complement hA) d.hasArcCollarsSource

/-- **Each source 2-cell is a component of `D ∖ P`.** -/
theorem source_cell_isComponent' (k : Bool) :
    ∀ z ∈ d.sourceRealization.cell (.face k),
      connectedComponentIn (inside C \ d.crossSet) z = d.sourceRealization.cell (.face k) :=
  d.source_cell_isComponent (fun _ hA => arc_complement hA) k

/-- **The labelling of the two source 2-cells.** -/
theorem source_closure_cell_inter' (k : Bool) :
    closure (d.sourceRealization.cell (.face k)) ∩ C = d.src.arcOf k :=
  d.source_closure_cell_inter (fun _ hA => arc_complement hA) k

/-- **The two source 2-cells are distinct.** -/
theorem source_cells_ne' :
    d.sourceRealization.cell (.face false) ≠ d.sourceRealization.cell (.face true) :=
  d.source_cells_ne (fun _ hA => arc_complement hA)

/-- **The two target 2-cells exhaust `Q° ∖ [u(a), u(b)]`.** -/
theorem target_cells_cover' :
    inside modelCurve \ d.tgt.chordSet =
      d.targetRealization.cell (.face false) ∪ d.targetRealization.cell (.face true) :=
  d.target_cells_cover (fun _ hA => arc_complement hA)

/-- **The labelling of the two target 2-cells.** -/
theorem target_closure_cell_inter' (k : Bool) :
    closure (d.targetRealization.cell (.face k)) ∩ modelCurve = d.tgt.arcOf k :=
  d.target_closure_cell_inter (fun _ hA => arc_complement hA) k

/-- **Each target 2-cell is a component of `Q° ∖ [u(a), u(b)]`.** The source side had this
already; the target side did not. -/
theorem target_cell_isComponent (k : Bool) :
    ∀ z ∈ d.targetRealization.cell (.face k),
      connectedComponentIn (inside modelCurve \ d.tgt.chordSet) z =
        d.targetRealization.cell (.face k) := by
  cases k
  · exact d.isCrosscutTarget.side_isComponent forall_isSeparating_of_isJordanCurve
      d.isCutPairTarget
  · exact d.isCrosscutTarget.side_isComponent forall_isSeparating_of_isJordanCurve
      d.isCutPairTarget.symm

/-- **The two target 2-cells are distinct.** -/
theorem target_cells_ne :
    d.targetRealization.cell (.face false) ≠ d.targetRealization.cell (.face true) :=
  d.isCrosscutTarget.side_ne forall_isSeparating_of_isJordanCurve d.isCutPairTarget

/-! ### The matched labelling

`def:matched-pair` clause 1 asks that "the two distinguished outer cycles correspond". On the
initial pair this is not automatic from the abstract structure alone: `arcOf` is read off the
*geometry* of each realization, so the two 2-cell labellings — `source_closure_cell_inter'` and
`target_closure_cell_inter'` — are made independently. They correspond because the source
outer edges are, by construction, the `w`-images of the target ones. -/

theorem src_outer (i : Fin 6) : d.src.outer i = fun t => d.w (tgtOuter d.xa d.xb i t) := rfl

theorem tgt_outer (i : Fin 6) : d.tgt.outer i = tgtOuter d.xa d.xb i := rfl

theorem src_pos (i : Fin 6) : d.src.pos i = d.w (d.tgt.pos i) := rfl

/-- **Corresponding 0-cells correspond**, in the geometric form `prop:initial-pair` states it:
the six source subdivision points are the `u`-preimages of the four corners of `Q` and of
`u(a), u(b)`. (`SkeletonHomeo.pos_apply` says the same thing about the *abstract* 0-cells.) -/
theorem u_src_pos (i : Fin 6) : d.u (d.src.pos i) = d.tgt.pos i :=
  d.homeo.rightInvOn (tgtPos_mem_modelCurve d.abs_xa d.abs_xb i)

/-- The four target corners, named. -/
theorem tgt_pos_corners :
    d.tgt.pos 0 = Plane.mk 1 1 ∧ d.tgt.pos 2 = Plane.mk (-1) 1 ∧
      d.tgt.pos 3 = Plane.mk (-1) (-1) ∧ d.tgt.pos 5 = Plane.mk 1 (-1) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The nonadjacency clause of `prop:initial-pair`, geometrically**: `u(a)` lies in the
relative interior of the top side of `S`. -/
theorem u_a_mem_openTop : d.u d.a ∈ openTop := by
  rw [d.u_apply_a]
  exact mem_openTop.2 ⟨by simp, by simpa using d.abs_xa⟩

/-- `u(b)` lies in the relative interior of the *opposite*, bottom side. -/
theorem u_b_mem_openBottom : d.u d.b ∈ openBottom := by
  rw [d.u_apply_b]
  exact mem_openBottom.2 ⟨by simp, by simpa using d.abs_xb⟩

/-- Each source outer edge is the `w`-image of the corresponding target one. -/
theorem src_outer_image (i : Fin 6) : d.src.outer i '' I = d.w '' (d.tgt.outer i '' I) := by
  rw [← Set.image_comp]; rfl

theorem tgt_outer_subset_modelCurve (i : Fin 6) : d.tgt.outer i '' I ⊆ modelCurve :=
  tgtOuter_subset_modelCurve d.abs_xa d.abs_xb i

/-- `u` undoes `w` on any subset of the model curve. -/
theorem u_image_w_image {X : Set Plane} (hX : X ⊆ modelCurve) : d.u '' (d.w '' X) = X := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rwa [d.homeo.rightInvOn (hX hx)]
  · exact fun hy => ⟨d.w y, ⟨y, hy, rfl⟩, d.homeo.rightInvOn (hX hy)⟩

theorem tgt_arcOf_subset_modelCurve (k : Bool) : d.tgt.arcOf k ⊆ modelCurve := by
  intro z hz
  rw [← d.tgt_outerArcs]
  exact d.tgt.arcOf_subset_outerArcs k hz

theorem src_arcOf_subset_curve (k : Bool) : d.src.arcOf k ⊆ C := by
  intro z hz
  rw [← d.src_outerArcs]
  exact d.src.arcOf_subset_outerArcs k hz

/-- **The source boundary arc is the `w`-image of the target one.** -/
theorem src_arcOf_eq_image (k : Bool) : d.src.arcOf k = d.w '' d.tgt.arcOf k := by
  cases k <;>
    simp only [HexData.arcOf_false, HexData.arcOf_true, Set.image_union, d.src_outer_image]

/-- **The target half of the 2-cell labelling is the `u`-image of the source half.** This is
what makes the pair *matched*: `A₁, A₂` on the source and `u(A₁), u(A₂)` on the target are not
two independent choices of labelling, they are the same one. -/
theorem tgt_arcOf_eq_image (k : Bool) : d.tgt.arcOf k = d.u '' d.src.arcOf k := by
  rw [d.src_arcOf_eq_image k, d.u_image_w_image (d.tgt_arcOf_subset_modelCurve k)]

/-- The same statement through the skeleton homeomorphism `g` of `def:matched-pair`, which is
`u` on the outer cycle. -/
theorem skeletonHomeo_image_arcOf (k : Bool) :
    d.skeletonHomeo.toFun '' d.src.arcOf k = d.tgt.arcOf k := by
  rw [d.tgt_arcOf_eq_image k]
  exact Set.image_congr fun x hx => d.skeletonHomeo_eq_u (d.src_arcOf_subset_curve k hx)

/-- **The two 2-cell labellings correspond.** `lem:crosscut-side-correspondence` reads the
labelling of a crosscut side off the closure of the side; on a matched pair the source and the
target answers are `u`-images of one another, for the *same* abstract 2-cell `face k`. -/
theorem closure_cell_face_link (k : Bool) :
    closure (d.targetRealization.cell (.face k)) ∩ modelCurve =
      d.u '' (closure (d.sourceRealization.cell (.face k)) ∩ C) := by
  rw [d.target_closure_cell_inter' k, d.source_closure_cell_inter' k, d.tgt_arcOf_eq_image k]

/-- The same through `g`. -/
theorem closure_cell_face_link_homeo (k : Bool) :
    d.skeletonHomeo.toFun '' (closure (d.sourceRealization.cell (.face k)) ∩ C) =
      closure (d.targetRealization.cell (.face k)) ∩ modelCurve := by
  rw [d.target_closure_cell_inter' k, d.source_closure_cell_inter' k]
  exact d.skeletonHomeo_image_arcOf k

/-! ### `def:admissible-graph` for the target: every edge is polygonal -/

/-- Each target outer edge is a straight segment, hence polygonal. -/
theorem isPolygonal_tgt_outer (i : Fin 6) : IsPolygonal (d.tgt.outer i '' I) := by
  rw [d.tgt_outer i, tgtOuter_image]
  exact isPolygonal_segment _ _

/-- **Every edge of the target realization is polygonal** — the clause of
`def:admissible-graph` for an admissible graph in `Q` that `InitialPair.lean` leaves unstated. -/
theorem isPolygonal_tgt_edgeArc {e : InitialCell} (he : e ∈ E(initSkel)) :
    IsPolygonal (Graph.edgeArc d.tgt.draw e) := by
  rcases (he : e ∈ InitialCell.edges) with ⟨i, rfl⟩ | rfl
  · rw [HexData.edgeArc_edge]
    exact d.isPolygonal_tgt_outer i
  · rw [HexData.edgeArc_chord]
    change IsPolygonal d.tgt.chordSet
    rw [d.tgt_chordSet]
    exact isPolygonal_segment _ _

/-- Both target boundary arcs are polygonal. -/
theorem isPolygonal_tgt_arcOf (k : Bool) : IsPolygonal (d.tgt.arcOf k) :=
  d.tgt.isPolygonal_arcOf d.isPolygonal_tgt_outer k

/-- **The whole target skeleton is polygonal.** -/
theorem isPolygonal_targetRealization_skeletonSet :
    IsPolygonal d.targetRealization.skeletonSet := by
  rw [d.targetRealization_skeletonSet]
  refine isPolygonal_modelCurve.union ?_ ?_
  · rw [d.tgt_chordSet]; exact isPolygonal_segment _ _
  · refine ⟨Plane.mk d.xa 1, tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1, ?_⟩
    rw [d.tgt_chordSet]
    exact left_mem_segment ℝ _ _

/-- The source realization satisfies the source form of `def:admissible-graph`: its edges *not*
contained in `C` — here only the crosscut — are polygonal, with interior in `D`. -/
theorem isPolygonal_src_nonboundary_edgeArc :
    IsPolygonal (Graph.edgeArc d.src.draw .chord) ∧
      Graph.edgeArc d.src.draw .chord \ C ⊆ inside C := by
  refine ⟨d.polygonal_cross, ?_⟩
  rintro z ⟨hz, hzC⟩
  refine d.cross_inside ⟨hz, ?_⟩
  rintro (rfl | rfl)
  exacts [hzC d.a_mem, hzC d.b_mem]

end InitialData

/-- **`prop:initial-pair`, assembled and complete.**

Over any Jordan curve `C` and any fixed anchor set `𝒜` there is a matched pair whose source
realization is `C` subdivided at the `u`-preimages of the four corners of `Q` and at two further
points `a, b ∈ 𝒜` lying in two nonadjacent corner arcs, together with one polygonal crosscut of
`D` from `a` to `b`, and whose target realization is `S` correspondingly subdivided together
with the straight chord `[u(a), u(b)]`.

Beyond `Schoenflies.initial_pair` this adds: no hypotheses at all; the anchor clause with its
consequence that `a` and `b` are strongly accessible; the polygonality of every target edge; and
the fact that the two 2-cell labellings correspond. -/
theorem initial_pair' (hC : IsJordanCurve C) (A : AnchorSet C) :
    ∃ d : InitialData C,
      -- the anchor clause of `prop:initial-pair`, and what it is for
      d.a ∈ A.carrier ∧ d.b ∈ A.carrier ∧
      StronglyAccessible (inside C) d.a ∧ StronglyAccessible (inside C) d.b ∧
      -- the two chosen points lie in two nonadjacent corner arcs
      d.u d.a ∈ openTop ∧ d.u d.b ∈ openBottom ∧
      -- `C` is subdivided at the `u`-preimages of the four corners and of `u(a), u(b)`
      (∀ i : Fin 6, d.u (d.src.pos i) = d.tgt.pos i) ∧
      -- `def:admissible-graph` on both sides
      (d.sourceRealization.graph).IsTwoConnected ∧
      (d.targetRealization.graph).IsTwoConnected ∧
      d.sourceRealization.outerSet = C ∧
      d.targetRealization.outerSet = modelCurve ∧
      IsConnected d.sourceRealization.nonboundary ∧
      IsConnected d.targetRealization.nonboundary ∧
      IsPolygonal d.crossSet ∧
      (∀ e ∈ E(initSkel), IsPolygonal (Graph.edgeArc d.tgt.draw e)) ∧
      -- `def:matched-pair` clauses 2 and 3
      d.tgt.chordSet = segment ℝ (d.u d.a) (d.u d.b) ∧
      (∀ x ∈ C, d.skeletonHomeo.toFun x = d.u x) ∧
      -- the matched labelling of the two 2-cells
      (∀ k : Bool, d.tgt.arcOf k = d.u '' d.src.arcOf k) ∧
      (∀ k : Bool, closure (d.sourceRealization.cell (.face k)) ∩ C = d.src.arcOf k) ∧
      (∀ k : Bool, closure (d.targetRealization.cell (.face k)) ∩ modelCurve = d.tgt.arcOf k) := by
  obtain ⟨D⟩ := exists_anchoredInitialData hC A
  refine ⟨D.toInitialData, D.a_mem_anchors, D.b_mem_anchors, D.stronglyAccessible_a,
    D.stronglyAccessible_b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.toInitialData.u_a_mem_openTop
  · exact D.toInitialData.u_b_mem_openBottom
  · exact D.toInitialData.u_src_pos
  · exact D.toInitialData.isTwoConnected_sourceRealization
  · exact D.toInitialData.isTwoConnected_targetRealization
  · exact D.toInitialData.sourceRealization_outerSet
  · exact D.toInitialData.targetRealization_outerSet
  · exact D.toInitialData.isConnected_sourceRealization_nonboundary
  · exact D.toInitialData.isConnected_targetRealization_nonboundary
  · exact D.toInitialData.polygonal_cross
  · exact fun e he => D.toInitialData.isPolygonal_tgt_edgeArc he
  · rw [D.toInitialData.tgt_chordSet, D.toInitialData.u_apply_a, D.toInitialData.u_apply_b]
  · exact fun x hx => D.toInitialData.skeletonHomeo_eq_u hx
  · exact D.toInitialData.tgt_arcOf_eq_image
  · exact D.toInitialData.source_closure_cell_inter'
  · exact D.toInitialData.target_closure_cell_inter'

end Schoenflies
