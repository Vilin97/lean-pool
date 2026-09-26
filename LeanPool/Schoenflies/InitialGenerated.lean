/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.FiniteTransfer
public import LeanPool.Schoenflies.InitialPairFixed
public import LeanPool.Schoenflies.BoundaryContinuity2

/-!
# Stage 0: the initial pair as a `GeneratedPair`

`Schoenflies/FiniteTransfer.lean` defines `Schoenflies.GeneratedPair`, the object every stage of
the Schönflies recursion is and that `thm:finite-transfer` consumes and produces. Nothing built
one. This module builds the first: the initial matched pair of `prop:initial-pair`, which is
generated from itself by the empty sequence of elementary operations.

## What has to be shown

The two realizations, the skeleton homeomorphism and weak admissibility are all in
`Schoenflies/InitialPair.lean` and `Schoenflies/InitialPairFixed.lean` already, or one step from
what is there. The work is the two `IsCellDecomposition` fields — assertion (i) of
`lem:cellulation-invariants` — and they are the same work twice, because both realizations have
the same shape: a `HexData` whose six outer arcs form a Jordan curve and whose chord is a
crosscut of it. So assertion (i) is proved **once**, for an arbitrary `HexData` carrying that
crosscut configuration (`Schoenflies.HexData.isCellDecomposition`), and instantiated on each
side. The same is true of weak admissibility (`Schoenflies.HexData.isWeaklyAdmissible`).

The four clauses go as follows.

* `nonempty` — the seven 0-cells are points; the seven open 1-cells are arcs minus their two
  endpoints (`IsArcBetween.nonempty_diff`); the two 2-cells are the two sides of the crosscut,
  nonempty by `thm:general-crosscut`.
* `disjoint` — fifteen cells, but only five kinds of pair. Two vertices are distinct points;
  a vertex misses every open edge it is not an end of (`HexData.mem_outer_iff`,
  `.mem_chord_iff`), and is an end of the ones it does meet; two open edges are disjoint by the
  two meeting conditions of `HexData`; every 1- or 0-cell lies on the skeleton and every 2-cell
  is inside the curve and off the crosscut; and the two 2-cells are the two sides of one
  crosscut.
* `iUnion_eq` — the 0-cells and open 1-cells reassemble the skeleton `C ∪ P`
  (`HexData.iUnion_cellSet`), and the two 2-cells exhaust `D ∖ P`
  (`thm:general-crosscut`), so together they are `C ∪ D`.
* `closure_eq` — a finite case check against `Schoenflies.initSub`, the base value of `≼_abs`
  that the blueprint fixes. The four `initSub_iff_*` lemmas below read it off, and then the only
  topology needed is `closure (A ∖ {p, q}) = A` for an arc (`IsArcBetween.closure_diff`) and the
  closure of a crosscut side (`Schoenflies.crosscut_cell_partition`).

## The input is `InitialData`, not `AnchoredInitialData`

`AnchoredInitialData` adds exactly two fields, `a ∈ 𝒜` and `b ∈ 𝒜`. Nothing in `GeneratedPair`
mentions the anchor set: the anchoring is what lets a *later* stage run a fresh crosscut into `a`
or `b`, and it is read off `AnchoredInitialData.stronglyAccessible_a` at that point. So the pair
is built from `InitialData` — the weaker input — and
`Schoenflies.AnchoredInitialData.generatedPair` is the one-line specialisation for a consumer
holding the anchored form.

## Blueprint

* `Schoenflies.combInvariants_initialStructure` — `lem:cellulation-invariants` (iii), (v), (vi)
  and abstract (viii) for the base structure: the base case of
  `Schoenflies.GeneratedStructure.combInvariants`, which the whole recursion needs.
* `Schoenflies.initSub_iff_vert`, `.._edge`, `.._chord`, `.._face` — the base value of `≼_abs`
  (tex 1590–1602) read as "the subcells of each cell are exactly these".
* `Schoenflies.HexData.isCellDecomposition` — `lem:cellulation-invariants`(i) for either
  realization of `prop:initial-pair`, with `HexData.iUnion_cellSet`,
  `HexData.biUnion_of_three_edges` and `HexData.biUnion_faceCells` as its two reassembly steps.
* `Schoenflies.HexData.isWeaklyAdmissible` — `def:admissible-graph` minus the connectedness
  clause, for either realization.
* `Schoenflies.InitialData.generatedPair`, `Schoenflies.AnchoredInitialData.generatedPair` —
  `def:generated-structure` at stage 0: `prop:initial-pair` is a generated matched cellulation.
* `Schoenflies.HexData.isOpen_cellSet_face`,
  `Schoenflies.InitialData.isOpen_sourceRealization_cell_face`,
  `.isOpen_targetRealization_cell_face` — openness of the two 2-cells: the hypothesis
  `lem:cellulation-invariants`(viii) takes and `IsCellDecomposition` does not record.
* `Schoenflies.infinite_initialCell` — the base case meets the recursion: `thm:finite-transfer`
  needs `[Infinite γ]`, and `InitialCell` supplies it through its spare constructor `aux`.
* `Schoenflies.modelCurve_union_inside` — `S ∪ Int(S) = Q`, the closed target domain.
* `Schoenflies.InitialData.generatedPair_src_isAdmissible`, `.generatedPair_tgt_isAdmissible` —
  the *strong* form of
  `def:admissible-graph` on both sides, which the initial pair does satisfy
  (`rem:intermediate-disconnection` waives it only at intermediate stages).
-/

public section

open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

open Graph

/-! ### The cells of the initial structure, and `≼_abs`

`initialStructure` declares every one of `InitialCell`'s four *named* constructors a cell. The
fifth, `InitialCell.aux`, is the spare supply of fresh names that `def:generated-structure`
needs and that `thm:finite-transfer` asks for as `[Infinite γ]`; no `aux` name is a cell.

`recOnCells` is the shape every clause of assertion (i) below uses: case analysis on a *cell*,
with the spare names ruled out by the membership hypothesis the clause already carries. -/

/-- The spare names are not cells: `cells` is `vertices ∪ edges ∪ faces`, and each of those is a
range of one of the four named constructors. -/
theorem aux_notMem_cells (n : ℕ) : (InitialCell.aux n) ∉ initialStructure.cells :=
  aux_notMem_cellNames n

theorem mem_cells_initialStructure_of_vert (i : Fin 6) :
    (InitialCell.vert i) ∈ initialStructure.cells := Or.inl (Or.inl ⟨i, rfl⟩)

theorem mem_cells_initialStructure_of_edge (i : Fin 6) :
    (InitialCell.edge i) ∈ initialStructure.cells := Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))

theorem mem_cells_initialStructure_of_chord :
    InitialCell.chord ∈ initialStructure.cells := Or.inl (Or.inr (Or.inr rfl))

theorem mem_cells_initialStructure_of_face (k : Bool) :
    (InitialCell.face k) ∈ initialStructure.cells := Or.inr ⟨k, rfl⟩

/-- The four named constructors are cell names. -/
theorem mem_cellNames_of_vert (i : Fin 6) : (InitialCell.vert i) ∈ cellNames :=
  Or.inl (Or.inl ⟨i, rfl⟩)

theorem mem_cellNames_of_edge (i : Fin 6) : (InitialCell.edge i) ∈ cellNames :=
  Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))

theorem mem_cellNames_chord : InitialCell.chord ∈ cellNames := Or.inl (Or.inr (Or.inr rfl))

theorem mem_cellNames_of_face (k : Bool) : (InitialCell.face k) ∈ cellNames := Or.inr ⟨k, rfl⟩

/-- Every cell of a 2-cell's boundary walk is a cell. -/
theorem mem_cells_of_mem_faceCells {k : Bool} {c : InitialCell} (h : c ∈ faceCells k) :
    c ∈ initialStructure.cells := by
  cases k <;>
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        first
          | exact mem_cells_initialStructure_of_vert _
          | exact mem_cells_initialStructure_of_edge _
          | exact mem_cells_initialStructure_of_chord

/-- **Case analysis on a cell of the initial structure.** The four named constructors exhaust
the cells; the spare `aux` names are excluded by the membership hypothesis. -/
def recOnCells {motive : InitialCell → Sort*} {c : InitialCell}
    (hc : c ∈ initialStructure.cells) (hv : ∀ i, motive (.vert i)) (he : ∀ i, motive (.edge i))
    (hch : motive .chord) (hf : ∀ k, motive (.face k)) : motive c := by
  match c with
  | .vert i => exact hv i
  | .edge i => exact he i
  | .chord => exact hch
  | .face k => exact hf k
  | .aux n => exact absurd hc (aux_notMem_cells n)

/-- A `face` name is never a 0-cell or a 1-cell. -/
theorem face_notMem_faceCells {k l : Bool} : InitialCell.face k ∉ faceCells l := by
  cases l <;> simp [faceCells]

/-- The subcells of a 0-cell are itself alone. -/
theorem initSub_iff_vert {i : Fin 6} {c : InitialCell} :
    initSub c (.vert i) ↔ c = .vert i := by
  refine ⟨fun h => ?_, fun h => by subst h; exact initSub_refl (mem_cellNames_of_vert i)⟩
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, hk, -⟩
  · exact h
  · exact absurd h (by simp [InitialCell.edges])
  · exact absurd hk (by simp)

/-- The subcells of an outer 1-cell are itself and its two ends. -/
theorem initSub_iff_edge {i : Fin 6} {c : InitialCell} :
    initSub c (.edge i) ↔ c = .edge i ∨ c = .vert i ∨ c = .vert (i + 1) := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h | h⟩ | ⟨k, hk, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hk (by simp)
  · rintro (rfl | rfl | rfl)
    · exact initSub_refl (mem_cellNames_of_edge i)
    · exact (initSub_ends (InitialCell.edge_mem_edges i)).1
    · exact (initSub_ends (InitialCell.edge_mem_edges i)).2

/-- The subcells of the crosscut are itself and its two ends. -/
theorem initSub_iff_chord {c : InitialCell} :
    initSub c .chord ↔ c = .chord ∨ c = .vert 1 ∨ c = .vert 4 := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h | h⟩ | ⟨k, hk, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hk (by simp)
  · rintro (rfl | rfl | rfl)
    · exact initSub_refl mem_cellNames_chord
    · exact (initSub_ends InitialCell.chord_mem_edges).1
    · exact (initSub_ends InitialCell.chord_mem_edges).2

/-- The subcells of a 2-cell are itself together with the cells of its boundary walk. -/
theorem initSub_iff_face {k : Bool} {c : InitialCell} :
    initSub c (.face k) ↔ c = .face k ∨ c ∈ faceCells k := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨l, hl, hmem⟩)
    · exact Or.inl h
    · exact absurd h (by simp [InitialCell.edges])
    · cases hl; exact Or.inr hmem
  · rintro (rfl | h)
    · exact initSub_refl (mem_cellNames_of_face k)
    · exact initSub_face h

/-! ### The combinatorial invariants at the base

`Schoenflies.GeneratedStructure.combInvariants` propagates `lem:cellulation-invariants` (iii),
(v), (vi) and abstract (viii) along the two elementary operations *given the base case*. This is
the base case. Assertion (vi) is `Schoenflies.outerEdgeUniqueFace_initialStructure`, already on
`main`; the other seven clauses are read off `initSub`. -/

/-- **The combinatorial invariants hold for the initial structure.** The base case of
`Schoenflies.GeneratedStructure.combInvariants`, hence of `GeneratedPair.combInvariants`. -/
theorem combInvariants_initialStructure : initialStructure.CombInvariants where
  sub_mem_left := by
    rintro c d (⟨rfl, hc⟩ | ⟨hd, rfl | rfl⟩ | ⟨k, rfl, hmem⟩)
    · exact hc
    · exact Or.inl (Or.inl (InitialCell.ends_mem_vertices hd).1)
    · exact Or.inl (Or.inl (InitialCell.ends_mem_vertices hd).2)
    · exact mem_cells_of_mem_faceCells hmem
  sub_mem_right := by
    rintro c d (⟨-, hd⟩ | ⟨hd, -⟩ | ⟨k, rfl, -⟩)
    · exact hd
    · exact Or.inl (Or.inr hd)
    · exact mem_cells_initialStructure_of_face k
  sub_refl := fun {_} hc => initSub_refl hc
  sub_isLink := by
    rintro f a b ⟨hf, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    exacts [(initSub_ends hf).1, (initSub_ends hf).2]
  face_maximal := by
    rintro F τ ⟨k, rfl⟩ h
    rcases h with ⟨h, -⟩ | ⟨he, hends⟩ | ⟨l, rfl, hmem⟩
    · exact h.symm
    · -- both ends of a 1-cell are 0-cells, and a 2-cell name is neither
      rcases he with ⟨j, rfl⟩ | rfl <;> simp [InitialCell.ends] at hends
    · exact absurd hmem face_notMem_faceCells
  nonboundary_edge := by
    rintro F ⟨k, rfl⟩
    refine ⟨.chord, InitialCell.chord_mem_edges, by simp [InitialCell.outerEdges], ?_⟩
    exact initSub_face (by cases k <;> simp [faceCells])
  mem_face := by
    rintro c hc
    -- every cell appears among the subcells of one of the two 2-cells
    cases c with
    | aux n => exact absurd hc (aux_notMem_cells n)
    | vert i =>
      refine ⟨.face (![true, false, false, false, true, true] i), ⟨_, rfl⟩, initSub_face ?_⟩
      fin_cases i <;> simp [faceCells]
    | edge i =>
      refine ⟨.face (![true, false, false, false, true, true] i), ⟨_, rfl⟩, initSub_face ?_⟩
      fin_cases i <;> simp [faceCells]
    | chord => exact ⟨.face false, ⟨_, rfl⟩, initSub_face (by simp [faceCells])⟩
    | face k => exact ⟨.face k, ⟨k, rfl⟩, initSub_refl (mem_cellNames_of_face k)⟩
  outerEdge_unique := outerEdgeUniqueFace_initialStructure

/-! ### The open cells of a `HexData`

Everything assertion (i) needs about the fifteen realized open cells, stated for an arbitrary
`HexData` so that the source and the target realization are served by one proof. Nothing in this
section mentions the crosscut configuration; that enters only for the two 2-cells. -/

namespace HexData

variable (H : HexData)

@[simp] theorem cellSet_vert (i : Fin 6) : H.cellSet (.vert i) = {H.pos i} := rfl

@[simp] theorem cellSet_edge (i : Fin 6) :
    H.cellSet (.edge i) = H.outer i '' I \ {H.pos i, H.pos (i + 1)} := rfl

@[simp] theorem cellSet_chord : H.cellSet .chord = H.chordSet \ {H.pos 1, H.pos 4} := rfl

@[simp] theorem cellSet_face (k : Bool) :
    H.cellSet (.face k) = inside (H.arcOf k ∪ H.chordSet) := rfl

theorem cellSet_edge_subset (i : Fin 6) : H.cellSet (.edge i) ⊆ H.outer i '' I := sdiff_subset

theorem cellSet_edge_subset_outerArcs (i : Fin 6) : H.cellSet (.edge i) ⊆ H.outerArcs :=
  (H.cellSet_edge_subset i).trans (Set.subset_iUnion (fun i : Fin 6 => H.outer i '' I) i)

theorem cellSet_chord_subset : H.cellSet .chord ⊆ H.chordSet := sdiff_subset

theorem pos_mem_outerArcs (i : Fin 6) : H.pos i ∈ H.outerArcs :=
  Set.mem_iUnion.2 ⟨i, H.pos_mem_outer i⟩

/-- **The 1-cells are nonempty**: an arc has more points than its two endpoints. -/
theorem nonempty_cellSet_edge (i : Fin 6) : (H.cellSet (.edge i)).Nonempty :=
  (H.isArcBetween_outer i).nonempty_diff

theorem nonempty_cellSet_chord : (H.cellSet .chord).Nonempty :=
  H.isArcBetween_chordSet.nonempty_diff

/-- **A closed 1-cell is the drawn edge**: an arc is the closure of its interior. -/
theorem closure_cellSet_edge (i : Fin 6) :
    closure (H.cellSet (.edge i)) = H.outer i '' I :=
  (H.isArcBetween_outer i).closure_diff

theorem closure_cellSet_chord : closure (H.cellSet .chord) = H.chordSet :=
  H.isArcBetween_chordSet.closure_diff

/-- **A 0-cell never lies on an open 1-cell.** A vertex on a drawn outer edge is one of its two
ends (`HexData.mem_outer_iff`), and the open edge is exactly the drawn edge without them. -/
theorem pos_notMem_cellSet_edge (k i : Fin 6) : H.pos k ∉ H.cellSet (.edge i) := by
  rintro ⟨hz, hne⟩
  rcases H.mem_outer_iff hz with rfl | rfl
  exacts [hne (Or.inl rfl), hne (Or.inr rfl)]

theorem pos_notMem_cellSet_chord (k : Fin 6) : H.pos k ∉ H.cellSet .chord := by
  rintro ⟨hz, hne⟩
  rcases H.mem_chord_iff hz with rfl | rfl
  exacts [hne (Or.inl rfl), hne (Or.inr rfl)]

/-- **Two distinct open outer 1-cells are disjoint.** The two edges meet only at points that are
ends of both, and those are removed. -/
theorem disjoint_cellSet_edge {i j : Fin 6} (hij : i ≠ j) :
    Disjoint (H.cellSet (.edge i)) (H.cellSet (.edge j)) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzi, hne⟩ ⟨hzj, -⟩
  exact hne (H.outer_meet i j hij ⟨hzi, hzj⟩).1

/-- **The open crosscut misses every open outer 1-cell.** -/
theorem disjoint_cellSet_edge_chord (i : Fin 6) :
    Disjoint (H.cellSet (.edge i)) (H.cellSet .chord) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzi, -⟩ ⟨hzc, hne⟩
  exact hne (H.chord_meet i ⟨hzc, hzi⟩)

/-- A point of a drawn outer edge is on the open edge or is one of its two ends. -/
theorem mem_cellSet_edge_or {i : Fin 6} {z : Plane} (hz : z ∈ H.outer i '' I) :
    z ∈ H.cellSet (.edge i) ∨ z = H.pos i ∨ z = H.pos (i + 1) := by
  by_cases h : z ∈ ({H.pos i, H.pos (i + 1)} : Set Plane)
  · rcases h with h | h
    exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]
  · exact Or.inl ⟨hz, h⟩

/-- A point of the crosscut is on the open crosscut or is one of its two ends. -/
theorem mem_cellSet_chord_or {z : Plane} (hz : z ∈ H.chordSet) :
    z ∈ H.cellSet .chord ∨ z = H.pos 1 ∨ z = H.pos 4 := by
  by_cases h : z ∈ ({H.pos 1, H.pos 4} : Set Plane)
  · rcases h with h | h
    exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]
  · exact Or.inl ⟨hz, h⟩

/-- **The 0-cells and the open 1-cells reassemble the skeleton `C ∪ P`.** -/
theorem iUnion_cellSet (H : HexData) :
    (⋃ c : InitialCell, H.cellSet c) =
      (H.outerArcs ∪ H.chordSet) ∪ (H.cellSet (.face false) ∪ H.cellSet (.face true)) := by
  refine Subset.antisymm (Set.iUnion_subset fun c => ?_) fun z hz => ?_
  · cases c with
    | vert i =>
      rintro z rfl
      exact Or.inl (Or.inl (H.pos_mem_outerArcs i))
    | edge i => exact fun z hz => Or.inl (Or.inl (H.cellSet_edge_subset_outerArcs i hz))
    | chord => exact fun z hz => Or.inl (Or.inr (H.cellSet_chord_subset hz))
    | aux n => exact Set.empty_subset _
    | face k =>
      cases k
      exacts [fun z hz => Or.inr (Or.inl hz), fun z hz => Or.inr (Or.inr hz)]
  · rcases hz with (hz | hz) | (hz | hz)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
      rcases H.mem_cellSet_edge_or hi with h | rfl | rfl
      exacts [Set.mem_iUnion.2 ⟨.edge i, h⟩, Set.mem_iUnion.2 ⟨.vert i, rfl⟩,
        Set.mem_iUnion.2 ⟨.vert (i + 1), rfl⟩]
    · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion.2 ⟨.chord, h⟩, Set.mem_iUnion.2 ⟨.vert 1, rfl⟩,
        Set.mem_iUnion.2 ⟨.vert 4, rfl⟩]
    · exact Set.mem_iUnion.2 ⟨.face false, hz⟩
    · exact Set.mem_iUnion.2 ⟨.face true, hz⟩

/-- **Three consecutive outer edges and the crosscut reassemble their union.** The two 2-cells of
the initial structure differ only in *which* three outer edges bound them, so the union over the
cells of a boundary walk is computed once, for an arbitrary set `F` of cells presented as the
four vertices, the three edges and the crosscut. -/
theorem biUnion_of_three_edges (H : HexData) (F : Set InitialCell) {i j l : Fin 6}
    (hij : i + 1 = j) (hjl : j + 1 = l)
    (hmem : ∀ c ∈ F, c = .vert i ∨ c = .vert j ∨ c = .vert l ∨ c = .vert (l + 1) ∨
      c = .edge i ∨ c = .edge j ∨ c = .edge l ∨ c = .chord)
    (hvi : InitialCell.vert i ∈ F) (hvj : InitialCell.vert j ∈ F)
    (hvl : InitialCell.vert l ∈ F) (hvl1 : InitialCell.vert (l + 1) ∈ F)
    (hei : InitialCell.edge i ∈ F) (hej : InitialCell.edge j ∈ F)
    (hel : InitialCell.edge l ∈ F) (hch : InitialCell.chord ∈ F)
    (hv1 : InitialCell.vert 1 ∈ F) (hv4 : InitialCell.vert 4 ∈ F) :
    (⋃ c ∈ F, H.cellSet c)
      = (H.outer i '' I ∪ (H.outer j '' I ∪ H.outer l '' I)) ∪ H.chordSet := by
  refine Subset.antisymm (Set.iUnion₂_subset fun c hc => ?_) fun z hz => ?_
  · rcases hmem c hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rintro z rfl; exact Or.inl (Or.inl (H.pos_mem_outer i))
    · rintro z rfl; exact Or.inl (Or.inl (H.pos_mem_outer_of_succ hij))
    · rintro z rfl; exact Or.inl (Or.inr (Or.inl (H.pos_mem_outer_of_succ hjl)))
    · rintro z rfl; exact Or.inl (Or.inr (Or.inr (H.pos_succ_mem_outer l)))
    · exact fun z hz => Or.inl (Or.inl (H.cellSet_edge_subset i hz))
    · exact fun z hz => Or.inl (Or.inr (Or.inl (H.cellSet_edge_subset j hz)))
    · exact fun z hz => Or.inl (Or.inr (Or.inr (H.cellSet_edge_subset l hz)))
    · exact fun z hz => Or.inr (H.cellSet_chord_subset hz)
  · rcases hz with (hz | hz | hz) | hz
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hei, h⟩, Set.mem_iUnion₂.2 ⟨_, hvi, rfl⟩,
        Set.mem_iUnion₂.2 ⟨InitialCell.vert (i + 1), by rw [hij]; exact hvj, rfl⟩]
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hej, h⟩, Set.mem_iUnion₂.2 ⟨_, hvj, rfl⟩,
        Set.mem_iUnion₂.2 ⟨InitialCell.vert (j + 1), by rw [hjl]; exact hvl, rfl⟩]
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hel, h⟩, Set.mem_iUnion₂.2 ⟨_, hvl, rfl⟩,
        Set.mem_iUnion₂.2 ⟨_, hvl1, rfl⟩]
    · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hch, h⟩, Set.mem_iUnion₂.2 ⟨_, hv1, rfl⟩,
        Set.mem_iUnion₂.2 ⟨_, hv4, rfl⟩]

/-- **The cells of a 2-cell's boundary walk reassemble `Aₖ ∪ P`.** The blueprint declares
`faceCells k` to be the subcells of `Rₖ`; geometrically that union is exactly the boundary curve
of `Rₖ`, which is what `closure_eq` has to match at a 2-cell. -/
theorem biUnion_faceCells (H : HexData) (k : Bool) :
    (⋃ c ∈ faceCells k, H.cellSet c) = H.arcOf k ∪ H.chordSet := by
  cases k
  · rw [HexData.arcOf_false]
    refine H.biUnion_of_three_edges _ (i := 1) (j := 2) (l := 3) (by decide) (by decide)
      (fun c hc => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    all_goals (simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff]; decide)
  · rw [HexData.arcOf_true]
    refine H.biUnion_of_three_edges _ (i := 4) (j := 5) (l := 0) (by decide) (by decide)
      (fun c hc => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    all_goals (simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff]; decide)

/-! ### Assertion (i) and `def:admissible-graph`, for either realization

Both realizations of `prop:initial-pair` are a `HexData` whose six outer arcs form a Jordan curve
and whose chord is a crosscut of it. Everything that distinguishes assertion (i) from bookkeeping
is `thm:general-crosscut`, in the packaged form `Schoenflies.crosscut_cell_partition`: the two
2-cells are open, nonempty, disjoint from each other and from the open crosscut, they exhaust
`D ∖ P` together with it, and the closure of each is itself together with its own boundary
curve. -/

/-- **`lem:cellulation-invariants`(i) for a realization of the initial structure.** The open cells
are nonempty and pairwise disjoint, they cover `C ∪ D`, and every closed cell is the union of its
open subcells for the base value of `≼_abs` the blueprint fixes.

The three hypotheses are exactly `thm:general-crosscut`'s: the chord is a crosscut of the outer
cycle, the two boundary arcs are the two arcs it cuts the outer cycle into, and the crosscut has
collars. On the source side they are `InitialData.isCrosscut`, `.isCutPair` and
`.hasArcCollarsSource`; on the target side `.isCrosscutTarget`, `.isCutPairTarget` and
`.hasArcCollarsTarget`. -/
theorem isCellDecomposition (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4))
    (hcut : IsCutPair H.outerArcs (H.pos 1) (H.pos 4) (H.arcOf false) (H.arcOf true))
    (hcollars : HasArcCollars (inside H.outerArcs) H.chordSet) :
    H.realization.IsCellDecomposition (H.outerArcs ∪ inside H.outerArcs) := by
  obtain ⟨hsplit, hdisj12, hdisj1P, hdisj2P, -, -, hne1, hne2, hcl1, hcl2⟩ :=
    crosscut_cell_partition forall_isSeparating_of_isJordanCurve hcross hcut hcollars
  -- the four facts about the two 2-cells, indexed by the label
  have hface : ∀ k : Bool, H.cellSet (.face k) ⊆ inside H.outerArcs := by
    intro k z hz
    rw [hsplit]
    cases k
    exacts [Or.inl (Or.inl hz), Or.inl (Or.inr hz)]
  have hfaceOuter : ∀ k : Bool, Disjoint (H.cellSet (.face k)) H.outerArcs := by
    intro k
    rw [Set.disjoint_left]
    exact fun z hz hzo => (hface k hz).1 hzo
  have hfaceChord : ∀ k : Bool, Disjoint (H.cellSet (.face k)) (H.cellSet .chord) := by
    intro k; cases k; exacts [hdisj1P, hdisj2P]
  have hfaceNe : ∀ k : Bool, (H.cellSet (.face k)).Nonempty := by
    intro k; cases k; exacts [hne1, hne2]
  have hfaceCl : ∀ k : Bool,
      closure (H.cellSet (.face k)) = H.cellSet (.face k) ∪ (H.arcOf k ∪ H.chordSet) := by
    intro k; cases k; exacts [hcl1, hcl2]
  -- the mixed-dimension disjointness facts, stated once
  have hvertEdge : ∀ k i : Fin 6, Disjoint (H.cellSet (.vert k)) (H.cellSet (.edge i)) := by
    intro k i
    rw [Set.disjoint_left]
    rintro z rfl h
    exact H.pos_notMem_cellSet_edge k i h
  have hvertChord : ∀ k : Fin 6, Disjoint (H.cellSet (.vert k)) (H.cellSet .chord) := by
    intro k
    rw [Set.disjoint_left]
    rintro z rfl h
    exact H.pos_notMem_cellSet_chord k h
  have hvertFace : ∀ (k : Fin 6) (l : Bool),
      Disjoint (H.cellSet (.vert k)) (H.cellSet (.face l)) := by
    intro k l
    rw [Set.disjoint_left]
    rintro z rfl h
    exact (hface l h).1 (H.pos_mem_outerArcs k)
  have hedgeFace : ∀ (i : Fin 6) (l : Bool),
      Disjoint (H.cellSet (.edge i)) (H.cellSet (.face l)) :=
    fun i l => (hfaceOuter l).symm.mono_left (H.cellSet_edge_subset_outerArcs i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- every open cell is nonempty
    rintro c hc
    cases c with
    | aux n => exact absurd hc (aux_notMem_cells n)
    | vert i => exact ⟨H.pos i, rfl⟩
    | edge i => exact H.nonempty_cellSet_edge i
    | chord => exact H.nonempty_cellSet_chord
    | face k => exact hfaceNe k
  · -- distinct open cells are disjoint
    rintro c d hc hd hcd
    cases c with
    | aux n => exact absurd hc (aux_notMem_cells n)
    | vert k =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m =>
        rw [Set.disjoint_left]
        rintro z rfl h
        exact hcd (congrArg InitialCell.vert (H.injective_pos h))
      | edge i => exact hvertEdge k i
      | chord => exact hvertChord k
      | face l => exact hvertFace k l
    | edge i =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m => exact (hvertEdge m i).symm
      | edge j => exact H.disjoint_cellSet_edge fun h => hcd (congrArg InitialCell.edge h)
      | chord => exact H.disjoint_cellSet_edge_chord i
      | face l => exact hedgeFace i l
    | chord =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m => exact (hvertChord m).symm
      | edge j => exact (H.disjoint_cellSet_edge_chord j).symm
      | chord => exact absurd rfl hcd
      | face l => exact (hfaceChord l).symm
    | face k =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m => exact (hvertFace m k).symm
      | edge j => exact (hedgeFace j k).symm
      | chord => exact hfaceChord k
      | face l =>
        cases k <;> cases l
        exacts [absurd rfl hcd, hdisj12, hdisj12.symm, absurd rfl hcd]
  · -- the open cells cover `C ∪ D`
    have hall : (⋃ c ∈ initialStructure.cells, H.realization.cell c)
        = ⋃ c : InitialCell, H.cellSet c := by
      refine Subset.antisymm (Set.iUnion₂_subset fun c _ => Set.subset_iUnion _ c)
        (Set.iUnion_subset fun c => ?_)
      match c with
      | .vert i => exact Set.subset_biUnion_of_mem (mem_cells_initialStructure_of_vert i)
      | .edge i => exact Set.subset_biUnion_of_mem (mem_cells_initialStructure_of_edge i)
      | .chord => exact Set.subset_biUnion_of_mem mem_cells_initialStructure_of_chord
      | .face k => exact Set.subset_biUnion_of_mem (mem_cells_initialStructure_of_face k)
      | .aux n => exact Set.empty_subset _
    rw [hall, H.iUnion_cellSet]
    refine Subset.antisymm (Set.union_subset (Set.union_subset Set.subset_union_left ?_) ?_) ?_
    · intro z hz
      rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      · exact Or.inr (by rw [hsplit]; exact Or.inr h)
      · exact Or.inl (H.pos_mem_outerArcs 1)
      · exact Or.inl (H.pos_mem_outerArcs 4)
    · rintro z (hz | hz)
      exacts [Or.inr (hface false hz), Or.inr (hface true hz)]
    · rintro z (hz | hz)
      · exact Or.inl (Or.inl hz)
      · rw [hsplit] at hz
        rcases hz with (hz | hz) | hz
        exacts [Or.inr (Or.inl hz), Or.inr (Or.inr hz),
          Or.inl (Or.inr (H.cellSet_chord_subset hz))]
  · -- every closed cell is the union of its open subcells
    rintro τ hτ
    have hidx : {c | c ∈ initialStructure.cells ∧ initialStructure.sub c τ}
        = {c | initSub c τ} := by
      ext c
      exact ⟨fun h => h.2, fun h => ⟨combInvariants_initialStructure.sub_mem_left h, h⟩⟩
    rw [hidx]
    cases τ with
    | aux n => exact absurd hτ (aux_notMem_cells n)
    | vert i =>
      have hset : {c | initSub c (.vert i)} = ({InitialCell.vert i} : Set InitialCell) := by
        ext c; exact initSub_iff_vert
      rw [hset, Set.biUnion_singleton]
      exact closure_singleton
    | edge i =>
      have hset : {c | initSub c (.edge i)}
          = ({InitialCell.edge i, .vert i, .vert (i + 1)} : Set InitialCell) := by
        ext c; exact initSub_iff_edge
      rw [hset]
      change closure (H.cellSet (.edge i)) = _
      rw [H.closure_cellSet_edge i]
      refine Subset.antisymm (fun z hz => ?_) ?_
      · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
        exacts [Set.mem_iUnion₂.2 ⟨_, Or.inl rfl, h⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inl rfl), rfl⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inr rfl), rfl⟩]
      · refine Set.iUnion₂_subset fun c hc => ?_
        rcases hc with rfl | rfl | rfl
        · exact H.cellSet_edge_subset i
        · rintro z rfl; exact H.pos_mem_outer i
        · rintro z rfl; exact H.pos_succ_mem_outer i
    | chord =>
      have hset : {c | initSub c .chord}
          = ({InitialCell.chord, .vert 1, .vert 4} : Set InitialCell) := by
        ext c; exact initSub_iff_chord
      rw [hset]
      change closure (H.cellSet .chord) = _
      rw [H.closure_cellSet_chord]
      refine Subset.antisymm (fun z hz => ?_) ?_
      · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
        exacts [Set.mem_iUnion₂.2 ⟨_, Or.inl rfl, h⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inl rfl), rfl⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inr rfl), rfl⟩]
      · refine Set.iUnion₂_subset fun c hc => ?_
        rcases hc with rfl | rfl | rfl
        · exact H.cellSet_chord_subset
        · rintro z rfl
          exact ⟨0, zero_mem_I, H.chord_zero⟩
        · rintro z rfl
          exact ⟨1, one_mem_I, H.chord_one⟩
    | face k =>
      have hset : {c | initSub c (.face k)} = insert (InitialCell.face k) (faceCells k) := by
        ext c; exact initSub_iff_face
      rw [hset, Set.biUnion_insert]
      change closure (H.cellSet (.face k))
        = H.cellSet (.face k) ∪ ⋃ x ∈ faceCells k, H.cellSet x
      rw [H.biUnion_faceCells k]
      exact hfaceCl k

/-- **The two 2-cells are open.** `IsCellDecomposition` does not record this, but
`IsCellDecomposition.face_eq` — assertion (viii) — takes it as a hypothesis, and
`thm:general-crosscut` hands it to the producer for free. Exported here so that no consumer has
to rederive it at stage 0. -/
theorem isOpen_cellSet_face (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4))
    (hcut : IsCutPair H.outerArcs (H.pos 1) (H.pos 4) (H.arcOf false) (H.arcOf true))
    (hcollars : HasArcCollars (inside H.outerArcs) H.chordSet) (k : Bool) :
    IsOpen (H.cellSet (.face k)) := by
  obtain ⟨-, -, -, -, hopen1, hopen2, -⟩ :=
    crosscut_cell_partition forall_isSeparating_of_isJordanCurve hcross hcut hcollars
  cases k
  exacts [hopen1, hopen2]

/-- **Assertion (vii) for the initial hexagonal cellulation.**  Each of its two faces was
defined as the inside of the curve obtained by joining one boundary arc to the crosscut; the
crosscut theorem says that curve is Jordan. -/
theorem isFaceJordan (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4))
    (hcut : IsCutPair H.outerArcs (H.pos 1) (H.pos 4) (H.arcOf false) (H.arcOf true)) :
    H.realization.IsFaceJordan where
  isJordanCurve := by
    intro F hF
    obtain ⟨k, rfl⟩ := hF
    cases k
    · change IsJordanCurve (frontier (H.cellSet (.face false)))
      rw [H.cellSet_face,
        (jordan_curve_theorem (hcross.isJordanCurve_union hcut)).frontier_inside]
      exact hcross.isJordanCurve_union hcut
    · change IsJordanCurve (frontier (H.cellSet (.face true)))
      rw [H.cellSet_face,
        (jordan_curve_theorem (hcross.isJordanCurve_union hcut.symm)).frontier_inside]
      exact hcross.isJordanCurve_union hcut.symm
  cell_eq_inside := by
    intro F hF
    obtain ⟨k, rfl⟩ := hF
    cases k
    · change inside (H.arcOf false ∪ H.chordSet) =
        inside (frontier (inside (H.arcOf false ∪ H.chordSet)))
      rw [(jordan_curve_theorem (hcross.isJordanCurve_union hcut)).frontier_inside]
    · change inside (H.arcOf true ∪ H.chordSet) =
        inside (frontier (inside (H.arcOf true ∪ H.chordSet)))
      rw [(jordan_curve_theorem (hcross.isJordanCurve_union hcut.symm)).frontier_inside]

/-- **`def:admissible-graph` minus the connectedness clause, for a realization of the initial
structure.** The 2-connectivity is `HexData.isTwoConnected_graph`; the outer cycle is the union
of the six outer arcs by construction; the one nonboundary edge is the crosscut, which is
polygonal and has its interior in the open domain because it is a crosscut.

`rem:intermediate-disconnection` waives connectedness of the open nonboundary part at
intermediate stages only. The initial pair does satisfy it — `HexData.isConnected_nonboundary` —
and `InitialData.generatedPair_isAdmissible` records the strong form. -/
theorem isWeaklyAdmissible (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4)) :
    H.realization.IsWeaklyAdmissible H.outerArcs (H.outerArcs ∪ inside H.outerArcs) where
  isTwoConnected := H.isTwoConnected_graph
  outerSet_eq := H.outerSet_realization
  isPolygonal := by
    rintro e he hne
    -- the only nonboundary 1-cell is the crosscut
    rcases (he : e ∈ InitialCell.edges) with ⟨i, rfl⟩ | rfl
    · exact absurd (Set.mem_range_self i) hne
    · exact hcross.polygonal
  cell_subset := by
    rintro e he hne
    rcases (he : e ∈ InitialCell.edges) with ⟨i, rfl⟩ | rfl
    · exact absurd (Set.mem_range_self i) hne
    · intro z hz
      exact ⟨Or.inr (hcross.sdiff_subset hz), (hcross.sdiff_subset hz).1⟩
  skeletonSet_subset := by
    rw [H.skeletonSet_realization]
    refine Set.union_subset Set.subset_union_left fun z hz => ?_
    rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
    · exact Or.inr (hcross.sdiff_subset h)
    · exact Or.inl (H.pos_mem_outerArcs 1)
    · exact Or.inl (H.pos_mem_outerArcs 4)

end HexData

/-! ### The closed square, as a domain

`GeneratedPair` asks for the *closed* target domain. `Schoenflies.inside_modelCurve` identifies
the Jordan domain of `S` with the open square, so the closed domain `S ∪ Int(S)` is literally
`Q = [-1,1]²`. -/

/-- **`S ∪ Int(S) = Q`.** -/
theorem modelCurve_union_inside : modelCurve ∪ inside modelCurve = Plane.closedSquare 0 1 := by
  rw [inside_modelCurve]
  ext x
  rw [Set.mem_union, mem_openSquare_zero_one, mem_closedSquare_zero_one]
  constructor
  · rintro (h | h)
    · exact le_of_eq (h : Plane.supNorm x = 1)
    · exact h.le
  · intro h
    rcases lt_or_eq_of_le h with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

/-! ### The initial pair is a `GeneratedPair`

Both realizations are instances of the two `HexData` theorems above; all that is left is to
present the hypotheses in the shape they take, which on the source side means rewriting
`d.src.outerArcs` to `C` and on the target side `d.tgt.outerArcs` to `S`. -/

namespace InitialData

variable {C : Set Plane} (d : InitialData C)

/-- The crosscut configuration on the source side, with the outer cycle named as the `HexData`
sees it. -/
theorem isCrosscut_src : IsCrosscut d.src.outerArcs d.src.chordSet (d.src.pos 1) (d.src.pos 4) := by
  rw [d.src_outerArcs]; exact d.isCrosscut

/-- The crosscut configuration on the target side. -/
theorem isCrosscut_tgt : IsCrosscut d.tgt.outerArcs d.tgt.chordSet (d.tgt.pos 1) (d.tgt.pos 4) := by
  rw [d.tgt_outerArcs]; exact d.isCrosscutTarget

/-- **Assertion (i) on the source side**: the fifteen open cells of `Γ` decompose `C ∪ D`. -/
theorem src_isCellDecomposition : d.sourceRealization.IsCellDecomposition (C ∪ inside C) := by
  have h := d.src.isCellDecomposition d.isCrosscut_src
    (by rw [d.src_outerArcs]; exact d.isCutPair)
    (by rw [d.src_outerArcs]; exact d.hasArcCollarsSource)
  rwa [d.src_outerArcs] at h

/-- **Assertion (i) on the target side**: the fifteen open cells of `Γ'` decompose `Q`. -/
theorem tgt_isCellDecomposition :
    d.targetRealization.IsCellDecomposition (Plane.closedSquare 0 1) := by
  have h := d.tgt.isCellDecomposition d.isCrosscut_tgt
    (by rw [d.tgt_outerArcs]; exact d.isCutPairTarget)
    (by rw [d.tgt_outerArcs]; exact d.hasArcCollarsTarget)
  rwa [d.tgt_outerArcs, modelCurve_union_inside] at h

/-- **`def:admissible-graph` (weak form) on the source side.** -/
theorem src_isWeaklyAdmissible : d.sourceRealization.IsWeaklyAdmissible C (C ∪ inside C) := by
  have h := d.src.isWeaklyAdmissible d.isCrosscut_src
  rwa [d.src_outerArcs] at h

/-- **`def:admissible-graph` (weak form) on the target side.** -/
theorem tgt_isWeaklyAdmissible :
    d.targetRealization.IsWeaklyAdmissible modelCurve (Plane.closedSquare 0 1) := by
  have h := d.tgt.isWeaklyAdmissible d.isCrosscut_tgt
  rwa [d.tgt_outerArcs, modelCurve_union_inside] at h

/-- **The two source 2-cells are open** — the hypothesis
`IsCellDecomposition.face_eq` takes and `IsCellDecomposition` does not record. -/
theorem isOpen_sourceRealization_cell_face (k : Bool) :
    IsOpen (d.sourceRealization.cell (.face k)) :=
  d.src.isOpen_cellSet_face d.isCrosscut_src (by rw [d.src_outerArcs]; exact d.isCutPair)
    (by rw [d.src_outerArcs]; exact d.hasArcCollarsSource) k

/-- **The two target 2-cells are open.** -/
theorem isOpen_targetRealization_cell_face (k : Bool) :
    IsOpen (d.targetRealization.cell (.face k)) :=
  d.tgt.isOpen_cellSet_face d.isCrosscut_tgt (by rw [d.tgt_outerArcs]; exact d.isCutPairTarget)
    (by rw [d.tgt_outerArcs]; exact d.hasArcCollarsTarget) k

/-- **Stage 0 of the Schönflies recursion.** The initial matched pair of `prop:initial-pair` is a
generated matched cellulation: it is generated from `Schoenflies.initialStructure` by the empty
sequence of elementary operations (`GeneratedStructure.base`), its two realizations are the two
realizations of `prop:initial-pair`, and the two cell decompositions are
`lem:cellulation-invariants`(i) on each side.

This is the base case of the whole construction: `thm:finite-transfer` consumes a `GeneratedPair`
and produces one, and this is the first. -/
noncomputable def generatedPair :
    GeneratedPair initialStructure C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) where
  str := initialStructure
  generated := GeneratedStructure.base
  str_combInvariants := combInvariants_initialStructure
  str_boundaryCycles := boundaryCycles_initialStructure
  src := d.sourceRealization
  tgt := d.targetRealization
  homeo := d.skeletonHomeo
  src_isCellDecomposition := d.src_isCellDecomposition
  tgt_isCellDecomposition := d.tgt_isCellDecomposition
  src_isFaceJordan := d.src.isFaceJordan d.isCrosscut_src
    (by rw [d.src_outerArcs]; exact d.isCutPair)
  tgt_isFaceJordan := d.tgt.isFaceJordan d.isCrosscut_tgt
    (by rw [d.tgt_outerArcs]; exact d.isCutPairTarget)
  tgtInterior_isOpen := by
    rw [closedSquare_sdiff_modelCurve]
    exact Plane.isOpen_openSquare 0 1
  tgtInterior_frontier_subset := by
    rw [closedSquare_sdiff_modelCurve]
    refine (Plane.frontier_openSquare_subset 0 1).trans ?_
    rw [← modelCurve_eq_frontier, ← d.tgt_isWeaklyAdmissible.outerSet_eq]
    exact d.targetRealization.outerSet_subset_skeletonSet
  tgt_isPolygonal := by
    intro e he
    change e ∈ E(initSkel) at he
    change IsPolygonal (Graph.edgeArc d.tgt.draw e)
    exact d.isPolygonal_tgt_edgeArc he
  src_isWeaklyAdmissible := d.src_isWeaklyAdmissible
  tgt_isWeaklyAdmissible := d.tgt_isWeaklyAdmissible

@[simp] theorem generatedPair_str : d.generatedPair.str = initialStructure := rfl

@[simp] theorem generatedPair_src : d.generatedPair.src = d.sourceRealization := rfl

@[simp] theorem generatedPair_tgt : d.generatedPair.tgt = d.targetRealization := rfl

@[simp] theorem generatedPair_homeo : d.generatedPair.homeo = d.skeletonHomeo := rfl

/-- The combinatorial invariants at stage 0, read off the bundle: this is what
`GeneratedPair.combInvariants` needs supplied at the base, and what every later stage inherits. -/
theorem generatedPair_combInvariants : d.generatedPair.str.CombInvariants :=
  d.generatedPair.combInvariants combInvariants_initialStructure

/-- **The initial pair is admissible in the strong sense**, on both sides.
`rem:intermediate-disconnection` waives connectedness of the open nonboundary part at
intermediate stages; at stage 0 it holds, the open nonboundary part being the open crosscut. -/
theorem generatedPair_src_isAdmissible :
    d.generatedPair.src.IsAdmissible C (C ∪ inside C) :=
  d.generatedPair.src_isAdmissible d.isConnected_sourceRealization_nonboundary

theorem generatedPair_tgt_isAdmissible :
    d.generatedPair.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) :=
  d.generatedPair.tgt_isAdmissible d.isConnected_sourceRealization_nonboundary

end InitialData

/-- **Stage 0 from the anchored initial pair.** `AnchoredInitialData` adds only the clause
`a, b ∈ 𝒜`, which no field of `GeneratedPair` mentions; it is what lets a later stage run a fresh
crosscut into `a` or `b` (`AnchoredInitialData.stronglyAccessible_a`). So the pair is built from
the underlying `InitialData`, and this is the specialisation for a consumer holding the anchored
form. -/
noncomputable def AnchoredInitialData.generatedPair {C : Set Plane} {A : AnchorSet C}
    (D : AnchoredInitialData C A) :
    GeneratedPair initialStructure C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  D.toInitialData.generatedPair

/-! ### The base case meets the recursion

`Schoenflies.finite_transfer_toward_square` and `Schoenflies.EarStep` carry `[Infinite γ]`, and
`FiniteTransfer.lean` argues that without it `EarStep` is *false*: an ear insertion consumes
fresh cell names for the ear's interior vertices, its edges and the two 2-cells the split
creates, so a naming type that the current stage has exhausted refutes it.

The initial structure names fifteen cells. `InitialCell` therefore carries a fifth constructor,
`InitialCell.aux : ℕ → InitialCell`, which is the spare supply and nothing else: no `aux` name is
a cell, every `aux` name has empty open cell, and `initSub` relates none of them — the reflexive
clause of `≼_abs` is restricted to `Schoenflies.cellNames` precisely so that
`CombInvariants.sub_mem_left` and `.sub_mem_right`, which say that `≼_abs` relates cells to
cells, stay true.

The alternative was a relabelling of a `CellStructure` and both of its realizations along an
injection `InitialCell ↪ γ` into an infinite naming type. That is several hundred lines and buys
nothing the spare constructor does not, since the base of `GeneratedStructure` is a parameter and
stage 0 uses only the `base` constructor — no inductive derivation has to be transported. -/

instance : Infinite InitialCell :=
  Infinite.of_injective InitialCell.aux fun _ _ h => by injection h

/-- **The naming type of the initial structure is infinite**, so the base case really can be fed
to `thm:finite-transfer`, whose `[Infinite γ]` is not decoration: an ear insertion consumes fresh
cell names, and on a finite naming type `Schoenflies.EarStep` is false. The supply is
`InitialCell.aux`, and no `aux` name is a cell of `initialStructure`. -/
theorem infinite_initialCell : Infinite InitialCell := inferInstance

/-! ### The interface, exercised

A machine-checked statement that stage 0 delivers exactly what `thm:finite-transfer` reads off a
`GeneratedPair`: the abstract structure carries the combinatorial invariants, the source and
target realizations are cell decompositions of the two closed domains, and both are admissible in
the strong sense. Nothing below mentions how the pair was built. -/
example {C : Set Plane} (hC : IsJordanCurve C) :
    ∃ P : GeneratedPair initialStructure C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1),
      P.str.CombInvariants ∧ P.src.IsAdmissible C (C ∪ inside C) ∧
        P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) :=
  ⟨(initialData hC).generatedPair, (initialData hC).generatedPair_combInvariants,
    (initialData hC).generatedPair_src_isAdmissible,
    (initialData hC).generatedPair_tgt_isAdmissible⟩

end Schoenflies
