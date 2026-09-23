/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.RefinementStars
public import LeanPool.Schoenflies.Inversion

/-!
# The limit homeomorphism of the interiors

The blueprint opens this section with a sentence that is an instruction to the formalizer: "We
now forget how the decompositions were constructed and use only their nesting, matching, and
shrinking properties." This module takes it literally. `LimitTower` is a structure recording
exactly those properties — a sequence of matched cell structures with two realizations each, a
`Realization.Refines` instance between consecutive stages on each side sharing one parent map,
nested skeleton homeomorphisms, and the two shrinking hypotheses of `prop:shrinking-stars` — and
everything from the definition of `F` to `prop:interior-homeomorphism` is proved against it.
Nothing below mentions a mesh, a grid, or a constructor. The still-open construction has to
produce one `LimitTower`; none of the analysis waits for it.

## What is *not* a field

Three things the task list expected to appear as hypotheses turned out to be derivable and are
therefore proved here rather than assumed.

* **`lem:outer-incidence`.** `docs/ROADMAP.md` records it as done in `CombinatorialInvariance.lean`
  under `outerEdge_face_corresponds`; that is a different statement (assertion (vi) of
  `lem:cellulation-invariants`, transported). The real `lem:outer-incidence` — `closure σ` meets
  `C` iff some outer cell is a subcell of `σ` iff `closure σ'` meets `S` — is proved below as
  `Realization.IsCellDecomposition.closure_cell_meets_outer_iff` and, for stars,
  `LimitTower.star_meets_bdry_iff`. The one geometric input it needs is
  `Realization.outerSet_eq_iUnion_cell`: the realized outer cycle is exactly the union of the
  open cells of the outer cells, which is a consequence of the two `Realization` clauses
  `cell_vertex` and `cell_edge` and holds for any subcomplex.
* **Assertion (vii) of `lem:cellulation-invariants`** (every 2-cell boundary a Jordan curve with
  the open cell its bounded region). The limit argument was expected to need it, through
  assertion (viii). It does not: the only use is "a 2-cell is not a proper subcell of a 2-cell",
  and that is `CombInvariants.face_maximal`, which is already an inductive invariant on `main`.
  There is therefore no field for (vii) and no dependency on it.
* **`prop:target-skeleton-dense`.** The blueprint's surjectivity proof goes through the density
  of the target skeleton and a compactness argument in `C ∪ D`. That is not needed: the sets
  `⋂ₙ St_{Γₙ}(car_{Γ'ₙ}(y))` — the *source* stars of the *target* carriers of `y` — are a nested
  sequence of nonempty compacts, and any point of their intersection is already a preimage of
  `y`. `prop:target-skeleton-dense` is proved anyway, because the boundary-continuity module
  cites it, but it is not on the critical path to `prop:F-surjective`.

## The two shrinking hypotheses are not symmetric

`prop:shrinking-stars` gives *pointwise* convergence of the source star diameters and *uniform*
convergence of the target ones. The asymmetry is real and is used: `F` is defined, and continuous,
on the whole closed domain (only the uniform bound enters), whereas injectivity and the continuity
of the inverse hold on the open region (they need the pointwise bound at a point of `D`).

One hypothesis that the blueprint does not state is carried throughout: the closed domains are
bounded. It is not optional — `Metric.diam` is `0` on an unbounded set, so without it the star
diameter bounds are false rather than weak — and it is trivially true for a closed Jordan domain.

## Blueprint

All of the following live in `Schoenflies.CellStructure`.

* `LimitTower` — the abstraction of the head of the section: "we now forget how the
  decompositions were constructed and use only their nesting, matching, and shrinking
  properties".
* The definition of `F` (tex "The limit homeomorphism of the interiors") —
  `LimitTower.F`, with `LimitTower.iInter_tgtStar_eq` its characterisation
  (`lem:nested-compact` applied to the nested stars `LimitTower.tgtStar`),
  `LimitTower.F_mem_tgtStar` and `LimitTower.eq_F_of_mem_iInter`.
* `lem:outer-incidence` — `Realization.IsCellDecomposition.closure_cell_meets_outer_iff` and
  `Realization.IsCellDecomposition.star_meets_outer_iff`, with the matched form the limit
  argument cites, `LimitTower.star_meets_bdry_iff`. Their geometric input is
  `Realization.outerSet_eq_iUnion_cell`.
* `prop:skeleton-agreement` — `LimitTower.F_eq_skelHomeo`.
* `prop:F-continuous` — `LimitTower.continuousOn_F`, on the *closed* domain.
* `prop:image-interior` — `LimitTower.F_mem_region'`.
* `prop:F-injective` — `LimitTower.injOn_F`.
* `prop:target-skeleton-dense` — `LimitTower.exists_mem_tgt_skeletonSet`.
* `prop:F-surjective` — `LimitTower.exists_mem_region_F_eq`, through `LimitTower.preStar` and
  `LimitTower.F_eq_of_mem_iInter_preStar`.
* `lem:exact-cell-correspondence` — `LimitTower.image_cell`, with the corollary the inverse
  argument actually uses, `LimitTower.tgt_carrier_F`.
* `prop:inverse-continuous` — `LimitTower.continuousOn_inv`, on the explicit inverse
  `LimitTower.inv`.
* `prop:interior-homeomorphism` — `LimitTower.isHomeoOn_F` and, with the skeleton clause,
  `LimitTower.interior_homeomorphism`; in the `Schoenflies.IsHomeoOn` shape that `Endgame.lean`
  and the boundary-continuity module consume.
* `lem:cell-neighborhood` is used, not restated: it is
  `Realization.IsCellDecomposition.sub_carrier_of_mem_cellNbhd` in `RefinementStars.lean`, and
  the cross-realization form the limit map needs is
  `LimitTower.tgtStar_subset_of_mem_cellNbhd`.
-/

@[expose] public section

open Set Metric Bornology Filter
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-! ### The realized skeleton and outer cycle, cell by cell

`Realization.skeletonSet` and `Realization.outerSet` are defined as point sets of drawn graphs.
The limit argument needs them as unions of *open cells*, because that is the form in which they
interact with `IsCellDecomposition`: "the carrier of any point of `C` is an outer cell" is the
first sentence of the blueprint's proof of `lem:outer-incidence`, and it is exactly this
rewriting. -/

/-- Every outer cell is a cell. -/
theorem outerCells_subset_cells : S.outerCells ⊆ S.cells := by
  rintro κ (hv | he)
  · exact S.mem_cells_of_mem_vertexSet (S.outerGraph_le.vertexSet_mono hv)
  · exact S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono he)

/-- A cell that is neither a 0-cell nor a 1-cell of the skeleton is a 2-cell — the three
collections exhaust `cells`. -/
theorem mem_faces_of_notMem_skel {σ : γ} (hσ : σ ∈ S.cells) (h : σ ∉ V(S.skel) ∪ E(S.skel)) :
    σ ∈ S.faces := by
  rcases hσ with hσ | hσ
  · exact absurd hσ h
  · exact hσ

/-- A proper subcell of a 2-cell is a 0- or 1-cell: nothing but the 2-cell itself is a 2-cell
below it. -/
theorem mem_skel_of_sub_face (hS : S.CombInvariants) {σ F : γ}
    (hσ : σ ∈ S.cells) (hsub : S.sub σ F) (hne : σ ≠ F) : σ ∈ V(S.skel) ∪ E(S.skel) := by
  rcases hσ with hσ | hσ
  · exact hσ
  · exact absurd (hS.face_maximal hσ hsub).symm hne

/-- A 2-cell is never an outer cell: outer cells are 0- and 1-cells of the skeleton. -/
theorem notMem_outerCells_of_mem_faces {F : γ} (hF : F ∈ S.faces) : F ∉ S.outerCells := by
  rintro (hv | he)
  · exact S.faces_ne_vertexSet hF (S.outerGraph_le.vertexSet_mono hv) rfl
  · exact S.faces_ne_edgeSet hF (S.outerGraph_le.edgeSet_mono he) rfl

/-- A **nonboundary edge** — assertion (iii) of `lem:cellulation-invariants` produces one on every
2-cell boundary — is not an outer cell. -/
theorem notMem_outerCells_of_nonboundary_edge {f : γ} (hf : f ∈ E(S.skel))
    (h : f ∉ E(S.outerGraph)) : f ∉ S.outerCells := by
  rintro (hv | he)
  · exact S.vertexSet_ne_edgeSet (S.outerGraph_le.vertexSet_mono hv) hf rfl
  · exact h he

namespace Realization

variable (R : S.Realization)

/-- The realized point set of a subcomplex of the skeleton is the union of the open cells of its
0- and 1-cells. A drawn edge is its open cell together with the two 0-cells at its ends, and
those ends belong to the subcomplex whenever the edge does. -/
theorem pointSet_map_eq_iUnion_cell {H : Graph γ γ} (hH : H ≤ S.skel) :
    Graph.pointSet (H.map R.pos) R.drawing = ⋃ κ ∈ V(H) ∪ E(H), R.cell κ := by
  refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun κ hκ => ?_)
  · rcases hz with hz | hz
    · -- a drawn 0-cell
      rw [Graph.vertexSet_map] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      exact Set.mem_biUnion (Or.inl hv)
        (by rw [R.cell_vertex (hH.vertexSet_mono hv)]; rfl)
    · -- a point of a drawn 1-cell: either interior to it, or one of its two ends
      rw [Graph.edgeSet_map] at hz
      obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
      obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      by_cases hend : z ∈ ({R.pos a, R.pos b} : Set Plane)
      · rcases hend with rfl | rfl
        · exact Set.mem_biUnion (Or.inl hl.left_mem)
            (by rw [R.cell_vertex (hH.vertexSet_mono hl.left_mem)]; rfl)
        · exact Set.mem_biUnion (Or.inl hl.right_mem)
            (by rw [R.cell_vertex (hH.vertexSet_mono hl.right_mem)]; rfl)
      · exact Set.mem_biUnion (Or.inr he) (by rw [R.cell_edge (hl.mono hH)]; exact ⟨hze, hend⟩)
  · rcases hκ with hv | he
    · rw [R.cell_vertex (hH.vertexSet_mono hv)]
      exact Set.singleton_subset_iff.2 (Graph.vertexSet_subset_pointSet
        (by rw [Graph.vertexSet_map]; exact ⟨κ, hv, rfl⟩))
    · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      rw [R.cell_edge (hl.mono hH)]
      exact Set.Subset.trans Set.sdiff_subset
        (Graph.edgeArc_subset_pointSet (by rw [Graph.edgeSet_map]; exact he))

/-- **The realized 1-skeleton is the union of the open 0- and 1-cells.** -/
theorem skeletonSet_eq_iUnion_cell :
    R.skeletonSet = ⋃ κ ∈ V(S.skel) ∪ E(S.skel), R.cell κ :=
  R.pointSet_map_eq_iUnion_cell le_rfl

/-- **The realized outer cycle is the union of the open outer cells.** This is the sentence "`C`
is exactly the union of the outer vertices and the open outer edges" at the head of the
blueprint's proof of `lem:outer-incidence`. -/
theorem outerSet_eq_iUnion_cell : R.outerSet = ⋃ κ ∈ S.outerCells, R.cell κ :=
  R.pointSet_map_eq_iUnion_cell S.outerGraph_le

variable {R}

theorem cell_subset_outerSet {κ : γ} (hκ : κ ∈ S.outerCells) : R.cell κ ⊆ R.outerSet := by
  rw [R.outerSet_eq_iUnion_cell]; exact Set.subset_biUnion_of_mem hκ

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ : γ} {x : Plane}

/-- Off the outer cycle, the open cell of a cell that is not an outer cell. Open cells are
disjoint and the outer cycle is the union of the outer ones, so a cell's open part misses the
outer cycle exactly when the cell is not outer. -/
theorem cell_disjoint_outerSet (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells)
    (hout : σ ∉ S.outerCells) : Disjoint (R.cell σ) R.outerSet := by
  rw [R.outerSet_eq_iUnion_cell, Set.disjoint_iUnion₂_right]
  intro κ hκ
  exact h.disjoint hσ (outerCells_subset_cells hκ) (fun hcon => hout (hcon ▸ hκ))

/-- An open cell is disjoint from the union of the open cells of any collection of cells not
containing it. This is how `IsCellDecomposition` sees the realized skeleton and the realized
outer cycle, once those have been rewritten as unions of open cells. -/
theorem cell_disjoint_biUnion (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) {K : Set γ}
    (hK : K ⊆ S.cells) (hnot : σ ∉ K) : Disjoint (R.cell σ) (⋃ κ ∈ K, R.cell κ) := by
  rw [Set.disjoint_iUnion₂_right]
  exact fun κ hκ => h.disjoint hσ (hK hκ) fun hcon => hnot (hcon ▸ hκ)

/-- **An open 2-cell never meets the realized skeleton.** -/
theorem cell_disjoint_skeletonSet (h : R.IsCellDecomposition D) {F : γ} (hF : F ∈ S.faces) :
    Disjoint (R.cell F) R.skeletonSet := by
  rw [R.skeletonSet_eq_iUnion_cell]
  refine h.cell_disjoint_biUnion (S.mem_cells_of_mem_faces hF) (fun κ hκ => ?_) ?_
  · rcases hκ with hv | he
    exacts [S.mem_cells_of_mem_vertexSet hv, S.mem_cells_of_mem_edgeSet he]
  · rintro (hv | he)
    exacts [S.faces_ne_vertexSet hF hv rfl, S.faces_ne_edgeSet hF he rfl]

/-- The realized skeleton lies in the closed domain. -/
theorem skeletonSet_subset_domain (h : R.IsCellDecomposition D) : R.skeletonSet ⊆ D := by
  rw [R.skeletonSet_eq_iUnion_cell]
  refine Set.iUnion₂_subset fun κ hκ => h.cell_subset_domain ?_
  rcases hκ with hv | he
  exacts [S.mem_cells_of_mem_vertexSet hv, S.mem_cells_of_mem_edgeSet he]

/-- **The closed star of a 2-cell is its own closed cell.** By `lem:star-face-mesh` a closed star
is the union of the closed 2-cells above the cell, and `CombInvariants.face_maximal` says the
only 2-cell above a 2-cell is itself. This is the step the blueprint attributes to assertion
(viii) of `lem:cellulation-invariants`, and it needs neither (vii) nor openness of the open
2-cell. -/
theorem star_face_eq_closure (h : R.IsCellDecomposition D) (hS : S.CombInvariants) {F : γ}
    (hF : F ∈ S.faces) : R.star F = closure (R.cell F) := by
  rw [h.star_eq_faces hS (S.mem_cells_of_mem_faces hF)]
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun T hT => ?_)
    (Set.subset_biUnion_of_mem (u := fun T => closure (R.cell T))
      (show F ∈ {T | T ∈ S.faces ∧ S.sub F T} from
        ⟨hF, h.sub_refl (S.mem_cells_of_mem_faces hF)⟩))
  exact (congrArg (fun c => closure (R.cell c)) (hS.face_maximal hF hT.2)).le

/-- The carrier of a point of the realized outer cycle is an outer cell. -/
theorem carrier_mem_outerCells [Nonempty γ] (h : R.IsCellDecomposition D)
    (hx : x ∈ R.outerSet) : R.carrier x ∈ S.outerCells := by
  rw [R.outerSet_eq_iUnion_cell] at hx
  obtain ⟨κ, hκ, hxκ⟩ := Set.mem_iUnion₂.1 hx
  rwa [h.carrier_eq (outerCells_subset_cells hκ) hxκ]

/-- **`lem:outer-incidence`**, the closed-cell form: a closed cell meets the realized outer cycle
exactly when some outer cell is one of its subcells. The middle condition is a statement of the
abstract structure alone, which is what makes the equivalence transfer between the two
realizations with nothing to transport. -/
theorem closure_cell_meets_outer_iff (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    (closure (R.cell τ) ∩ R.outerSet).Nonempty ↔ ∃ κ ∈ S.outerCells, S.sub κ τ := by
  constructor
  · rintro ⟨p, hpτ, hpout⟩
    rw [R.outerSet_eq_iUnion_cell] at hpout
    obtain ⟨κ, hκ, hpκ⟩ := Set.mem_iUnion₂.1 hpout
    exact ⟨κ, hκ, h.sub_of_mem (outerCells_subset_cells hκ) hτ hpκ hpτ⟩
  · rintro ⟨κ, hκ, hsub⟩
    obtain ⟨z, hz⟩ := h.nonempty (outerCells_subset_cells hκ)
    exact ⟨z, h.subset_closure (outerCells_subset_cells hκ) hτ hsub hz, cell_subset_outerSet hκ hz⟩

/-- **`lem:outer-incidence`**, the star form: a closed star meets the realized outer cycle
exactly when some supercell of the cell has an outer subcell. -/
theorem star_meets_outer_iff (h : R.IsCellDecomposition D)
    (hS : S.CombInvariants) (σ : γ) :
    (R.star σ ∩ R.outerSet).Nonempty ↔ ∃ τ, S.sub σ τ ∧ ∃ κ ∈ S.outerCells, S.sub κ τ := by
  constructor
  · rintro ⟨p, hpstar, hpout⟩
    obtain ⟨τ, hτ, hpτ⟩ := mem_star_iff.1 hpstar
    exact ⟨τ, hτ, (h.closure_cell_meets_outer_iff (hS.sub_mem_right hτ)).1 ⟨p, hpτ, hpout⟩⟩
  · rintro ⟨τ, hτ, hex⟩
    obtain ⟨p, hpτ, hpout⟩ := (h.closure_cell_meets_outer_iff (hS.sub_mem_right hτ)).2 hex
    exact ⟨p, closure_cell_subset_star hτ hpτ, hpout⟩

end IsCellDecomposition

end Realization

/-! ### The tower of matched cellulations

Every field below is an obligation on whoever eventually constructs the sequence of
decompositions, and there is nothing here that the limit argument does not use. -/

/-- **The nesting, matching and shrinking properties of a sequence of matched cellulations**, and
nothing else. The blueprint's "we now forget how the decompositions were constructed" is this
structure.

`str n` is the stage-`n` abstract matched cell structure; `src n` and `tgt n` are its two
realizations, in the closed Jordan domain `dom` and in the closed square `dom'`; `skelHomeo n` is
the stage-`n` skeleton homeomorphism `g_n`. Consecutive stages are related by a pair of
`Realization.Refines` instances **sharing one parent map** `par n` — that sharing is
`lem:refinement-compatibility`(c), "corresponding cells have corresponding parents", under the
representation of `CombinatorialInvariance.lean`, where cells are abstract names.

The shrinking clauses are `prop:shrinking-stars`, and they are deliberately asymmetric, exactly
as the blueprint states them: the *target* star diameters are bounded uniformly by a null
sequence `eps`, while the *source* star diameters are only assumed to tend to zero pointwise, and
only at points of the open region. -/
structure LimitTower (γ : Type*) [Nonempty γ] where
  /-- The stage-`n` abstract matched cell structure. -/
  str : ℕ → CellStructure γ
  /-- The source realization, in the closed Jordan domain. -/
  src : ∀ n, (str n).Realization
  /-- The target realization, in the closed square. -/
  tgt : ∀ n, (str n).Realization
  /-- The stage-`n` skeleton homeomorphism `g_n`. -/
  skelHomeo : ∀ n, SkeletonHomeo (src n) (tgt n)
  /-- The composite parent map from stage `n + 1` to stage `n`, shared by the two sides. -/
  par : ℕ → γ → γ
  /-- The closed source domain `C ∪ D`. -/
  dom : Set Plane
  /-- The source outer curve `C`. -/
  bdry : Set Plane
  /-- The closed target domain `Q`. -/
  dom' : Set Plane
  /-- The target outer curve `S`. -/
  bdry' : Set Plane
  /-- The uniform target mesh: `2 ε_n` of the blueprint. -/
  eps : ℕ → ℝ
  /-- **Assertions (i) and (ii)** on the source side. -/
  srcDecomp : ∀ n, (src n).IsCellDecomposition dom
  /-- **Assertions (i) and (ii)** on the target side. -/
  tgtDecomp : ∀ n, (tgt n).IsCellDecomposition dom'
  /-- **Assertions (iii), (v), (vi)** and the rest of the combinatorial invariants. -/
  comb : ∀ n, (str n).CombInvariants
  /-- Consecutive source stages refine, along `par n`. -/
  srcRefines : ∀ n, (src (n + 1)).Refines (src n) (par n)
  /-- Consecutive target stages refine, along the *same* `par n`. -/
  tgtRefines : ∀ n, (tgt (n + 1)).Refines (tgt n) (par n)
  /-- The realized source outer cycle is `C`, at every stage. -/
  srcOuterSet : ∀ n, (src n).outerSet = bdry
  /-- The realized target outer cycle is `S`, at every stage. -/
  tgtOuterSet : ∀ n, (tgt n).outerSet = bdry'
  /-- `C ∪ D` is closed. -/
  isClosed_dom : IsClosed dom
  /-- `Q` is closed. -/
  isClosed_dom' : IsClosed dom'
  /-- `C ∪ D` is bounded. Not in the blueprint, and not optional: `Metric.diam` is `0` on an
  unbounded set. -/
  isBounded_dom : IsBounded dom
  /-- `Q` is bounded, for the same reason. -/
  isBounded_dom' : IsBounded dom'
  /-- `D = Int(C)` is open. -/
  isOpen_int : IsOpen (dom \ bdry)
  /-- `Q°` is open. -/
  isOpen_int' : IsOpen (dom' \ bdry')
  /-- The realized source skeletons grow. -/
  skeletonSet_mono : ∀ n, (src n).skeletonSet ⊆ (src (n + 1)).skeletonSet
  /-- **The skeleton maps are nested**: "an edge subdivision leaves the skeleton map unchanged as
  a point map, and a 2-cell split extends it by the chosen homeomorphism on the new ear". -/
  skelHomeo_succ : ∀ n,
    Set.EqOn (skelHomeo (n + 1)).toFun (skelHomeo n).toFun (src n).skeletonSet
  /-- **`prop:shrinking-stars`, the uniform half**: every stage-`n` target star has diameter at
  most `eps n`. -/
  diam_tgtStar_le : ∀ n, ∀ ⦃σ⦄, σ ∈ (str n).cells → diam ((tgt n).star σ) ≤ eps n
  /-- …and `eps` is a null sequence. -/
  tendsto_eps : Tendsto eps atTop (nhds 0)
  /-- **`prop:shrinking-stars`, the pointwise half**: at every point of the open region the
  source star diameters tend to zero. -/
  tendsto_diam_srcStar : ∀ ⦃x⦄, x ∈ dom \ bdry →
    Tendsto (fun n => diam ((src n).star ((src n).carrier x))) atTop (nhds 0)

namespace LimitTower

variable [Nonempty γ] (L : LimitTower γ) {x y z : Plane} {m n : ℕ} {σ : γ}

/-- The open source region `D = Int(C)`. -/
def region : Set Plane := L.dom \ L.bdry

/-- The open target region `Q°`. -/
def region' : Set Plane := L.dom' \ L.bdry'

/-- `St_{Γ'_n}(σ'_n(x))`, written `T_n(x)` in the blueprint: the closed target star of the cell
corresponding to the source carrier of `x`. -/
def tgtStar (n : ℕ) (x : Plane) : Set Plane := (L.tgt n).star ((L.src n).carrier x)

/-- `St_{Γ_n}(x)`, the closed source star of the source carrier of `x`. -/
def srcStar (n : ℕ) (x : Plane) : Set Plane := (L.src n).star ((L.src n).carrier x)

variable {L}

theorem mem_region_iff : x ∈ L.region ↔ x ∈ L.dom ∧ x ∉ L.bdry := Iff.rfl

theorem mem_region'_iff : x ∈ L.region' ↔ x ∈ L.dom' ∧ x ∉ L.bdry' := Iff.rfl

theorem region_subset_dom : L.region ⊆ L.dom := Set.sdiff_subset

theorem region'_subset_dom' : L.region' ⊆ L.dom' := Set.sdiff_subset

theorem isOpen_region (L : LimitTower γ) : IsOpen L.region := L.isOpen_int

theorem isOpen_region' (L : LimitTower γ) : IsOpen L.region' := L.isOpen_int'

theorem tgtStar_eq (n : ℕ) (x : Plane) :
    L.tgtStar n x = (L.tgt n).star ((L.src n).carrier x) := rfl

theorem srcStar_eq (n : ℕ) (x : Plane) :
    L.srcStar n x = (L.src n).star ((L.src n).carrier x) := rfl

/-- A null real sequence is eventually below any positive bound. Used with `eps` and with the
pointwise source-star diameters. -/
theorem exists_lt_of_tendsto_zero {f : ℕ → ℝ} (h : Tendsto f atTop (nhds 0)) {r : ℝ}
    (hr : 0 < r) : ∃ n, f n < r :=
  (h.eventually (Iio_mem_nhds hr)).exists

/-! #### Stars of the tower -/

theorem srcStar_subset_dom (n : ℕ) (σ : γ) : (L.src n).star σ ⊆ L.dom :=
  ((L.srcDecomp n).star_subset_closure_domain (L.comb n)).trans L.isClosed_dom.closure_subset

theorem tgtStar_subset_dom' (n : ℕ) (σ : γ) : (L.tgt n).star σ ⊆ L.dom' :=
  ((L.tgtDecomp n).star_subset_closure_domain (L.comb n)).trans L.isClosed_dom'.closure_subset

theorem isBounded_tgt_star (n : ℕ) (σ : γ) : IsBounded ((L.tgt n).star σ) :=
  (L.tgtDecomp n).isBounded_star (L.comb n) L.isBounded_dom'

theorem isBounded_src_star (n : ℕ) (σ : γ) : IsBounded ((L.src n).star σ) :=
  (L.srcDecomp n).isBounded_star (L.comb n) L.isBounded_dom

theorem isBounded_srcStar (n : ℕ) (x : Plane) : IsBounded (L.srcStar n x) :=
  isBounded_src_star n _

theorem isBounded_tgtStar (n : ℕ) (x : Plane) : IsBounded (L.tgtStar n x) :=
  isBounded_tgt_star n _

theorem mem_srcStar_self (hx : x ∈ L.dom) (n : ℕ) : x ∈ L.srcStar n x :=
  (L.srcDecomp n).mem_star_carrier hx

theorem tendsto_diam_srcStar_point (hx : x ∈ L.region) :
    Tendsto (fun n => diam (L.srcStar n x)) atTop (nhds 0) :=
  L.tendsto_diam_srcStar hx

/-- **`lem:refinement-compatibility`(b)** at a point: `T_{n+1}(x) ⊆ T_n(x)`. -/
theorem tgtStar_succ_subset (hx : x ∈ L.dom) (n : ℕ) : L.tgtStar (n + 1) x ⊆ L.tgtStar n x :=
  (L.srcRefines n).target_star_subset (L.tgtRefines n) (L.comb (n + 1)) (L.srcDecomp n)
    (L.srcDecomp (n + 1)) hx

theorem tgtStar_antitone (hx : x ∈ L.dom) : Antitone (fun n => L.tgtStar n x) :=
  antitone_nat_of_succ_le (L.tgtStar_succ_subset hx)

theorem tgtStar_nonempty (hx : x ∈ L.dom) (n : ℕ) : (L.tgtStar n x).Nonempty :=
  (L.tgtDecomp n).star_nonempty ((L.srcDecomp n).mem_cells_carrier hx)

theorem isCompact_tgtStar (n : ℕ) (x : Plane) : IsCompact (L.tgtStar n x) :=
  (L.tgtDecomp n).isCompact_star (L.comb n) L.isBounded_dom'

theorem diam_tgtStar (hx : x ∈ L.dom) (n : ℕ) : diam (L.tgtStar n x) ≤ L.eps n :=
  L.diam_tgtStar_le n ((L.srcDecomp n).mem_cells_carrier hx)

theorem tendsto_diam_tgtStar (hx : x ∈ L.dom) :
    Tendsto (fun n => diam (L.tgtStar n x)) atTop (nhds 0) :=
  squeeze_zero (fun _ => diam_nonneg) (L.diam_tgtStar hx) L.tendsto_eps

/-! #### The limit map -/

theorem exists_eq_singleton_iInter_tgtStar (hx : x ∈ L.dom) :
    ∃ p, ⋂ n, L.tgtStar n x = {p} :=
  Plane.eq_singleton_iInter_of_diam_tendsto_zero (L.tgtStar_nonempty hx)
    (fun n => L.isCompact_tgtStar n x) (L.tgtStar_antitone hx) (L.tendsto_diam_tgtStar hx)

open scoped Classical in
/-- **The limit map `F`**: the unique point of `⋂ₙ T_n(x)`. Junk off the closed domain; every
lemma about it carries `x ∈ L.dom`. -/
noncomputable def F (L : LimitTower γ) (x : Plane) : Plane :=
  if h : ∃ p, ⋂ n, L.tgtStar n x = {p} then h.choose else 0

/-- **The characterising property of `F`.** -/
theorem iInter_tgtStar_eq (hx : x ∈ L.dom) : ⋂ n, L.tgtStar n x = {L.F x} := by
  rw [F, dite_eq_left (L.exists_eq_singleton_iInter_tgtStar hx)]
  exact (L.exists_eq_singleton_iInter_tgtStar hx).choose_spec

theorem F_mem_iInter (hx : x ∈ L.dom) : L.F x ∈ ⋂ n, L.tgtStar n x := by
  rw [L.iInter_tgtStar_eq hx]
  exact rfl

theorem F_mem_tgtStar (hx : x ∈ L.dom) (n : ℕ) : L.F x ∈ L.tgtStar n x :=
  Set.mem_iInter.1 (L.F_mem_iInter hx) n

/-- Uniqueness: anything in every `T_n(x)` is `F x`. -/
theorem eq_F_of_mem_iInter (hx : x ∈ L.dom) (hz : ∀ n, z ∈ L.tgtStar n x) : z = L.F x := by
  have : z ∈ ⋂ n, L.tgtStar n x := Set.mem_iInter.2 hz
  rwa [L.iInter_tgtStar_eq hx, Set.mem_singleton_iff] at this

theorem F_mem_dom' (hx : x ∈ L.dom) : L.F x ∈ L.dom' :=
  tgtStar_subset_dom' 0 _ (L.F_mem_tgtStar hx 0)

/-- `F x` is within `eps n` of anything in the stage-`n` target star of `x`. -/
theorem dist_F_le_of_mem_tgtStar (hx : x ∈ L.dom) (hz : z ∈ L.tgtStar n x) :
    dist (L.F x) z ≤ L.eps n :=
  le_trans (dist_le_diam_of_mem (isBounded_tgt_star n _) (L.F_mem_tgtStar hx n) hz)
    (L.diam_tgtStar hx n)

/-! #### Agreement with the finite skeleton maps

The skeleton maps are nested, so `g_n = g_N` on `G_N` for every `n ≥ N`; at each such stage the
skeleton map carries the carrier of `x` onto the corresponding target cell, which sits inside
`T_n(x)`. The intersection of the `T_n(x)` is the single point `F x`. -/

theorem skeletonSet_mono_le (hmn : m ≤ n) : (L.src m).skeletonSet ⊆ (L.src n).skeletonSet := by
  induction n, hmn using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact ih.trans (L.skeletonSet_mono n)

/-- **The skeleton maps are nested**: `g_n = g_m` on `G_m` whenever `m ≤ n`. -/
theorem skelHomeo_eqOn (hmn : m ≤ n) :
    Set.EqOn (L.skelHomeo n).toFun (L.skelHomeo m).toFun (L.src m).skeletonSet := by
  induction n, hmn using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ n hmn ih =>
    intro w hw
    rw [L.skelHomeo_succ n (skeletonSet_mono_le hmn hw), ih hw]

/-- At a stage-`n` skeleton point the skeleton map lands in the stage-`n` target star: the
carrier of `x` is a 0- or 1-cell, and `g_n` carries its open cell onto the target open cell of
the same abstract name. -/
theorem skelHomeo_mem_tgtStar (hx : x ∈ (L.src n).skeletonSet) :
    (L.skelHomeo n).toFun x ∈ L.tgtStar n x := by
  rw [(L.src n).skeletonSet_eq_iUnion_cell] at hx
  obtain ⟨κ, hκ, hxκ⟩ := Set.mem_iUnion₂.1 hx
  have hcells : κ ∈ (L.str n).cells := by
    rcases hκ with hv | he
    exacts [(L.str n).mem_cells_of_mem_vertexSet hv, (L.str n).mem_cells_of_mem_edgeSet he]
  have hgx : (L.skelHomeo n).toFun x ∈ (L.tgt n).cell κ := by
    rw [← (L.skelHomeo n).image_cell hκ]
    exact Set.mem_image_of_mem _ hxκ
  rw [tgtStar_eq, (L.srcDecomp n).carrier_eq hcells hxκ]
  exact Realization.closure_cell_subset_star ((L.tgtDecomp n).sub_refl hcells)
    (_root_.subset_closure hgx)

/-- **`prop:skeleton-agreement`**: `F` agrees with the stage-`N` skeleton map on `G_N ∩ (C ∪ D)`.
Since the skeleton maps are nested, this is the blueprint's `F = g_∞` on `⋃ₙ Gₙ ∩ D` as well. -/
theorem F_eq_skelHomeo (hx : x ∈ (L.src n).skeletonSet) (hxD : x ∈ L.dom) :
    L.F x = (L.skelHomeo n).toFun x := by
  refine (eq_F_of_mem_iInter hxD fun m => ?_).symm
  rcases le_or_gt n m with hnm | hmn
  · rw [← skelHomeo_eqOn hnm hx]
    exact skelHomeo_mem_tgtStar (skeletonSet_mono_le hnm hx)
  · exact tgtStar_antitone hxD hmn.le (skelHomeo_mem_tgtStar hx)

/-! #### Continuity -/

/-- The cross-realization form of `lem:cell-neighborhood` the limit map needs: for `z` in the
stage-`n` source cell neighbourhood of `x`, `T_n(z) ⊆ T_n(x)`. The subcell relation is read in
the source realization and used in the target one; it is a relation of the common abstract
structure, so nothing is transported. -/
theorem tgtStar_subset_of_mem_cellNbhd (hx : x ∈ L.dom) (hzD : z ∈ L.dom)
    (hz : z ∈ (L.src n).cellNbhd x) : L.tgtStar n z ⊆ L.tgtStar n x :=
  (L.tgtDecomp n).star_anti_of_sub (L.comb n) ((L.srcDecomp n).mem_cells_carrier hx)
    ((L.srcDecomp n).mem_cells_carrier hzD)
    ((L.srcDecomp n).sub_carrier_of_mem_cellNbhd hx hz hzD)

/-- **`prop:F-continuous`**, on the whole *closed* domain. Only the uniform half of
`prop:shrinking-stars` enters, so nothing here restricts `x` to the open region. -/
theorem continuousOn_F (L : LimitTower γ) : ContinuousOn L.F L.dom := by
  rw [Metric.continuousOn_iff]
  intro x hx η hη
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero L.tendsto_eps hη
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.1 ((L.src n).isOpen_cellNbhd x) x ((L.src n).mem_cellNbhd_self x)
  refine ⟨δ, hδ, fun a ha hadist => ?_⟩
  rw [dist_comm]
  exact lt_of_le_of_lt (dist_F_le_of_mem_tgtStar hx
    (tgtStar_subset_of_mem_cellNbhd hx ha (hball (Metric.mem_ball.2 hadist))
      (L.F_mem_tgtStar ha n))) hn

/-! #### The image lies in the interior -/

/-- **`lem:outer-incidence`, matched form**: a stage-`n` source star meets `C` exactly when the
target star of the *same abstract cell* meets `S`. Both sides reduce to the middle condition of
the blueprint's statement, which mentions only the abstract structure and its outer cycle. -/
theorem star_meets_bdry_iff (L : LimitTower γ) (n : ℕ) (σ : γ) :
    ((L.src n).star σ ∩ L.bdry).Nonempty ↔ ((L.tgt n).star σ ∩ L.bdry').Nonempty := by
  rw [← L.srcOuterSet n, ← L.tgtOuterSet n, (L.srcDecomp n).star_meets_outer_iff (L.comb n) σ,
    (L.tgtDecomp n).star_meets_outer_iff (L.comb n) σ]

/-- At a point of the open region the source star is eventually contained in the region: the
point lies in its own star, and the star diameters tend to zero. -/
theorem exists_srcStar_subset_region (hx : x ∈ L.region) : ∃ n, L.srcStar n x ⊆ L.region := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 L.isOpen_region x hx
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero (L.tendsto_diam_srcStar hx) hr
  refine ⟨n, fun w hw => hball (Metric.mem_ball.2 (lt_of_le_of_lt ?_ hn))⟩
  exact dist_le_diam_of_mem (isBounded_srcStar n x) hw
    (mem_srcStar_self (region_subset_dom hx) n)

/-- **`prop:image-interior`**: `F(D) ⊆ Q°`. -/
theorem F_mem_region' (hx : x ∈ L.region) : L.F x ∈ L.region' := by
  obtain ⟨n, hn⟩ := exists_srcStar_subset_region hx
  refine ⟨F_mem_dom' (region_subset_dom hx), fun hcon => ?_⟩
  obtain ⟨w, hw, hwb⟩ := (L.star_meets_bdry_iff n ((L.src n).carrier x)).2
    ⟨L.F x, L.F_mem_tgtStar (region_subset_dom hx) n, hcon⟩
  exact (hn hw).2 hwb

/-! #### Injectivity -/

/-- **`prop:F-injective`**. This is where the pointwise half of `prop:shrinking-stars` is needed,
and it is why injectivity is asserted on the open region rather than on the closed domain. -/
theorem injOn_F (L : LimitTower γ) : Set.InjOn L.F L.region := by
  intro x hx y hy hxy
  -- the target stars meet at every stage, so `lem:star-intersection` makes the source stars meet
  have hmeet : ∀ n, (L.srcStar n x ∩ L.srcStar n y).Nonempty := fun n =>
    (Realization.star_inter_nonempty_congr (L.tgtDecomp n) (L.srcDecomp n) (L.comb n)).1
      ⟨L.F x, L.F_mem_tgtStar (region_subset_dom hx) n,
        hxy ▸ L.F_mem_tgtStar (region_subset_dom hy) n⟩
  have hbound : ∀ n, dist x y ≤ diam (L.srcStar n x) + diam (L.srcStar n y) := by
    intro n
    obtain ⟨w, hwx, hwy⟩ := hmeet n
    refine le_trans (dist_triangle x w y) (add_le_add ?_ ?_)
    · exact dist_le_diam_of_mem (isBounded_srcStar n x)
        (mem_srcStar_self (region_subset_dom hx) n) hwx
    · exact dist_le_diam_of_mem (isBounded_srcStar n y) hwy
        (mem_srcStar_self (region_subset_dom hy) n)
  have hzero : dist x y ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds
      (by simpa using (tendsto_diam_srcStar_point hx).add (tendsto_diam_srcStar_point hy)) hbound
  exact dist_le_zero.1 hzero

/-! #### Density of the target skeleton -/

/-- An open cell that is not an outer cell lies in the open region: open cells are disjoint and
`S` is the union of the open outer ones. -/
theorem tgt_cell_subset_region' (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).cells)
    (hout : σ ∉ (L.str n).outerCells) : (L.tgt n).cell σ ⊆ L.region' := by
  intro w hw
  refine ⟨(L.tgtDecomp n).cell_subset_domain hσ hw, fun hb => ?_⟩
  rw [← L.tgtOuterSet n] at hb
  exact Set.disjoint_left.1 ((L.tgtDecomp n).cell_disjoint_outerSet hσ hout) hw hb

/-- **`prop:target-skeleton-dense`**: every point of `Q°` is approximated by target skeleton
points of `Q°`. If `y` is not already on the stage-`n` skeleton its carrier is a 2-cell, and
assertion (iii) of `lem:cellulation-invariants` puts a nonboundary edge on its boundary; that
edge's open cell lies in the star of the carrier, of diameter at most `eps n`. -/
theorem exists_mem_tgt_skeletonSet (hy : y ∈ L.region') {δ : ℝ} (hδ : 0 < δ) :
    ∃ n w, w ∈ (L.tgt n).skeletonSet ∧ w ∈ L.region' ∧ dist y w < δ := by
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero L.tendsto_eps hδ
  by_cases hys : y ∈ (L.tgt n).skeletonSet
  · exact ⟨n, y, hys, hy, by simpa using hδ⟩
  have hyD : y ∈ L.dom' := region'_subset_dom' hy
  have hcar : (L.tgt n).carrier y ∈ (L.str n).cells := (L.tgtDecomp n).mem_cells_carrier hyD
  -- the carrier of `y` is a 2-cell: otherwise its open cell would sit on the skeleton
  have hface : (L.tgt n).carrier y ∈ (L.str n).faces := by
    refine mem_faces_of_notMem_skel hcar fun hmem => hys ?_
    exact Realization.cell_subset_skeletonSet hmem ((L.tgtDecomp n).mem_cell_carrier hyD)
  obtain ⟨f, hf, hfout, hfsub⟩ := (L.comb n).nonboundary_edge hface
  have hfc : f ∈ (L.str n).cells := (L.str n).mem_cells_of_mem_edgeSet hf
  obtain ⟨w, hw⟩ := (L.tgtDecomp n).nonempty hfc
  have hwstar : w ∈ (L.tgt n).star ((L.tgt n).carrier y) :=
    Realization.closure_cell_subset_star ((L.tgtDecomp n).sub_refl hcar)
      ((L.tgtDecomp n).subset_closure hfc hcar hfsub hw)
  refine ⟨n, w, Realization.cell_subset_skeletonSet (Or.inr hf) hw,
    tgt_cell_subset_region' n hfc (notMem_outerCells_of_nonboundary_edge hf hfout) hw,
    lt_of_le_of_lt (le_trans (dist_le_diam_of_mem (isBounded_tgt_star n _)
      ((L.tgtDecomp n).mem_star_carrier hyD) hwstar) (L.diam_tgtStar_le n hcar)) hn⟩

/-! #### Surjectivity

The blueprint reaches `y` through the density of the target skeleton and a compactness argument
in `C ∪ D`. The route taken here is shorter and needs neither: the *source* stars of the
*target* carriers of `y` are themselves a nested sequence of nonempty compacts, and every point
of their intersection is already a preimage of `y`. -/

/-- `St_{Γ_n}(car_{Γ'_n}(y))`: the source star of the target carrier of `y`. This is the set the
blueprint calls `K`, read at every stage instead of at one. -/
def preStar (L : LimitTower γ) (n : ℕ) (y : Plane) : Set Plane :=
  (L.src n).star ((L.tgt n).carrier y)

theorem preStar_succ_subset (hy : y ∈ L.dom') (n : ℕ) :
    L.preStar (n + 1) y ⊆ L.preStar n y :=
  (L.tgtRefines n).target_star_subset (L.srcRefines n) (L.comb (n + 1)) (L.tgtDecomp n)
    (L.tgtDecomp (n + 1)) hy

theorem preStar_nonempty (hy : y ∈ L.dom') (n : ℕ) : (L.preStar n y).Nonempty :=
  (L.srcDecomp n).star_nonempty ((L.tgtDecomp n).mem_cells_carrier hy)

theorem isCompact_preStar (n : ℕ) (y : Plane) : IsCompact (L.preStar n y) :=
  (L.srcDecomp n).isCompact_star (L.comb n) L.isBounded_dom

theorem nonempty_iInter_preStar (hy : y ∈ L.dom') : (⋂ n, L.preStar n y).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (fun n => preStar_succ_subset hy n) (preStar_nonempty hy) (isCompact_preStar 0 y)
    fun n => (isCompact_preStar n y).isClosed

/-- **The heart of surjectivity**: a point lying in every `preStar n y` is carried to `y`. At
each stage the source carrier of `x` and the target carrier of `y` share a supercell `τ`, so the
two target stars meet, and both have diameter at most `eps n`. -/
theorem F_eq_of_mem_iInter_preStar (hy : y ∈ L.dom') (hxD : x ∈ L.dom)
    (hx : ∀ n, x ∈ L.preStar n y) : L.F x = y := by
  have hbound : ∀ n, dist (L.F x) y ≤ 2 * L.eps n := by
    intro n
    obtain ⟨τ, hτ, hxτ⟩ := Realization.mem_star_iff.1 (hx n)
    have hτc : τ ∈ (L.str n).cells := (L.comb n).sub_mem_right hτ
    -- `τ` is a supercell of the source carrier of `x` as well
    have hsub : (L.str n).sub ((L.src n).carrier x) τ :=
      (L.srcDecomp n).sub_of_mem ((L.srcDecomp n).mem_cells_carrier hxD) hτc
        ((L.srcDecomp n).mem_cell_carrier hxD) hxτ
    obtain ⟨w, hw⟩ := (L.tgtDecomp n).nonempty hτc
    have hwx : w ∈ L.tgtStar n x :=
      Realization.closure_cell_subset_star hsub (_root_.subset_closure hw)
    have hwy : w ∈ (L.tgt n).star ((L.tgt n).carrier y) :=
      Realization.closure_cell_subset_star hτ (_root_.subset_closure hw)
    have h₁ : dist (L.F x) w ≤ L.eps n := dist_F_le_of_mem_tgtStar hxD hwx
    have h₂ : dist w y ≤ L.eps n :=
      le_trans (dist_le_diam_of_mem (isBounded_tgt_star n _) hwy
        ((L.tgtDecomp n).mem_star_carrier hy))
        (L.diam_tgtStar_le n ((L.tgtDecomp n).mem_cells_carrier hy))
    calc dist (L.F x) y ≤ dist (L.F x) w + dist w y := dist_triangle _ _ _
      _ ≤ 2 * L.eps n := by linarith
  have hzero : dist (L.F x) y ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds
      (by simpa using L.tendsto_eps.const_mul 2) hbound
  exact dist_le_zero.1 hzero

/-- At a point of `Q°` the target star is eventually inside `Q°`. Here the *uniform* half of
`prop:shrinking-stars` is what is available, and it suffices. -/
theorem exists_tgt_star_subset_region' (hy : y ∈ L.region') :
    ∃ n, (L.tgt n).star ((L.tgt n).carrier y) ⊆ L.region' := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 L.isOpen_region' y hy
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero L.tendsto_eps hr
  refine ⟨n, fun w hw => hball (Metric.mem_ball.2 ?_)⟩
  have h₁ : dist w y ≤ diam ((L.tgt n).star ((L.tgt n).carrier y)) :=
    dist_le_diam_of_mem (isBounded_tgt_star n _) hw
      ((L.tgtDecomp n).mem_star_carrier (region'_subset_dom' hy))
  have h₂ := L.diam_tgtStar_le n ((L.tgtDecomp n).mem_cells_carrier (region'_subset_dom' hy))
  linarith

/-- **`prop:F-surjective`**: every point of `Q°` is `F` of a point of `D`. -/
theorem exists_mem_region_F_eq (hy : y ∈ L.region') : ∃ x, x ∈ L.region ∧ L.F x = y := by
  obtain ⟨n, hn⟩ := exists_tgt_star_subset_region' hy
  obtain ⟨x, hx⟩ := nonempty_iInter_preStar (region'_subset_dom' hy)
  have hmem : ∀ m, x ∈ L.preStar m y := Set.mem_iInter.1 hx
  have hxD : x ∈ L.dom := srcStar_subset_dom 0 _ (hmem 0)
  refine ⟨x, ⟨hxD, fun hb => ?_⟩, F_eq_of_mem_iInter_preStar (region'_subset_dom' hy) hxD hmem⟩
  -- the stage-`n` source star of the target carrier of `y` misses `C`, by `lem:outer-incidence`
  obtain ⟨w, hw, hwb⟩ := (L.star_meets_bdry_iff n ((L.tgt n).carrier y)).1 ⟨x, hmem n, hb⟩
  exact (hn hw).2 hwb

/-! #### Exact cell correspondence -/

/-- The source counterpart of `tgt_cell_subset_region'`. -/
theorem src_cell_subset_region (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).cells)
    (hout : σ ∉ (L.str n).outerCells) : (L.src n).cell σ ⊆ L.region := by
  intro w hw
  refine ⟨(L.srcDecomp n).cell_subset_domain hσ hw, fun hb => ?_⟩
  rw [← L.srcOuterSet n] at hb
  exact Set.disjoint_left.1 ((L.srcDecomp n).cell_disjoint_outerSet hσ hout) hw hb

/-- A point of the open region has a nonboundary carrier: an outer cell's open cell lies on the
outer cycle. -/
theorem src_carrier_notMem_outerCells (hx : x ∈ L.region) (n : ℕ) :
    (L.src n).carrier x ∉ (L.str n).outerCells := fun hc =>
  hx.2 (by
    rw [← L.srcOuterSet n]
    exact Realization.cell_subset_outerSet hc ((L.srcDecomp n).mem_cell_carrier hx.1))

theorem tgt_carrier_notMem_outerCells (hy : y ∈ L.region') (n : ℕ) :
    (L.tgt n).carrier y ∉ (L.str n).outerCells := fun hc =>
  hy.2 (by
    rw [← L.tgtOuterSet n]
    exact Realization.cell_subset_outerSet hc ((L.tgtDecomp n).mem_cell_carrier hy.1))

/-- The half of `lem:exact-cell-correspondence` that carries the argument: an open source 2-cell
is mapped **into** the corresponding open target 2-cell.

The closed star of a 2-cell is its own closed cell, so `F x` lies in `closure σ'`; if it lay on
the frontier it would be a stage-`n` target skeleton point, and its skeleton preimage `w` would
be a second point of `D` with `F w = F x`, contradicting injectivity — while `x` itself, lying in
an open 2-cell, is not a skeleton point. -/
theorem F_mem_cell_of_mem_cell_face (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).faces)
    (hx : x ∈ (L.src n).cell σ) : L.F x ∈ (L.tgt n).cell σ := by
  have hσc : σ ∈ (L.str n).cells := (L.str n).mem_cells_of_mem_faces hσ
  have hxr : x ∈ L.region :=
    src_cell_subset_region n hσc (notMem_outerCells_of_mem_faces hσ) hx
  have hcar : (L.src n).carrier x = σ := (L.srcDecomp n).carrier_eq hσc hx
  -- `T_n(x)` is exactly the closed target 2-cell
  have hclos : L.F x ∈ closure ((L.tgt n).cell σ) := by
    have := L.F_mem_tgtStar hxr.1 n
    rwa [tgtStar_eq, hcar, (L.tgtDecomp n).star_face_eq_closure (L.comb n) hσ] at this
  rw [(L.tgtDecomp n).closure_eq hσc] at hclos
  obtain ⟨ρ, ⟨hρ, hρsub⟩, hFρ⟩ := Set.mem_iUnion₂.1 hclos
  by_cases hρσ : ρ = σ
  · exact hρσ ▸ hFρ
  -- otherwise `F x` is a stage-`n` target skeleton point; its preimage contradicts injectivity
  exfalso
  have hFskel : L.F x ∈ (L.tgt n).skeletonSet :=
    Realization.cell_subset_skeletonSet (mem_skel_of_sub_face (L.comb n) hρ hρsub hρσ) hFρ
  obtain ⟨w, hwskel, hwF⟩ : ∃ w ∈ (L.src n).skeletonSet, (L.skelHomeo n).toFun w = L.F x := by
    rw [← (L.skelHomeo n).image_skeletonSet] at hFskel
    exact hFskel
  have hFr : L.F x ∈ L.region' := F_mem_region' hxr
  have hwr : w ∈ L.region := by
    refine ⟨(L.srcDecomp n).skeletonSet_subset_domain hwskel, fun hb => hFr.2 ?_⟩
    rw [← L.tgtOuterSet n, ← hwF, ← (L.skelHomeo n).image_outerSet]
    exact Set.mem_image_of_mem _ (by rwa [L.srcOuterSet n])
  have hwx : w = x := L.injOn_F hwr hxr (by
    rw [F_eq_skelHomeo hwskel hwr.1, hwF])
  exact Set.disjoint_left.1 ((L.srcDecomp n).cell_disjoint_skeletonSet hσ) hx (hwx ▸ hwskel)

/-- **`lem:exact-cell-correspondence`**: `F` carries each nonboundary open cell of the stage-`n`
source decomposition **onto** the corresponding open cell of the target decomposition. For a 0- or
1-cell this is `prop:skeleton-agreement` together with the skeleton homeomorphism; for a 2-cell it
is the previous lemma plus surjectivity. -/
theorem image_cell (n : ℕ) {σ : γ} (hσ : σ ∈ (L.str n).cells)
    (hout : σ ∉ (L.str n).outerCells) : L.F '' ((L.src n).cell σ) = (L.tgt n).cell σ := by
  by_cases hskel : σ ∈ V((L.str n).skel) ∪ E((L.str n).skel)
  · -- on the skeleton `F` *is* `g_n`
    rw [Set.image_congr (fun w hw => F_eq_skelHomeo
      (Realization.cell_subset_skeletonSet hskel hw)
      ((L.srcDecomp n).cell_subset_domain hσ hw))]
    exact (L.skelHomeo n).image_cell hskel
  have hface : σ ∈ (L.str n).faces := mem_faces_of_notMem_skel hσ hskel
  refine Set.Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact F_mem_cell_of_mem_cell_face n hface hw
  -- surjectivity produces a preimage; its carrier is a 2-cell, and open 2-cells are disjoint
  obtain ⟨w, hwr, rfl⟩ := exists_mem_region_F_eq (tgt_cell_subset_region' n hσ hout hy)
  refine Set.mem_image_of_mem _ ?_
  set ρ := (L.src n).carrier w with hρdef
  have hρc : ρ ∈ (L.str n).cells := (L.srcDecomp n).mem_cells_carrier hwr.1
  have hρface : ρ ∈ (L.str n).faces := by
    refine mem_faces_of_notMem_skel hρc fun hmem => ?_
    -- a skeleton carrier would put `F w` on the target skeleton, which misses the open 2-cell
    refine Set.disjoint_left.1 ((L.tgtDecomp n).cell_disjoint_skeletonSet hface) hy ?_
    rw [F_eq_skelHomeo (Realization.cell_subset_skeletonSet hmem
      ((L.srcDecomp n).mem_cell_carrier hwr.1)) hwr.1]
    refine Realization.cell_subset_skeletonSet hmem ?_
    rw [← (L.skelHomeo n).image_cell hmem]
    exact Set.mem_image_of_mem _ ((L.srcDecomp n).mem_cell_carrier hwr.1)
  have hin : L.F w ∈ (L.tgt n).cell ρ :=
    F_mem_cell_of_mem_cell_face n hρface ((L.srcDecomp n).mem_cell_carrier hwr.1)
  have : ρ = σ := by
    by_contra hne
    exact Set.disjoint_left.1 ((L.tgtDecomp n).disjoint hρc hσ hne) hin hy
  rw [← this]
  exact (L.srcDecomp n).mem_cell_carrier hwr.1

/-- **The corollary the inverse argument runs on**: `F` matches carriers. -/
theorem tgt_carrier_F (hx : x ∈ L.region) (n : ℕ) :
    (L.tgt n).carrier (L.F x) = (L.src n).carrier x := by
  refine (L.tgtDecomp n).carrier_eq ((L.srcDecomp n).mem_cells_carrier hx.1) ?_
  rw [← image_cell n ((L.srcDecomp n).mem_cells_carrier hx.1)
    (src_carrier_notMem_outerCells hx n)]
  exact Set.mem_image_of_mem _ ((L.srcDecomp n).mem_cell_carrier hx.1)

/-! #### The inverse, and the interior homeomorphism -/

open scoped Classical in
/-- **The inverse of `F`**, as an explicit function `Plane → Plane` rather than a bundled
`Homeomorph`: a chosen preimage in `D`. Surjectivity makes the choice possible and injectivity
makes it irrelevant. `Endgame.lean` consumes the pair `(F, inv)` in the `IsHomeoOn` shape, which
needs the inverse named. -/
noncomputable def inv (L : LimitTower γ) (y : Plane) : Plane :=
  if h : ∃ x, x ∈ L.region ∧ L.F x = y then h.choose else 0

theorem inv_spec (h : ∃ x, x ∈ L.region ∧ L.F x = y) :
    L.inv y ∈ L.region ∧ L.F (L.inv y) = y := by
  rw [inv, dite_eq_left h]
  exact h.choose_spec

theorem inv_mem_region (hy : y ∈ L.region') : L.inv y ∈ L.region :=
  (inv_spec (exists_mem_region_F_eq hy)).1

theorem F_inv (hy : y ∈ L.region') : L.F (L.inv y) = y :=
  (inv_spec (exists_mem_region_F_eq hy)).2

theorem inv_F (hx : x ∈ L.region) : L.inv (L.F x) = x :=
  L.injOn_F (inv_spec ⟨x, hx, rfl⟩).1 hx (inv_spec ⟨x, hx, rfl⟩).2

/-- `tgt_carrier_F` read at `inv y`. -/
theorem src_carrier_inv (hy : y ∈ L.region') (n : ℕ) :
    (L.src n).carrier (L.inv y) = (L.tgt n).carrier y := by
  have h := tgt_carrier_F (inv_mem_region hy) n
  rw [F_inv hy] at h
  exact h.symm

/-- **`prop:inverse-continuous`**: `F⁻¹ : Q° → D` is continuous. `lem:cell-neighborhood` is
applied on the *target* side; `lem:exact-cell-correspondence`, in the form `src_carrier_inv`,
transports the resulting subcell relation to the source, where the source star of `x` is small. -/
theorem continuousOn_inv (L : LimitTower γ) : ContinuousOn L.inv L.region' := by
  rw [Metric.continuousOn_iff]
  intro y hy η hη
  have hxr : L.inv y ∈ L.region := inv_mem_region hy
  obtain ⟨n, hn⟩ := exists_lt_of_tendsto_zero (tendsto_diam_srcStar_point hxr) hη
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.1 ((L.tgt n).isOpen_cellNbhd y) y ((L.tgt n).mem_cellNbhd_self y)
  refine ⟨δ, hδ, fun z hz hzdist => ?_⟩
  have hsub : (L.str n).sub ((L.tgt n).carrier y) ((L.tgt n).carrier z) :=
    (L.tgtDecomp n).sub_carrier_of_mem_cellNbhd (region'_subset_dom' hy)
      (hball (Metric.mem_ball.2 hzdist)) (region'_subset_dom' hz)
  rw [← src_carrier_inv hy n, ← src_carrier_inv hz n] at hsub
  have hmem : L.inv z ∈ L.srcStar n (L.inv y) :=
    (L.srcDecomp n).star_anti_of_sub (L.comb n) ((L.srcDecomp n).mem_cells_carrier hxr.1)
      ((L.srcDecomp n).mem_cells_carrier (inv_mem_region hz).1) hsub
      ((L.srcDecomp n).mem_star_carrier (inv_mem_region hz).1)
  exact lt_of_le_of_lt
    (dist_le_diam_of_mem (isBounded_srcStar n _) hmem (mem_srcStar_self hxr.1 n)) hn

/-- **`prop:interior-homeomorphism`**: `F : Int(C) → Q°` is a homeomorphism, in the
`Schoenflies.IsHomeoOn` shape — the map, its explicit inverse, and the four laws on the two
sets — that `Endgame.lean` and the boundary-continuity module consume. -/
theorem isHomeoOn_F (L : LimitTower γ) : IsHomeoOn L.F L.inv L.region L.region' where
  mapsTo := fun _ hx => F_mem_region' hx
  mapsTo_inv := fun _ hy => inv_mem_region hy
  continuousOn := L.continuousOn_F.mono region_subset_dom
  continuousOn_inv := L.continuousOn_inv
  invOn := ⟨fun _ hx => inv_F hx, fun _ hy => F_inv hy⟩

theorem image_region (L : LimitTower γ) : L.F '' L.region = L.region' :=
  L.isHomeoOn_F.image_eq

/-- **`prop:interior-homeomorphism`** as the blueprint states it: a homeomorphism of `Int(C)` onto
`Q°` that agrees with the stage-`N` skeleton map on `G_N ∩ (C ∪ D)` for every `N`. -/
theorem interior_homeomorphism (L : LimitTower γ) :
    IsHomeoOn L.F L.inv L.region L.region' ∧
      ∀ n, ∀ x ∈ (L.src n).skeletonSet, x ∈ L.dom → L.F x = (L.skelHomeo n).toFun x :=
  ⟨L.isHomeoOn_F, fun _ _ hx hxD => F_eq_skelHomeo hx hxD⟩

end LimitTower

end CellStructure

end Schoenflies
