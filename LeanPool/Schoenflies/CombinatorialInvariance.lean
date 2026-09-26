/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Mathlib.Combinatorics.Graph.Maps
public import LeanPool.Schoenflies.Graph.Drawing
public import LeanPool.Schoenflies.Graph.TwoConnected

/-!
# Combinatorial invariance

The first module of Part II. It introduces the abstract record of a matched cellulation, the
notion of a geometric realization of that record, and proves that everything a realization
inherits from the record is the same for two realizations of one record —
`lem:combinatorial-invariance`.

Per the blueprint's citation index this lemma has no internal prerequisites: the whole point of
the design is that the combinatorial content of the cellulation machinery is separated from all
of the geometry, so this can be built while the Jordan curve theorem is still unproved.

## What is defined here, and how faithful it is

`CellStructure` is the *abstract* record of `def:matched-cellulation`: the finite cell sets in
each dimension, the endpoint maps, the outer subcomplex, the boundary walks, and the subcell
relation. Cells of all three dimensions are names drawn from one type `γ`; the 0- and 1-cells
are the vertices and the edges of an abstract multigraph `skel : Graph γ γ`, the 2-cells are a
set `faces`, and the three collections are disjoint. What is deliberately **not** in the record:
the parent maps (they belong to a refinement — a pair of stages — not to a stage), and any
compatibility between `sub` and the realizations (that is assertion (ix) of
`lem:cellulation-invariants`, and the blueprint is explicit that `≼_abs` "enters as a raw
datum"). No reflexivity or transitivity of `sub` is assumed; the one lemma that needs
transitivity takes it as a hypothesis.

`CellStructure.Realization` is one of the two geometric realizations. The repository's plane
graphs have `V(G) : Set Plane` — vertices *are* points — so the drawn skeleton cannot literally
be the abstract graph. It is instead the pushforward `S.skel.map pos` along the positions of
the 0-cells, with `pos` injective on `V(S.skel)`. This is the representation choice of the
module, and the alternative — carrying an abstract graph isomorphism as data — was rejected
because with the pushforward "the two skeleta realize the *same* abstract graph" is a
definitional identity rather than a theorem, which is exactly what the blueprint's proof of
part (a) asserts.

The price of the choice is paid here, once: `Graph.isTwoConnected_map_iff` and
`Graph.connected_map_iff` transport connectivity along an injective relabelling of the
vertices, so that 2-connectivity of the *drawn* graph — which is what
`def:admissible-graph` requires — transfers between the realizations. Those two, and the walk
and vertex-deletion lemmas they rest on, are general facts about `Graph.map` in the root
`Graph` namespace and belong in `Schoenflies/Graph/` if a second consumer appears.

`SkeletonHomeo` is `g : |Γ| → |Γ'|` of `def:matched-pair`, as a set-level homeomorphism with
its inverse supplied as data (so that no finiteness hypothesis is needed to invert it).
Clause 3 of `def:matched-pair` is recorded in the weaker form "`g` carries each drawn edge onto
the corresponding drawn edge", which is all that is used and which the full clause implies.

## The three parts of the lemma

Only part (b) has topological content. Parts (a) and (c) are, under this representation, either
definitional identities or one-line consequences of the fact that the index sets involved are
fields of the single structure both realizations realize; that is precisely the blueprint's
argument ("all the data in (c) belong to the common abstract cell structure"), and the
statements below are shaped so that a consumer gets the geometric conclusion on *both* sides
from one combinatorial hypothesis.

## Blueprint

* `Schoenflies.CellStructure` — the abstract record of `def:matched-cellulation`.
* `Schoenflies.CellStructure.Realization` — one of its two geometric realizations.
* `Schoenflies.CellStructure.Realization.nonboundary` — the open nonboundary part
  `|Γ| \ C` of `def:admissible-graph`.
* `Schoenflies.CellStructure.Realization.star` — the closed star `St(σ) = ⋃_{σ ≼ τ} closure τ`.
* `Schoenflies.CellStructure.SkeletonHomeo` — the skeleton homeomorphism of
  `def:matched-pair`.
* `Schoenflies.CellStructure.combinatorial_invariance` — `lem:combinatorial-invariance`,
  assembled from:
  * (a) `Realization.graph_eq_map`, `Realization.edgeSet_graph_congr`,
    `Realization.isTwoConnected_congr`, `SkeletonHomeo.image_outerSet`;
  * (b) `SkeletonHomeo.image_nonboundary`, `SkeletonHomeo.isConnected_nonboundary_iff`;
  * (c) `Realization.star_mono`, `Realization.star_transfer`,
    `Realization.star_subset_of_sub`, `outerEdge_face_corresponds`.
* `Graph.isTwoConnected_map_iff`, `Graph.connected_map_iff` — connectivity is invariant under
  an injective relabelling of the vertices; the transport that the pushforward representation
  of a realization needs.
-/

public section

open Set Schoenflies
open scoped Graph

namespace Graph

variable {α α' β : Type*} {G : Graph α β} {f : α → α'} {u v x : α} {W : List β}

theorem IsWalk.map (f : α → α') (h : G.IsWalk u W v) : (G.map f).IsWalk (f u) W (f v) := by
  induction h with
  | nil hx => exact .nil (by simpa using Set.mem_image_of_mem f hx)
  | cons hl _ ih => exact .cons (hl.map f) ih

theorem Reaches.map (f : α → α') (h : G.Reaches u v) : (G.map f).Reaches (f u) (f v) :=
  ⟨h.choose, h.choose_spec.map f⟩

theorem Connected.map (f : α → α') (h : G.Connected) : (G.map f).Connected := by
  obtain ⟨⟨u, hu⟩, hreach⟩ := h
  refine ⟨⟨f u, by simpa using Set.mem_image_of_mem f hu⟩, ?_⟩
  rintro a ha b hb
  simp only [vertexSet_map, Set.mem_image] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  exact (hreach ha' hb').map f

theorem HasThreeVertices.map (hf : InjOn f V(G)) (h : G.HasThreeVertices) :
    (G.map f).HasThreeVertices := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  have hmem : ∀ {z}, z ∈ V(G) → f z ∈ V(G.map f) := fun hz => by
    simpa using Set.mem_image_of_mem f hz
  exact ⟨f p, hmem hp, f q, hmem hq, f r, hmem hr, fun hcon => hpq (hf hp hq hcon),
    fun hcon => hpr (hf hp hr hcon), fun hcon => hqr (hf hq hr hcon)⟩

/-- Deleting a vertex commutes with an injective relabelling of the vertices. -/
theorem map_deleteVerts_singleton (hf : InjOn f V(G)) (hx : x ∈ V(G)) :
    (G.map f).deleteVerts {f x} = (G.deleteVerts {x}).map f := by
  refine Graph.ext ?_ ?_
  · rw [vertexSet_deleteVerts, vertexSet_map, vertexSet_map, vertexSet_deleteVerts]
    rw [hf.image_sdiff_subset (Set.singleton_subset_iff.2 hx), Set.image_singleton]
  · intro e a b
    rw [deleteVerts_isLink]
    simp only [map_isLink, Relation.map_apply, deleteVerts_isLink, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨p, q, hpq, rfl, rfl⟩, hp, hq⟩
      exact ⟨p, q, ⟨hpq, fun h => hp (by rw [h]), fun h => hq (by rw [h])⟩, rfl, rfl⟩
    · rintro ⟨p, q, ⟨hpq, hp, hq⟩, rfl, rfl⟩
      exact ⟨⟨p, q, hpq, rfl, rfl⟩, fun h => hp (hf hpq.left_mem hx h),
        fun h => hq (hf hpq.right_mem hx h)⟩

theorem IsTwoConnected.map (hf : InjOn f V(G)) (h : G.IsTwoConnected) :
    (G.map f).IsTwoConnected where
  hasThreeVertices := h.hasThreeVertices.map hf
  connected := h.connected.map f
  deleteVerts_connected := by
    intro a ha
    simp only [vertexSet_map, Set.mem_image] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [map_deleteVerts_singleton hf hx]
    exact (h.deleteVerts_connected hx).map f

/-- An injective relabelling can be undone: `Function.invFunOn` inverts it on the vertex set. -/
theorem map_map_invFunOn [Nonempty α] (hf : InjOn f V(G)) :
    (G.map f).map (Function.invFunOn f V(G)) = G := by
  have key : G.map (Function.invFunOn f V(G) ∘ f) = G.map id :=
    map_eq_of_eqOn fun z hz => hf.leftInvOn_invFunOn hz
  rw [map_map, key, map_id]

theorem connected_map_iff (hf : InjOn f V(G)) : (G.map f).Connected ↔ G.Connected := by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  obtain ⟨a, ha⟩ := h.nonempty
  rw [vertexSet_map] at ha
  obtain ⟨z, hz, -⟩ := ha
  have : Nonempty α := ⟨z⟩
  have himg : InjOn (Function.invFunOn f V(G)) V(G.map f) := by
    rw [vertexSet_map]; exact Function.invFunOn_injOn_image f V(G)
  have := h.map (Function.invFunOn f V(G))
  rwa [map_map_invFunOn hf] at this

theorem isTwoConnected_map_iff (hf : InjOn f V(G)) :
    (G.map f).IsTwoConnected ↔ G.IsTwoConnected := by
  refine ⟨fun h => ?_, fun h => h.map hf⟩
  obtain ⟨a, ha⟩ := h.connected.nonempty
  rw [vertexSet_map] at ha
  obtain ⟨z, hz, -⟩ := ha
  have : Nonempty α := ⟨z⟩
  have himg : InjOn (Function.invFunOn f V(G)) V(G.map f) := by
    rw [vertexSet_map]; exact Function.invFunOn_injOn_image f V(G)
  have := h.map himg
  rwa [map_map_invFunOn hf] at this

/-! ### The point set of a subgraph -/

variable {δ : Type*} {H K : Graph Plane δ} {drawing : δ → ℝ → Plane}

theorem pointSet_mono (h : H ≤ K) : pointSet H drawing ⊆ pointSet K drawing :=
  Set.union_subset_union h.vertexSet_mono
    (Set.biUnion_subset_biUnion_left h.edgeSet_mono)

end Graph

namespace Schoenflies

open Graph

variable {γ : Type*}

/-- The abstract record of a matched cellulation (def:matched-cellulation), stripped to the
data every consumer of combinatorial invariance reads.

The cells of all three dimensions are names drawn from one type `γ`: the 0-cells are the
vertices of the skeleton, the 1-cells are its edges, and the 2-cells are `faces`. The three
collections are required to be disjoint, so "the dimension of a cell" is well defined without
being a field.

`sub` is the abstract subcell relation `≼_abs`. The blueprint is explicit that it "enters as a
raw datum" and imposes no compatibility with the realizations: that compatibility is assertion
(ix) of lem:cellulation-invariants, proved elsewhere and for generated structures only. No
reflexivity or transitivity is assumed here either; the two lemmas below that need
transitivity take it as a hypothesis. -/
structure CellStructure (γ : Type*) where
  /-- The abstract 1-skeleton: its vertices are the 0-cells, its edges the 1-cells. -/
  skel : Graph γ γ
  /-- The 2-cells. -/
  faces : Set γ
  /-- The distinguished outer cycle, as a subgraph of the skeleton. -/
  outerGraph : Graph γ γ
  /-- The outer cycle is part of the skeleton. -/
  outerGraph_le : outerGraph ≤ skel
  /-- The cyclic boundary walk of each 2-cell, as a list of edge names. Raw datum: the
  blueprint lists it in the record of a matched cellulation and updates it explicitly under
  the two constructors. -/
  boundary : γ → List γ
  /-- The abstract subcell relation `≼_abs`. -/
  sub : γ → γ → Prop
  /-- Finitely many 0-cells. -/
  finite_vertexSet : V(skel).Finite
  /-- Finitely many 1-cells. -/
  finite_edgeSet : E(skel).Finite
  /-- Finitely many 2-cells. -/
  finite_faces : faces.Finite
  /-- A name is not both a 0-cell and a 1-cell. -/
  disjoint_vertexSet_edgeSet : Disjoint V(skel) E(skel)
  /-- A name is not both a 2-cell and a 0-cell. -/
  disjoint_faces_vertexSet : Disjoint faces V(skel)
  /-- A name is not both a 2-cell and a 1-cell. -/
  disjoint_faces_edgeSet : Disjoint faces E(skel)

namespace CellStructure

variable (S : CellStructure γ)

/-- All cells of the structure. -/
@[expose] def cells : Set γ := V(S.skel) ∪ E(S.skel) ∪ S.faces

/-- The cells of the distinguished outer cycle: its vertices and its edges. -/
def outerCells : Set γ := V(S.outerGraph) ∪ E(S.outerGraph)

/-- The supercells of a cell: the index set of its closed star. -/
def supercells (σ : γ) : Set γ := {τ | S.sub σ τ}

/-- A cell is incident with the outer cycle when some outer cell is a subcell of it. This is
the middle, purely combinatorial condition of lem:outer-incidence. -/
def MeetsOuter (τ : γ) : Prop := ∃ κ ∈ S.outerCells, S.sub κ τ

theorem mem_supercells {σ τ : γ} : τ ∈ S.supercells σ ↔ S.sub σ τ := Iff.rfl

theorem supercells_subset_of_sub (htrans : ∀ ⦃a b c⦄, S.sub a b → S.sub b c → S.sub a c)
    {σ τ : γ} (h : S.sub σ τ) :
    S.supercells τ ⊆ S.supercells σ := fun _ hρ => htrans h hρ

/-! ### Realizations -/

/-- A geometric realization of the abstract structure: a position for each 0-cell, a
parametrization for each 1-cell, and a point set for every open cell.

The drawn graph is `S.skel.map pos` — literally the pushforward of the *one* abstract
skeleton. That is what makes "two realizations of the same abstract graph" a matter of
definition rather than of a transported isomorphism.

Nothing is required of `cell` on a 2-cell. What it would have to satisfy — that the open
2-cell is the bounded complementary region of the Jordan curve of its boundary walk — is
assertion (vii) of lem:cellulation-invariants, which is not available at this point in the
development and which combinatorial invariance does not use. -/
structure Realization (S : CellStructure γ) where
  /-- Where each 0-cell sits. -/
  pos : γ → Plane
  /-- How each 1-cell runs. -/
  drawing : γ → ℝ → Plane
  /-- Distinct 0-cells sit at distinct points. -/
  injOn_pos : InjOn pos V(S.skel)
  /-- The positions and parametrizations draw the skeleton in the plane. -/
  isDrawing : IsDrawing (S.skel.map pos) drawing
  /-- The point set of each open cell. -/
  cell : γ → Set Plane
  /-- A 0-cell is realized by its point. -/
  cell_vertex : ∀ ⦃v⦄, v ∈ V(S.skel) → cell v = {pos v}
  /-- A 1-cell is realized by its open arc: the drawn arc minus its two endpoints. -/
  cell_edge : ∀ ⦃e x y⦄, S.skel.IsLink e x y → cell e = edgeArc drawing e \ {pos x, pos y}

namespace Realization

variable {S}
variable (R : S.Realization)

/-- The drawn skeleton: the pushforward of the abstract skeleton along the positions. -/
def graph : Graph Plane γ := S.skel.map R.pos

@[simp] theorem vertexSet_graph : V(R.graph) = R.pos '' V(S.skel) := vertexSet_map _ _

@[simp] theorem edgeSet_graph : E(R.graph) = E(S.skel) := edgeSet_map _ _

instance finite_graph : (R.graph).Finite where
  finite_vertexSet := by rw [vertexSet_graph]; exact S.finite_vertexSet.image _
  finite_edgeSet := by rw [edgeSet_graph]; exact S.finite_edgeSet

/-- The realized 1-skeleton `|Γ|`. -/
def skeletonSet : Set Plane := pointSet R.graph R.drawing

/-- The realized outer cycle: `C` in the source realization, `S` in the target one. -/
def outerSet : Set Plane := pointSet (S.outerGraph.map R.pos) R.drawing

/-- The **open nonboundary part** `|Γ| \ C` of def:admissible-graph. -/
def nonboundary : Set Plane := R.skeletonSet \ R.outerSet

/-- The closed star of a cell: the union of the closures of its supercells. The index set is
abstract; only the summands are geometric. -/
@[expose] def star (σ : γ) : Set Plane := ⋃ τ ∈ S.supercells σ, closure (R.cell τ)

theorem outerSet_subset_skeletonSet : R.outerSet ⊆ R.skeletonSet :=
  pointSet_mono (S.outerGraph_le.map R.pos)

theorem isCompact_skeletonSet : IsCompact R.skeletonSet :=
  @IsDrawing.isCompact_pointSet _ _ _ R.finite_graph R.isDrawing

/-- An open 0-cell or 1-cell is part of the realized skeleton: a 0-cell is realized by a drawn
vertex, a 1-cell by part of a drawn edge.

Hoisted here because `Schoenflies/LimitMap.lean` and `Schoenflies/FiniteTransfer.lean` each
proved it independently and the duplicate gate caught the collision — two alpha-equivalent
`Prop`s pass Lean's import checker under proof irrelevance, so a clean build would not have. -/
theorem cell_subset_skeletonSet {R : S.Realization} {κ : γ}
    (hκ : κ ∈ V(S.skel) ∪ E(S.skel)) : R.cell κ ⊆ R.skeletonSet := by
  rcases hκ with hv | he
  · rw [R.cell_vertex hv]
    exact Set.singleton_subset_iff.2 (vertexSet_subset_pointSet
      (by rw [Realization.vertexSet_graph]; exact ⟨κ, hv, rfl⟩))
  · obtain ⟨a, b, hl⟩ := exists_isLink_of_mem_edgeSet he
    rw [R.cell_edge hl]
    exact Set.sdiff_subset.trans (edgeArc_subset_pointSet
      (by rw [Realization.edgeSet_graph]; exact he))

end Realization

/-! ### The skeleton homeomorphism -/

/-- The skeleton homeomorphism `g : |Γ| → |Γ'|` of def:matched-pair, between two realizations
of one abstract cell structure.

Clause 3 of def:matched-pair — "on each corresponding pair of edges, `g` restricts to a fixed
chosen homeomorphism between them, matching endpoints" — is recorded here in the weaker form
`edgeArc_image`, which says only that `g` carries each drawn edge onto the corresponding drawn
edge. That is all combinatorial invariance uses, and it is implied by the stronger clause.

Clause 2 of def:matched-pair, `g = u` on `C`, is *not* recorded: the boundary homeomorphism
`u` is not part of a cell structure. A consumer that needs the identification carries it
alongside; nothing here depends on it.

The inverse is supplied as data rather than produced from compactness, so that no finiteness
hypothesis is needed to speak of a homeomorphism; a producer holding `u⁻¹` has it anyway. -/
structure SkeletonHomeo {S : CellStructure γ} (R₁ R₂ : S.Realization) where
  /-- The map. -/
  toFun : Plane → Plane
  /-- Its inverse. -/
  invFun : Plane → Plane
  /-- The map is continuous on the skeleton. -/
  continuousOn_toFun : ContinuousOn toFun R₁.skeletonSet
  /-- The inverse is continuous on the other skeleton. -/
  continuousOn_invFun : ContinuousOn invFun R₂.skeletonSet
  /-- The inverse undoes the map. -/
  leftInvOn : LeftInvOn invFun toFun R₁.skeletonSet
  /-- The map undoes the inverse. -/
  rightInvOn : RightInvOn invFun toFun R₂.skeletonSet
  /-- Corresponding 0-cells correspond. -/
  pos_apply : ∀ ⦃v⦄, v ∈ V(S.skel) → toFun (R₁.pos v) = R₂.pos v
  /-- Corresponding 1-cells correspond. -/
  edgeArc_image : ∀ ⦃e⦄, e ∈ E(S.skel) → toFun '' edgeArc R₁.drawing e = edgeArc R₂.drawing e

namespace SkeletonHomeo

variable {S} {R₁ R₂ : S.Realization} (g : SkeletonHomeo R₁ R₂)

/-- `g` carries the realization of any subcomplex of the skeleton onto the realization of the
same subcomplex on the other side. Used for the whole skeleton and for the outer cycle. -/
theorem image_pointSet_map {H : Graph γ γ} (hH : H ≤ S.skel) :
    g.toFun '' pointSet (H.map R₁.pos) R₁.drawing = pointSet (H.map R₂.pos) R₂.drawing := by
  rw [pointSet, pointSet, Set.image_union, Set.image_iUnion₂]
  congr 1
  · rw [vertexSet_map, vertexSet_map, ← Set.image_comp]
    exact Set.image_congr fun v hv => g.pos_apply (hH.vertexSet_mono hv)
  · rw [edgeSet_map]
    exact Set.iUnion₂_congr fun e he => g.edgeArc_image (hH.edgeSet_mono he)

theorem image_skeletonSet : g.toFun '' R₁.skeletonSet = R₂.skeletonSet :=
  g.image_pointSet_map le_rfl

/-- **The outer cycle corresponds** — part (a) of lem:combinatorial-invariance, at the level of
the two realizations. -/
theorem image_outerSet : g.toFun '' R₁.outerSet = R₂.outerSet :=
  g.image_pointSet_map S.outerGraph_le

theorem injOn : InjOn g.toFun R₁.skeletonSet := g.leftInvOn.injOn

/-- The homeomorphism run backwards. -/
def symm : SkeletonHomeo R₂ R₁ where
  toFun := g.invFun
  invFun := g.toFun
  continuousOn_toFun := g.continuousOn_invFun
  continuousOn_invFun := g.continuousOn_toFun
  leftInvOn := g.rightInvOn
  rightInvOn := g.leftInvOn
  pos_apply := by
    intro v hv
    have hmem : R₁.pos v ∈ R₁.skeletonSet :=
      vertexSet_subset_pointSet (by rw [Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)
    rw [← g.pos_apply hv, g.leftInvOn hmem]
  edgeArc_image := by
    intro e he
    have hsub : edgeArc R₁.drawing e ⊆ R₁.skeletonSet :=
      edgeArc_subset_pointSet (by rwa [Realization.edgeSet_graph])
    rw [← g.edgeArc_image he]
    exact g.leftInvOn.image_image' hsub

@[simp] theorem symm_toFun : g.symm.toFun = g.invFun := rfl

/-- **The open nonboundary part corresponds** — the geometric half of part (b) of
lem:combinatorial-invariance. The skeleton homeomorphism carries the outer cycle onto the
outer cycle, hence restricts to a bijection of the two open nonboundary parts. -/
theorem image_nonboundary : g.toFun '' R₁.nonboundary = R₂.nonboundary := by
  have : g.toFun '' (R₁.skeletonSet \ R₁.outerSet) = R₂.skeletonSet \ R₂.outerSet := by
    rw [g.injOn.image_sdiff_subset R₁.outerSet_subset_skeletonSet, g.image_skeletonSet,
      g.image_outerSet]
  exact this

/-- **Connectedness of the open nonboundary part is invariant** — part (b) of
lem:combinatorial-invariance. This is the one clause with genuine topological content: it is
what makes admissibility (def:admissible-graph) transfer between the two realizations. -/
theorem isConnected_nonboundary_iff (g : SkeletonHomeo R₁ R₂) :
    IsConnected R₁.nonboundary ↔ IsConnected R₂.nonboundary := by
  constructor
  · intro h
    rw [← g.image_nonboundary]
    exact h.image _ (g.continuousOn_toFun.mono Set.sdiff_subset)
  · intro h
    rw [← g.symm.image_nonboundary]
    exact h.image _ (g.symm.continuousOn_toFun.mono Set.sdiff_subset)

theorem isPreconnected_nonboundary_iff (g : SkeletonHomeo R₁ R₂) :
    IsPreconnected R₁.nonboundary ↔ IsPreconnected R₂.nonboundary := by
  constructor
  · intro h
    rw [← g.image_nonboundary]
    exact h.image _ (g.continuousOn_toFun.mono Set.sdiff_subset)
  · intro h
    rw [← g.symm.image_nonboundary]
    exact h.image _ (g.symm.continuousOn_toFun.mono Set.sdiff_subset)

end SkeletonHomeo

/-! ### Combinatorial invariance -/

variable {S}

/-- **The abstract skeleton is one graph** — part (a) of lem:combinatorial-invariance. Both
drawn skeleta are pushforwards of `S.skel`, so in particular they carry the same edge names. -/
theorem Realization.graph_eq_map (R : S.Realization) : R.graph = S.skel.map R.pos := rfl

theorem Realization.edgeSet_graph_congr (R₁ R₂ : S.Realization) : E(R₁.graph) = E(R₂.graph) := by
  rw [Realization.edgeSet_graph, Realization.edgeSet_graph]

/-- **Connectedness of the skeleton is invariant** — part (a). -/
theorem Realization.connected_congr (R₁ R₂ : S.Realization) :
    R₁.graph.Connected ↔ R₂.graph.Connected :=
  (connected_map_iff R₁.injOn_pos).trans (connected_map_iff R₂.injOn_pos).symm

/-- **2-connectivity of the skeleton is invariant** — part (a) of
lem:combinatorial-invariance, and the clause the finite-transfer theorem cites when it
concludes that a reproduced realization "has the same 2-connectivity" as the given one. -/
theorem Realization.isTwoConnected_congr (R₁ R₂ : S.Realization) :
    R₁.graph.IsTwoConnected ↔ R₂.graph.IsTwoConnected :=
  (isTwoConnected_map_iff R₁.injOn_pos).trans (isTwoConnected_map_iff R₂.injOn_pos).symm

/-- The closed star is a union over an index set that belongs to the abstract structure, so an
inclusion of index sets gives an inclusion of stars in *every* realization. This is what part
(c) of lem:combinatorial-invariance means by "all star-containment statements induced by
refinement". -/
theorem Realization.star_mono (R : S.Realization) {σ τ : γ}
    (h : S.supercells σ ⊆ S.supercells τ) : R.star σ ⊆ R.star τ :=
  Set.biUnion_subset_biUnion_left h

/-- The same combinatorial hypothesis yields the geometric containment on both sides. -/
theorem Realization.star_transfer (R₁ R₂ : S.Realization) {σ τ : γ}
    (h : S.supercells σ ⊆ S.supercells τ) :
    R₁.star σ ⊆ R₁.star τ ∧ R₂.star σ ⊆ R₂.star τ :=
  ⟨R₁.star_mono h, R₂.star_mono h⟩

/-- A subcell has the larger star, once the abstract relation is known to be transitive. -/
theorem Realization.star_subset_of_sub (R : S.Realization)
    (htrans : ∀ ⦃a b c⦄, S.sub a b → S.sub b c → S.sub a c) {σ τ : γ} (h : S.sub σ τ) :
    R.star τ ⊆ R.star σ :=
  R.star_mono (S.supercells_subset_of_sub htrans h)

/-- The clause "every outer edge is a subcell of exactly one 2-cell" — assertion (vi) of
lem:cellulation-invariants — as a property of the abstract structure alone. -/
def OuterEdgeUniqueFace (S : CellStructure γ) : Prop :=
  ∀ ⦃e⦄, e ∈ E(S.outerGraph) → ∃! F, F ∈ S.faces ∧ S.sub e F

/-- **The 2-cell incident with an outer edge is combinatorial** — part (c) of
lem:combinatorial-invariance. There is nothing to transport: the witness is a single abstract
cell `F`, and the two realizations realize that one cell as `R₁.cell F` and `R₂.cell F`. -/
theorem outerEdge_face_corresponds (h : OuterEdgeUniqueFace S) {e : γ}
    (he : e ∈ E(S.outerGraph)) :
    ∃ F, F ∈ S.faces ∧ S.sub e F ∧ ∀ T, T ∈ S.faces → S.sub e T → T = F := by
  obtain ⟨F, ⟨hF, hsub⟩, huniq⟩ := h he
  exact ⟨F, hF, hsub, fun T hT hTsub => huniq T ⟨hT, hTsub⟩⟩

/-- **Combinatorial invariance** (lem:combinatorial-invariance), assembled.

Given two realizations of one generated matched cell structure and the skeleton
homeomorphism between them:

* (a) the two drawn skeleta are pushforwards of the same abstract graph `S.skel`, they carry
  the same edge names, 2-connectivity holds for one iff it holds for the other, and the
  realized outer cycles correspond under `g`;
* (b) the realized open nonboundary parts correspond under `g`, so one is connected iff the
  other is;
* (c) an inclusion of supercell sets — a statement of the common abstract structure — gives
  the corresponding star containment in both realizations.

The subcell relation, the parent maps and the collection of supercells of a cell do not
appear in the conclusion because under this representation they are not two objects to be
compared: they are fields of the single `S` that both realizations are realizations *of*. -/
theorem combinatorial_invariance {R₁ R₂ : S.Realization} (g : SkeletonHomeo R₁ R₂) :
    (E(R₁.graph) = E(R₂.graph) ∧
      (R₁.graph.IsTwoConnected ↔ R₂.graph.IsTwoConnected) ∧
      g.toFun '' R₁.outerSet = R₂.outerSet) ∧
    (g.toFun '' R₁.nonboundary = R₂.nonboundary ∧
      (IsConnected R₁.nonboundary ↔ IsConnected R₂.nonboundary)) ∧
    (∀ σ τ : γ, S.supercells σ ⊆ S.supercells τ →
      R₁.star σ ⊆ R₁.star τ ∧ R₂.star σ ⊆ R₂.star τ) :=
  ⟨⟨R₁.edgeSet_graph_congr R₂, R₁.isTwoConnected_congr R₂, g.image_outerSet⟩,
    ⟨g.image_nonboundary, g.isConnected_nonboundary_iff⟩,
    fun _ _ h => Realization.star_transfer R₁ R₂ h⟩

end CellStructure

end Schoenflies
