/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.AccessibleJoin
public import LeanPool.Schoenflies.JordanClosed
public import LeanPool.Schoenflies.Inversion
public import LeanPool.Schoenflies.ModelCurve
public import LeanPool.Schoenflies.ArcComplementPrep
public import LeanPool.Schoenflies.Graph.Drawing

/-!
# `lem:skeleton-crosscuts`: a crosscut inside one stage of the skeleton

Two anchors lying in a common finite stage are joined by a polygonal crosscut of the Jordan
domain that lies *in that stage's skeleton* (`jordan_schoenflies.tex` 2857-2872). This file
proves the first clause, for the source side.

Everything here concerns **one finite plane graph**: a stage is a
finite plane graph whose point set carries the Jordan curve `C` as its outer boundary
(`Graph.IsStageOn`), and nothing below mentions the sequence of stages that produces it.

The blueprint's proof splits on whether some *nonboundary* edge — one whose arc is not
contained in `C` — has both of its ends on `C`. If one does, its open interior is a whole
component of the open nonboundary part, so it is the only nonboundary edge and is itself the
crosscut. Otherwise every nonboundary edge meeting `C` has its other end inside, and the
interior subgraph `interiorPart` is connected because the half-open attached edges partition
the open nonboundary part into relatively clopen pieces.

## What is here, and what is not

This module was written in one sitting that ended early, and it stops after the source-side
crosscut. The rest of the section — the target crosscut of clause 2,
`lem:crosscut-side-correspondence`, `prop:boundary-continuity`, and the assembly of
`thm:square-extension` — is in `Schoenflies/BoundaryContinuity2.lean`, which imports this one.
An earlier version of this docstring listed those as if they were here; they never were.

## Blueprint

* `Graph.IsStageOn` — a finite plane graph carrying `C` as its outer boundary.
* `Graph.Nonboundary`, `Graph.interiorPart`, `Graph.attachEdges`,
  `Graph.isPreconnected_interiorPart` — the interior subgraph and its connectedness, which is
  the substance of the second case.
* `Graph.IsStageOn.exists_crosscut` — **`lem:skeleton-crosscuts`, clause 1**: the source-side
  polygonal crosscut between two prescribed points of `C` that the stage joins. Clause 2, the
  target crosscut, is in `Schoenflies/BoundaryContinuity2.lean`.
-/

public section

open Metric Set Schoenflies
open scoped Graph

/-! ## `lem:skeleton-crosscuts`

A stage of the skeleton is a finite plane graph whose point set carries the Jordan curve `C` as
its outer boundary. The blueprint's proof splits on whether some *nonboundary* edge — an edge
whose arc is not contained in `C` — has both of its ends on `C`.

Everything in this section speaks about one finite plane graph and never
about the stages that produce it.
-/

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {C D : Set Plane}

/-- An edge is **nonboundary** when its arc is not contained in the outer boundary. -/
def Nonboundary (drawing : β → ℝ → Plane) (C : Set Plane) (e : β) : Prop :=
  ¬ edgeArc drawing e ⊆ C

/-- **One finite stage of the skeleton**, as `lem:skeleton-crosscuts` uses it.

`C` is the outer boundary and `D` the region it bounds. The two substantive clauses are
`edge_split` — every edge either runs inside `C` or has all of its non-endpoint points in `D` —
and `isConnected_diff`, the admissibility hypothesis that the *open nonboundary part*
`|Γ| ∖ C` is connected.

`D` is an arbitrary set disjoint from `C`, not `Schoenflies.inside C`: the proof uses nothing
about it, and the consumer instantiates it with the Jordan domain. -/
structure IsStageOn (G : Graph Plane β) (drawing : β → ℝ → Plane) (C D : Set Plane) : Prop where
  /-- the graph is drawn in the plane -/
  isDrawing : IsDrawing G drawing
  /-- every **nonboundary** edge is drawn as a polygonal arc.

  Only the nonboundary edges: `def:admissible-graph` says "its edges *not contained in `C`* are
  polygonal arcs", and for a source stage that restriction is not a convenience but a necessity.
  The outer edges of a source stage are subarcs of the wild Jordan curve `C`, which is in general
  nowhere polygonal, so a field asking `IsPolygonal` of every edge would make `IsStageOn`
  unsatisfiable for exactly the graphs `lem:skeleton-crosscuts` is about. It was stated that way
  and is repaired here; both proofs below already applied it only to nonboundary edges. -/
  polygonal : ∀ ⦃e⦄, e ∈ E(G) → Nonboundary drawing C e →
    Schoenflies.IsPolygonal (edgeArc drawing e)
  /-- the outer boundary and the region it bounds are disjoint -/
  disjoint : Disjoint C D
  /-- a vertex off the outer boundary lies in the region -/
  vertex_mem : ∀ ⦃v⦄, v ∈ V(G) → v ∉ C → v ∈ D
  /-- an edge either lies on the outer boundary or has its interior in the region -/
  edge_split : ∀ ⦃e x y⦄, G.IsLink e x y →
    edgeArc drawing e ⊆ C ∨ edgeArc drawing e \ {x, y} ⊆ D
  /-- **admissibility**: the open nonboundary part is connected -/
  isConnected_diff : IsConnected (pointSet G drawing \ C)

namespace IsStageOn

theorem notMem_of_mem_curve (h : IsStageOn G drawing C D) {z : Plane} (hz : z ∈ C) : z ∉ D :=
  fun hD => (h.disjoint.ne_of_mem hz hD) rfl

theorem notMem_curve (h : IsStageOn G drawing C D) {z : Plane} (hz : z ∈ D) : z ∉ C :=
  fun hzC => h.notMem_of_mem_curve hzC hz

/-- Off the outer boundary, the point set of the stage lies in the region. This is the reading
of `edge_split` and `vertex_mem` the crosscut extraction needs. -/
theorem pointSet_diff_subset (h : IsStageOn G drawing C D) :
    pointSet G drawing \ C ⊆ D := by
  rintro p ⟨hp, hpC⟩
  rcases hp with hv | hp
  · exact h.vertex_mem hv hpC
  · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.1 hp
    obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet he
    rcases h.edge_split hl with hsub | hsub
    · exact absurd (hsub hpe) hpC
    · -- `p` is on the edge and off the curve; if it is an end, the end is off the curve too.
      by_cases hpxy : p ∈ ({x, y} : Set Plane)
      · rcases hpxy with rfl | rfl
        · exact h.vertex_mem hl.left_mem hpC
        · exact h.vertex_mem hl.right_mem hpC
      · exact hsub ⟨hpe, hpxy⟩

/-- On a nonboundary edge the outer boundary is met only at the two ends. -/
theorem edgeArc_inter_curve (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e) :
    edgeArc drawing e ∩ C ⊆ {x, y} := by
  rcases h.edge_split hl with hsub | hsub
  · exact absurd hsub hnb
  · rintro p ⟨hpe, hpC⟩
    by_contra hp
    exact h.notMem_of_mem_curve hpC (hsub ⟨hpe, hp⟩)

/-- The two ends of an edge lie on its arc. -/
theorem left_mem_edgeArc (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) : x ∈ edgeArc drawing e :=
  (h.isDrawing.edge_isArcBetween hl).left_mem

theorem right_mem_edgeArc (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) : y ∈ edgeArc drawing e :=
  (h.isDrawing.edge_isArcBetween hl).right_mem

/-- A nonboundary edge whose two ends lie in the region runs entirely inside it. -/
theorem edgeArc_subset_of_ends (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e) (hx : x ∈ D) (hy : y ∈ D) :
    edgeArc drawing e ⊆ D := by
  intro p hp
  by_cases hpxy : p ∈ ({x, y} : Set Plane)
  · simp only [mem_insert_iff, mem_singleton_iff] at hpxy
    rcases hpxy with rfl | rfl
    · exact hx
    · exact hy
  · rcases h.edge_split hl with hc | hd
    · exact absurd hc hnb
    · exact hd ⟨hp, hpxy⟩

/-! ### Case 1: a nonboundary edge with both ends on the outer boundary

*Its open interior `e°` is a connected component of `X = |Γ| ∖ C`, because an edge interior
meets the rest of the graph only at its endpoints, and those endpoints have been removed. Hence
`X = e°`, and there is then only one nonboundary edge.* -/

/-- **Case 1, first half.** If a nonboundary edge `e` has both ends on `C`, the whole open
nonboundary part lies on `e`.

The proof is `lem:clopen-component` in the closed-set form: `edgeArc e` and the rest of the
drawing are two closed sets covering the point set whose common part misses `X`. -/
theorem diff_subset_edgeArc [G.Finite] (h : IsStageOn G drawing C D)
    {e : β} {x y : Plane} (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e)
    (hx : x ∈ C) (hy : y ∈ C) : pointSet G drawing \ C ⊆ edgeArc drawing e := by
  classical
  -- Everything the drawing occupies apart from the interior of `e`.
  set R : Set Plane := V(G) ∪ ⋃ f ∈ {f | f ∈ E(G) ∧ f ≠ e}, edgeArc drawing f with hRdef
  have hRclosed : IsClosed R := by
    refine (Graph.finite_vertexSet (G := G)).isCompact.isClosed.union ?_
    refine (Set.Finite.isCompact_biUnion ?_
      fun f hf => h.isDrawing.isCompact_edgeArc hf.1).isClosed
    exact (Graph.finite_edgeSet (G := G)).subset fun f hf => hf.1
  have hcover : pointSet G drawing ⊆ edgeArc drawing e ∪ R := by
    rintro p (hv | hp)
    · exact Or.inr (Or.inl hv)
    · obtain ⟨f, hf, hpf⟩ := mem_iUnion₂.1 hp
      by_cases hfe : f = e
      · exact Or.inl (hfe ▸ hpf)
      · exact Or.inr (Or.inr (mem_iUnion₂.2 ⟨f, ⟨hf, hfe⟩, hpf⟩))
  -- The two closed sets meet only at vertices, and both ends of `e` were removed.
  have hmeet : (pointSet G drawing \ C) ∩ (edgeArc drawing e ∩ R) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro p ⟨⟨-, hpC⟩, hpe, hpR⟩
    have hpV : p ∈ V(G) := by
      rcases hpR with hv | hp
      · exact hv
      · obtain ⟨f, ⟨hf, hfe⟩, hpf⟩ := mem_iUnion₂.1 hp
        exact h.isDrawing.arcs_meet_at_vertex hl.edge_mem hf (Ne.symm hfe) hpe hpf
    rcases h.isDrawing.vertex_mem_edgeArc hl hpV hpe with h1 | h1
    · exact hpC (h1 ▸ hx)
    · exact hpC (h1 ▸ hy)
  intro p hp
  by_contra hpe
  have hne1 : ((pointSet G drawing \ C) ∩ edgeArc drawing e).Nonempty := by
    obtain ⟨z, hze, hzC⟩ := not_subset.1 hnb
    exact ⟨z, ⟨edgeArc_subset_pointSet hl.edge_mem hze, hzC⟩, hze⟩
  have hne2 : ((pointSet G drawing \ C) ∩ R).Nonempty :=
    ⟨p, hp, (hcover hp.1).resolve_left hpe⟩
  have hcon := isPreconnected_closed_iff.1 h.isConnected_diff.2 _ _
    (h.isDrawing.isCompact_edgeArc hl.edge_mem).isClosed hRclosed
    (fun z hz => hcover hz.1) hne1 hne2
  rw [hmeet] at hcon
  exact hcon.ne_empty rfl

/-- **Case 1, second half.** With `X` reduced to one edge interior there is only one nonboundary
edge, so the two prescribed boundary points are exactly the ends of `e`. -/
theorem isLink_of_ends_mem [G.Finite] (h : IsStageOn G drawing C D)
    {e : β} {x y : Plane} (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e)
    (hx : x ∈ C) (hy : y ∈ C) {a b : Plane} (hab : a ≠ b)
    (ha : ∃ f, G.Inc f a ∧ Nonboundary drawing C f)
    (hb : ∃ f, G.Inc f b ∧ Nonboundary drawing C f) : G.IsLink e a b := by
  have hsub := h.diff_subset_edgeArc hl hnb hx hy
  -- Any nonboundary edge carries a point of `X`, hence a point of `e` off the vertices.
  have key : ∀ f, f ∈ E(G) → Nonboundary drawing C f → f = e := by
    intro f hfE hf
    obtain ⟨z, hzf, hzC⟩ := not_subset.1 hf
    have hze : z ∈ edgeArc drawing e :=
      hsub ⟨edgeArc_subset_pointSet hfE hzf, hzC⟩
    by_contra hfe
    have hzV : z ∈ V(G) :=
      h.isDrawing.arcs_meet_at_vertex hl.edge_mem hfE (Ne.symm hfe) hze hzf
    rcases h.isDrawing.vertex_mem_edgeArc hl hzV hze with h1 | h1
    · exact hzC (h1 ▸ hx)
    · exact hzC (h1 ▸ hy)
  obtain ⟨fa, hfa, hfanb⟩ := ha
  obtain ⟨fb, hfb, hfbnb⟩ := hb
  have hia : G.Inc e a := key fa hfa.edge_mem hfanb ▸ hfa
  have hib : G.Inc e b := key fb hfb.edge_mem hfbnb ▸ hfb
  have h1 := hia.eq_or_eq_of_isLink hl
  have h2 := hib.eq_or_eq_of_isLink hl
  rw [hl.isLink_iff]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hab
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩
  · exact absurd (h1.trans h2.symm) hab

end IsStageOn

/-! ### Case 2: the interior subgraph

*Let `Λ` be the finite subgraph consisting of all vertices in `D` and all edges whose two
endpoints lie in `D`, allowing isolated interior vertices.* Only its point set is ever needed,
so `interiorPart` is that set rather than a `Graph`. -/

/-- The point set of the blueprint's interior subgraph `Λ`: the vertices lying in the region,
together with the edges that run entirely inside it. -/
def interiorPart (G : Graph Plane β) (drawing : β → ℝ → Plane) (D : Set Plane) : Set Plane :=
  (V(G) ∩ D) ∪ ⋃ e ∈ {e | e ∈ E(G) ∧ edgeArc drawing e ⊆ D}, edgeArc drawing e

theorem interiorPart_subset : interiorPart G drawing D ⊆ D := by
  rintro p (⟨-, hp⟩ | hp)
  · exact hp
  · obtain ⟨e, ⟨-, hsub⟩, hpe⟩ := mem_iUnion₂.1 hp
    exact hsub hpe

theorem interiorPart_subset_pointSet : interiorPart G drawing D ⊆ pointSet G drawing := by
  rintro p (⟨hp, -⟩ | hp)
  · exact Or.inl hp
  · obtain ⟨e, ⟨heE, -⟩, hpe⟩ := mem_iUnion₂.1 hp
    exact edgeArc_subset_pointSet heE hpe

theorem isClosed_interiorPart [G.Finite] (h : IsDrawing G drawing) :
    IsClosed (interiorPart G drawing D) := by
  refine ((Graph.finite_vertexSet (G := G)).inter_of_left D).isCompact.isClosed.union ?_
  refine (Set.Finite.isCompact_biUnion ?_ fun e he => h.isCompact_edgeArc he.1).isClosed
  exact (Graph.finite_edgeSet (G := G)).subset fun e he => he.1

/-- The union of a subset of `Λ` with the closed edges meeting it. The blueprint attaches the
*half-open* edges; taking the whole closed edge instead gives a set that is closed in the
plane, and intersecting back with `X = |Γ| ∖ C` recovers the blueprint's set, because the
removed ends are exactly the points of those edges lying on `C`. -/
def attachEdges (G : Graph Plane β) (drawing : β → ℝ → Plane) (S : Set Plane) : Set Plane :=
  S ∪ ⋃ e ∈ {e | e ∈ E(G) ∧ (edgeArc drawing e ∩ S).Nonempty}, edgeArc drawing e

theorem subset_attachEdges {S : Set Plane} : S ⊆ attachEdges G drawing S := subset_union_left

theorem isClosed_attachEdges [G.Finite] (h : IsDrawing G drawing) {S : Set Plane}
    (hS : IsClosed S) : IsClosed (attachEdges G drawing S) := by
  refine hS.union ?_
  refine (Set.Finite.isCompact_biUnion ?_ fun e he => h.isCompact_edgeArc he.1).isClosed
  exact (Graph.finite_edgeSet (G := G)).subset fun e he => he.1

namespace IsStageOn

variable (hcase : ∀ ⦃e : β⦄ ⦃x y : Plane⦄, G.IsLink e x y → Nonboundary drawing C e →
  x ∈ C → y ∉ C)

/-- A **half edge** — a nonboundary edge with exactly one end on `C` — meets `Λ` only in its
other end. This is what makes the attached pieces of `X` half-open. -/
theorem edgeArc_inter_interiorPart (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) (hx : x ∈ C) :
    edgeArc drawing e ∩ interiorPart G drawing D ⊆ {y} := by
  rintro p ⟨hpe, hpL⟩
  have hpD : p ∈ D := interiorPart_subset hpL
  have hpV : p ∈ V(G) := by
    rcases hpL with ⟨hv, -⟩ | hp
    · exact hv
    · obtain ⟨f, ⟨hfE, hfD⟩, hpf⟩ := mem_iUnion₂.1 hp
      by_cases hfe : f = e
      · -- `e` would run inside `D`, yet its end `x` is on `C`
        exact absurd (hfD (hfe ▸ h.left_mem_edgeArc hl)) (h.notMem_of_mem_curve hx)
      · exact h.isDrawing.arcs_meet_at_vertex hl.edge_mem hfE (Ne.symm hfe) hpe hpf
  rcases h.isDrawing.vertex_mem_edgeArc hl hpV hpe with h1 | h1
  · exact absurd (h1 ▸ hpD) (h.notMem_of_mem_curve hx)
  · exact h1

/-- **The selection step.** If `Λ` is split into two disjoint closed pieces `S`, `S'` and an
edge meets `S`, then everything that edge shares with `Λ` lies in `S`.

An edge running inside `D` is connected and contained in `S ∪ S'`, so it lies in one piece; a
half edge meets `Λ` in a single point. -/
theorem edgeArc_inter_interiorPart_subset (h : IsStageOn G drawing C D)
    {S S' : Set Plane} (hSc : IsClosed S) (hS'c : IsClosed S')
    (hunion : S ∪ S' = interiorPart G drawing D) (hinter : S ∩ S' = ∅)
    {e : β} (heE : e ∈ E(G)) (hmeet : (edgeArc drawing e ∩ S).Nonempty) :
    edgeArc drawing e ∩ interiorPart G drawing D ⊆ S := by
  obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heE
  obtain ⟨z, hze, hzS⟩ := hmeet
  have hzL : z ∈ interiorPart G drawing D := hunion ▸ Or.inl hzS
  have hzD : z ∈ D := interiorPart_subset hzL
  have hnb : Nonboundary drawing C e := fun hsub => h.notMem_of_mem_curve (hsub hze) hzD
  by_cases hxC : x ∈ C
  · -- half edge with `C`-end `x`; `Λ` is met only at `y`
    have hy := h.edgeArc_inter_interiorPart hl hxC
    intro p hp
    rw [show p = y from hy hp, ← show z = y from hy ⟨hze, hzL⟩]
    exact hzS
  · by_cases hyC : y ∈ C
    · -- half edge with `C`-end `y`; `Λ` is met only at `x`
      have hx := h.edgeArc_inter_interiorPart hl.symm hyC
      intro p hp
      rw [show p = x from hx hp, ← show z = x from hx ⟨hze, hzL⟩]
      exact hzS
    · -- an interior edge: connected, so it lies in one of the two pieces
      have hxD : x ∈ D := h.vertex_mem hl.left_mem hxC
      have hyD : y ∈ D := h.vertex_mem hl.right_mem hyC
      have heD : edgeArc drawing e ⊆ D := h.edgeArc_subset_of_ends hl hnb hxD hyD
      have heL : edgeArc drawing e ⊆ interiorPart G drawing D :=
        fun p hp => Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, heD⟩, hp⟩)
      have hconn : IsPreconnected (edgeArc drawing e) :=
        ((h.isDrawing.edge_isArcBetween hl).isArc.isConnected).2
      have hsub : edgeArc drawing e ⊆ S := by
        by_contra hcon
        obtain ⟨w, hwe, hwS⟩ := not_subset.1 hcon
        have hwS' : w ∈ S' := by
          have := heL hwe
          rw [← hunion] at this
          exact this.resolve_left hwS
        have := isPreconnected_closed_iff.1 hconn S S' hSc hS'c
          (fun p hp => by rw [← hunion] at heL; exact heL hp) ⟨z, hze, hzS⟩ ⟨w, hwe, hwS'⟩
        obtain ⟨v, -, hv⟩ := this
        rw [hinter] at hv
        exact hv
      exact fun p hp => hsub hp.1

include hcase in
/-- **Case 2, the connectedness of `Λ`.** *For each component `L` of `|Λ|`, the union of `L`
with all half-open edges attached to vertices of `L` is both open and closed in `X`; these sets
partition `X`. Connectedness of `X` therefore implies that `|Λ|` is connected.* -/
theorem isPreconnected_interiorPart [G.Finite] (h : IsStageOn G drawing C D) :
    IsPreconnected (interiorPart G drawing D) := by
  classical
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcov hmt hmt'
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  set S : Set Plane := interiorPart G drawing D ∩ t with hSdef
  set S' : Set Plane := interiorPart G drawing D ∩ t' with hS'def
  have hSc : IsClosed S := (isClosed_interiorPart h.isDrawing).inter ht
  have hS'c : IsClosed S' := (isClosed_interiorPart h.isDrawing).inter ht'
  have hunion : S ∪ S' = interiorPart G drawing D := by
    refine subset_antisymm (fun p hp => hp.elim (fun h' => h'.1) (fun h' => h'.1)) ?_
    intro p hp
    rcases hcov hp with h' | h'
    · exact Or.inl ⟨hp, h'⟩
    · exact Or.inr ⟨hp, h'⟩
  have hinter : S ∩ S' = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro p ⟨⟨hp, hpt⟩, -, hpt'⟩
    rw [eq_empty_iff_forall_notMem] at hempty
    exact hempty p ⟨hp, hpt, hpt'⟩
  have hSsub : S ⊆ interiorPart G drawing D := fun p hp => hp.1
  have hS'sub : S' ⊆ interiorPart G drawing D := fun p hp => hp.1
  -- The two attached pieces are closed, cover `X`, and meet it in disjoint sets.
  have hsel : ∀ R R' : Set Plane, IsClosed R → IsClosed R' → R ∪ R' = interiorPart G drawing D →
      R ∩ R' = ∅ → ∀ e ∈ E(G), (edgeArc drawing e ∩ R).Nonempty →
      edgeArc drawing e ∩ interiorPart G drawing D ⊆ R :=
    fun R R' hR hR' hu hi e he hm =>
      h.edgeArc_inter_interiorPart_subset hR hR' hu hi he hm
  have hSsel := hsel S S' hSc hS'c hunion hinter
  have hS'sel := hsel S' S hS'c hSc (by rw [union_comm]; exact hunion)
    (by rw [inter_comm]; exact hinter)
  -- `X` is covered by the two attached pieces.
  have hcovX : pointSet G drawing \ C ⊆
      attachEdges G drawing S ∪ attachEdges G drawing S' := by
    rintro p hp
    have hpD : p ∈ D := h.pointSet_diff_subset hp
    rcases hp.1 with hv | hpe
    · have : p ∈ interiorPart G drawing D := Or.inl ⟨hv, hpD⟩
      rw [← hunion] at this
      exact this.elim (fun h' => Or.inl (subset_attachEdges h'))
        (fun h' => Or.inr (subset_attachEdges h'))
    · obtain ⟨e, heE, hpe⟩ := mem_iUnion₂.1 hpe
      obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heE
      have hnb : Nonboundary drawing C e := fun hsub => h.notMem_of_mem_curve (hsub hpe) hpD
      -- Locate an end of `e` inside `Λ`; the edge follows it.
      have hend : ∃ w, w ∈ edgeArc drawing e ∧ w ∈ interiorPart G drawing D := by
        by_cases hxC : x ∈ C
        · have hyC : y ∉ C := hcase hl hnb hxC
          exact ⟨y, h.right_mem_edgeArc hl, Or.inl ⟨hl.right_mem, h.vertex_mem hl.right_mem hyC⟩⟩
        · exact ⟨x, h.left_mem_edgeArc hl, Or.inl ⟨hl.left_mem, h.vertex_mem hl.left_mem hxC⟩⟩
      obtain ⟨w, hwe, hwL⟩ := hend
      rw [← hunion] at hwL
      rcases hwL with hwS | hwS
      · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, ⟨w, hwe, hwS⟩⟩, hpe⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, ⟨w, hwe, hwS⟩⟩, hpe⟩))
  -- and meets the two of them in disjoint sets.
  have hdisjX : (pointSet G drawing \ C) ∩
      (attachEdges G drawing S ∩ attachEdges G drawing S') = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro p ⟨hp, hpT, hpT'⟩
    have hpD : p ∈ D := h.pointSet_diff_subset hp
    -- In every case `p` ends up in `Λ`, and then in both `S` and `S'`.
    have hkey : ∀ R R' : Set Plane, R ⊆ interiorPart G drawing D →
        (∀ e ∈ E(G), (edgeArc drawing e ∩ R).Nonempty →
          edgeArc drawing e ∩ interiorPart G drawing D ⊆ R) →
        p ∈ attachEdges G drawing R → p ∈ attachEdges G drawing R' →
        p ∈ interiorPart G drawing D → p ∈ R := by
      rintro R R' hRsub hRsel (hpR | hpR) - hpL
      · exact hpR
      · obtain ⟨e, ⟨heE, hme⟩, hpe⟩ := mem_iUnion₂.1 hpR
        exact hRsel e heE hme ⟨hpe, hpL⟩
    have hpL : p ∈ interiorPart G drawing D := by
      rcases hpT with hpS | hpe
      · exact hSsub hpS
      · obtain ⟨e, ⟨heE, hme⟩, hpe⟩ := mem_iUnion₂.1 hpe
        rcases hpT' with hpS' | hpe'
        · exact hS'sub hpS'
        · obtain ⟨f, ⟨hfE, hmf⟩, hpf⟩ := mem_iUnion₂.1 hpe'
          by_cases hef : e = f
          · -- the same edge meets both pieces, so the two pieces already meet
            obtain ⟨v, hve, hvS⟩ := hme
            have hvL : v ∈ interiorPart G drawing D := hSsub hvS
            have := hS'sel f hfE hmf ⟨hef ▸ hve, hvL⟩
            rw [eq_empty_iff_forall_notMem] at hinter
            exact absurd ⟨hvS, this⟩ (hinter v)
          · have : p ∈ V(G) := h.isDrawing.arcs_meet_at_vertex heE hfE hef hpe hpf
            exact Or.inl ⟨this, hpD⟩
    have h1 := hkey S S' hSsub hSsel hpT hpT' hpL
    have h2 := hkey S' S hS'sub hS'sel hpT' hpT hpL
    rw [eq_empty_iff_forall_notMem] at hinter
    exact hinter p ⟨h1, h2⟩
  obtain ⟨p, hpL, hpt⟩ := hmt
  obtain ⟨q, hqL, hqt'⟩ := hmt'
  have hne1 : ((pointSet G drawing \ C) ∩ attachEdges G drawing S).Nonempty :=
    ⟨p, ⟨interiorPart_subset_pointSet hpL, h.notMem_curve (interiorPart_subset hpL)⟩,
      subset_attachEdges ⟨hpL, hpt⟩⟩
  have hne2 : ((pointSet G drawing \ C) ∩ attachEdges G drawing S').Nonempty :=
    ⟨q, ⟨interiorPart_subset_pointSet hqL, h.notMem_curve (interiorPart_subset hqL)⟩,
      subset_attachEdges ⟨hqL, hqt'⟩⟩
  have hcon := isPreconnected_closed_iff.1 h.isConnected_diff.2 _ _
    (isClosed_attachEdges h.isDrawing hSc) (isClosed_attachEdges h.isDrawing hS'c)
    hcovX hne1 hne2
  rw [hdisjX] at hcon
  exact hcon.ne_empty rfl

/-! ### `lem:skeleton-crosscuts` -/

/-- **`lem:skeleton-crosscuts`.** Two distinct points of the outer boundary, each incident with
a nonboundary edge of the stage, are joined by a polygonal crosscut lying in the stage's
skeleton: a simple polygonal arc between them meeting `C` only at its two ends.

In case 1 the crosscut is a single edge; in case 2 it is extracted from
`Y = e_a ∪ |Λ| ∪ e_b` by `lem:finite-polygonal-union`
(`Schoenflies.exists_crosscut_arc_of_biUnion_finite`). -/
theorem exists_crosscut [G.Finite] (h : IsStageOn G drawing C D) {a b : Plane}
    (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (ha : ∃ e, G.Inc e a ∧ Nonboundary drawing C e)
    (hb : ∃ e, G.Inc e b ∧ Nonboundary drawing C e) :
    ∃ P ⊆ pointSet G drawing, IsPolygonal P ∧ IsArcBetween P a b ∧
      P ∩ C = {a, b} ∧ P \ {a, b} ⊆ D := by
  classical
  by_cases hbig : ∃ (e : β) (x y : Plane),
      G.IsLink e x y ∧ Nonboundary drawing C e ∧ x ∈ C ∧ y ∈ C
  · -- Case 1: the single nonboundary edge is itself the crosscut.
    obtain ⟨e, x, y, hl, hnb, hx, hy⟩ := hbig
    have hlab : G.IsLink e a b := h.isLink_of_ends_mem hl hnb hx hy hab ha hb
    refine ⟨edgeArc drawing e, edgeArc_subset_pointSet hlab.edge_mem,
      h.polygonal hlab.edge_mem hnb, h.isDrawing.edge_isArcBetween hlab, ?_, ?_⟩
    · refine subset_antisymm (h.edgeArc_inter_curve hlab hnb) ?_
      rintro p (rfl | rfl)
      · exact ⟨h.left_mem_edgeArc hlab, haC⟩
      · exact ⟨h.right_mem_edgeArc hlab, hbC⟩
    · rcases h.edge_split hlab with hc | hd
      · exact absurd hc hnb
      · exact hd
  · -- Case 2: extract the crosscut from `Y = e_a ∪ |Λ| ∪ e_b`.
    have hcase : ∀ ⦃e : β⦄ ⦃x y : Plane⦄, G.IsLink e x y → Nonboundary drawing C e →
        x ∈ C → y ∉ C := fun e x y hl hnb hx hy => hbig ⟨e, x, y, hl, hnb, hx, hy⟩
    obtain ⟨ea, ⟨ya, hla⟩, hanb⟩ := ha
    obtain ⟨eb, ⟨yb, hlb⟩, hbnb⟩ := hb
    have hyaD : ya ∈ D := h.vertex_mem hla.right_mem (hcase hla hanb haC)
    have hybD : yb ∈ D := h.vertex_mem hlb.right_mem (hcase hlb hbnb hbC)
    have hyaL : ya ∈ interiorPart G drawing D := Or.inl ⟨hla.right_mem, hyaD⟩
    have hybL : yb ∈ interiorPart G drawing D := Or.inl ⟨hlb.right_mem, hybD⟩
    have hLconn : IsConnected (interiorPart G drawing D) :=
      ⟨⟨ya, hyaL⟩, h.isPreconnected_interiorPart hcase⟩
    set EE : Set β := {e | e ∈ E(G) ∧ (edgeArc drawing e ⊆ D ∨ e = ea ∨ e = eb)} with hEEdef
    set Y : Set Plane := (V(G) ∩ D) ∪ ⋃ e ∈ EE, edgeArc drawing e with hYdef
    have hbi : (⋃ i ∈ (Sum.inl '' (V(G) ∩ D) ∪ Sum.inr '' EE : Set (Plane ⊕ β)),
        Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing) i) = Y := by
      rw [hYdef, biUnion_union, biUnion_image, biUnion_image]
      simp only [Sum.elim_inl, Sum.elim_inr, biUnion_of_singleton]
    -- `Y` is the blueprint's `e_a ∪ |Λ| ∪ e_b`, bracketed so that each step meets the previous.
    have hYeq : Y = (interiorPart G drawing D ∪ edgeArc drawing ea) ∪ edgeArc drawing eb := by
      refine subset_antisymm ?_ ?_
      · rintro p (hp | hp)
        · exact Or.inl (Or.inl (Or.inl hp))
        · obtain ⟨e, ⟨heE, hcond⟩, hpe⟩ := mem_iUnion₂.1 hp
          rcases hcond with hD | rfl | rfl
          · exact Or.inl (Or.inl (Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, hD⟩, hpe⟩)))
          · exact Or.inl (Or.inr hpe)
          · exact Or.inr hpe
      · rintro p ((hp | hp) | hp)
        · rcases hp with hp | hp
          · exact Or.inl hp
          · obtain ⟨e, ⟨heE, hD⟩, hpe⟩ := mem_iUnion₂.1 hp
            exact Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, Or.inl hD⟩, hpe⟩)
        · exact Or.inr (mem_iUnion₂.2 ⟨ea, ⟨hla.edge_mem, Or.inr (Or.inl rfl)⟩, hp⟩)
        · exact Or.inr (mem_iUnion₂.2 ⟨eb, ⟨hlb.edge_mem, Or.inr (Or.inr rfl)⟩, hp⟩)
    have hYconn : IsPreconnected Y := by
      rw [hYeq]
      refine (IsConnected.union ⟨yb, Or.inl hybL, h.right_mem_edgeArc hlb⟩
        (IsConnected.union ⟨ya, hyaL, h.right_mem_edgeArc hla⟩ hLconn
          (h.isDrawing.edge_isArcBetween hla).isArc.isConnected)
        (h.isDrawing.edge_isArcBetween hlb).isArc.isConnected).2
    have hYpoint : Y ⊆ pointSet G drawing := by
      rintro p (⟨hp, -⟩ | hp)
      · exact Or.inl hp
      · obtain ⟨e, ⟨heE, -⟩, hpe⟩ := mem_iUnion₂.1 hp
        exact edgeArc_subset_pointSet heE hpe
    have haY : a ∈ Y := hYeq ▸ Or.inl (Or.inr (h.left_mem_edgeArc hla))
    have hbY : b ∈ Y := hYeq ▸ Or.inr (h.left_mem_edgeArc hlb)
    have hYcurve : Y ∩ C ⊆ {a, b} := by
      rintro p ⟨hpY, hpC⟩
      rw [hYeq] at hpY
      rcases hpY with (hp | hp) | hp
      · exact absurd hpC (h.notMem_curve (interiorPart_subset hp))
      · rcases h.edgeArc_inter_curve hla hanb ⟨hp, hpC⟩ with h1 | h1
        · exact Or.inl h1
        · exact absurd (h1 ▸ hpC) (h.notMem_curve hyaD)
      · rcases h.edgeArc_inter_curve hlb hbnb ⟨hp, hpC⟩ with h1 | h1
        · exact Or.inr h1
        · exact absurd (h1 ▸ hpC) (h.notMem_curve hybD)
    -- Every edge of `EE` is nonboundary: one lying in `D` cannot lie in `C`, and `ea`, `eb`
    -- were chosen nonboundary. This is what makes `polygonal` applicable to all of them.
    have hEEnb : ∀ e ∈ EE, Nonboundary drawing C e := by
      rintro e ⟨heG, hD | rfl | rfl⟩
      · intro hC
        obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heG
        exact (h.disjoint.ne_of_mem (hC (h.left_mem_edgeArc hl)) (hD (h.left_mem_edgeArc hl))) rfl
      · exact hanb
      · exact hbnb
    have hfin : (Sum.inl '' (V(G) ∩ D) ∪ Sum.inr '' EE : Set (Plane ⊕ β)).Finite :=
      (((Graph.finite_vertexSet (G := G)).inter_of_left D).image _).union
        (((Graph.finite_edgeSet (G := G)).subset fun e he => he.1).image _)
    have hApoly : ∀ i ∈ (Sum.inl '' (V(G) ∩ D) ∪ Sum.inr '' EE : Set (Plane ⊕ β)),
        IsPolygonal (Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing) i) := by
      rintro (v | e) hi
      · exact ⟨[v], rfl⟩
      · have he : e ∈ EE := by
          rcases hi with ⟨w, -, hw⟩ | ⟨w, hw, hw'⟩
          · exact absurd hw (by simp)
          · exact (Sum.inr_injective hw') ▸ hw
        exact h.polygonal he.1 (hEEnb e he)
    obtain ⟨P, hPsub, hPpoly, hParc, hPcut, hPD⟩ :=
      exists_crosscut_arc_of_biUnion_finite (ι := Plane ⊕ β)
        (s := Sum.inl '' (V(G) ∩ D) ∪ Sum.inr '' EE)
        (A := Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing))
        (D := D) hfin hApoly (by rw [hbi]; exact hYconn) hab haC hbC
        (by rw [hbi]; exact haY) (by rw [hbi]; exact hbY)
        (by rw [hbi]; exact hYcurve)
        (by rw [hbi]; exact fun p hp => h.pointSet_diff_subset ⟨hYpoint hp.1, hp.2⟩)
    rw [hbi] at hPsub
    exact ⟨P, hPsub.trans hYpoint, hPpoly, hParc, hPcut, hPD⟩

end IsStageOn

end Graph
