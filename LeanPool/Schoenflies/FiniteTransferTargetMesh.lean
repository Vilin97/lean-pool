/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.FiniteTransferTarget
public import LeanPool.Schoenflies.SquareMeshClosed

/-!
# Anchored square meshes supply the boundary anchors for reverse finite transfer

`Schoenflies.TargetBoundaryAnchored` is the fixed geometric input isolated from finite-transfer
direction (b): every nonouter target edge ending on the model curve must end at the image of a
strongly accessible source anchor.

The anchored square mesh was built to have exactly this property.  Its clause 4,
`Schoenflies.squareMesh_inner_edge_at_fresh`, says that every mesh edge which meets the model
curve without lying in it meets the curve at one of the prescribed fresh points.  Thus, if the
fresh list consists of target images of strongly accessible source anchors, the whole boundary
condition follows with no ear-order argument.

## Blueprint

* `Schoenflies.targetBoundaryAnchored_squareMesh` — anchored-square-mesh clause 4 discharges the
  strong-accessibility input of reverse finite transfer.
* `Schoenflies.targetEarFreshCombinatorics_squareMesh_of_outerIncidenceAtMostTwo` — mesh
  uniqueness and the local two-branch property of the generated outer cycle discharge the
  evolving fresh-incidence input.
* `Schoenflies.targetEarFreshCombinatorics_squareMesh_of_outerCycle` — the preceding local
  property follows from one simple-cycle check on the base structure.
* `Schoenflies.isSourceExtension_relabelledSquareMesh_closedSquare` — edge relabelling and all
  fixed mesh clauses reduce the extension interface to the three actual subdivision statements.
* `Schoenflies.finite_transfer_toward_source_relabelledSquareMesh_of_outerCycle` — reverse
  transfer over any infinite abstract cell-name type.
* `Schoenflies.finite_transfer_toward_source_squareMesh` — direction (b) for an anchored square
  mesh, reduced only to the evolving fresh-incidence combinatorics.
* `Schoenflies.finite_transfer_toward_source_squareMesh_of_outerIncidenceAtMostTwo` — the same
  conclusion reduced to propagation of one static outer-cycle invariant.
-/

@[expose] public section

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {S₀ : CellStructure Piece} {srcOuter srcDom tgtDom : Set Plane}

/-- At a point of the model curve, two nonouter square-mesh edges cannot both be incident.
Clause 4 first recognizes the point as fresh from either edge, then its uniqueness half
identifies the two pieces. -/
theorem squareMesh_nonouter_incident_eq
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) {z : Plane} (hz : z ∈ modelCurve) {P Q : Piece}
    (hP : P ∈ E(squareMesh delta fresh anchors))
    (hQ : Q ∈ E(squareMesh delta fresh anchors))
    (hPinc : (squareMesh delta fresh anchors).Inc P z)
    (hQinc : (squareMesh delta fresh anchors).Inc Q z)
    (hPnot : ¬ edgeArc segmentDrawing P ⊆ modelCurve)
    (hQnot : ¬ edgeArc segmentDrawing Q ⊆ modelCurve) :
    P = Q := by
  have hdraw := squareMesh_isDrawing hfresh delta anchors
  have endpoint_data : ∀ {R : Piece}, R ∈ E(squareMesh delta fresh anchors) →
      (squareMesh delta fresh anchors).Inc R z →
      ¬ edgeArc segmentDrawing R ⊆ modelCurve →
      R ∈ E(squareMesh delta fresh anchors) ∧
        (z = R.1 ∨ z = R.2) ∧ ¬ R.seg ⊆ modelCurve ∧ z ∈ fresh := by
    intro R hR hRinc hRnot
    have hzArc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hRinc
    have hzSeg : z ∈ R.seg := by
      rwa [edgeArc_segmentDrawing] at hzArc
    have hmeet : (R.seg ∩ modelCurve).Nonempty := ⟨z, hzSeg, hz⟩
    have hRnotSeg : ¬ R.seg ⊆ modelCurve := by
      simpa only [edgeArc_segmentDrawing] using hRnot
    obtain ⟨w, hwFresh, hinter, hwEnd, -⟩ :=
      squareMesh_inner_edge_at_fresh hfresh delta hR hmeet hRnotSeg
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hinter ▸ ⟨hzSeg, hz⟩
      simpa only [Set.mem_singleton_iff] using this
    exact ⟨hR, hzw ▸ hwEnd, hRnotSeg, hzw ▸ hwFresh⟩
  have hPd := endpoint_data hP hPinc hPnot
  have hQd := endpoint_data hQ hQinc hQnot
  obtain ⟨R, hR, huniq⟩ :=
    squareMesh_unique_inner_edge hfresh delta anchors hPd.2.2.2
  exact (huniq P ⟨hPd.1, hPd.2.1, hPd.2.2.1⟩).trans
    (huniq Q ⟨hQd.1, hQd.2.1, hQd.2.2.1⟩).symm

/-- The name-independent form of square-mesh clause 4: at a point of the model curve there is
at most one incident mesh edge which is not contained in the curve. -/
theorem nonouterIncidenceUniqueAtBoundary_squareMesh
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) :
    NonouterIncidenceUniqueAtBoundary
      (squareMesh delta fresh anchors) segmentDrawing modelCurve := by
  intro z P Q hz hP hQ hPinc hQinc hPnot hQnot
  exact squareMesh_nonouter_incident_eq hfresh delta hz hP hQ hPinc hQinc hPnot hQnot

/-- The edges of any finite graph can be injectively renamed into an infinite type while
avoiding a prescribed finite set of names. -/
theorem exists_finiteGraph_edgeRelabeling_avoiding
    {β : Type*} (γ : Type*) [Infinite γ] (H : Graph Plane β) [H.Finite]
    (used : Set γ) (hused : used.Finite) :
    ∃ name : β → γ, InjOn name E(H) ∧ ∀ e ∈ E(H), name e ∉ used := by
  classical
  obtain ⟨freshName, hfreshName, havoid⟩ :=
    exists_injective_avoiding used hused E(H)
  let fallback : γ := Classical.choice (inferInstance : Nonempty γ)
  let name : β → γ := fun e =>
    if he : e ∈ E(H) then freshName ⟨e, he⟩ else fallback
  refine ⟨name, ?_, ?_⟩
  · intro e he g hg heg
    have hnames : freshName (⟨e, he⟩ : E(H)) = freshName ⟨g, hg⟩ := by
      dsimp only [name] at heg
      rw [dite_eq_left he, dite_eq_left hg] at heg
      exact heg
    exact congrArg Subtype.val (hfreshName hnames)
  · intro e he
    dsimp only [name]
    rw [dite_eq_left he]
    exact havoid (⟨e, he⟩ : E(H))

/-- A finite square mesh can have all of its edges injectively renamed into any infinite cell
name type, avoiding any prescribed finite set of names. -/
theorem exists_squareMesh_edgeRelabeling_avoiding (γ : Type*) [Infinite γ]
    (delta : ℝ) (fresh anchors : List Plane) (used : Set γ) (hused : used.Finite) :
    ∃ name : Piece → γ, InjOn name E(squareMesh delta fresh anchors) ∧
      ∀ e ∈ E(squareMesh delta fresh anchors), name e ∉ used :=
  exists_finiteGraph_edgeRelabeling_avoiding γ (squareMesh delta fresh anchors) used hused

/-- A relabelled square mesh is finite. -/
theorem squareMesh_relabelEdges_finite {γ : Type*}
    (delta : ℝ) (fresh anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(squareMesh delta fresh anchors)) :
    ((squareMesh delta fresh anchors).relabelEdges name hname).Finite :=
  Graph.Finite.relabelEdges hname

/-- The straight-line square-mesh drawing transports to the new edge names. -/
theorem squareMesh_relabelEdges_isDrawing {γ : Type*}
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (name : Piece → γ)
    (hname : InjOn name E(squareMesh delta fresh anchors)) :
    Graph.IsDrawing ((squareMesh delta fresh anchors).relabelEdges name hname)
      ((squareMesh delta fresh anchors).relabelDrawing name segmentDrawing) :=
  (squareMesh_isDrawing hfresh delta anchors).relabelEdges hname

/-- Relabelling does not change the geometric carrier of the square mesh. -/
theorem squareMesh_pointSet_relabelEdges {γ : Type*}
    (delta : ℝ) (fresh anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(squareMesh delta fresh anchors)) :
    Graph.pointSet ((squareMesh delta fresh anchors).relabelEdges name hname)
        ((squareMesh delta fresh anchors).relabelDrawing name segmentDrawing) =
      Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing :=
  Graph.pointSet_relabelEdges hname

/-- The relabelled mesh remains 2-connected under the same density hypotheses. -/
theorem squareMesh_relabelEdges_isTwoConnected {γ : Type*}
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (name : Piece → γ) (hname : InjOn name E(squareMesh delta fresh anchors)) :
    ((squareMesh delta fresh anchors).relabelEdges name hname).IsTwoConnected :=
  (squareMesh_isTwoConnected hfresh hdense hdelta anchors).relabelEdges hname

/-- Every square-mesh edge is either contained in the model curve or is a polygonal edge whose
nonvertex points avoid that curve.  A nonouter edge can meet the curve only at its unique fresh
endpoint, and that endpoint is a graph vertex. -/
theorem squareMesh_edge_dichotomy
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) {dom : Set Plane}
    (hpointSet : Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing ⊆ dom) :
    ∀ ⦃f⦄, f ∈ E(squareMesh delta fresh anchors) →
      edgeArc segmentDrawing f ⊆ modelCurve ∨
        (IsPolygonal (edgeArc segmentDrawing f) ∧
          edgeArc segmentDrawing f \ V(squareMesh delta fresh anchors) ⊆
            dom \ modelCurve) := by
  intro f hf
  by_cases hout : edgeArc segmentDrawing f ⊆ modelCurve
  · exact Or.inl hout
  · refine Or.inr ⟨?_, ?_⟩
    · rw [edgeArc_segmentDrawing]
      exact isPolygonal_segment _ _
    · intro x hx
      refine ⟨hpointSet (Graph.edgeArc_subset_pointSet hf hx.1), ?_⟩
      intro hxOuter
      have hxSeg : x ∈ f.seg := by
        rw [← edgeArc_segmentDrawing]
        exact hx.1
      have hnotSeg : ¬ f.seg ⊆ modelCurve := by
        simpa only [edgeArc_segmentDrawing] using hout
      obtain ⟨z, -, hinter, hzEnd, -⟩ :=
        squareMesh_inner_edge_at_fresh hfresh delta hf ⟨x, hxSeg, hxOuter⟩ hnotSeg
      have hxz : x = z := by
        have : x ∈ ({z} : Set Plane) := hinter ▸ ⟨hxSeg, hxOuter⟩
        simpa only [Set.mem_singleton_iff] using this
      obtain ⟨-, -, hlink⟩ := (squareMesh_isDrawing hfresh delta anchors).edge_param hf
      apply hx.2
      rw [hxz]
      rcases hzEnd with rfl | rfl
      · simpa [segmentDrawing] using hlink.left_mem
      · simpa [segmentDrawing] using hlink.right_mem

/-- Assemble the relabelled square mesh as a target extension from hypotheses stated entirely
against the original `Piece`-named mesh.  Finiteness, planarity, 2-connectivity, and every
geometric carrier equality are transported automatically. -/
theorem isSourceExtension_relabelledSquareMesh
    {γ : Type*} {Sbase : CellStructure γ}
    {srcOuter srcDom tgtDom : Set Plane}
    (P : GeneratedPair Sbase srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (name : Piece → γ) (hname : InjOn name E(squareMesh delta fresh anchors))
    (hvertices : V(P.tgt.graph) ⊆ V(squareMesh delta fresh anchors))
    (hskeleton : P.tgt.skeletonSet ⊆
      Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing)
    (hedge : ∀ ⦃e : γ⦄, e ∈ E(P.str.skel) → ∀ ⦃f : Piece⦄,
      f ∈ E(squareMesh delta fresh anchors) →
      (edgeArc segmentDrawing f ∩
        (P.tgt.cell e \ V(squareMesh delta fresh anchors))).Nonempty →
      edgeArc segmentDrawing f ⊆ edgeArc P.tgt.drawing e)
    (hpointSet : Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing ⊆ tgtDom)
    (hdichotomy : ∀ ⦃f⦄, f ∈ E(squareMesh delta fresh anchors) →
      edgeArc segmentDrawing f ⊆ modelCurve ∨
        (IsPolygonal (edgeArc segmentDrawing f) ∧
          edgeArc segmentDrawing f \ V(squareMesh delta fresh anchors) ⊆
            tgtDom \ modelCurve))
    (hconnected : IsConnected
      (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \ modelCurve)) :
    IsSourceExtension P.tgt modelCurve tgtDom
      ((squareMesh delta fresh anchors).relabelEdges name hname)
      ((squareMesh delta fresh anchors).relabelDrawing name segmentDrawing) where
  finite := squareMesh_relabelEdges_finite delta fresh anchors name hname
  isDrawing := squareMesh_relabelEdges_isDrawing hfresh delta name hname
  isTwoConnected := squareMesh_relabelEdges_isTwoConnected hfresh hdense hdelta name hname
  vertexSet_subset := by
    rw [Graph.vertexSet_relabelEdges]
    exact hvertices
  skeletonSet_subset := by
    rw [squareMesh_pointSet_relabelEdges]
    exact hskeleton
  edge_subset := by
    intro e he d hd hmeet
    obtain ⟨f, hf, rfl⟩ := hd
    rw [Graph.edgeArc_relabelDrawing hname hf, Graph.vertexSet_relabelEdges] at hmeet
    rw [Graph.edgeArc_relabelDrawing hname hf]
    exact hedge he hf hmeet
  pointSet_subset := by
    rw [squareMesh_pointSet_relabelEdges]
    exact hpointSet
  edge_dichotomy := by
    intro d hd
    obtain ⟨f, hf, rfl⟩ := hd
    rw [Graph.edgeArc_relabelDrawing hname hf, Graph.vertexSet_relabelEdges]
    exact hdichotomy hf
  isConnected := by
    rw [squareMesh_pointSet_relabelEdges]
    exact hconnected

/-- For the model closed square, the square-mesh construction itself supplies the domain
containment, edge dichotomy, connected complement, planarity, and 2-connectivity.  A caller only
has to say that the current target skeleton is subdivided by the mesh. -/
theorem isSourceExtension_relabelledSquareMesh_closedSquare
    {γ : Type*} {Sbase : CellStructure γ} {srcOuter srcDom : Set Plane}
    (P : GeneratedPair Sbase srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (name : Piece → γ) (hname : InjOn name E(squareMesh delta fresh anchors))
    (hvertices : V(P.tgt.graph) ⊆ V(squareMesh delta fresh anchors))
    (hskeleton : P.tgt.skeletonSet ⊆
      Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing)
    (hedge : ∀ ⦃e : γ⦄, e ∈ E(P.str.skel) → ∀ ⦃f : Piece⦄,
      f ∈ E(squareMesh delta fresh anchors) →
      (edgeArc segmentDrawing f ∩
        (P.tgt.cell e \ V(squareMesh delta fresh anchors))).Nonempty →
      edgeArc segmentDrawing f ⊆ edgeArc P.tgt.drawing e) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((squareMesh delta fresh anchors).relabelEdges name hname)
      ((squareMesh delta fresh anchors).relabelDrawing name segmentDrawing) := by
  have hpoint := squareMesh_pointSet_subset hfresh delta anchors
  obtain ⟨z, hz, -, -, -⟩ := exists_two_distinct_fresh_of_freshDense hdense hdelta
  exact isSourceExtension_relabelledSquareMesh P hfresh hdense hdelta name hname
    hvertices hskeleton hedge hpoint (squareMesh_edge_dichotomy hfresh delta hpoint)
    (squareMesh_isConnected_diff hfresh delta anchors hz)

/-- An anchored square mesh satisfies the fixed boundary-anchor condition for reverse finite
transfer.  The only hypothesis beyond membership in the model curve is the one the stage
constructor records: every prescribed fresh target point pulls back to a strongly accessible
source anchor. -/
theorem targetBoundaryAnchored_squareMesh
    {γ : Type*} {Sbase : CellStructure γ}
    (P : GeneratedPair Sbase srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ) :
    TargetBoundaryAnchored P (squareMesh delta fresh anchors) segmentDrawing := by
  intro f y hf hinc hy hnot
  have hdraw := squareMesh_isDrawing hfresh delta anchors
  obtain ⟨z, hlink⟩ := hinc
  have hyArc : y ∈ edgeArc segmentDrawing f :=
    (hdraw.edge_isArcBetween hlink).left_mem
  have hySeg : y ∈ f.seg := by
    rwa [edgeArc_segmentDrawing] at hyArc
  have hmeet : (f.seg ∩ modelCurve).Nonempty := ⟨y, hySeg, hy⟩
  have hnotSeg : ¬ f.seg ⊆ modelCurve := by
    simpa only [edgeArc_segmentDrawing] using hnot
  obtain ⟨w, hw, hinter, -, -⟩ :=
    squareMesh_inner_edge_at_fresh hfresh delta hf hmeet hnotSeg
  have hyw : y = w := by
    have : y ∈ ({w} : Set Plane) := hinter ▸ ⟨hySeg, hy⟩
    simpa only [Set.mem_singleton_iff] using this
  rw [hyw]
  exact hstrong w hw

/-- A wild-boundary endpoint of the next square-mesh ear is outer-only in the current
abstract skeleton.  If a current nonouter abstract edge reached it, local carrier reflection
would produce a current ambient nonouter edge there.  Clause 4 identifies that edge with the
new ear edge, contradicting that every edge of the ear is absent from the current graph. -/
theorem targetEarEndpointsOuterOnly_squareMesh
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    {B : Graph Plane Piece} {a b : Plane} {D : List Piece} {par : Piece → Piece}
    (hBH : B ≤ squareMesh delta fresh anchors)
    (hpath : (squareMesh delta fresh anchors).IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    {T : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom}
    (hT : IsTargetPartialTransferOf T P B segmentDrawing par)
    (w : TargetSideEarStepData T B (squareMesh delta fresh anchors)
      segmentDrawing a b D) :
    (T.src.pos w.splitData.source ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.source) ∧
    (T.src.pos w.splitData.target ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.target) := by
  exact targetEarEndpointsOuterOnly_of_nonouterIncidenceUnique P hH
    (nonouterIncidenceUniqueAtBoundary_squareMesh hfresh delta)
    hBH hpath hab haB hbB hnew hT w

/-- For a square mesh, the reverse-ear fresh-incidence invariant follows from the static fact
that every generated outer graph is locally at most two-branched.  Clause 4 makes each new
wild-boundary endpoint outer-only; the local two-branch bound then makes its selected face the
unique incident face. -/
theorem targetEarFreshCombinatorics_squareMesh_of_outerIncidenceAtMostTwo
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (htwo : ∀ (S : CellStructure Piece), GeneratedStructure S₀ S →
      S.OuterIncidenceAtMostTwoEverywhere) :
    TargetEarFreshCombinatorics P (squareMesh delta fresh anchors) segmentDrawing := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  obtain ⟨hsourceOuterOnly, htargetOuterOnly⟩ :=
    targetEarEndpointsOuterOnly_squareMesh P hfresh delta hH hBH hpath hab
      haB hbB hnew hT w
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  have htwoT := htwo T.str T.generated
  constructor
  · intro hx
    have houter : T.str.OuterOnlyAt d.source := hsourceOuterOnly hx
    exact ⟨T.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt d.source_mem_skel houter,
      T.unique_source_face_of_outerOnly d.source_mem_skel d.face_mem hsourceSub
        houter (htwoT d.source)⟩
  · intro hx
    have houter : T.str.OuterOnlyAt d.target := htargetOuterOnly hx
    exact ⟨T.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt d.target_mem_skel houter,
      T.unique_source_face_of_outerOnly d.target_mem_skel d.face_mem htargetSub
        houter (htwoT d.target)⟩

/-- It is enough to verify once, on the base cell structure, that the distinguished outer
edges form a simple cycle.  The two generated-structure constructors preserve that fact. -/
theorem targetEarFreshCombinatorics_squareMesh_of_outerCycle
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (hcycle : S₀.OuterEdgesFormCycle) :
    TargetEarFreshCombinatorics P (squareMesh delta fresh anchors) segmentDrawing :=
  targetEarFreshCombinatorics_squareMesh_of_outerIncidenceAtMostTwo
    P hfresh delta hH fun _ h => h.outerIncidenceAtMostTwoEverywhere hcycle

/-- Reverse finite transfer for an anchored square mesh.  Strong accessibility is completely
discharged from the mesh's fresh-point clause; only carrier freshness and unique current-face
incidence remain for the prescribed ear order. -/
theorem finite_transfer_toward_source_squareMesh
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (hcomb : TargetEarFreshCombinatorics P
      (squareMesh delta fresh anchors) segmentDrawing) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom) (par : Piece → Piece),
      IsTargetTransferOf T P (squareMesh delta fresh anchors) segmentDrawing par :=
  finite_transfer_toward_source_of_boundaryAnchored hH
    (targetBoundaryAnchored_squareMesh P hfresh hstrong delta) hcomb

/-- Reverse finite transfer for an anchored square mesh, reduced to a supplied propagation of
the static local outer-cycle invariant. -/
theorem finite_transfer_toward_source_squareMesh_of_outerIncidenceAtMostTwo
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (htwo : ∀ (S : CellStructure Piece), GeneratedStructure S₀ S →
      S.OuterIncidenceAtMostTwoEverywhere) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom) (par : Piece → Piece),
      IsTargetTransferOf T P (squareMesh delta fresh anchors) segmentDrawing par :=
  finite_transfer_toward_source_squareMesh P hfresh hstrong delta hH
    (targetEarFreshCombinatorics_squareMesh_of_outerIncidenceAtMostTwo
      P hfresh delta hH htwo)

/-- Reverse finite transfer for an anchored square mesh from the natural base invariant: its
distinguished outer edges form a simple cycle. -/
theorem finite_transfer_toward_source_squareMesh_of_outerCycle
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom) (par : Piece → Piece),
      IsTargetTransferOf T P (squareMesh delta fresh anchors) segmentDrawing par :=
  finite_transfer_toward_source_squareMesh P hfresh hstrong delta hH
    (targetEarFreshCombinatorics_squareMesh_of_outerCycle P hfresh delta hH hcycle)

/-- Reverse finite transfer for a square mesh whose finitely many `Piece` edge labels have been
injectively renamed into the abstract cell-name type.  This is the integration form used by the
`InitialCell`-named initial pair. -/
theorem finite_transfer_toward_source_relabelledSquareMesh_of_outerCycle
    {γ : Type*} [Infinite γ] {Sbase : CellStructure γ}
    (P : GeneratedPair Sbase srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ) (name : Piece → γ)
    (hname : InjOn name E(squareMesh delta fresh anchors))
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      ((squareMesh delta fresh anchors).relabelEdges name hname)
      ((squareMesh delta fresh anchors).relabelDrawing name segmentDrawing))
    (hcycle : Sbase.OuterEdgesFormCycle) :
    ∃ (T : GeneratedPair Sbase srcOuter srcDom modelCurve tgtDom) (par : γ → γ),
      IsTargetTransferOf T P
        ((squareMesh delta fresh anchors).relabelEdges name hname)
        ((squareMesh delta fresh anchors).relabelDrawing name segmentDrawing) par :=
  finite_transfer_toward_source_of_boundaryGeometry hH
    (TargetBoundaryAnchored.relabelEdges
      (targetBoundaryAnchored_squareMesh (anchors := anchors) P hfresh hstrong delta) hname)
    (NonouterIncidenceUniqueAtBoundary.relabelEdges
      (nonouterIncidenceUniqueAtBoundary_squareMesh (anchors := anchors) hfresh delta) hname)
    hcycle

end Schoenflies
