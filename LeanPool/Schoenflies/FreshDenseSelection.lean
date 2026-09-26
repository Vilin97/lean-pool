/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.BoundaryContinuity2
public import LeanPool.Schoenflies.TargetOverlay
public import Mathlib.Topology.Separation.Connected

/-!
# Selecting a finite dense list of fresh boundary anchors

`FreshDense fresh delta` is the order-free condition used by the anchored square mesh: every
connected subset of the model curve avoiding `fresh` has diameter at most `delta / 2`.

A dense set of eligible anchors contains a finite list with this property.  For each pair of
model-curve points at distance at least `delta / 2`, two eligible anchors separate the pair.
The same anchors separate every nearby pair, because the complementary sides of the associated
cut arcs are open.  The far-pair set is compact, so finitely many such neighborhoods cover it.
Any connected set avoiding all selected anchors must therefore have the required diameter.

## Blueprint

* `Schoenflies.exists_finite_freshDense_of_dense` — a dense eligible subset of the model curve
  supplies a finite `FreshDense` list at every positive scale.
* `Schoenflies.TargetSegmentCover.MeshOverlayTransferData` — the complete output of one
  reverse overlay-transfer stage, packaged for the stage recursion.
* `Schoenflies.TargetSegmentCover.nonempty_meshOverlayTransferData_inside` — in the standard
  closed Jordan domain, separation and the outer-cycle invariant construct that stage data.
* `Schoenflies.TargetSegmentCover.MeshOverlayTransferData.diam_targetStar_lt` — the transferred
  target stars have diameter less than twice the selected mesh scale.
-/

public section

open Metric Set Topology
open scoped Graph

namespace Schoenflies

/-- Removing finitely many forbidden points from a relatively dense subset of a Jordan curve
leaves it relatively dense.  The proof works in the curve subtype, which is a nontrivial
connected T₁ space and therefore has no isolated points. -/
theorem IsJordanCurve.subset_closure_sdiff_finite
    {C eligible forbidden : Set Plane} (hC : IsJordanCurve C)
    (heligible : eligible ⊆ C) (hdense : C ⊆ closure eligible)
    (hforbidden : forbidden.Finite) : C ⊆ closure (eligible \ forbidden) := by
  let eligible' : Set C := {x | x.1 ∈ eligible}
  let forbidden' : Set C := {x | x.1 ∈ forbidden}
  have heligibleImage : ((↑) : C → Plane) '' eligible' = eligible := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, heligible hx⟩, hx, rfl⟩
  have heligibleDense : Dense eligible' := by
    rw [Subtype.dense_iff, heligibleImage]
    exact hdense
  have hforbiddenFinite : forbidden'.Finite := by
    apply hforbidden.preimage
    exact Set.injOn_of_injective Subtype.val_injective
  let _ : ConnectedSpace C := Subtype.connectedSpace hC.isConnected
  let _ : Nontrivial C := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hC.exists_ne
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩⟩
  have hcleanDense : Dense (eligible' \ forbidden') :=
    heligibleDense.sdiff_finite hforbiddenFinite
  rw [Subtype.dense_iff] at hcleanDense
  have hcleanImage : ((↑) : C → Plane) '' (eligible' \ forbidden') =
      eligible \ forbidden := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyEligible, hyForbidden⟩, rfl⟩
      exact ⟨hyEligible, hyForbidden⟩
    · rintro ⟨hxEligible, hxForbidden⟩
      exact ⟨⟨x, heligible hxEligible⟩, ⟨hxEligible, hxForbidden⟩, rfl⟩
  rwa [hcleanImage] at hcleanDense

/-- A dense eligible subset of the model curve contains a finite list which separates every
pair of model-curve points at distance more than `delta / 2`. -/
theorem exists_finite_freshDense_of_dense {eligible : Set Plane}
    (heligible : eligible ⊆ modelCurve) (hdense : modelCurve ⊆ closure eligible)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ fresh : List Plane, (∀ z ∈ fresh, z ∈ eligible) ∧ FreshDense fresh delta := by
  classical
  let farPairs : Set (Plane × Plane) :=
    modelCurve ×ˢ modelCurve ∩
      {q | delta / 2 ≤ dist q.1 q.2}
  have hfarClosed : IsClosed {q : Plane × Plane | delta / 2 ≤ dist q.1 q.2} :=
    isClosed_le continuous_const (continuous_fst.dist continuous_snd)
  have hfarCompact : IsCompact farPairs :=
    (isCompact_modelCurve.prod isCompact_modelCurve).inter_right hfarClosed
  have hseparate : ∀ q : farPairs,
      ∃ a ∈ eligible, ∃ b ∈ eligible, ∃ A₁ A₂ : Set Plane,
        a ≠ b ∧ IsCutPair modelCurve a b A₁ A₂ ∧
          q.1.1 ∈ A₁ ∧ q.1.1 ∉ A₂ ∧ q.1.2 ∈ A₂ ∧ q.1.2 ∉ A₁ := by
    intro q
    have hqCurve : q.1.1 ∈ modelCurve ∧ q.1.2 ∈ modelCurve := q.2.1
    have hqne : q.1.1 ≠ q.1.2 := by
      intro h
      have hle := q.2.2
      change delta / 2 ≤ dist q.1.1 q.1.2 at hle
      rw [h, dist_self] at hle
      linarith
    exact exists_separating_anchors isJordanCurve_modelCurve heligible hdense
      hqCurve.1 hqCurve.2 hqne
  choose a haEligible b hbEligible A₁ A₂ hab hcut hxA₁ hxA₂ hyA₂ hyA₁ using hseparate
  let U : farPairs → Set (Plane × Plane) := fun q => (A₂ q)ᶜ ×ˢ (A₁ q)ᶜ
  have hUopen : ∀ q, IsOpen (U q) := by
    intro q
    exact hcut q |>.snd.isArc.isClosed.isOpen_compl.prod
      (hcut q |>.fst.isArc.isClosed.isOpen_compl)
  have hfarCover : farPairs ⊆ ⋃ q, U q := by
    intro q hq
    exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hxA₂ ⟨q, hq⟩, hyA₁ ⟨q, hq⟩⟩
  obtain ⟨indices, hindices⟩ :=
    hfarCompact.elim_finite_subcover U hUopen hfarCover
  let fresh : List Plane := indices.toList.flatMap fun q => [a q, b q]
  refine ⟨fresh, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq, hzq⟩ := List.mem_flatMap.1 hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hzq
    rcases hzq with rfl | rfl
    · exact haEligible q
    · exact hbEligible q
  · intro S hS hSconn x hx y hy
    by_contra hxy
    have hxyFar : delta / 2 ≤ dist x y := le_of_not_ge hxy
    have hpair : (x, y) ∈ farPairs := by
      exact ⟨⟨(hS hx).1, (hS hy).1⟩, hxyFar⟩
    obtain ⟨q, hqIndices, hqU⟩ := Set.mem_iUnion₂.1 (hindices hpair)
    have hqList : q ∈ indices.toList := by simpa using hqIndices
    have haFresh : a q ∈ fresh := by
      apply List.mem_flatMap.2
      exact ⟨q, hqList, by simp⟩
    have hbFresh : b q ∈ fresh := by
      apply List.mem_flatMap.2
      exact ⟨q, hqList, by simp⟩
    have haNotS : a q ∉ S := by
      intro haS
      exact (hS haS).2 haFresh
    have hbNotS : b q ∉ S := by
      intro hbS
      exact (hS hbS).2 hbFresh
    have hScover : S ⊆ (A₂ q)ᶜ ∪ (A₁ q)ᶜ := by
      intro z hzS
      have hzCurve : z ∈ modelCurve := (hS hzS).1
      have hzUnion : z ∈ A₁ q ∪ A₂ q := by
        rw [hcut q |>.union_eq]
        exact hzCurve
      rcases hzUnion with hzA₁ | hzA₂
      · by_cases hzA₂ : z ∈ A₂ q
        · have hzEnds : z ∈ ({a q, b q} : Set Plane) := by
            rw [← hcut q |>.inter_eq]
            exact ⟨hzA₁, hzA₂⟩
          rcases hzEnds with rfl | rfl
          · exact (haNotS hzS).elim
          · exact (hbNotS hzS).elim
        · exact Or.inl hzA₂
      · by_cases hzA₁ : z ∈ A₁ q
        · have hzEnds : z ∈ ({a q, b q} : Set Plane) := by
            rw [← hcut q |>.inter_eq]
            exact ⟨hzA₁, hzA₂⟩
          rcases hzEnds with rfl | rfl
          · exact (haNotS hzS).elim
          · exact (hbNotS hzS).elim
        · exact Or.inr hzA₁
    have hxOpen : x ∈ (A₂ q)ᶜ := hqU.1
    have hyOpen : y ∈ (A₁ q)ᶜ := hqU.2
    obtain ⟨z, hzS, hzA₂, hzA₁⟩ := hSconn
      (A₂ q)ᶜ (A₁ q)ᶜ
      (hcut q |>.snd.isArc.isClosed.isOpen_compl)
      (hcut q |>.fst.isArc.isClosed.isOpen_compl) hScover
      ⟨x, hx, hxOpen⟩ ⟨y, hy, hyOpen⟩
    have hzUnion : z ∈ A₁ q ∪ A₂ q := by
      rw [hcut q |>.union_eq]
      exact (hS hzS).1
    exact hzUnion.elim hzA₁ hzA₂

/-- A finite boundary list is a metric net at scale `delta`.  This explicit consequence is
retained for the boundary-continuity construction; `FreshDense` itself is the order-free
connected-component estimate needed by the target mesh. -/
def FreshNet (fresh : List Plane) (delta : ℝ) : Prop :=
  ∀ x ∈ modelCurve, ∃ z ∈ fresh, dist x z < delta

theorem FreshDense.mono {fresh fresh' : List Plane} {delta : ℝ}
    (h : FreshDense fresh delta) (hsub : ∀ z ∈ fresh, z ∈ fresh') :
    FreshDense fresh' delta := by
  intro A hA hAconn x hx y hy
  apply h A _ hAconn x hx y hy
  intro z hz
  have hz' := hA hz
  exact ⟨hz'.1, fun hzf => hz'.2 (hsub z hzf)⟩

theorem FreshNet.mono {fresh fresh' : List Plane} {delta : ℝ}
    (h : FreshNet fresh delta) (hsub : ∀ z ∈ fresh, z ∈ fresh') :
    FreshNet fresh' delta := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := h x hx
  exact ⟨z, hsub z hz, hzx⟩

/-- A relatively dense eligible subset of the compact model curve supplies a finite metric
net consisting entirely of eligible points. -/
theorem exists_finite_freshNet_of_dense {eligible : Set Plane}
    (hdense : modelCurve ⊆ closure eligible)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ fresh : List Plane, (∀ z ∈ fresh, z ∈ eligible) ∧ FreshNet fresh delta := by
  let U : eligible → Set Plane := fun z => ball (z : Plane) delta
  have hcover : modelCurve ⊆ ⋃ z, U z := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.1 (hdense hx) delta hdelta
    apply Set.mem_iUnion.2
    refine ⟨⟨z, hz⟩, ?_⟩
    exact mem_ball.2 hzx
  obtain ⟨indices, hindices⟩ :=
    isCompact_modelCurve.elim_finite_subcover U (fun _ => isOpen_ball) hcover
  let fresh : List Plane := indices.toList.map Subtype.val
  refine ⟨fresh, ?_, ?_⟩
  · intro z hz
    change z ∈ indices.toList.map Subtype.val at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    exact w.property
  · intro x hx
    obtain ⟨z, hzi, hz⟩ := Set.mem_iUnion₂.1 (hindices hx)
    refine ⟨z, ?_, ?_⟩
    · apply List.mem_map.2
      exact ⟨z, by simpa using hzi, rfl⟩
    · exact mem_ball.1 hz

/-- The two finite selections can be combined without losing either property. -/
theorem exists_finite_freshDenseNet_of_dense {eligible : Set Plane}
    (heligible : eligible ⊆ modelCurve) (hdense : modelCurve ⊆ closure eligible)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ fresh : List Plane, (∀ z ∈ fresh, z ∈ eligible) ∧
      FreshDense fresh delta ∧ FreshNet fresh delta := by
  obtain ⟨dense, hdenseMem, hdenseProp⟩ :=
    exists_finite_freshDense_of_dense heligible hdense hdelta
  obtain ⟨net, hnetMem, hnetProp⟩ :=
    exists_finite_freshNet_of_dense hdense hdelta
  refine ⟨dense ++ net, ?_, hdenseProp.mono ?_, hnetProp.mono ?_⟩
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact hdenseMem z hz
    · exact hnetMem z hz
  · exact fun z hz => List.mem_append_left _ hz
  · exact fun z hz => List.mem_append_right _ hz

/-! ### Fresh lists for a generated target overlay -/

namespace TargetSegmentCover

variable {S₀ : CellStructure γ} {srcOuter srcDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}

/-- Strongly accessible points on the source boundary. -/
def accessibleSourceBoundary
    (_P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) :
    Set Plane :=
  {x | x ∈ srcOuter ∧ StronglyAccessible (srcDom \ srcOuter) x}

/-- Boundary points whose source-side preimages are strongly accessible. -/
def accessibleTargetBoundary
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)) :
    Set Plane :=
  {z | z ∈ modelCurve ∧
    StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)}

/-- Relative density of strongly accessible source-boundary points transports through the
current skeleton homeomorphism to relative density on the model curve. -/
theorem accessibleTargetBoundary_dense_of_source
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    (hsource : srcOuter ⊆ closure (accessibleSourceBoundary P)) :
    modelCurve ⊆ closure (accessibleTargetBoundary P) := by
  intro z hzCurve
  rw [Metric.mem_closure_iff]
  intro epsilon hepsilon
  have hzTgtOuter : z ∈ P.tgt.outerSet := by
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hzCurve
  have hzTgtSkeleton : z ∈ P.tgt.skeletonSet :=
    P.tgt.outerSet_subset_skeletonSet hzTgtOuter
  have hxSrcOuterSet : P.homeo.invFun z ∈ P.src.outerSet := by
    rw [← P.homeo.symm.image_outerSet]
    exact ⟨z, hzTgtOuter, rfl⟩
  have hxSrcOuter : P.homeo.invFun z ∈ srcOuter := by
    exact (Set.ext_iff.mp P.src_isWeaklyAdmissible.outerSet_eq _).mp
      hxSrcOuterSet
  have hxSrcSkeleton : P.homeo.invFun z ∈ P.src.skeletonSet :=
    P.src.outerSet_subset_skeletonSet hxSrcOuterSet
  have hright : P.homeo.toFun (P.homeo.invFun z) = z :=
    P.homeo.rightInvOn hzTgtSkeleton
  obtain ⟨delta, hdelta, hclose⟩ := Metric.continuousWithinAt_iff.1
    (P.homeo.continuousOn_toFun _ hxSrcSkeleton) epsilon hepsilon
  obtain ⟨x, hxAccessible, hxdist⟩ :=
    Metric.mem_closure_iff.1 (hsource hxSrcOuter) delta hdelta
  have hxSrcOuterSet' : x ∈ P.src.outerSet := by
    rw [P.src_isWeaklyAdmissible.outerSet_eq]
    exact hxAccessible.1
  have hxSrcSkeleton' : x ∈ P.src.skeletonSet :=
    P.src.outerSet_subset_skeletonSet hxSrcOuterSet'
  have hxTgtOuter : P.homeo.toFun x ∈ P.tgt.outerSet := by
    rw [← P.homeo.image_outerSet]
    exact ⟨x, hxSrcOuterSet', rfl⟩
  have hxCurve : P.homeo.toFun x ∈ modelCurve := by
    exact (Set.ext_iff.mp P.tgt_isWeaklyAdmissible.outerSet_eq _).mp
      hxTgtOuter
  have hleft : P.homeo.invFun (P.homeo.toFun x) = x :=
    P.homeo.leftInvOn hxSrcSkeleton'
  refine ⟨P.homeo.toFun x, ⟨hxCurve, ?_⟩, ?_⟩
  · rw [hleft]
    exact hxAccessible.2
  · have := hclose hxSrcSkeleton' (by rwa [dist_comm])
    rwa [hright, dist_comm] at this

/-- In the standard generated-pair setting, tangent density on the source region supplies the
density hypothesis needed by finite fresh-list selection. -/
theorem accessibleTargetBoundary_dense_of_region
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    (hsep : IsSeparating srcOuter)
    (hregion : IsRegionOf srcOuter (srcDom \ srcOuter)) :
    modelCurve ⊆ closure (accessibleTargetBoundary P) :=
  accessibleTargetBoundary_dense_of_source P (tangent_dense hsep hregion)

/-- For the closed Jordan domain used by the stage tower, the required source region is
literally `inside srcOuter`, so accessible target-boundary density follows from
separation of the source curve. -/
theorem accessibleTargetBoundary_dense_inside
    {C : Set Plane}
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hsep : IsSeparating C) :
    modelCurve ⊆ closure (accessibleTargetBoundary P) := by
  apply accessibleTargetBoundary_dense_of_region P hsep
  rw [union_inside_sdiff]
  exact IsRegionOf.inside C

/-- If accessible target-boundary points are relatively dense, then at every positive scale
there is a finite dense list of accessible points avoiding all old target vertices and hence
all old nonouter target-edge carriers. -/
theorem exists_clean_freshDense_of_accessibleTargetBoundary_dense
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
    (haccessible : modelCurve ⊆ closure (accessibleTargetBoundary P))
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ fresh : List Plane,
      (∀ z ∈ fresh, z ∈ modelCurve) ∧
      (∀ z ∈ fresh,
        StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)) ∧
      FreshAvoidsTargetNonouterEdges P fresh ∧ FreshDense fresh delta ∧
      FreshNet fresh delta := by
  let _ : Graph.Finite P.tgt.graph :=
    CellStructure.Realization.finite_graph P.tgt
  have haccessibleSubset : accessibleTargetBoundary P ⊆ modelCurve :=
    fun _ hz => hz.1
  have hcleanDense : modelCurve ⊆
      closure (accessibleTargetBoundary P \ V(P.tgt.graph)) :=
    isJordanCurve_modelCurve.subset_closure_sdiff_finite
      haccessibleSubset haccessible (Graph.finite_vertexSet (G := P.tgt.graph))
  obtain ⟨fresh, hfreshClean, hdense, hnet⟩ := exists_finite_freshDenseNet_of_dense
    (Set.sdiff_subset.trans haccessibleSubset) hcleanDense hdelta
  have hfresh : ∀ z ∈ fresh, z ∈ modelCurve := by
    intro z hz
    exact (hfreshClean z hz).1.1
  have hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z) := by
    intro z hz
    exact (hfreshClean z hz).1.2
  have havoidVertices : ∀ z ∈ fresh, z ∉ V(P.tgt.graph) := by
    intro z hz
    exact (hfreshClean z hz).2
  exact ⟨fresh, hfresh, hstrong,
    freshAvoidsTargetNonouterEdges_of_avoids_targetVertices hfresh havoidVertices,
    hdense, hnet⟩

/-- Dense accessible boundary points now suffice for the full overlay reverse transfer.  The
mesh scale, finite clean fresh list, fresh abstract edge names, and transferred generated pair
are all selected internally. -/
theorem exists_finite_transfer_toward_source_meshOverlay_of_accessibleBoundary_dense
    [Infinite γ] (Q : TargetSegmentCover P)
    (haccessible : modelCurve ⊆ closure (accessibleTargetBoundary P))
    (hcycle : S₀.OuterEdgesFormCycle) (anchors : List Plane) :
    ∃ (delta : ℝ) (fresh : List Plane),
      0 < delta ∧ delta < 4 ∧
      (∀ z ∈ fresh, z ∈ modelCurve) ∧
      (∀ z ∈ fresh,
        StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)) ∧
      FreshAvoidsTargetNonouterEdges P fresh ∧ FreshDense fresh delta ∧
      FreshNet fresh delta ∧
      ∃ (name : Piece → γ) (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
          (T : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1))
          (par : γ → γ),
        IsTargetTransferOf T P
          ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
          ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) par := by
  obtain ⟨delta, hdelta, hdelta4, htransfer⟩ :=
    Q.exists_scale_finite_transfer_toward_source_meshOverlay hcycle
  obtain ⟨fresh, hfresh, hstrong, havoid, hdense, hnet⟩ :=
    exists_clean_freshDense_of_accessibleTargetBoundary_dense
      P haccessible hdelta
  obtain ⟨name, hname, T, par, hT⟩ :=
    htransfer fresh anchors hfresh hstrong havoid hdense
  exact ⟨delta, fresh, hdelta, hdelta4, hfresh, hstrong, havoid, hdense, hnet,
    name, hname, T, par, hT⟩

/-- The complete finite data selected by one reverse overlay-transfer stage.  Packaging the
dependent edge relabelling and its transferred generated pair together makes this construction
directly usable by the stage recursion. -/
structure MeshOverlayTransferData (Q : TargetSegmentCover P) (anchors : List Plane) where
  /-- The positive mesh scale selected for this target. -/
  delta : ℝ
  /-- The finite accessible boundary-anchor list. -/
  fresh : List Plane
  delta_pos : 0 < delta
  delta_lt_four : delta < 4
  fresh_mem : ∀ z ∈ fresh, z ∈ modelCurve
  fresh_accessible : ∀ z ∈ fresh,
    StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z)
  fresh_avoids : FreshAvoidsTargetNonouterEdges P fresh
  fresh_dense : FreshDense fresh delta
  /-- The selected points also form an explicit metric net on the target boundary. -/
  fresh_net : FreshNet fresh delta
  /-- Fresh abstract names for all edges of the finite overlay. -/
  name : Piece → γ
  name_inj : InjOn name E(Q.meshOverlay delta fresh anchors)
  /-- The generated pair after reverse transfer. -/
  pair : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)
  /-- The abstract parent map of the transfer. -/
  parent : γ → γ
  transfer : IsTargetTransferOf pair P
    ((Q.meshOverlay delta fresh anchors).relabelEdges name name_inj)
    ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) parent

/-- Dense accessible target-boundary points construct the packaged data for one complete
reverse overlay-transfer stage. -/
theorem nonempty_meshOverlayTransferData_of_accessibleBoundary_dense
    [Infinite γ] (Q : TargetSegmentCover P)
    (haccessible : modelCurve ⊆ closure (accessibleTargetBoundary P))
    (hcycle : S₀.OuterEdgesFormCycle) (anchors : List Plane) :
    Nonempty (MeshOverlayTransferData Q anchors) := by
  obtain ⟨delta, fresh, hdelta, hdelta4, hfresh, hstrong, havoid, hdense, hnet,
      name, hname, T, par, hT⟩ :=
    Q.exists_finite_transfer_toward_source_meshOverlay_of_accessibleBoundary_dense
      haccessible hcycle anchors
  exact ⟨{
    delta := delta
    fresh := fresh
    delta_pos := hdelta
    delta_lt_four := hdelta4
    fresh_mem := hfresh
    fresh_accessible := hstrong
    fresh_avoids := havoid
    fresh_dense := hdense
    fresh_net := hnet
    name := name
    name_inj := hname
    pair := T
    parent := par
    transfer := hT }⟩

/-- **Reverse overlay-transfer stage for a closed Jordan domain.** Tangent
density supplies the accessible anchors, finite deletion avoids the old target vertices, and
compactness selects a finite `FreshDense` list at the internally chosen mesh scale. -/
theorem nonempty_meshOverlayTransferData_inside
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}
    (Q : TargetSegmentCover P) (hsep : IsSeparating C)
    (hcycle : S₀.OuterEdgesFormCycle) (anchors : List Plane) :
    Nonempty (MeshOverlayTransferData Q anchors) :=
  nonempty_meshOverlayTransferData_of_accessibleBoundary_dense Q
    (accessibleTargetBoundary_dense_inside P hsep) hcycle anchors

/-- The packaged reverse-transfer data can be selected below any positive prescribed scale. -/
theorem exists_meshOverlayTransferData_lt_of_accessibleBoundary_dense
    [Infinite γ] (Q : TargetSegmentCover P)
    (haccessible : modelCurve ⊆ closure (accessibleTargetBoundary P))
    (hcycle : S₀.OuterEdgesFormCycle) (anchors : List Plane)
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ w : MeshOverlayTransferData Q anchors, w.delta < bound := by
  obtain ⟨delta, hdelta, hdelta4, hdeltabound, htransfer⟩ :=
    Q.exists_scale_finite_transfer_toward_source_meshOverlay_lt hcycle hbound
  obtain ⟨fresh, hfresh, hstrong, havoid, hdense, hnet⟩ :=
    exists_clean_freshDense_of_accessibleTargetBoundary_dense
      P haccessible hdelta
  obtain ⟨name, hname, T, par, hT⟩ :=
    htransfer fresh anchors hfresh hstrong havoid hdense
  exact ⟨{
    delta := delta
    fresh := fresh
    delta_pos := hdelta
    delta_lt_four := hdelta4
    fresh_mem := hfresh
    fresh_accessible := hstrong
    fresh_avoids := havoid
    fresh_dense := hdense
    fresh_net := hnet
    name := name
    name_inj := hname
    pair := T
    parent := par
    transfer := hT }, hdeltabound⟩

/-- In the standard closed Jordan domain, a reverse-transfer stage exists below every positive
prescribed scale. -/
theorem exists_meshOverlayTransferData_lt_inside
    [Infinite γ] {C : Set Plane}
    {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}
    (Q : TargetSegmentCover P) (hsep : IsSeparating C)
    (hcycle : S₀.OuterEdgesFormCycle) (anchors : List Plane)
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ w : MeshOverlayTransferData Q anchors, w.delta < bound :=
  exists_meshOverlayTransferData_lt_of_accessibleBoundary_dense Q
    (accessibleTargetBoundary_dense_inside P hsep) hcycle anchors hbound

namespace MeshOverlayTransferData

variable {Q : TargetSegmentCover P} {anchors : List Plane}

/-- Every target face created by the reverse overlay transfer has diameter below the selected
mesh scale.  The target cell is connected and misses the new skeleton, hence lies in one bounded
face of the contained square mesh; `squareMesh_face_small` supplies the bound. -/
theorem diam_closure_targetFace_lt (w : MeshOverlayTransferData Q anchors)
    {F : γ} (hF : F ∈ w.pair.str.faces) :
    Metric.diam (closure (w.pair.tgt.cell F)) < w.delta := by
  obtain ⟨z, hz⟩ := w.pair.tgt_isFaceJordan.nonempty hF
  have hzOpen : z ∈ Plane.openSquare 0 1 := by
    have hzInterior := w.pair.tgt_face_subset_interior hF hz
    rwa [closedSquare_sdiff_modelCurve] at hzInterior
  have hmeshSkel :
      Graph.pointSet (squareMesh w.delta w.fresh anchors) segmentDrawing ⊆
        w.pair.tgt.skeletonSet := by
    rw [w.transfer.skeletonSet_eq, Graph.pointSet_relabelEdges]
    exact Q.squareMesh_subset_meshOverlay w.delta w.fresh anchors
  have hcellExterior : w.pair.tgt.cell F ⊆
      Graph.exterior (squareMesh w.delta w.fresh anchors) segmentDrawing := by
    intro x hxCell hxMesh
    exact Set.disjoint_left.1
      (w.pair.tgt.disjoint_cell_skeletonSet w.pair.tgt_isCellDecomposition hF)
      hxCell (hmeshSkel hxMesh)
  have hzExterior :
      z ∈ Graph.exterior (squareMesh w.delta w.fresh anchors) segmentDrawing :=
    hcellExterior hz
  have hcellFace : w.pair.tgt.cell F ⊆
      Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z :=
    (w.pair.tgt_isFaceJordan.isConnected hF).isPreconnected.subset_connectedComponentIn
      hz hcellExterior
  have hfaceCurveCompl :
      Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z ⊆ modelCurveᶜ := by
    intro x hxFace hxCurve
    exact Graph.face_subset_exterior _ _ _ hxFace
      (modelCurve_subset_squareMesh_pointSet w.delta w.fresh anchors hxCurve)
  have hfaceOpen :
      Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z ⊆
        Plane.openSquare 0 1 := by
    have hcomp := (Graph.isConnected_face hzExterior).isPreconnected.subset_connectedComponentIn
      (Graph.mem_face hzExterior) hfaceCurveCompl
    rw [modelCurve_eq_frontier,
      connectedComponentIn_compl_frontier_closedSquare hzOpen] at hcomp
    exact hcomp
  have hfaceBounded : Bornology.IsBounded
      (Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z) :=
    (Plane.isBounded_closedSquare 0 1).subset
      (hfaceOpen.trans (Plane.openSquare_subset_closedSquare 0 1))
  have hsmall := squareMesh_face_small w.fresh_mem w.delta_pos w.fresh_dense
    hzExterior hfaceBounded
  calc
    Metric.diam (closure (w.pair.tgt.cell F)) =
        Metric.diam (w.pair.tgt.cell F) := Metric.diam_closure _
    _ ≤ Metric.diam
        (Graph.face (squareMesh w.delta w.fresh anchors) segmentDrawing z) :=
      Metric.diam_mono hcellFace hfaceBounded
    _ < w.delta := hsmall.2

/-- Consequently every closed target star has diameter less than twice the selected scale. -/
theorem diam_targetStar_lt (w : MeshOverlayTransferData Q anchors)
    {σ : γ} (hσ : σ ∈ w.pair.str.cells) :
    Metric.diam (w.pair.tgt.star σ) < 2 * w.delta :=
  w.pair.tgt_isCellDecomposition.diam_star_lt w.pair.str_combInvariants
    (Plane.isBounded_closedSquare 0 1) hσ
    (fun _ hF _ => w.diam_closure_targetFace_lt hF)

end MeshOverlayTransferData

end TargetSegmentCover

end Schoenflies
