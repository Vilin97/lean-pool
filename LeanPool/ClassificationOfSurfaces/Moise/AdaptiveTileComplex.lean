/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveOpenComplex
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceModel
import LeanPool.ClassificationOfSurfaces.Moise.GraphRefinement
import LeanPool.ClassificationOfSurfaces.Moise.ConeExtension

/-!
# Finite conforming meshes on adaptive open-complex tiles

An adaptive tile is a closed face of an iterated midpoint subdivision, transported to the
original intrinsic realization.  Its faithful subdivision chart followed by
`facePlaneHomeomorph` identifies it with the standard plane triangle.  We mark every vertex of
every touching adaptive tile on its boundary, refine the standard boundary graph at those
marks, and cone that graph to an interior point.  This file packages the resulting honest finite
plane complex for one tile.  The next layer proves that the transported tile complexes agree on
overlaps and takes their locally finite union.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)
variable [K.AdaptiveSafety U]
variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

/-- A transported adaptive tile, as a closed subspace of the original realization. -/
abbrev AdaptiveClosedFace (t : K.AdaptiveFace U) :=
  {p : K.realization // p ∈ K.adaptiveFaceCarrier U t}

theorem levelFaceHomeoSymm_mem_carrier {n : ℕ} (t : K.LevelFace n)
    {p : K.realization} (hp : p ∈ K.levelFaceCarrier t) :
    (K.safeSubdivision n).homeo.symm p ∈
      (K.safeSubdivision n).refined.faceCarrier t.1 := by
  obtain ⟨x, hx, rfl⟩ := hp
  simpa only [(K.safeSubdivision n).homeo.symm_apply_apply] using hx

/-- Remove the faithful subdivision transport from one adaptive tile. -/
noncomputable def adaptiveFaceSourceHomeomorph (t : K.AdaptiveFace U) :
    K.AdaptiveClosedFace U t ≃ₜ
      (K.safeSubdivision t.1).refined.ClosedFace t.2.1 where
  toFun p := ⟨(K.safeSubdivision t.1).homeo.symm p.1,
    K.levelFaceHomeoSymm_mem_carrier t.2.1 p.2⟩
  invFun x := ⟨(K.safeSubdivision t.1).homeo x.1, ⟨x.1, x.2, rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact (K.safeSubdivision t.1).homeo.apply_symm_apply p.1
  right_inv x := by
    apply Subtype.ext
    exact (K.safeSubdivision t.1).homeo.symm_apply_apply x.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (K.safeSubdivision t.1).homeo.symm.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (K.safeSubdivision t.1).homeo.continuous.comp continuous_subtype_val

/-- The canonical standard-plane chart of an adaptive tile. -/
noncomputable def adaptiveFacePlaneHomeomorph (t : K.AdaptiveFace U) :
    K.AdaptiveClosedFace U t ≃ₜ standardTrianglePlaneComplex.support :=
  (K.adaptiveFaceSourceHomeomorph U t).trans
    ((K.safeSubdivision t.1).refined.facePlaneHomeomorph t.2.1)

/-- A point on an adaptive edge pulls back to the corresponding edge of the refined face. -/
theorem homeo_symm_mem_levelFaceEdgeCarrier {n : ℕ} (t : K.LevelFace n)
    (i : ZMod 3) {p : K.realization} (hp : p ∈ K.levelFaceEdgeCarrier t i) :
    (K.safeSubdivision n).homeo.symm p ∈
      (K.safeSubdivision n).refined.faceCarrier
        ((K.safeSubdivision n).refined.faceEdge t i).1 := by
  obtain ⟨x, hx, rfl⟩ := hp
  simpa only [(K.safeSubdivision n).homeo.symm_apply_apply] using hx

/-- The finite type of resolved boundary points of one adaptive tile. -/
abbrev AdaptiveBoundaryVertex (hU : IsOpen U) (t : K.AdaptiveFace U) :=
  {p : K.realization // p ∈ K.boundaryVertices U hU t}

/-- A resolved boundary point in the standard plane chart of its adaptive tile. -/
noncomputable def adaptiveBoundaryPlanePoint (hU : IsOpen U)
    (t : K.AdaptiveFace U) (p : K.AdaptiveBoundaryVertex U hU t) : Plane :=
  K.adaptiveFacePlaneHomeomorph U t
    ⟨p.1, ((K.mem_boundaryVertices_iff U hU t p.1).mp p.2).1⟩

/-- Every resolved boundary mark lies in the standard triangle's one-skeleton. -/
theorem adaptiveBoundaryPlanePoint_mem_standardOneSkeleton (hU : IsOpen U)
    (t : K.AdaptiveFace U) (p : K.AdaptiveBoundaryVertex U hU t) :
    K.adaptiveBoundaryPlanePoint U hU t p ∈
      standardTrianglePlaneComplex.oneSkeleton.support := by
  have hpCarrier : p.1 ∈ K.adaptiveFaceCarrier U t :=
    ((K.mem_boundaryVertices_iff U hU t p.1).mp p.2).1
  have hpNot : p.1 ∉ K.adaptiveFaceRelInterior U t :=
    K.boundaryVertices_not_mem_relInterior U hU t p.2
  obtain ⟨i, hpEdge⟩ :=
    K.exists_levelFaceEdge_of_mem_not_relInterior t.2.1 hpCarrier hpNot
  rw [standardTriangle_oneSkeleton_support]
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [← (K.safeSubdivision t.1).refined.facePlaneHomeomorph_image_edge t.2.1 i]
  let x : (K.safeSubdivision t.1).refined.ClosedFace t.2.1 :=
    ⟨(K.safeSubdivision t.1).homeo.symm p.1,
      K.levelFaceHomeoSymm_mem_carrier t.2.1 hpCarrier⟩
  refine ⟨x, K.homeo_symm_mem_levelFaceEdgeCarrier t.2.1 i hpEdge, ?_⟩
  rfl

/-- The standard boundary graph refined at every touching-tile vertex. -/
noncomputable def adaptiveBoundarySubdivision (hU : IsOpen U)
    (t : K.AdaptiveFace U) : PlaneComplex :=
  standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision
    (K.adaptiveBoundaryPlanePoint U hU t)

theorem adaptiveBoundarySubdivision_support (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveBoundarySubdivision U hU t).support =
      frontier standardTrianglePlaneComplex.support := by
  rw [adaptiveBoundarySubdivision,
    standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_support_eq
      (K.adaptiveBoundaryPlanePoint U hU t)
      standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph,
    standardTriangle_oneSkeleton_support, standardTriangleCircle_carrier,
    standardTrianglePlaneComplex_support]

/-- Remove any arrangement vertices not used by the refined boundary graph. -/
noncomputable def adaptiveBoundaryGraph (hU : IsOpen U)
    (t : K.AdaptiveFace U) : PlaneComplex :=
  (K.adaptiveBoundarySubdivision U hU t).used

theorem adaptiveBoundaryGraph_support (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveBoundaryGraph U hU t).support =
      frontier standardTrianglePlaneComplex.support := by
  rw [adaptiveBoundaryGraph, PlaneComplex.used_support,
    K.adaptiveBoundarySubdivision_support U hU t]

theorem adaptiveBoundaryGraph_isGraph (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    ∀ s ∈ (K.adaptiveBoundaryGraph U hU t).simplexes, s.card ≤ 2 := by
  intro s hs
  let L := K.adaptiveBoundarySubdivision U hU t
  have hsub : L.Subdivides standardTrianglePlaneComplex.oneSkeleton :=
    standardTrianglePlaneComplex.oneSkeleton.markedEdgeSubdivision_subdivides
      (K.adaptiveBoundaryPlanePoint U hU t)
      standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph
  have hsL : s.map L.usedEmbedding ∈ L.simplexes := L.mem_usedSimplexes.mp hs
  obtain ⟨u, hu, hsu⟩ := hsub.2 _ hsL
  have hcard := PlaneComplex.card_le_two_of_cellCarrier_subset_face hsL hu
    (standardTrianglePlaneComplex.oneSkeleton.oneSkeleton_isGraph u hu) hsu
  calc
    s.card = (s.map L.usedEmbedding).card := (Finset.card_map L.usedEmbedding).symm
    _ ≤ 2 := hcard

/-- Exact support on the polygonal frontier rules out isolated used vertices: every boundary
vertex belongs to a two-vertex face. -/
theorem adaptiveBoundaryGraph_vertex_mem_edge (hU : IsOpen U)
    (t : K.AdaptiveFace U) (v : (K.adaptiveBoundaryGraph U hU t).Vertex) :
    ∃ e ∈ (K.adaptiveBoundaryGraph U hU t).simplexes,
      v ∈ e ∧ e.card = 2 := by
  classical
  let G := K.adaptiveBoundaryGraph U hU t
  have hvFace : ({v} : Finset G.Vertex) ∈ G.simplexes :=
    (K.adaptiveBoundarySubdivision U hU t).used_vertex_face v
  have hvCarrier : G.position v ∈ G.cellCarrier ({v} : Finset G.Vertex) := by
    rw [PlaneComplex.cellCarrier]
    exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, rfl⟩
  by_contra hno
  push Not at hno
  let other : Set Plane := ⋃ s : {s : Finset G.Vertex // s ∈ G.simplexes ∧ s ≠ {v}},
    G.cellCarrier s.1
  have hpNot : G.position v ∉ other := by
    intro hp
    obtain ⟨s, hps⟩ := Set.mem_iUnion.mp hp
    have hinter : G.position v ∈ G.cellCarrier (({v} : Finset G.Vertex) ∩ s.1) := by
      change G.position v ∈ convexHull ℝ
        (G.position '' ((({v} : Finset G.Vertex) ∩ s.1 : Finset G.Vertex) : Set G.Vertex))
      rw [← G.face_inter ({v} : Finset G.Vertex) hvFace s.1 s.2.1]
      exact ⟨hvCarrier, hps⟩
    have hvs : v ∈ s.1 := by
      by_contra hvs
      have hempty : ({v} : Finset G.Vertex) ∩ s.1 = ∅ := by
        ext w
        simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty,
          iff_false]
        rintro ⟨rfl, hw⟩
        exact hvs hw
      rw [hempty, PlaneComplex.cellCarrier] at hinter
      simp at hinter
    have hsle := K.adaptiveBoundaryGraph_isGraph U hU t s.1 s.2.1
    have hstwo : s.1.card = 2 := by
      have hsone : 1 ≤ s.1.card := Finset.one_le_card.mpr ⟨v, hvs⟩
      have hsneone : s.1.card ≠ 1 := by
        intro hsone'
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hsone'
        have hva : v = a := Finset.mem_singleton.mp (ha ▸ hvs)
        have hsingle : s.1 = {v} := by simpa only [hva] using ha
        exact s.2.2 hsingle
      omega
    exact hno s.1 s.2.1 hvs hstwo
  have hotherClosed : IsClosed other := by
    apply isClosed_iUnion_of_finite
    intro s
    exact (G.isCompact_cellCarrier s.1).isClosed
  have hpOpen : G.position v ∈ otherᶜ := Set.mem_compl hpNot
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hotherClosed.isOpen_compl
    (G.position v) hpOpen
  have hpSupport : G.position v ∈ G.support := G.cellCarrier_subset_support hvFace hvCarrier
  have hpFrontier : G.position v ∈ frontier standardTrianglePlaneComplex.support := by
    rw [← K.adaptiveBoundaryGraph_support U hU t]
    exact hpSupport
  have hpCircle : G.position v ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardTrianglePlaneComplex_support] using hpFrontier
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpCircle
  change ZMod 3 at i
  let a := standardTriangleVertex ((ZMod.finEquiv 3).symm (i + 1))
  let b := standardTriangleVertex ((ZMod.finEquiv 3).symm i)
  have hab : b ≠ a := by
    apply standardTriangleVertex_injective.ne
    exact (ZMod.finEquiv 3).symm.injective.ne
      ((by decide : ∀ j : ZMod 3, j ≠ j + 1) i)
  let q := if h : G.position v ≠ a then a else b
  have hpq : G.position v ≠ q := by
    dsimp only [q]
    split_ifs with h
    · exact h
    · intro hp
      apply hab
      exact hp.symm.trans (not_ne_iff.mp h)
  have hqSide : q ∈ standardTriangleCircle.edgeSegment i := by
    dsimp only [q, a, b]
    split_ifs
    · exact right_mem_segment ℝ _ _
    · exact left_mem_segment ℝ _ _
  have hpqSide : segment ℝ (G.position v) q ⊆
      standardTriangleCircle.edgeSegment i :=
    (convex_segment _ _).segment_subset hpi hqSide
  obtain ⟨z, hzOpen, hzBall⟩ := exists_mem_openSegment_inter_ball hpq hε
  have hzSide : z ∈ standardTriangleCircle.edgeSegment i :=
    hpqSide (openSegment_subset_segment ℝ _ _ hzOpen)
  have hzFrontier : z ∈ frontier standardTrianglePlaneComplex.support := by
    have hzCircle : z ∈ standardTriangleCircle.carrier :=
      Set.mem_iUnion.mpr ⟨i, hzSide⟩
    rw [standardTriangleCircle_carrier] at hzCircle
    simpa only [standardTrianglePlaneComplex_support] using hzCircle
  have hzSupport : z ∈ G.support := by
    rw [K.adaptiveBoundaryGraph_support U hU t]
    exact hzFrontier
  rw [PlaneComplex.support] at hzSupport
  simp only [Set.mem_iUnion] at hzSupport
  obtain ⟨s, hs, hzs⟩ := hzSupport
  by_cases hsv : s = {v}
  · subst s
    have hzv : z = G.position v := by
      simpa [PlaneComplex.cellCarrier] using hzs
    exact hpq (left_mem_openSegment_iff.mp (hzv ▸ hzOpen))
  · have hzOther : z ∈ other := Set.mem_iUnion.mpr ⟨⟨s, hs, hsv⟩, hzs⟩
    exact (hball hzBall) hzOther

/-- Every simplex of the boundary graph is contained in an edge. -/
theorem adaptiveBoundaryGraph_isPureOne (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    ∀ s ∈ (K.adaptiveBoundaryGraph U hU t).simplexes,
      ∃ e ∈ (K.adaptiveBoundaryGraph U hU t).simplexes,
        s ⊆ e ∧ e.card = 2 := by
  intro s hs
  have hspos : 0 < s.card := Finset.card_pos.mpr
    ((K.adaptiveBoundaryGraph U hU t).nonempty_of_mem s hs)
  have hsle := K.adaptiveBoundaryGraph_isGraph U hU t s hs
  have hscases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hscases with hscard | hscard
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hscard
    obtain ⟨e, he, hve, hecard⟩ :=
      K.adaptiveBoundaryGraph_vertex_mem_edge U hU t v
    exact ⟨e, he, Finset.singleton_subset_iff.mpr hve, hecard⟩
  · exact ⟨s, hs, subset_rfl, hscard⟩

/-- A fixed interior point of the standard triangle, used as every tile's cone vertex. -/
noncomputable def standardAdaptiveConePoint : Plane :=
  Classical.choose standardTrianglePlaneComplex_isTriangle.infinite_interior.nonempty

theorem standardAdaptiveConePoint_mem_interior :
    standardAdaptiveConePoint ∈ interior standardTrianglePlaneComplex.support :=
  Classical.choose_spec standardTrianglePlaneComplex_isTriangle.infinite_interior.nonempty

theorem standardAdaptiveConePoint_not_mem_boundaryGraph_range (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    standardAdaptiveConePoint ∉ Set.range (K.adaptiveBoundaryGraph U hU t).position := by
  rintro ⟨v, hv⟩
  have hvSupport : (K.adaptiveBoundaryGraph U hU t).position v ∈
      (K.adaptiveBoundaryGraph U hU t).support := by
    exact (K.adaptiveBoundaryGraph U hU t).cellCarrier_subset_support
      ((K.adaptiveBoundarySubdivision U hU t).used_vertex_face v)
      (subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, rfl⟩)
  rw [K.adaptiveBoundaryGraph_support U hU t, hv] at hvSupport
  exact (disjoint_interior_frontier (s := standardTrianglePlaneComplex.support)).le_bot
    ⟨standardAdaptiveConePoint_mem_interior, hvSupport⟩

/-- The finite cone triangulation of one adaptive tile in standard plane coordinates. -/
noncomputable def adaptiveTilePlaneComplex (hU : IsOpen U)
    (t : K.AdaptiveFace U) : PlaneComplex :=
  (K.adaptiveBoundaryGraph U hU t).cone
    standardTrianglePlaneComplex.support
    standardTrianglePlaneComplex_isTriangle.convex
    standardAdaptiveConePoint
    standardAdaptiveConePoint_mem_interior
    (K.standardAdaptiveConePoint_not_mem_boundaryGraph_range U hU t)
    (K.adaptiveBoundaryGraph_isGraph U hU t)
    (K.adaptiveBoundaryGraph_support U hU t)

theorem adaptiveTilePlaneComplex_support (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveTilePlaneComplex U hU t).support =
      standardTrianglePlaneComplex.support := by
  apply (K.adaptiveBoundaryGraph U hU t).cone_support_eq
    standardTrianglePlaneComplex.support
    standardTrianglePlaneComplex_isTriangle.convex
    standardTrianglePlaneComplex_isTriangle.isCompact
    standardAdaptiveConePoint
    standardAdaptiveConePoint_mem_interior
    (K.standardAdaptiveConePoint_not_mem_boundaryGraph_range U hU t)
    (K.adaptiveBoundaryGraph_isGraph U hU t)
    (K.adaptiveBoundaryGraph_support U hU t)
    standardTrianglePlaneComplex_isTriangle.frontier_nonempty

/-- Coning a pure boundary graph produces a pure two-dimensional tile complex. -/
theorem adaptiveTilePlaneComplex_isPure2 (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveTilePlaneComplex U hU t).IsPure2 := by
  let G := K.adaptiveBoundaryGraph U hU t
  change ∀ s ∈ G.coneSimplexes,
    ∃ u ∈ G.coneSimplexes, s ⊆ u ∧ u.card = 3
  intro s hs
  obtain ⟨hsne, b, hb, hsb⟩ := G.mem_coneSimplexes_iff.mp hs
  obtain ⟨e, he, hbe, hecard⟩ :=
    K.adaptiveBoundaryGraph_isPureOne U hU t b hb
  let τ : Finset (Option G.Vertex) := insert none (G.liftFace e)
  refine ⟨τ, ?_, ?_, ?_⟩
  · apply G.mem_coneSimplexes_iff.mpr
    exact ⟨⟨none, Finset.mem_insert_self none (G.liftFace e)⟩,
      e, he, subset_rfl⟩
  · intro z hz
    have hzParent := hsb hz
    cases z with
    | none => exact Finset.mem_insert_self none (G.liftFace e)
    | some z =>
        apply Finset.mem_insert_of_mem
        change some z ∈ e.map Function.Embedding.some
        apply Finset.mem_map.mpr
        refine ⟨z, ?_, rfl⟩
        apply hbe
        have : some z ∈ G.liftFace b := by
          simpa only [Option.some.injEq, Finset.mem_insert, Option.some_ne_none,
            false_or] using hzParent
        simpa [PlaneComplex.liftFace] using this
  · have hnone : none ∉ G.liftFace e := by simp [PlaneComplex.liftFace]
    dsimp only [τ]
    calc
      (insert none (G.liftFace e)).card = (G.liftFace e).card + 1 :=
        Finset.card_insert_of_notMem hnone
      _ = e.card + 1 := by simp [PlaneComplex.liftFace]
      _ = 3 := by omega

/-- Identify a tile cone's support with the corresponding adaptive closed face. -/
noncomputable def adaptiveTileSupportHomeomorph (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveTilePlaneComplex U hU t).support ≃ₜ K.AdaptiveClosedFace U t :=
  (Homeomorph.setCongr (K.adaptiveTilePlaneComplex_support U hU t)).trans
    (K.adaptiveFacePlaneHomeomorph U t).symm

/-- Embed a tile cone support into the open subspace. -/
noncomputable def adaptiveTileSupportEmbed (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    (K.adaptiveTilePlaneComplex U hU t).support → U :=
  fun p ↦ ⟨(K.adaptiveTileSupportHomeomorph U hU t p).1,
    K.adaptiveFaceCarrier_subset U t
      (K.adaptiveTileSupportHomeomorph U hU t p).2⟩

theorem isEmbedding_adaptiveTileSupportEmbed (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    _root_.Topology.IsEmbedding (K.adaptiveTileSupportEmbed U hU t) := by
  let e : K.AdaptiveClosedFace U t → U := fun p ↦
    ⟨p.1, K.adaptiveFaceCarrier_subset U t p.2⟩
  have he : _root_.Topology.IsEmbedding e :=
    _root_.Topology.IsEmbedding.subtypeVal.codRestrict U
      (fun p ↦ K.adaptiveFaceCarrier_subset U t p.2)
  unfold adaptiveTileSupportEmbed
  change _root_.Topology.IsEmbedding
    (e ∘ (K.adaptiveTileSupportHomeomorph U hU t))
  exact he.comp (K.adaptiveTileSupportHomeomorph U hU t).isEmbedding

theorem range_adaptiveTileSupportEmbed (hU : IsOpen U)
    (t : K.AdaptiveFace U) :
    Set.range (K.adaptiveTileSupportEmbed U hU t) =
      K.adaptiveFaceCarrierInOpen U t := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, rfl⟩
    exact (K.adaptiveTileSupportHomeomorph U hU t q).2
  · intro p hp
    let q : K.AdaptiveClosedFace U t := ⟨p.1, hp⟩
    let z := (K.adaptiveTileSupportHomeomorph U hU t).symm q
    refine ⟨z, ?_⟩
    change (⟨((K.adaptiveTileSupportHomeomorph U hU t) z).1,
      K.adaptiveFaceCarrier_subset U t
        ((K.adaptiveTileSupportHomeomorph U hU t) z).2⟩ : U) = p
    apply Subtype.ext
    have hzq :
        ((K.adaptiveTileSupportHomeomorph U hU t) z).1 = q.1 := by
      exact congrArg
        (fun x : K.AdaptiveClosedFace U t ↦ x.1)
        ((K.adaptiveTileSupportHomeomorph U hU t).apply_symm_apply q)
    exact hzq

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
