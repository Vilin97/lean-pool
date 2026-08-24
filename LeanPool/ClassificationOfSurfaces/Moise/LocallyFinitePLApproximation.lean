/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteCellwiseExtension

/-!
# Quantitative locally finite PL approximation

This file records the facewise metric control used in Moise Chapter 6, Theorem 3.  It is
deliberately pointwise: on a noncompact open complex no uniform positive tolerance exists, but a
strongly positive tolerance has a positive lower bound on every compact face.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}

/-! ## The original face map and the achievable side-control hypotheses -/

/-- A global vertex lies in a maximal face carrier exactly when it labels that face. -/
theorem vertexPoint_mem_faceCarrier_iff (f : K.Face) (v : K.Vertex) :
    K.vertexPoint v ∈ K.faceCarrier f ↔ v ∈ K.faceVertices f := by
  constructor
  · rintro ⟨x, hx⟩
    by_contra hv
    have hcoords := K.faceMap_eq_iff.mp hx.symm
    have hc := congrFun hcoords v
    rw [K.extendFaceCoordinates_vertex (K.incidentFace v)
      (K.mem_faceVertices_incidentFace v), Pi.single_eq_same,
      extendFaceCoordinates_of_notMem (K.faceVertices f) x hv] at hc
    norm_num at hc
  · intro hv
    exact K.vertexPoint_in_faceCarrier f hv

theorem vertexSupportPoint_mem_faceInSupport_iff (f : K.Face) (v : K.Vertex) :
    (⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩ : K.support) ∈
        faceInSupport (K := K) f ↔ v ∈ K.faceVertices f := by
  rw [K.faceInSupport_eq_preimage]
  exact K.vertexPoint_mem_faceCarrier_iff f v

/-- The original plane embedding, written in the standard coordinates of one face.  Values
outside the standard closed triangle are irrelevant. -/
noncomputable def faceOriginalMap (G : K.PlaneGraphRealization) (f : K.Face)
    (p : Plane) : Plane := by
  classical
  exact if hp : p ∈ standardFaceRegion then
    G.map (faceToSupport (K := K) f
      ((K.facePlaneHomeomorph f).symm ⟨p, hp⟩))
  else 0

@[simp] theorem faceOriginalMap_apply (f : K.Face) (p : standardFaceRegion) :
    faceOriginalMap G f p.1 =
      G.map (faceToSupport (K := K) f
        ((K.facePlaneHomeomorph f).symm p)) := by
  simp [faceOriginalMap, p.2]

theorem continuousOn_faceOriginalMap (f : K.Face) :
    ContinuousOn (faceOriginalMap G f) standardFaceRegion := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert G.isEmbedding.continuous.comp
    ((continuous_faceToSupport (K := K) f).comp
      (K.facePlaneHomeomorph f).symm.continuous) using 1
  funext p
  exact faceOriginalMap_apply (G := G) f p

theorem faceOriginalMap_mem_face_image (f : K.Face) (p : standardFaceRegion) :
    faceOriginalMap G f p.1 ∈ G.map '' faceInSupport (K := K) f := by
  refine ⟨faceToSupport (K := K) f
      ((K.facePlaneHomeomorph f).symm p), Set.mem_range_self _, ?_⟩
  exact (faceOriginalMap_apply (G := G) f p).symm

/-- The replacement graph is close to the original embedding on each face boundary, with a
radius allowed to depend on the face.  This is the quantitative hypothesis actually used in
Moise's side-preservation argument. -/
def FaceBoundariesClose (G : K.PlaneGraphRealization) (r : K.Face → ℝ) : Prop :=
  ∀ (f : K.Face) (q : StandardFaceBoundary),
    dist (G.graphReplacementMap (K.faceBoundaryLift f q))
      (faceOriginalMap G f q.1) < r f

/-- A face-indexed radius separates every nonincident vertex from the original embedded face.
The closed-ball/closed-thickening formulation is exactly what the bounded Tietze extension
argument consumes. -/
def FaceVertexThickeningsSeparated (G : K.PlaneGraphRealization)
    (r : K.Face → ℝ) : Prop :=
  ∀ (f : K.Face) (v : K.Vertex), v ∉ K.faceVertices f →
    Disjoint (Metric.closedBall (G.vertexImage v) (r f))
      (Metric.cthickening (r f) (G.map '' faceInSupport (K := K) f))

/-- The relatively locally finite set of all vertex images not belonging to one face, made
ambiently closed by adjoining the complement of the perturbation region. -/
def outsideVertexImages (G : K.PlaneGraphRealization) (f : K.Face) : Set Plane :=
  (⋃ v : {v : K.Vertex // v ∉ K.faceVertices f}, G.vertexImageCarrier v.1) ∪
    G.regionᶜ

private theorem isClosed_union_compl_of_isClosed_preimage'
    {X : Type*} [TopologicalSpace X] {V A : Set X} (hV : IsOpen V)
    (hA : IsClosed ((↑) ⁻¹' A : Set V)) : IsClosed (A ∪ Vᶜ) := by
  apply isOpen_compl_iff.mp
  have hopen := hV.isOpenEmbedding_subtypeVal.isOpenMap _ hA.isOpen_compl
  convert hopen using 1
  ext x
  constructor
  · intro hx
    have hxV : x ∈ V := by
      by_contra hxV
      exact hx (Or.inr hxV)
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    simpa only [Set.mem_compl_iff, Set.mem_preimage] using
      fun hxA ↦ hx (Or.inl hxA)
  · rintro ⟨y, hy, rfl⟩ h
    rcases h with hA | hV
    · exact hy hA
    · exact hV y.2

theorem isClosed_outsideVertexImages (f : K.Face) :
    IsClosed (outsideVertexImages G f) := by
  apply isClosed_union_compl_of_isClosed_preimage' G.regionOpen
  have hlocal : LocallyFinite
      (fun v : {v : K.Vertex // v ∉ K.faceVertices f} ↦
        G.vertexImageCarrierInRange v.1) :=
    G.locallyFinite_vertexImages.comp_injective
      (g := fun v : {v : K.Vertex // v ∉ K.faceVertices f} ↦ v.1)
      Subtype.val_injective
  have hclosed : IsClosed
      (⋃ v : {v : K.Vertex // v ∉ K.faceVertices f},
        G.vertexImageCarrierInRange v.1) := by
    apply hlocal.isClosed_iUnion
    intro v
    have hvclosed :=
      ((isClosed_singleton : IsClosed ({G.vertexImage v.1} : Set Plane)).preimage
        (continuous_subtype_val : Continuous (Subtype.val : G.region → Plane)))
    convert hvclosed using 1
    ext q
    simp [PlaneGraphRealization.vertexImageCarrierInRange,
      PlaneGraphRealization.vertexImageCarrier]
  convert hclosed using 1
  ext p
  simp only [PlaneGraphRealization.vertexImageCarrierInRange, Set.mem_preimage,
    Set.mem_iUnion, Set.mem_ofPred_eq]

theorem faceImage_disjoint_outsideVertexImages (f : K.Face) :
    Disjoint (G.map '' faceInSupport (K := K) f) (outsideVertexImages G f) := by
  rw [Set.disjoint_left]
  rintro q ⟨p, hpFace, rfl⟩ hqOutside
  rcases hqOutside with hqVertex | hqRegion
  · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hqVertex
    have heq : G.map p = G.vertexImage v.1 := by
      simpa [PlaneGraphRealization.vertexImageCarrier] using hv
    let vp : K.support :=
      ⟨K.vertexPoint v.1, K.vertexPoint_mem_support v.1⟩
    have hpv : p = vp := G.isEmbedding.injective heq
    have hvFace : vp ∈ faceInSupport (K := K) f := hpv ▸ hpFace
    exact v.2 ((K.vertexSupportPoint_mem_faceInSupport_iff f v.1).mp hvFace)
  · exact hqRegion (G.map_mem_region p)

/-- Every face admits one positive radius separating its compact image from all nonincident
vertices at once.  Local finiteness replaces the finite minimum used in the compact theorem. -/
theorem exists_faceVertexSeparationRadius (f : K.Face) :
    ∃ r : ℝ, 0 < r ∧
      ∀ v : K.Vertex, v ∉ K.faceVertices f →
        Disjoint (Metric.closedBall (G.vertexImage v) r)
          (Metric.cthickening r (G.map '' faceInSupport (K := K) f)) := by
  have hcompact : IsCompact (G.map '' faceInSupport (K := K) f) :=
    (isCompact_faceInSupport (K := K) f).image G.isEmbedding.continuous
  obtain ⟨r, hr, hdis⟩ :=
    (faceImage_disjoint_outsideVertexImages (G := G) f).exists_cthickenings hcompact
      (isClosed_outsideVertexImages (G := G) f)
  refine ⟨r, hr, fun v hv ↦ ?_⟩
  apply hdis.symm.mono
  · apply Metric.closedBall_subset_cthickening
    apply Set.mem_union_left
    apply Set.mem_iUnion.mpr
    exact ⟨⟨v, hv⟩, by simp [PlaneGraphRealization.vertexImageCarrier]⟩
  · exact Set.Subset.rfl

/-- A canonical positive side-separation radius for every face. -/
noncomputable def faceVertexSeparationRadius (G : K.PlaneGraphRealization)
    (f : K.Face) : ℝ :=
  Classical.choose (exists_faceVertexSeparationRadius (G := G) f)

theorem faceVertexSeparationRadius_pos (f : K.Face) :
    0 < faceVertexSeparationRadius G f :=
  (Classical.choose_spec (exists_faceVertexSeparationRadius (G := G) f)).1

theorem faceVertexSeparationRadius_separates :
    FaceVertexThickeningsSeparated G (faceVertexSeparationRadius G) := by
  intro f
  exact (Classical.choose_spec (exists_faceVertexSeparationRadius (G := G) f)).2

/-! ## The edgewise target for Moise's fine graph subdivision -/

/-- The finite family of coarse faces meeting an edge.  It contains, in particular, every face
having that edge as one of its sides. -/
def edgeMeetingFaces (K : LocallyFiniteTriangleComplex S) (e : K.Edge) : Set K.Face :=
  {f | (K.faceCarrier f ∩ K.edgeCarrier e).Nonempty}

theorem finite_edgeMeetingFaces (e : K.Edge) :
    (K.edgeMeetingFaces e).Finite := by
  exact K.locallyFinite.finite_nonempty_inter_compact
    (K.isCompact_edgeCarrier e)

theorem edgeFace_mem_edgeMeetingFaces (e : K.Edge) :
    K.edgeFace e ∈ K.edgeMeetingFaces e := by
  let v := K.edgeFirst e
  have hvEdge : K.vertexPoint v ∈ K.edgeCarrier e :=
    (K.vertexPoint_mem_edgeCarrier_iff v e).mpr (K.edgeFirst_mem e)
  have hvFace : K.vertexPoint v ∈ K.faceCarrier (K.edgeFace e) :=
    K.edgeCarrier_subset_faceCarrier e hvEdge
  exact ⟨K.vertexPoint v, hvFace, hvEdge⟩

/-- The minimum side-separation radius among the finitely many coarse faces meeting an edge.
This is the exact mesh target in Moise Chapter 6, Theorem 2: subdividing the edge until its
polygonal replacement is closer than this number preserves the side of every incident face. -/
noncomputable def edgeFaceSeparationRadius (G : K.PlaneGraphRealization)
    (e : K.Edge) : ℝ :=
  let F := (finite_edgeMeetingFaces (K := K) e).toFinset
  let hF : F.Nonempty := by
    refine ⟨K.edgeFace e, ?_⟩
    exact (Set.Finite.mem_toFinset _).mpr (K.edgeFace_mem_edgeMeetingFaces e)
  (F.image (faceVertexSeparationRadius G)).min' (hF.image _)

theorem edgeFaceSeparationRadius_pos (e : K.Edge) :
    0 < edgeFaceSeparationRadius G e := by
  let F := (finite_edgeMeetingFaces (K := K) e).toFinset
  let hF : F.Nonempty := by
    refine ⟨K.edgeFace e, ?_⟩
    exact (Set.Finite.mem_toFinset _).mpr (K.edgeFace_mem_edgeMeetingFaces e)
  have hmem := Finset.min'_mem (F.image (faceVertexSeparationRadius G)) (hF.image _)
  obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
  change 0 < (F.image (faceVertexSeparationRadius G)).min' _
  rw [← hf]
  exact faceVertexSeparationRadius_pos (G := G) f

theorem edgeFaceSeparationRadius_le_of_mem {e : K.Edge} {f : K.Face}
    (hf : f ∈ K.edgeMeetingFaces e) :
    edgeFaceSeparationRadius G e ≤ faceVertexSeparationRadius G f := by
  let F := (finite_edgeMeetingFaces (K := K) e).toFinset
  let hF : F.Nonempty := by
    refine ⟨K.edgeFace e, ?_⟩
    exact (Set.Finite.mem_toFinset _).mpr (K.edgeFace_mem_edgeMeetingFaces e)
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨f, (Set.Finite.mem_toFinset _).mpr hf, rfl⟩

theorem faceEdge_mem_edgeMeetingFaces (f : K.Face) (i : ZMod 3) :
    f ∈ K.edgeMeetingFaces (K.faceEdge f i) := by
  let v := K.edgeFirst (K.faceEdge f i)
  have hvEdge : K.vertexPoint v ∈ K.edgeCarrier (K.faceEdge f i) :=
    (K.vertexPoint_mem_edgeCarrier_iff v (K.faceEdge f i)).mpr
      (K.edgeFirst_mem (K.faceEdge f i))
  have hvFace : K.vertexPoint v ∈ K.faceCarrier f :=
    K.edgeCarrier_subset_faceCarrier_of_subset
      f (K.faceEdge f i) (K.faceEdge_subset_faceVertices f i) hvEdge
  exact ⟨K.vertexPoint v, hvFace, hvEdge⟩

/-- Edgewise diameter control below the incident-face minimum implies the facewise boundary
closeness consumed by the side-preservation theorem. -/
theorem faceBoundariesClose_of_edgeFaceSeparation_control
    (hsmall : ∀ e : K.Edge,
      2 * Metric.diam (G.edgeImage e) < edgeFaceSeparationRadius G e) :
    FaceBoundariesClose G (faceVertexSeparationRadius G) := by
  intro f q
  have hqSide : q.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using q.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hqSide
  let e := K.faceEdge f i
  have hqe : (K.faceBoundaryLift f q).1 ∈ edgeInSupport (K := K) e :=
    K.faceBoundarySupportPoint_mem_edge f i q hi
  calc
    dist (G.graphReplacementMap (K.faceBoundaryLift f q))
        (faceOriginalMap G f q.1) =
        dist (G.graphReplacementMap (K.faceBoundaryLift f q))
          (G.map (K.faceBoundaryLift f q).1) := by
            congr 1
            change faceOriginalMap G f
                (⟨q.1, standardFaceBoundary_mem_region q⟩ : standardFaceRegion).1 = _
            rw [faceOriginalMap_apply]
            rfl
    _ < 2 * Metric.diam (G.edgeImage e) := by
      rw [G.graphReplacementMap_eq e _ hqe]
      exact G.replacementEdgeMap_dist_lt_two_mul_edgeImage_diam e
        ⟨(K.faceBoundaryLift f q).1, hqe⟩
    _ < edgeFaceSeparationRadius G e := hsmall e
    _ ≤ faceVertexSeparationRadius G f :=
      edgeFaceSeparationRadius_le_of_mem (G := G)
        (K.faceEdge_mem_edgeMeetingFaces f i)

/-- The exact facewise estimate needed to control a Schoenflies filling.  Every point of a
replacement boundary is compared first with its original boundary point and then with an
arbitrary point of the same source face. -/
def FaceBoundariesControlled (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  ∀ (f : K.Face) (p : K.support),
    p ∈ faceInSupport (K := K) f → ∀ q : StandardFaceBoundary,
      dist (G.graphReplacementMap (K.faceBoundaryLift f q))
          (G.map (K.faceBoundaryLift f q).1) +
        dist (G.map (K.faceBoundaryLift f q).1) (G.map p) ≤ phi p

/-- Separate the graph approximation allowance from the oscillation of the original map on one
face.  This is the form discharged by an adaptive mesh. -/
def FaceOscillationControlled (G : K.PlaneGraphRealization)
    (rho phi : K.support → ℝ) : Prop :=
  ∀ (f : K.Face) (p : K.support),
    p ∈ faceInSupport (K := K) f → ∀ q : StandardFaceBoundary,
      rho (K.faceBoundaryLift f q).1 +
        dist (G.map (K.faceBoundaryLift f q).1) (G.map p) ≤ phi p

/-- Edgewise graph control plus within-face oscillation gives the exact boundary estimate used
by every Schoenflies filling. -/
theorem faceBoundariesControlled_of_graph_and_oscillation
    {rho phi : K.support → ℝ} (hgraph : G.EdgeImagesControlled rho)
    (hface : FaceOscillationControlled G rho phi) :
    FaceBoundariesControlled G phi := by
  intro f p hp q
  calc
    dist (G.graphReplacementMap (K.faceBoundaryLift f q))
          (G.map (K.faceBoundaryLift f q).1) +
        dist (G.map (K.faceBoundaryLift f q).1) (G.map p) ≤
        rho (K.faceBoundaryLift f q).1 +
          dist (G.map (K.faceBoundaryLift f q).1) (G.map p) :=
      add_le_add
        (G.isPhiApproximation_graphReplacementMap hgraph
          (K.faceBoundaryLift f q)).le le_rfl
    _ ≤ phi p := hface f p hp q

/-- Under facewise control, the entire polygonal disk selected by Schoenflies lies in the
prescribed ball about every point of its source face. -/
theorem facePolygonalCircle_closedRegion_subset_closedBall
    {phi : K.support → ℝ} (hcontrol : FaceBoundariesControlled G phi)
    (f : K.Face) (p : K.support) (hp : p ∈ faceInSupport (K := K) f) :
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆
      Metric.closedBall (G.map p) (phi p) := by
  apply (K.facePolygonalCircle (G := G) f).closedRegion_subset_closedBall_of_carrier_subset
  intro y hy
  rw [← K.faceBoundaryMap_image_polygon (G := G) f] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  let q' : StandardFaceBoundary := ⟨q, hq⟩
  rw [Metric.mem_closedBall, K.faceBoundaryMap_apply (G := G) f q']
  exact (dist_triangle _ (G.map (K.faceBoundaryLift f q').1) _).trans
    (hcontrol f p hp q')

/-- Pointwise control of the global cellwise replacement. -/
theorem polygonalReplacementMap_dist_le
    (H : K.CellwiseCompatibility G) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi) (p : K.support) :
    dist (K.polygonalReplacementMap H p).1.1 (G.map p) ≤ phi p := by
  let f := K.supportFace p
  let x := K.supportFacePoint p
  have hpFace : p ∈ faceInSupport (K := K) f := by
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact K.faceMap_supportFacePoint p
  have hmapFace : (K.polygonalReplacementMap H p).1.1 ∈
      (K.facePolygonalCircle (G := G) f).closedRegion := by
    rw [show p = faceToSupport (K := K) f x by
      apply Subtype.ext
      exact (K.faceMap_supportFacePoint p).symm,
      K.polygonalReplacementMap_faceToSupport H f x]
    rw [← (K.facePLFilling (G := G) f).range_faceMap]
    exact Set.mem_range_self x
  exact Metric.mem_closedBall.mp
    (facePolygonalCircle_closedRegion_subset_closedBall hcontrol f p hpFace hmapFace)

/-- A pointwise tolerance separates nonincident vertices from every source face. -/
def SeparatesVerticesFromFaces (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  ∀ (f : K.Face) (v : K.Vertex), v ∉ K.faceVertices f →
    ∀ p ∈ faceInSupport (K := K) f,
      phi p < dist (G.vertexImage v) (G.map p)

/-- Any pointwise smaller tolerance inherits vertex-to-face separation. -/
theorem SeparatesVerticesFromFaces.mono {phi psi : K.support → ℝ}
    (hsep : SeparatesVerticesFromFaces G phi) (hle : ∀ p, psi p ≤ phi p) :
    SeparatesVerticesFromFaces G psi :=
  fun f v hvf p hp ↦ (hle p).trans_lt (hsep f v hvf p hp)

/-- Local finiteness leaves only finitely many faces through any one support point. -/
theorem finite_setOf_mem_faceInSupport (p : K.support) :
    {f : K.Face | p ∈ faceInSupport (K := K) f}.Finite :=
  K.locallyFinite_faceInSupport.point_finite p

theorem mem_faceInSupport_supportFace (p : K.support) :
    p ∈ faceInSupport (K := K) (K.supportFace p) := by
  rw [K.faceInSupport_eq_preimage]
  exact K.mem_faceCarrier_supportFace p

/-- The finite set of maximal faces through one support point. -/
noncomputable def facesContaining (p : K.support) : Finset K.Face :=
  (finite_setOf_mem_faceInSupport (K := K) p).toFinset

theorem mem_facesContaining {p : K.support} {f : K.Face} :
    f ∈ facesContaining (K := K) p ↔ p ∈ faceInSupport (K := K) f :=
  Set.Finite.mem_toFinset _

theorem facesContaining_nonempty (p : K.support) :
    (facesContaining (K := K) p).Nonempty :=
  ⟨K.supportFace p, mem_facesContaining.mpr (mem_faceInSupport_supportFace p)⟩

/-- The pointwise vertex-to-face separation control: the smallest per-face separation radius
among the finitely many faces through the point.  This is the locally finite analogue of the
finite `exists_uniform_vertex_face_separation`: positive at every point, strongly positive on
compact sets, and smaller than the distance from any face through the point to any vertex not
incident to that face. -/
noncomputable def vertexSeparationControl (G : K.PlaneGraphRealization)
    (p : K.support) : ℝ :=
  ((facesContaining (K := K) p).image (faceVertexSeparationRadius G)).min'
    ((facesContaining_nonempty p).image _)

theorem vertexSeparationControl_le {p : K.support} {f : K.Face}
    (hf : p ∈ faceInSupport (K := K) f) :
    vertexSeparationControl G p ≤ faceVertexSeparationRadius G f :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ (mem_facesContaining.mpr hf))

theorem vertexSeparationControl_pos (p : K.support) :
    0 < vertexSeparationControl G p := by
  have hmem := Finset.min'_mem
    ((facesContaining (K := K) p).image (faceVertexSeparationRadius G))
    ((facesContaining_nonempty p).image _)
  obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
  rw [vertexSeparationControl, ← hf]
  exact faceVertexSeparationRadius_pos (G := G) f

/-- The canonical control separates every nonincident vertex from every face: each face image
is a positive thickening away from the vertex, and the control is below that radius. -/
theorem separatesVerticesFromFaces_vertexSeparationControl :
    SeparatesVerticesFromFaces G (vertexSeparationControl G) := by
  intro f v hvf p hp
  have hgap : faceVertexSeparationRadius G f < dist (G.vertexImage v) (G.map p) := by
    by_contra hle
    push Not at hle
    have hball : G.map p ∈
        Metric.closedBall (G.vertexImage v) (faceVertexSeparationRadius G f) := by
      rw [Metric.mem_closedBall, dist_comm]
      exact hle
    have hthick : G.map p ∈
        Metric.cthickening (faceVertexSeparationRadius G f)
          (G.map '' faceInSupport (K := K) f) :=
      Metric.self_subset_cthickening _ ⟨p, hp, rfl⟩
    exact Set.disjoint_left.mp
      (faceVertexSeparationRadius_separates (G := G) f v hvf) hball hthick
  exact (vertexSeparationControl_le hp).trans_lt hgap

/-- On every compact set the canonical separation control has a positive lower bound: only
finitely many faces meet the compact set, and each contributes a positive radius. -/
theorem stronglyPositiveOn_vertexSeparationControl :
    StronglyPositiveOn Set.univ (vertexSeparationControl G) := by
  intro C hC _
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact ⟨1, one_pos, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
  have hfin : {f : K.Face | (faceInSupport (K := K) f ∩ C).Nonempty}.Finite :=
    K.locallyFinite_faceInSupport.finite_nonempty_inter_compact hC
  obtain ⟨p₀, hp₀⟩ := hCne
  have hFne : hfin.toFinset.Nonempty :=
    ⟨K.supportFace p₀, (Set.Finite.mem_toFinset _).mpr
      ⟨p₀, mem_faceInSupport_supportFace p₀, hp₀⟩⟩
  refine ⟨(hfin.toFinset.image (faceVertexSeparationRadius G)).min' (hFne.image _),
    ?_, ?_⟩
  · have hmem := Finset.min'_mem
      (hfin.toFinset.image (faceVertexSeparationRadius G)) (hFne.image _)
    obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hmem
    rw [← hf]
    exact faceVertexSeparationRadius_pos (G := G) f
  · intro p hp
    apply Finset.le_min'
    intro r hr
    obtain ⟨f, hfp, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.min'_le
    apply Finset.mem_image_of_mem
    exact (Set.Finite.mem_toFinset _).mpr
      ⟨p, mem_facesContaining.mp hfp, hp⟩

/-- The vertex-side compatibility condition used in Moise's side-preservation argument. -/
def FaceFillingsVerticesAvoidClosedRegions (G : K.PlaneGraphRealization) : Prop :=
  ∀ (f : K.Face) (v : K.Vertex), v ∉ K.faceVertices f →
    G.vertexImage v ∉ (K.facePolygonalCircle (G := G) f).closedRegion

/-- Facewise metric control and vertex-to-face separation keep every nonincident vertex outside
the selected polygonal closed disk. -/
theorem faceFillingsVerticesAvoidClosedRegions_of_control
    {phi : K.support → ℝ} (hcontrol : FaceBoundariesControlled G phi)
    (hsep : SeparatesVerticesFromFaces G phi) :
    FaceFillingsVerticesAvoidClosedRegions G := by
  intro f v hvf hvClosed
  obtain ⟨z, hz⟩ := K.faceCarrier_nonempty f
  obtain ⟨x, rfl⟩ := hz
  let p : K.support := faceToSupport (K := K) f x
  have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self x
  have hball := facePolygonalCircle_closedRegion_subset_closedBall
    hcontrol f p hp hvClosed
  have hle : dist (G.vertexImage v) (G.map p) ≤ phi p :=
    Metric.mem_closedBall.mp hball
  exact (not_lt_of_ge hle) (hsep f v hvf p hp)

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
