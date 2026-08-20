/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteTriangulation
import LeanPool.ClassificationOfSurfaces.Moise.BrokenLine
import LeanPool.ClassificationOfSurfaces.Moise.FrontierGlue
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalArc
import LeanPool.ClassificationOfSurfaces.Moise.GraphPolygonalization

/-!
# Locally finite graph approximation controls

This file begins the noncompact form of Moise Chapter 6, Theorem 2.  The finite graph proof uses
one minimum separation radius over all vertices and edges.  A locally finite complex has no such
global minimum.  Instead every vertex receives its own positive radius, small enough to avoid all
nonincident edges and all other vertices.  Local finiteness makes the two obstacle families
closed, which is the only compactness input needed for this pointwise construction.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S]

theorem vertexPoint_mem_support (K : LocallyFiniteTriangleComplex S) (v : K.Vertex) :
    K.vertexPoint v ∈ K.support := by
  apply Set.mem_iUnion.mpr
  exact ⟨K.incidentFace v,
    K.vertexPoint_in_faceCarrier (K.incidentFace v)
      (K.mem_faceVertices_incidentFace v)⟩

/-- A realization of the ambient support in an open perturbation region of the plane.  The image
is allowed to have boundary in that region: in the Rado step it is an open subset of the old
polyhedral surface, not an ambiently open plane set.  Edge images need only be locally finite in
the perturbation region; they may accumulate at its omitted frontier. -/
structure PlaneGraphRealization (K : LocallyFiniteTriangleComplex S) where
  /-- The open plane region in which polygonal perturbations are allowed. -/
  region : Set Plane
  /-- The perturbation region is open. -/
  regionOpen : IsOpen region
  /-- The topological embedding into chart coordinates. -/
  map : K.support → Plane
  /-- The support is embedded, not merely mapped injectively. -/
  isEmbedding : _root_.Topology.IsEmbedding map
  /-- The original realization lies in the region where perturbations are allowed. -/
  map_mem_region : ∀ p, map p ∈ region
  /-- A positive upper bound for the disk chosen at each graph vertex. -/
  vertexApproximationControl : K.Vertex → ℝ
  /-- Every requested vertex control is positive. -/
  vertexApproximationControl_pos : ∀ v, 0 < vertexApproximationControl v
  /-- A positive upper bound for the central perturbation tube of each graph edge. -/
  edgeApproximationControl : K.Edge → ℝ
  /-- Every requested edge control is positive. -/
  edgeApproximationControl_pos : ∀ e, 0 < edgeApproximationControl e
  /-- The embedded support is closed relative to the perturbation region.  It may still
  accumulate at the omitted frontier of that region. -/
  mapClosedInRegion :
    IsClosed (Set.range fun p ↦ (⟨map p, map_mem_region p⟩ : region))
  /-- Edge images are locally finite in the open perturbation region. -/
  edgeLocallyFinite : LocallyFinite fun e : K.Edge ↦
    {q : region | q.1 ∈ map '' {p : K.support | p.1 ∈ K.edgeCarrier e}}

namespace PlaneGraphRealization

variable {K : LocallyFiniteTriangleComplex S} (G : K.PlaneGraphRealization)

/-- Reduce the quantitative replacement controls without changing the realized map, its target
region, or any local-finiteness data. -/
def withApproximationControls
    (vertexControl : K.Vertex → ℝ) (hvertex : ∀ v, 0 < vertexControl v)
    (edgeControl : K.Edge → ℝ) (hedge : ∀ e, 0 < edgeControl e) :
    K.PlaneGraphRealization where
  region := G.region
  regionOpen := G.regionOpen
  map := G.map
  isEmbedding := G.isEmbedding
  map_mem_region := G.map_mem_region
  vertexApproximationControl := vertexControl
  vertexApproximationControl_pos := hvertex
  edgeApproximationControl := edgeControl
  edgeApproximationControl_pos := hedge
  mapClosedInRegion := G.mapClosedInRegion
  edgeLocallyFinite := G.edgeLocallyFinite

@[simp] theorem withApproximationControls_region
    (vertexControl : K.Vertex → ℝ) (hvertex : ∀ v, 0 < vertexControl v)
    (edgeControl : K.Edge → ℝ) (hedge : ∀ e, 0 < edgeControl e) :
    (G.withApproximationControls vertexControl hvertex edgeControl hedge).region = G.region := rfl

@[simp] theorem withApproximationControls_map
    (vertexControl : K.Vertex → ℝ) (hvertex : ∀ v, 0 < vertexControl v)
    (edgeControl : K.Edge → ℝ) (hedge : ∀ e, 0 < edgeControl e) :
    (G.withApproximationControls vertexControl hvertex edgeControl hedge).map = G.map := rfl

/-- Include an edge point into the whole support. -/
def edgeToSupport (e : K.Edge) (p : K.edgeCarrier e) : K.support :=
  ⟨p.1, by
    apply Set.mem_iUnion.mpr
    exact ⟨K.edgeFace e, K.edgeCarrier_subset_faceCarrier e p.2⟩⟩

/-- The image of a global vertex in chart coordinates. -/
noncomputable def vertexImage (v : K.Vertex) : Plane :=
  G.map ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩

/-- The image of an edge carrier in chart coordinates. -/
def edgeImage (e : K.Edge) : Set Plane :=
  G.map '' {p : K.support | p.1 ∈ K.edgeCarrier e}

theorem edgeImage_eq_structure_family (e : K.Edge) :
    G.edgeImage e = G.map '' {p : K.support | p.1 ∈ K.edgeCarrier e} := rfl

/-- One edge image regarded as a subset of the open perturbation region. -/
def edgeImageInRange (e : K.Edge) : Set G.region :=
  {q | q.1 ∈ G.edgeImage e}

theorem locallyFinite_edgeImages : LocallyFinite G.edgeImageInRange := by
  exact G.edgeLocallyFinite

/-- A relatively closed subset of an open set becomes ambiently closed after adjoining the
complement of that open set. -/
private theorem isClosed_union_compl_of_isClosed_preimage
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
    simpa only [Set.mem_compl_iff, Set.mem_preimage] using fun hxA ↦ hx (Or.inl hxA)
  · rintro ⟨y, hy, rfl⟩ h
    rcases h with hA | hV
    · exact hy hA
    · exact hV y.2

/-- A compact ambient set contained in a subspace remains compact when regarded as a set in that
subspace. -/
theorem isCompact_preimage_subtypeVal_of_subset
    {X : Type*} [TopologicalSpace X] {V C : Set X}
    (hC : IsCompact C) (hCV : C ⊆ V) :
    IsCompact ((↑) ⁻¹' C : Set V) := by
  let f : C → V := fun x ↦ ⟨x.1, hCV x.2⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hrange : Set.range f = ((↑) ⁻¹' C : Set V) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩
  rw [← hrange]
  exact isCompact_range hf

/-- A locally finite family remains locally finite after embedding it as a closed subspace.
This is the transport used for a Rado overlap inside the open region obtained by deleting the
overlap frontier. -/
theorem locallyFinite_image_isEmbedding_of_isClosed_range
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : I → Set X} (hA : LocallyFinite A) {f : X → Y}
    (hf : _root_.Topology.IsEmbedding f) (hclosed : IsClosed (Set.range f)) :
    LocallyFinite fun i ↦ f '' A i := by
  intro y
  by_cases hy : y ∈ Set.range f
  · let e : X ≃ₜ Set.range f := hf.toHomeomorph
    let y' : Set.range f := ⟨y, hy⟩
    have hlocal : LocallyFinite fun i ↦ e.symm ⁻¹' A i :=
      hA.preimage_continuous e.symm.continuous
    obtain ⟨U, hUy, hfinite⟩ := hlocal y'
    obtain ⟨W, hWy, hWU⟩ := (mem_nhds_subtype (Set.range f) y' U).mp hUy
    refine ⟨W, hWy, ?_⟩
    apply hfinite.subset
    intro i hi
    obtain ⟨z, hzImage, hzW⟩ := hi
    obtain ⟨x, hxA, rfl⟩ := hzImage
    let z' : Set.range f := ⟨f x, ⟨x, rfl⟩⟩
    refine ⟨z', ?_, hWU hzW⟩
    change e.symm z' ∈ A i
    have hz'e : z' = e x := by
      apply Subtype.ext
      rfl
    rw [hz'e, e.symm_apply_apply]
    exact hxA
  · refine ⟨(Set.range f)ᶜ, hclosed.isOpen_compl.mem_nhds hy, ?_⟩
    have hempty : {i | (f '' A i ∩ (Set.range f)ᶜ).Nonempty} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.notMem_empty, iff_false]
      rintro ⟨z, ⟨x, -, rfl⟩, hz⟩
      exact hz ⟨x, rfl⟩
    rw [hempty]
    exact Set.finite_empty

theorem vertexImage_injective : Function.Injective G.vertexImage := by
  intro v w hvw
  apply K.vertexPoint_injective
  exact congrArg Subtype.val (G.isEmbedding.injective hvw)

theorem continuous_edgeToSupport (e : K.Edge) :
    Continuous (edgeToSupport (K := K) e) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem isEmbedding_edgeToSupport (e : K.Edge) :
    _root_.Topology.IsEmbedding (edgeToSupport (K := K) e) := by
  exact _root_.Topology.IsEmbedding.subtypeVal.codRestrict _ _

theorem isCompact_edgeImage (e : K.Edge) : IsCompact (G.edgeImage e) := by
  have hcarrier : {p : K.support | p.1 ∈ K.edgeCarrier e} =
      Set.range (edgeToSupport (K := K) e) := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨p.1, hp⟩, Subtype.ext rfl⟩
    · rintro ⟨q, rfl⟩
      exact q.2
  rw [edgeImage, hcarrier]
  have himage : G.map '' Set.range (edgeToSupport (K := K) e) =
      Set.range (G.map ∘ edgeToSupport (K := K) e) := by
    ext x
    constructor
    · rintro ⟨p, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨edgeToSupport (K := K) e q, ⟨q, rfl⟩, rfl⟩
  rw [himage]
  let : CompactSpace (K.edgeCarrier e) :=
    isCompact_iff_compactSpace.mp (K.isCompact_edgeCarrier e)
  exact isCompact_range
    (G.isEmbedding.continuous.comp (continuous_edgeToSupport (K := K) e))

theorem isClosed_edgeImage (e : K.Edge) : IsClosed (G.edgeImage e) :=
  (G.isCompact_edgeImage e).isClosed

/-- The canonical interval parametrization of an edge, included into the source support. -/
noncomputable def edgePathInSupport (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) : K.support :=
  edgeToSupport (K := K) e
    ⟨K.edgePath e r, by rw [← K.range_edgePath e]; exact Set.mem_range_self r⟩

theorem continuous_edgePathInSupport (e : K.Edge) :
    Continuous (edgePathInSupport (K := K) e) := by
  apply Continuous.subtype_mk
  exact K.continuous_edgePath e

theorem edgePathInSupport_injective (e : K.Edge) :
    Function.Injective (edgePathInSupport (K := K) e) := by
  intro r s hrs
  apply K.edgePath_injective e
  exact congrArg Subtype.val hrs

/-- The charted embedded arc carried by one abstract edge. -/
noncomputable def chartEdgePath (e : K.Edge) : Set.Icc (0 : ℝ) 1 → Plane :=
  G.map ∘ edgePathInSupport (K := K) e

theorem continuous_chartEdgePath (e : K.Edge) : Continuous (G.chartEdgePath e) :=
  G.isEmbedding.continuous.comp (continuous_edgePathInSupport (K := K) e)

theorem chartEdgePath_injective (e : K.Edge) :
    Function.Injective (G.chartEdgePath e) :=
  G.isEmbedding.injective.comp (edgePathInSupport_injective (K := K) e)

theorem range_chartEdgePath (e : K.Edge) :
    Set.range (G.chartEdgePath e) = G.edgeImage e := by
  apply Set.Subset.antisymm
  · rintro y ⟨r, rfl⟩
    exact ⟨edgePathInSupport (K := K) e r,
      by change K.edgePath e r ∈ K.edgeCarrier e
         rw [← K.range_edgePath e]
         exact Set.mem_range_self r,
      rfl⟩
  · rintro y ⟨p, hp, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, K.edgePath e r = p.1 := by
      have hp' : p.1 ∈ Set.range (K.edgePath e) := by
        rw [K.range_edgePath e]
        exact hp
      exact hp'
    refine ⟨r, ?_⟩
    change G.map (edgePathInSupport (K := K) e r) = G.map p
    congr 1
    exact Subtype.ext hr

theorem chartEdgePath_mem_edgeImage (e : K.Edge) (t : Set.Icc (0 : ℝ) 1) :
    G.chartEdgePath e t ∈ G.edgeImage e := by
  rw [← G.range_chartEdgePath e]
  exact Set.mem_range_self t

theorem chartEdgePath_zero (e : K.Edge) :
    G.chartEdgePath e ⟨0, by simp⟩ = G.vertexImage (K.edgeFirst e) := by
  change G.map (edgePathInSupport (K := K) e ⟨0, by simp⟩) =
    G.map ⟨K.vertexPoint (K.edgeFirst e), K.vertexPoint_mem_support _⟩
  congr 1
  apply Subtype.ext
  exact K.edgePath_zero e

theorem chartEdgePath_one (e : K.Edge) :
    G.chartEdgePath e ⟨1, by simp⟩ = G.vertexImage (K.edgeSecond e) := by
  change G.map (edgePathInSupport (K := K) e ⟨1, by simp⟩) =
    G.map ⟨K.vertexPoint (K.edgeSecond e), K.vertexPoint_mem_support _⟩
  congr 1
  apply Subtype.ext
  exact K.edgePath_one e

theorem vertexImage_mem_edgeImage_iff (v : K.Vertex) (e : K.Edge) :
    G.vertexImage v ∈ G.edgeImage e ↔ v ∈ e.1 := by
  constructor
  · rintro ⟨p, hpEdge, hp⟩
    have hsource :
        (⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩ : K.support) =
          p := G.isEmbedding.injective hp.symm
    have : K.vertexPoint v ∈ K.edgeCarrier e := by
      have hval := congrArg Subtype.val hsource
      change K.vertexPoint v = p.1 at hval
      rw [hval]
      exact hpEdge
    exact (K.vertexPoint_mem_edgeCarrier_iff v e).mp this
  · intro hve
    have hvCarrier := (K.vertexPoint_mem_edgeCarrier_iff v e).mpr hve
    exact ⟨⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩, hvCarrier, rfl⟩

theorem isPreconnected_edgeImage (e : K.Edge) :
    IsPreconnected (G.edgeImage e) := by
  rw [← G.range_chartEdgePath e]
  exact isPreconnected_range (G.continuous_chartEdgePath e)

theorem edgeImage_diam_pos (e : K.Edge) : 0 < Metric.diam (G.edgeImage e) := by
  have hfirst : G.vertexImage (K.edgeFirst e) ∈ G.edgeImage e :=
    (G.vertexImage_mem_edgeImage_iff (K.edgeFirst e) e).mpr (K.edgeFirst_mem e)
  have hsecond : G.vertexImage (K.edgeSecond e) ∈ G.edgeImage e :=
    (G.vertexImage_mem_edgeImage_iff (K.edgeSecond e) e).mpr (K.edgeSecond_mem e)
  exact (dist_pos.mpr fun h ↦
    K.edgeFirst_ne_edgeSecond e (G.vertexImage_injective h)).trans_le
      (Metric.dist_le_diam_of_mem (G.isCompact_edgeImage e).isBounded hfirst hsecond)

theorem endpointDist_le_edgeImage_diam (e : K.Edge) :
    dist (G.vertexImage (K.edgeFirst e)) (G.vertexImage (K.edgeSecond e)) ≤
      Metric.diam (G.edgeImage e) := by
  exact Metric.dist_le_diam_of_mem (G.isCompact_edgeImage e).isBounded
    ((G.vertexImage_mem_edgeImage_iff (K.edgeFirst e) e).mpr (K.edgeFirst_mem e))
    ((G.vertexImage_mem_edgeImage_iff (K.edgeSecond e) e).mpr (K.edgeSecond_mem e))

/-- A polygonal replacement of one charted edge inside a prescribed metric neighborhood. -/
structure EdgeBrokenLineApproximation (e : K.Edge) (eps : ℝ) where
  eps_pos : 0 < eps
  /-- The `data` declaration. -/
  data : BrokenLineData (Metric.thickening eps (G.edgeImage e))
  start_eq : data.start = G.vertexImage (K.edgeFirst e)
  finish_eq : data.finish = G.vertexImage (K.edgeSecond e)

theorem exists_edgeBrokenLineApproximation (e : K.Edge) {eps : ℝ} (heps : 0 < eps) :
    Nonempty (G.EdgeBrokenLineApproximation e eps) := by
  have hstart : G.vertexImage (K.edgeFirst e) ∈ G.edgeImage e :=
    (G.vertexImage_mem_edgeImage_iff (K.edgeFirst e) e).mpr (K.edgeFirst_mem e)
  have hfinish : G.vertexImage (K.edgeSecond e) ∈ G.edgeImage e :=
    (G.vertexImage_mem_edgeImage_iff (K.edgeSecond e) e).mpr (K.edgeSecond_mem e)
  have hjoined := brokenLine_in_thickening_of_preconnected
    (G.isPreconnected_edgeImage e) hstart hfinish heps
  obtain ⟨B, hBstart, hBfinish⟩ := BrokenLineData.exists_data_of_joined hjoined
  exact ⟨⟨heps, B, hBstart, hBfinish⟩⟩

/-- The `edgeBrokenLineApproximation` declaration. -/
noncomputable def edgeBrokenLineApproximation (e : K.Edge) {eps : ℝ} (heps : 0 < eps) :
    G.EdgeBrokenLineApproximation e eps :=
  Classical.choice (G.exists_edgeBrokenLineApproximation e heps)

namespace EdgeBrokenLineApproximation

variable {G} {e : K.Edge} {eps : ℝ}

theorem resolvedCarrier_subset (A : G.EdgeBrokenLineApproximation e eps) :
    A.data.resolvedCarrier ⊆ Metric.thickening eps (G.edgeImage e) := by
  apply A.data.resolvedCarrier_subset
  rw [A.start_eq]
  exact Metric.self_subset_thickening A.eps_pos _
    ((G.vertexImage_mem_edgeImage_iff (K.edgeFirst e) e).mpr (K.edgeFirst_mem e))

end EdgeBrokenLineApproximation

/-- Exact charted intersection of two distinct abstract edges. -/
theorem edgeImage_inter_eq_sharedVertices {e d : K.Edge} (hed : e ≠ d) :
    G.edgeImage e ∩ G.edgeImage d =
      {p | ∃ v : K.Vertex, v ∈ e.1 ∧ v ∈ d.1 ∧ p = G.vertexImage v} := by
  apply Set.Subset.antisymm
  · rintro p ⟨⟨q, hqe, hqp⟩, ⟨r, hrd, hrp⟩⟩
    have hqr : q = r := G.isEmbedding.injective (hqp.trans hrp.symm)
    have hqBoth : q.1 ∈ K.edgeCarrier e ∩ K.edgeCarrier d := by
      refine ⟨hqe, ?_⟩
      exact congrArg Subtype.val hqr ▸ hrd
    rw [K.edgeCarrier_inter_eq_sharedVertices hed] at hqBoth
    obtain ⟨v, hve, hvd, hqv⟩ := hqBoth
    refine ⟨v, hve, hvd, ?_⟩
    calc
      p = G.map q := hqp.symm
      _ = G.map ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩ := by
        congr 1
        exact Subtype.ext hqv
      _ = G.vertexImage v := rfl
  · rintro p ⟨v, hve, hvd, rfl⟩
    exact ⟨(G.vertexImage_mem_edgeImage_iff v e).mpr hve,
      (G.vertexImage_mem_edgeImage_iff v d).mpr hvd⟩

/-- The union of edge images not incident to `v`. -/
def nonincidentEdgeImage (v : K.Vertex) : Set Plane :=
  (⋃ e : {e : K.Edge // v ∉ e.1}, G.edgeImage e.1) ∪ G.regionᶜ

theorem isClosed_nonincidentEdgeImage (v : K.Vertex) :
    IsClosed (G.nonincidentEdgeImage v) := by
  let A := ⋃ e : {e : K.Edge // v ∉ e.1}, G.edgeImage e.1
  apply isClosed_union_compl_of_isClosed_preimage G.regionOpen
  have hlocal : LocallyFinite
      (fun e : {e : K.Edge // v ∉ e.1} ↦ G.edgeImageInRange e.1) :=
    G.locallyFinite_edgeImages.comp_injective
      (g := fun e : {e : K.Edge // v ∉ e.1} ↦ e.1) Subtype.val_injective
  have hclosed : IsClosed
      (⋃ e : {e : K.Edge // v ∉ e.1}, G.edgeImageInRange e.1) := by
    apply hlocal.isClosed_iUnion
    intro e
    exact (G.isClosed_edgeImage e.1).preimage continuous_subtype_val
  convert hclosed using 1
  ext p
  simp only [edgeImageInRange, Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]

theorem vertexImage_not_mem_nonincidentEdgeImage (v : K.Vertex) :
    G.vertexImage v ∉ G.nonincidentEdgeImage v := by
  intro hv
  rcases hv with hv | hv
  · obtain ⟨e, hve⟩ := Set.mem_iUnion.mp hv
    exact e.2 ((G.vertexImage_mem_edgeImage_iff v e.1).mp hve)
  · exact hv (G.map_mem_region
      ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩)

/-- Singleton chart images of the global vertices. -/
def vertexImageCarrier (v : K.Vertex) : Set Plane :=
  {G.vertexImage v}

/-- A singleton vertex image in the open chart range. -/
def vertexImageCarrierInRange (v : K.Vertex) : Set G.region :=
  {q | q.1 ∈ G.vertexImageCarrier v}

/-- Local finiteness of vertex images transported to the chart plane.  It follows from edge
local finiteness because every vertex belongs to an edge of one of its triangular faces. -/
theorem locallyFinite_vertexImages : LocallyFinite G.vertexImageCarrierInRange := by
  intro x
  obtain ⟨U, hUx, hfinite⟩ := G.locallyFinite_edgeImages x
  refine ⟨U, hUx, ?_⟩
  let E : Set K.Edge := {e | (G.edgeImageInRange e ∩ U).Nonempty}
  let V : Set K.Vertex := ⋃ e ∈ E, (e.1 : Set K.Vertex)
  have hVfinite : V.Finite := hfinite.biUnion fun e _ ↦ e.1.finite_toSet
  apply hVfinite.subset
  intro v hv
  obtain ⟨p, hpv, hpU⟩ := hv
  have hp : p.1 = G.vertexImage v := hpv
  obtain ⟨f, hfv⟩ := K.vertex_used v
  have hfcard := K.faceVertices_card f
  have hrest : (K.faceVertices f).erase v |>.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub : K.faceVertices f ⊆ {v} := by
      intro w hw
      by_contra hwv
      have hwv' : w ≠ v := by simpa using hwv
      have : w ∈ (K.faceVertices f).erase v := Finset.mem_erase.mpr ⟨hwv', hw⟩
      rw [hempty] at this
      exact Finset.notMem_empty w this
    have hcardle : (K.faceVertices f).card ≤ 1 :=
      Finset.card_le_card hsub |>.trans_eq (Finset.card_singleton v)
    omega
  let w : K.Vertex := hrest.choose
  have hwf : w ∈ K.faceVertices f := (Finset.mem_erase.mp hrest.choose_spec).2
  have hwv : w ≠ v := (Finset.mem_erase.mp hrest.choose_spec).1
  let e0 : Finset K.Vertex := {v, w}
  have he0card : e0.card = 2 := by simp [e0, Ne.symm hwv]
  have he0sub : e0 ⊆ K.faceVertices f := by
    intro q hq
    simp only [e0, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hfv
    · exact hwf
  let e : K.Edge := ⟨e0, he0card, ⟨f, he0sub⟩⟩
  apply Set.mem_iUnion₂.mpr
  refine ⟨e, ?_, ?_⟩
  · refine ⟨p, ?_, hpU⟩
    change p.1 ∈ G.edgeImage e
    rw [hp]
    exact (G.vertexImage_mem_edgeImage_iff v e).mpr (by simp [e, e0])
  · simp [e, e0]

/-- Every vertex of a triangle complex has another vertex in one of its incident faces. -/
theorem exists_vertex_ne (v : K.Vertex) : ∃ w : K.Vertex, w ≠ v := by
  obtain ⟨f, hfv⟩ := K.vertex_used v
  have hrest : ((K.faceVertices f).erase v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub : K.faceVertices f ⊆ {v} := by
      intro w hw
      by_contra hwv
      have hwv' : w ≠ v := by simpa using hwv
      have : w ∈ (K.faceVertices f).erase v := Finset.mem_erase.mpr ⟨hwv', hw⟩
      rw [hempty] at this
      exact Finset.notMem_empty w this
    have hcardle : (K.faceVertices f).card ≤ 1 :=
      (Finset.card_le_card hsub).trans_eq (Finset.card_singleton v)
    have hfcard := K.faceVertices_card f
    omega
  exact ⟨hrest.choose, (Finset.mem_erase.mp hrest.choose_spec).1⟩

/-- The chart images of all vertices other than `v`. -/
def otherVertexImages (v : K.Vertex) : Set Plane :=
  (⋃ w : {w : K.Vertex // w ≠ v}, G.vertexImageCarrier w.1) ∪
    G.regionᶜ

theorem isClosed_otherVertexImages (v : K.Vertex) :
    IsClosed (G.otherVertexImages v) := by
  apply isClosed_union_compl_of_isClosed_preimage G.regionOpen
  have hlocal : LocallyFinite
      (fun w : {w : K.Vertex // w ≠ v} ↦ G.vertexImageCarrierInRange w.1) :=
    G.locallyFinite_vertexImages.comp_injective
      (g := fun w : {w : K.Vertex // w ≠ v} ↦ w.1) Subtype.val_injective
  have hclosed : IsClosed
      (⋃ w : {w : K.Vertex // w ≠ v}, G.vertexImageCarrierInRange w.1) := by
    apply hlocal.isClosed_iUnion
    intro w
    have hwclosed :=
      ((isClosed_singleton : IsClosed ({G.vertexImage w.1} : Set Plane)).preimage
        (continuous_subtype_val : Continuous
          (Subtype.val : G.region → Plane)))
    convert hwclosed using 1
    ext q
    simp [vertexImageCarrierInRange, vertexImageCarrier]
  convert hclosed using 1
  ext p
  simp only [vertexImageCarrierInRange, Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]

theorem vertexImage_not_mem_otherVertexImages (v : K.Vertex) :
    G.vertexImage v ∉ G.otherVertexImages v := by
  intro hv
  rcases hv with hv | hv
  · obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hv
    have hImage : G.vertexImage v = G.vertexImage w.1 := by
      simpa [vertexImageCarrier] using hw
    have hvw : v = w.1 := G.vertexImage_injective hImage
    exact w.2 hvw.symm
  · exact hv (G.map_mem_region
      ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩)

theorem otherVertexImages_nonempty (v : K.Vertex) :
    (G.otherVertexImages v).Nonempty := by
  obtain ⟨w, hwv⟩ := exists_vertex_ne (K := K) v
  refine ⟨G.vertexImage w, ?_⟩
  apply Set.mem_union_left
  apply Set.mem_iUnion.mpr
  exact ⟨⟨w, hwv⟩, by simp [vertexImageCarrier]⟩

/-- Closed geometric obstacles that a vertex neighborhood must avoid: every nonincident edge and
every other vertex. -/
def vertexObstacle (v : K.Vertex) : Set Plane :=
  G.nonincidentEdgeImage v ∪ G.otherVertexImages v

theorem isClosed_vertexObstacle (v : K.Vertex) :
    IsClosed (G.vertexObstacle v) :=
  (G.isClosed_nonincidentEdgeImage v).union (G.isClosed_otherVertexImages v)

theorem vertexImage_not_mem_vertexObstacle (v : K.Vertex) :
    G.vertexImage v ∉ G.vertexObstacle v := by
  rw [vertexObstacle, Set.mem_union]
  exact not_or_intro (G.vertexImage_not_mem_nonincidentEdgeImage v)
    (G.vertexImage_not_mem_otherVertexImages v)

theorem vertexObstacle_nonempty (v : K.Vertex) :
    (G.vertexObstacle v).Nonempty :=
  (G.otherVertexImages_nonempty v).mono Set.subset_union_right

/-- A bounded quarter of the distance from a vertex to every nonincident edge and every other
vertex.  Unlike the finite graph construction, this radius is allowed to vary from vertex to
vertex.  The upper bound by one preserves local finiteness of the resulting disks. -/
noncomputable def vertexIsolationRadius (v : K.Vertex) : ℝ :=
  min (G.vertexApproximationControl v)
    (min 1 (Metric.infDist (G.vertexImage v) (G.vertexObstacle v) / 4))

theorem vertexIsolationRadius_pos (v : K.Vertex) :
    0 < G.vertexIsolationRadius v := by
  rw [vertexIsolationRadius]
  apply lt_min (G.vertexApproximationControl_pos v)
  apply lt_min (by norm_num)
  exact div_pos
    ((G.isClosed_vertexObstacle v).notMem_iff_infDist_pos
      (G.vertexObstacle_nonempty v) |>.mp (G.vertexImage_not_mem_vertexObstacle v))
    (by norm_num)

theorem vertexIsolationRadius_le_control (v : K.Vertex) :
    G.vertexIsolationRadius v ≤ G.vertexApproximationControl v := by
  exact min_le_left _ _

theorem vertexIsolationRadius_le_one (v : K.Vertex) :
    G.vertexIsolationRadius v ≤ 1 := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem vertexIsolationRadius_lt_infDist (v : K.Vertex) :
    G.vertexIsolationRadius v <
      Metric.infDist (G.vertexImage v) (G.vertexObstacle v) := by
  have hdist : 0 < Metric.infDist (G.vertexImage v) (G.vertexObstacle v) :=
    (G.isClosed_vertexObstacle v).notMem_iff_infDist_pos
      (G.vertexObstacle_nonempty v) |>.mp (G.vertexImage_not_mem_vertexObstacle v)
  calc
    G.vertexIsolationRadius v ≤
      Metric.infDist (G.vertexImage v) (G.vertexObstacle v) / 4 :=
      (min_le_right _ _).trans (min_le_right _ _)
    _ < Metric.infDist (G.vertexImage v) (G.vertexObstacle v) := by linarith

/-- The closed disk selected around a charted vertex. -/
def vertexDisk (v : K.Vertex) : Set Plane :=
  Metric.closedBall (G.vertexImage v) (G.vertexIsolationRadius v)

/-- A selected vertex disk, restricted to the open chart range. -/
def vertexDiskInRange (v : K.Vertex) : Set G.region :=
  {p | p.1 ∈ G.vertexDisk v}

theorem disjoint_vertexDisk_vertexObstacle (v : K.Vertex) :
    Disjoint (G.vertexDisk v) (G.vertexObstacle v) := by
  exact Metric.disjoint_closedBall_of_lt_infDist (G.vertexIsolationRadius_lt_infDist v)

theorem vertexDisk_subset_range (v : K.Vertex) :
    G.vertexDisk v ⊆ G.region := by
  intro p hp
  by_contra hpRange
  have hpObstacle : p ∈ G.vertexObstacle v := by
    apply Set.mem_union_left
    apply Set.mem_union_right
    exact hpRange
  exact Set.disjoint_left.mp (G.disjoint_vertexDisk_vertexObstacle v) hp hpObstacle

theorem disjoint_vertexDisk_nonincidentEdgeImage (v : K.Vertex) :
    Disjoint (G.vertexDisk v) (G.nonincidentEdgeImage v) :=
  (G.disjoint_vertexDisk_vertexObstacle v).mono_right Set.subset_union_left

theorem disjoint_vertexDisk_otherVertexImages (v : K.Vertex) :
    Disjoint (G.vertexDisk v) (G.otherVertexImages v) :=
  (G.disjoint_vertexDisk_vertexObstacle v).mono_right Set.subset_union_right

theorem vertexImage_mem_otherVertexImages {v w : K.Vertex} (hvw : w ≠ v) :
    G.vertexImage w ∈ G.otherVertexImages v := by
  apply Set.mem_union_left
  apply Set.mem_iUnion.mpr
  exact ⟨⟨w, hvw⟩, by simp [vertexImageCarrier]⟩

theorem vertexImage_mem_vertexObstacle {v w : K.Vertex} (hvw : w ≠ v) :
    G.vertexImage w ∈ G.vertexObstacle v :=
  Set.mem_union_right _ (G.vertexImage_mem_otherVertexImages hvw)

theorem vertexIsolationRadius_le_quarter_dist {v w : K.Vertex} (hvw : w ≠ v) :
    G.vertexIsolationRadius v ≤ dist (G.vertexImage v) (G.vertexImage w) / 4 := by
  calc
    G.vertexIsolationRadius v ≤
      Metric.infDist (G.vertexImage v) (G.vertexObstacle v) / 4 :=
      (min_le_right _ _).trans (min_le_right _ _)
    _ ≤ dist (G.vertexImage v) (G.vertexImage w) / 4 := by
      gcongr
      exact Metric.infDist_le_dist_of_mem (G.vertexImage_mem_vertexObstacle hvw)

theorem disjoint_vertexDisks {v w : K.Vertex} (hvw : v ≠ w) :
    Disjoint (G.vertexDisk v) (G.vertexDisk w) := by
  apply Metric.closedBall_disjoint_closedBall
  have hdist : 0 < dist (G.vertexImage v) (G.vertexImage w) :=
    dist_pos.mpr fun h ↦ hvw (G.vertexImage_injective h)
  have hv := G.vertexIsolationRadius_le_quarter_dist hvw.symm
  have hw := G.vertexIsolationRadius_le_quarter_dist hvw
  rw [dist_comm (G.vertexImage w) (G.vertexImage v)] at hw
  linarith

/-- The bounded vertex disks remain locally finite in the open chart range. -/
theorem locallyFinite_vertexDisks : LocallyFinite G.vertexDiskInRange := by
  intro x
  by_cases hcomp : G.regionᶜ.Nonempty
  · let d := Metric.infDist x.1 G.regionᶜ
    have hd : 0 < d := by
      apply (G.regionOpen.isClosed_compl.notMem_iff_infDist_pos hcomp).mp
      simpa only [Set.mem_compl_iff, not_not] using x.2
    let U : Set G.region :=
      {p | p.1 ∈ Metric.ball x.1 (d / 8)}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (div_pos hd (by norm_num))), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 (d / 2)
    have hCV : C ⊆ G.region := by
      intro z hz
      by_contra hzV
      have hzVc : z ∈ G.regionᶜ := hzV
      have hle := Metric.infDist_le_dist_of_mem (x := x.1) hzVc
      have hzdist : dist x.1 z ≤ d / 2 := by
        simpa only [C, dist_comm] using (Metric.mem_closedBall.mp hz)
      dsimp only [d] at hd hle hzdist
      linarith
    have hCcompact : IsCompact ((↑) ⁻¹' C : Set G.region) :=
      isCompact_preimage_subtypeVal_of_subset (isCompact_closedBall _ _) hCV
    have hfinite := G.locallyFinite_vertexImages.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro v hv
    obtain ⟨p, hpDisk, hpU⟩ := hv
    let c : G.region := ⟨G.vertexImage v,
      G.map_mem_region ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩⟩
    have hrComp : G.vertexIsolationRadius v ≤
        Metric.infDist (G.vertexImage v) G.regionᶜ / 4 := by
      calc
        G.vertexIsolationRadius v ≤
            Metric.infDist (G.vertexImage v) (G.vertexObstacle v) / 4 :=
          (min_le_right _ _).trans (min_le_right _ _)
        _ ≤ Metric.infDist (G.vertexImage v) G.regionᶜ / 4 := by
          gcongr
          apply Metric.infDist_le_infDist_of_subset _ hcomp
          intro z hz
          apply Set.mem_union_left
          apply Set.mem_union_right
          exact hz
    have hpCenter : dist (G.vertexImage v) x.1 ≤ d / 2 := by
      have hpc : dist (G.vertexImage v) p.1 ≤ G.vertexIsolationRadius v := by
        simpa only [vertexDiskInRange, vertexDisk, Set.mem_ofPred_eq,
          Metric.mem_closedBall, dist_comm] using hpDisk
      have hpx : dist p.1 x.1 < d / 8 := Metric.mem_ball.mp hpU
      have hinf : Metric.infDist (G.vertexImage v) G.regionᶜ ≤
          d + dist (G.vertexImage v) x.1 := by
        exact Metric.infDist_le_infDist_add_dist
      have hmain : dist (G.vertexImage v) x.1 <
          (d + dist (G.vertexImage v) x.1) / 4 + d / 8 := calc
        dist (G.vertexImage v) x.1 ≤
            dist (G.vertexImage v) p.1 + dist p.1 x.1 := dist_triangle _ _ _
        _ < G.vertexIsolationRadius v + d / 8 := add_lt_add_of_le_of_lt hpc hpx
        _ ≤ (d + dist (G.vertexImage v) x.1) / 4 + d / 8 := by
          gcongr
          exact hrComp.trans (div_le_div_of_nonneg_right hinf (by norm_num))
      linarith
    refine ⟨c, ?_, ?_⟩
    · simp [vertexImageCarrierInRange, vertexImageCarrier, c]
    · exact hpCenter
  · have hV : G.region = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      by_contra hz
      exact hcomp ⟨z, hz⟩
    let U : Set G.region := {p | p.1 ∈ Metric.ball x.1 1}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (by norm_num)), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 2
    have hCV : C ⊆ G.region := by rw [hV]; exact Set.subset_univ _
    have hCcompact : IsCompact ((↑) ⁻¹' C : Set G.region) :=
      isCompact_preimage_subtypeVal_of_subset (isCompact_closedBall _ _) hCV
    have hfinite := G.locallyFinite_vertexImages.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro v hv
    obtain ⟨p, hpDisk, hpU⟩ := hv
    let c : G.region := ⟨G.vertexImage v,
      G.map_mem_region ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩⟩
    have hpCenter : dist (G.vertexImage v) x.1 ≤ 2 := by
      have hpc : dist (G.vertexImage v) p.1 ≤ G.vertexIsolationRadius v := by
        simpa only [vertexDiskInRange, vertexDisk, Set.mem_ofPred_eq,
          Metric.mem_closedBall, dist_comm] using hpDisk
      have hpx : dist p.1 x.1 < 1 := Metric.mem_ball.mp hpU
      have hmain : dist (G.vertexImage v) x.1 <
          G.vertexIsolationRadius v + 1 := calc
        dist (G.vertexImage v) x.1 ≤
            dist (G.vertexImage v) p.1 + dist p.1 x.1 := dist_triangle _ _ _
        _ < G.vertexIsolationRadius v + 1 := add_lt_add_of_le_of_lt hpc hpx
      linarith [G.vertexIsolationRadius_le_one v]
    refine ⟨c, ?_, hpCenter⟩
    simp [vertexImageCarrierInRange, vertexImageCarrier, c]

/-! ## Pairwise-separated central edge carriers -/

/-- Open endpoint disks removed before independently perturbing the central part of an edge. -/
def edgeEndpointNeighborhood (e : K.Edge) : Set Plane :=
  Metric.ball (G.vertexImage (K.edgeFirst e))
      (G.vertexIsolationRadius (K.edgeFirst e)) ∪
    Metric.ball (G.vertexImage (K.edgeSecond e))
      (G.vertexIsolationRadius (K.edgeSecond e))

theorem isOpen_edgeEndpointNeighborhood (e : K.Edge) :
    IsOpen (G.edgeEndpointNeighborhood e) :=
  Metric.isOpen_ball.union Metric.isOpen_ball

/-- The compact middle of an edge after removing its two open endpoint disks. -/
def edgeCentralCarrier (e : K.Edge) : Set Plane :=
  G.edgeImage e \ G.edgeEndpointNeighborhood e

theorem isCompact_edgeCentralCarrier (e : K.Edge) :
    IsCompact (G.edgeCentralCarrier e) :=
  (G.isCompact_edgeImage e).diff (G.isOpen_edgeEndpointNeighborhood e)

theorem isClosed_edgeCentralCarrier (e : K.Edge) :
    IsClosed (G.edgeCentralCarrier e) :=
  (G.isCompact_edgeCentralCarrier e).isClosed

theorem edgeCentralCarrier_nonempty (e : K.Edge) :
    (G.edgeCentralCarrier e).Nonempty := by
  let U := Metric.ball (G.vertexImage (K.edgeFirst e))
    (G.vertexIsolationRadius (K.edgeFirst e))
  let V := Metric.ball (G.vertexImage (K.edgeSecond e))
    (G.vertexIsolationRadius (K.edgeSecond e))
  have hUV : Disjoint U V :=
    (G.disjoint_vertexDisks (K.edgeFirst_ne_edgeSecond e)).mono
      Metric.ball_subset_closedBall Metric.ball_subset_closedBall
  apply Set.nonempty_iff_ne_empty.mpr
  intro hcentral
  have hcover : G.edgeImage e ⊆ U ∪ V := by
    intro p hp
    by_contra hpUV
    have hpCentral : p ∈ G.edgeCentralCarrier e := by
      exact ⟨hp, by simpa [edgeEndpointNeighborhood, U, V] using hpUV⟩
    rw [hcentral] at hpCentral
    simp at hpCentral
  have hfirst : (G.edgeImage e ∩ U).Nonempty := by
    refine ⟨G.vertexImage (K.edgeFirst e),
      (G.vertexImage_mem_edgeImage_iff (K.edgeFirst e) e).mpr (K.edgeFirst_mem e), ?_⟩
    exact Metric.mem_ball_self (G.vertexIsolationRadius_pos (K.edgeFirst e))
  have hsecond : (G.edgeImage e ∩ V).Nonempty := by
    refine ⟨G.vertexImage (K.edgeSecond e),
      (G.vertexImage_mem_edgeImage_iff (K.edgeSecond e) e).mpr (K.edgeSecond_mem e), ?_⟩
    exact Metric.mem_ball_self (G.vertexIsolationRadius_pos (K.edgeSecond e))
  obtain ⟨p, -, hpU, hpV⟩ := G.isPreconnected_edgeImage e U V
    Metric.isOpen_ball Metric.isOpen_ball hcover hfirst hsecond
  exact Set.disjoint_left.mp hUV hpU hpV

theorem vertexImage_mem_edgeEndpointNeighborhood {e : K.Edge} {v : K.Vertex}
    (hve : v ∈ e.1) : G.vertexImage v ∈ G.edgeEndpointNeighborhood e := by
  rw [K.edge_eq_pair e] at hve
  simp only [Finset.mem_insert, Finset.mem_singleton] at hve
  rcases hve with rfl | rfl
  · exact Set.mem_union_left _
      (Metric.mem_ball_self (G.vertexIsolationRadius_pos (K.edgeFirst e)))
  · exact Set.mem_union_right _
      (Metric.mem_ball_self (G.vertexIsolationRadius_pos (K.edgeSecond e)))

theorem disjoint_edgeCentralCarriers {e d : K.Edge} (hed : e ≠ d) :
    Disjoint (G.edgeCentralCarrier e) (G.edgeCentralCarrier d) := by
  rw [Set.disjoint_left]
  intro p hpE hpD
  have hpInter : p ∈ G.edgeImage e ∩ G.edgeImage d := ⟨hpE.1, hpD.1⟩
  rw [G.edgeImage_inter_eq_sharedVertices hed] at hpInter
  obtain ⟨v, hve, -, rfl⟩ := hpInter
  exact hpE.2 (G.vertexImage_mem_edgeEndpointNeighborhood hve)

/-- A central edge carrier in the open chart range. -/
def edgeCentralCarrierInRange (e : K.Edge) : Set G.region :=
  {p | p.1 ∈ G.edgeCentralCarrier e}

theorem locallyFinite_edgeCentralCarriers :
    LocallyFinite G.edgeCentralCarrierInRange := by
  apply G.locallyFinite_edgeImages.subset
  intro e p hp
  exact hp.1

/-- The closed union of all central edge carriers other than `e`. -/
def otherEdgeCentralCarriers (e : K.Edge) : Set Plane :=
  (⋃ d : {d : K.Edge // d ≠ e}, G.edgeCentralCarrier d.1) ∪
    G.regionᶜ

theorem isClosed_otherEdgeCentralCarriers (e : K.Edge) :
    IsClosed (G.otherEdgeCentralCarriers e) := by
  apply isClosed_union_compl_of_isClosed_preimage G.regionOpen
  have hlocal : LocallyFinite
      (fun d : {d : K.Edge // d ≠ e} ↦ G.edgeCentralCarrierInRange d.1) :=
    G.locallyFinite_edgeCentralCarriers.comp_injective
      (g := fun d : {d : K.Edge // d ≠ e} ↦ d.1) Subtype.val_injective
  have hclosed : IsClosed
      (⋃ d : {d : K.Edge // d ≠ e}, G.edgeCentralCarrierInRange d.1) := by
    apply hlocal.isClosed_iUnion
    intro d
    exact (G.isClosed_edgeCentralCarrier d.1).preimage
      (continuous_subtype_val : Continuous (Subtype.val : G.region → Plane))
  convert hclosed using 1
  ext p
  simp only [edgeCentralCarrierInRange, Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]

theorem disjoint_edgeCentralCarrier_other (e : K.Edge) :
    Disjoint (G.edgeCentralCarrier e) (G.otherEdgeCentralCarriers e) := by
  rw [Set.disjoint_left]
  intro p hpE hpOther
  rcases hpOther with hpOther | hpOther
  · obtain ⟨d, hpD⟩ := Set.mem_iUnion.mp hpOther
    exact Set.disjoint_left.mp (G.disjoint_edgeCentralCarriers d.2.symm) hpE hpD
  · exact hpOther (by
      obtain ⟨q, hq, rfl⟩ := hpE.1
      exact G.map_mem_region q)

/-- The locally finite union of vertex disks not incident to a fixed edge. -/
def nonincidentVertexDisks (e : K.Edge) : Set Plane :=
  (⋃ v : {v : K.Vertex // v ∉ e.1}, G.vertexDisk v.1) ∪
    G.regionᶜ

theorem isClosed_nonincidentVertexDisks (e : K.Edge) :
    IsClosed (G.nonincidentVertexDisks e) := by
  apply isClosed_union_compl_of_isClosed_preimage G.regionOpen
  have hlocal : LocallyFinite
      (fun v : {v : K.Vertex // v ∉ e.1} ↦ G.vertexDiskInRange v.1) :=
    G.locallyFinite_vertexDisks.comp_injective
      (g := fun v : {v : K.Vertex // v ∉ e.1} ↦ v.1) Subtype.val_injective
  have hclosed : IsClosed
      (⋃ v : {v : K.Vertex // v ∉ e.1}, G.vertexDiskInRange v.1) := by
    apply hlocal.isClosed_iUnion
    intro v
    exact Metric.isClosed_closedBall.preimage
      (continuous_subtype_val : Continuous (Subtype.val : G.region → Plane))
  convert hclosed using 1
  ext p
  simp only [vertexDiskInRange, Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]

theorem disjoint_edgeCentralCarrier_nonincidentVertexDisks (e : K.Edge) :
    Disjoint (G.edgeCentralCarrier e) (G.nonincidentVertexDisks e) := by
  rw [Set.disjoint_left]
  intro p hpEdge hpVertices
  rcases hpVertices with hpVertices | hpVertices
  · obtain ⟨v, hpDisk⟩ := Set.mem_iUnion.mp hpVertices
    have hpNonincident : p ∈ G.nonincidentEdgeImage v.1 := by
      apply Set.mem_union_left
      apply Set.mem_iUnion.mpr
      exact ⟨⟨e, v.2⟩, hpEdge.1⟩
    exact Set.disjoint_left.mp (G.disjoint_vertexDisk_nonincidentEdgeImage v.1)
      hpDisk hpNonincident
  · exact hpVertices (by
      obtain ⟨q, hq, rfl⟩ := hpEdge.1
      exact G.map_mem_region q)

/-- All closed obstacles from which the middle of `e` must be separated. -/
def edgeCentralObstacle (e : K.Edge) : Set Plane :=
  G.otherEdgeCentralCarriers e ∪ G.nonincidentVertexDisks e

theorem isClosed_edgeCentralObstacle (e : K.Edge) :
    IsClosed (G.edgeCentralObstacle e) :=
  (G.isClosed_otherEdgeCentralCarriers e).union
    (G.isClosed_nonincidentVertexDisks e)

theorem disjoint_edgeCentralCarrier_obstacle (e : K.Edge) :
    Disjoint (G.edgeCentralCarrier e) (G.edgeCentralObstacle e) :=
  (G.disjoint_edgeCentralCarrier_other e).union_right
    (G.disjoint_edgeCentralCarrier_nonincidentVertexDisks e)

/-- A positive lower separation scale from one compact central edge carrier to the closed union
of all the others. -/
noncomputable def centralSeparationNN (e : K.Edge) : NNReal :=
  Classical.choose (Metric.exists_pos_forall_lt_edist
    (G.isCompact_edgeCentralCarrier e) (G.isClosed_edgeCentralObstacle e)
    (G.disjoint_edgeCentralCarrier_obstacle e))

theorem centralSeparationNN_pos (e : K.Edge) : 0 < G.centralSeparationNN e :=
  (Classical.choose_spec (Metric.exists_pos_forall_lt_edist
    (G.isCompact_edgeCentralCarrier e) (G.isClosed_edgeCentralObstacle e)
    (G.disjoint_edgeCentralCarrier_obstacle e))).1

theorem centralSeparationNN_lt_dist (e : K.Edge)
    {x y : Plane} (hx : x ∈ G.edgeCentralCarrier e)
    (hy : y ∈ G.edgeCentralObstacle e) :
    (G.centralSeparationNN e : ℝ) < dist x y := by
  have h := (Classical.choose_spec (Metric.exists_pos_forall_lt_edist
    (G.isCompact_edgeCentralCarrier e) (G.isClosed_edgeCentralObstacle e)
    (G.disjoint_edgeCentralCarrier_obstacle e))).2 x hx y hy
  simpa [centralSeparationNN, edist_dist] using h

/-- A bounded quarter-separation tube radius for one central edge carrier.  The additional
endpoint-distance cap is the quantitative ingredient used in Chapter 6: once the charted edge
has small diameter, every point of its replacement arc is correspondingly close to that edge. -/
noncomputable def centralTubeRadius (e : K.Edge) : ℝ :=
  min (G.edgeApproximationControl e)
    (min (min 1 ((G.centralSeparationNN e : ℝ) / 4))
      (dist (G.vertexImage (K.edgeFirst e))
        (G.vertexImage (K.edgeSecond e)) / 4))

theorem centralTubeRadius_pos (e : K.Edge) : 0 < G.centralTubeRadius e := by
  rw [centralTubeRadius]
  apply lt_min (G.edgeApproximationControl_pos e)
  apply lt_min
  · apply lt_min (by norm_num)
    exact div_pos (by exact_mod_cast G.centralSeparationNN_pos e) (by norm_num)
  · apply div_pos
    · exact dist_pos.mpr fun h ↦ K.edgeFirst_ne_edgeSecond e
        (G.vertexImage_injective h)
    · norm_num

theorem centralTubeRadius_le_control (e : K.Edge) :
    G.centralTubeRadius e ≤ G.edgeApproximationControl e := by
  exact min_le_left _ _

theorem centralTubeRadius_le_one (e : K.Edge) : G.centralTubeRadius e ≤ 1 :=
  (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))

theorem centralTubeRadius_le_quarter_endpointDist (e : K.Edge) :
    G.centralTubeRadius e ≤
      dist (G.vertexImage (K.edgeFirst e))
        (G.vertexImage (K.edgeSecond e)) / 4 :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem four_mul_centralTubeRadius_lt_dist {e d : K.Edge} (hed : e ≠ d)
    {x y : Plane} (hx : x ∈ G.edgeCentralCarrier e)
    (hy : y ∈ G.edgeCentralCarrier d) :
    4 * G.centralTubeRadius e < dist x y := by
  have hyOther : y ∈ G.otherEdgeCentralCarriers e := by
    apply Set.mem_union_left
    apply Set.mem_iUnion.mpr
    exact ⟨⟨d, hed.symm⟩, hy⟩
  have hsep := G.centralSeparationNN_lt_dist e hx
    (Set.mem_union_left _ hyOther)
  have hrle : G.centralTubeRadius e ≤ (G.centralSeparationNN e : ℝ) / 4 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  linarith

/-- The open tube in which the central part of edge `e` may be polygonalized. -/
def edgeCentralTube (e : K.Edge) : Set Plane :=
  Metric.thickening (G.centralTubeRadius e) (G.edgeCentralCarrier e)

theorem disjoint_edgeCentralTube_nonincidentVertexDisk (e : K.Edge)
    (v : K.Vertex) (hve : v ∉ e.1) :
    Disjoint (G.edgeCentralTube e) (G.vertexDisk v) := by
  rw [Set.disjoint_left]
  intro z hzTube hzDisk
  obtain ⟨x, hxCentral, hzx⟩ := Metric.mem_thickening_iff.mp hzTube
  have hzObstacle : z ∈ G.edgeCentralObstacle e := by
    apply Set.mem_union_right
    apply Set.mem_union_left
    apply Set.mem_iUnion.mpr
    exact ⟨⟨v, hve⟩, hzDisk⟩
  have hsep := G.centralSeparationNN_lt_dist e hxCentral hzObstacle
  have hrle : G.centralTubeRadius e ≤ (G.centralSeparationNN e : ℝ) / 4 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdist : dist x z < G.centralTubeRadius e := by
    simpa [dist_comm] using hzx
  have hsepNonneg : 0 ≤ (G.centralSeparationNN e : ℝ) := NNReal.coe_nonneg _
  linarith

theorem disjoint_edgeCentralTubes {e d : K.Edge} (hed : e ≠ d) :
    Disjoint (G.edgeCentralTube e) (G.edgeCentralTube d) := by
  rw [Set.disjoint_left]
  intro z hzE hzD
  obtain ⟨x, hx, hzx⟩ := Metric.mem_thickening_iff.mp hzE
  obtain ⟨y, hy, hzy⟩ := Metric.mem_thickening_iff.mp hzD
  have hE := G.four_mul_centralTubeRadius_lt_dist hed hx hy
  have hD := G.four_mul_centralTubeRadius_lt_dist hed.symm hy hx
  rw [dist_comm y x] at hD
  have htri : dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
  have hxz : dist x z < G.centralTubeRadius e := by simpa [dist_comm] using hzx
  have hdistRad : dist x y <
      G.centralTubeRadius e + G.centralTubeRadius d :=
    htri.trans_lt (add_lt_add hxz hzy)
  have hre : G.centralTubeRadius e < dist x y / 4 := by linarith
  have hrd : G.centralTubeRadius d < dist x y / 4 := by linarith
  have hradDist : G.centralTubeRadius e + G.centralTubeRadius d < dist x y := by
    have hdistNonneg : 0 ≤ dist x y := dist_nonneg
    linarith
  exact (lt_asymm hdistRad hradDist)

/-- A central perturbation tube regarded as a subset of the open chart range. -/
def edgeCentralTubeInRange (e : K.Edge) : Set G.region :=
  {p | p.1 ∈ G.edgeCentralTube e}

theorem edgeCentralTube_subset_range (e : K.Edge) :
    G.edgeCentralTube e ⊆ G.region := by
  intro z hzTube
  by_contra hzRange
  obtain ⟨x, hxCentral, hzx⟩ := Metric.mem_thickening_iff.mp hzTube
  have hzObstacle : z ∈ G.edgeCentralObstacle e := by
    apply Set.mem_union_left
    apply Set.mem_union_right
    exact hzRange
  have hsep := G.centralSeparationNN_lt_dist e hxCentral hzObstacle
  have hrle : G.centralTubeRadius e ≤ (G.centralSeparationNN e : ℝ) / 4 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdist : dist x z < G.centralTubeRadius e := by
    simpa [dist_comm] using hzx
  have hsepNonneg : 0 ≤ (G.centralSeparationNN e : ℝ) := NNReal.coe_nonneg _
  linarith

theorem centralTubeRadius_le_quarter_infDist_compl (e : K.Edge)
    (hcomp : G.regionᶜ.Nonempty) {x : Plane}
    (hx : x ∈ G.edgeCentralCarrier e) :
    G.centralTubeRadius e ≤
      Metric.infDist x G.regionᶜ / 4 := by
  obtain ⟨y, hyComp, hyDist⟩ :=
    G.regionOpen.isClosed_compl.exists_infDist_eq_dist hcomp x
  have hyObstacle : y ∈ G.edgeCentralObstacle e := by
    apply Set.mem_union_left
    apply Set.mem_union_right
    exact hyComp
  have hsep := G.centralSeparationNN_lt_dist e hx hyObstacle
  calc
    G.centralTubeRadius e ≤ (G.centralSeparationNN e : ℝ) / 4 :=
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    _ ≤ Metric.infDist x G.regionᶜ / 4 := by
      rw [hyDist]
      gcongr

/-- The bounded central tubes remain locally finite in the open chart range. -/
theorem locallyFinite_edgeCentralTubes : LocallyFinite G.edgeCentralTubeInRange := by
  intro x
  by_cases hcomp : G.regionᶜ.Nonempty
  · let d := Metric.infDist x.1 G.regionᶜ
    have hd : 0 < d := by
      apply (G.regionOpen.isClosed_compl.notMem_iff_infDist_pos hcomp).mp
      simpa only [Set.mem_compl_iff, not_not] using x.2
    let U : Set G.region :=
      {p | p.1 ∈ Metric.ball x.1 (d / 8)}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (div_pos hd (by norm_num))), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 (d / 2)
    have hCV : C ⊆ G.region := by
      intro z hz
      by_contra hzV
      have hle := Metric.infDist_le_dist_of_mem (x := x.1)
        (show z ∈ G.regionᶜ from hzV)
      have hzdist : dist x.1 z ≤ d / 2 := by
        simpa only [C, dist_comm] using (Metric.mem_closedBall.mp hz)
      dsimp only [d] at hd hle hzdist
      linarith
    have hCcompact : IsCompact (((↑) ⁻¹' C : Set G.region)) :=
      isCompact_preimage_subtypeVal_of_subset (isCompact_closedBall _ _) hCV
    have hfinite :=
      G.locallyFinite_edgeCentralCarriers.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro e he
    obtain ⟨z, hzTube, hzU⟩ := he
    obtain ⟨p, hpCentral, hzp⟩ := Metric.mem_thickening_iff.mp hzTube
    let c : G.region := ⟨p, by
      obtain ⟨q, hq, rfl⟩ := hpCentral.1
      exact G.map_mem_region q⟩
    have hrComp := G.centralTubeRadius_le_quarter_infDist_compl e hcomp hpCentral
    have hpCenter : dist p x.1 ≤ d / 2 := by
      have hpz : dist p z.1 < G.centralTubeRadius e := by
        simpa [dist_comm] using hzp
      have hzx : dist z.1 x.1 < d / 8 := Metric.mem_ball.mp hzU
      have hinf : Metric.infDist p G.regionᶜ ≤
          d + dist p x.1 := Metric.infDist_le_infDist_add_dist
      have hmain : dist p x.1 < (d + dist p x.1) / 4 + d / 8 := calc
        dist p x.1 ≤ dist p z.1 + dist z.1 x.1 := dist_triangle _ _ _
        _ < G.centralTubeRadius e + d / 8 := add_lt_add hpz hzx
        _ ≤ (d + dist p x.1) / 4 + d / 8 := by
          gcongr
          exact hrComp.trans (div_le_div_of_nonneg_right hinf (by norm_num))
      linarith
    refine ⟨c, hpCentral, ?_⟩
    exact hpCenter
  · have hV : G.region = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      by_contra hz
      exact hcomp ⟨z, hz⟩
    let U : Set G.region := {p | p.1 ∈ Metric.ball x.1 1}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (by norm_num)), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 2
    have hCV : C ⊆ G.region := by rw [hV]; exact Set.subset_univ _
    have hCcompact : IsCompact (((↑) ⁻¹' C : Set G.region)) :=
      isCompact_preimage_subtypeVal_of_subset (isCompact_closedBall _ _) hCV
    have hfinite :=
      G.locallyFinite_edgeCentralCarriers.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro e he
    obtain ⟨z, hzTube, hzU⟩ := he
    obtain ⟨p, hpCentral, hzp⟩ := Metric.mem_thickening_iff.mp hzTube
    let c : G.region := ⟨p, by
      obtain ⟨q, hq, rfl⟩ := hpCentral.1
      exact G.map_mem_region q⟩
    have hpCenter : dist p x.1 ≤ 2 := by
      have hpz : dist p z.1 < G.centralTubeRadius e := by
        simpa [dist_comm] using hzp
      have hzx : dist z.1 x.1 < 1 := Metric.mem_ball.mp hzU
      have hmain : dist p x.1 < G.centralTubeRadius e + 1 :=
        (dist_triangle p z.1 x.1).trans_lt (add_lt_add hpz hzx)
      linarith [G.centralTubeRadius_le_one e]
    exact ⟨c, hpCentral, hpCenter⟩

/-! ## Last-exit trims and central polygonal arcs -/

/-- A globally defined charted edge curve, clamped to the unit interval. -/
noncomputable def chartEdgeCurve (e : K.Edge) (t : ℝ) : Plane :=
  G.chartEdgePath e (Set.projIcc 0 1 zero_le_one t)

theorem continuous_chartEdgeCurve (e : K.Edge) : Continuous (G.chartEdgeCurve e) :=
  (G.continuous_chartEdgePath e).comp continuous_projIcc

theorem chartEdgeCurve_eq_of_mem (e : K.Edge) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    G.chartEdgeCurve e t = G.chartEdgePath e ⟨t, ht⟩ := by
  apply congrArg (G.chartEdgePath e)
  apply Subtype.ext
  rw [Set.coe_projIcc]
  simp [ht.1, ht.2]

@[simp] theorem chartEdgeCurve_zero (e : K.Edge) :
    G.chartEdgeCurve e 0 = G.vertexImage (K.edgeFirst e) := by
  rw [G.chartEdgeCurve_eq_of_mem e (by simp)]
  exact G.chartEdgePath_zero e

@[simp] theorem chartEdgeCurve_one (e : K.Edge) :
    G.chartEdgeCurve e 1 = G.vertexImage (K.edgeSecond e) := by
  rw [G.chartEdgeCurve_eq_of_mem e (by simp)]
  exact G.chartEdgePath_one e

/-- Ordered exits from the two (possibly differently sized) endpoint disks. -/
structure EdgeTrimData (e : K.Edge) where
  /-- The `left` declaration. -/
  left : ℝ
  /-- The `right` declaration. -/
  right : ℝ
  left_pos : 0 < left
  left_lt_right : left < right
  right_lt_one : right < 1
  left_on_sphere : dist (G.chartEdgeCurve e left)
    (G.vertexImage (K.edgeFirst e)) = G.vertexIsolationRadius (K.edgeFirst e)
  right_on_sphere : dist (G.chartEdgeCurve e right)
    (G.vertexImage (K.edgeSecond e)) = G.vertexIsolationRadius (K.edgeSecond e)
  after_left : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t →
    G.chartEdgeCurve e t ∉ G.vertexDisk (K.edgeFirst e)
  before_right : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t → t < right →
    G.chartEdgeCurve e t ∉ G.vertexDisk (K.edgeSecond e)

theorem exists_edgeTrimData (e : K.Edge) : Nonempty (G.EdgeTrimData e) := by
  have hends : K.edgeFirst e ≠ K.edgeSecond e := K.edgeFirst_ne_edgeSecond e
  have hsecondBall : G.vertexImage (K.edgeSecond e) ∈
      G.vertexDisk (K.edgeSecond e) :=
    Metric.mem_closedBall_self (G.vertexIsolationRadius_pos (K.edgeSecond e)).le
  have hfinishOutside : G.chartEdgeCurve e 1 ∉ G.vertexDisk (K.edgeFirst e) := by
    rw [G.chartEdgeCurve_one e]
    intro hfirstBall
    exact Set.disjoint_left.mp (G.disjoint_vertexDisks hends)
      hfirstBall hsecondBall
  obtain ⟨L⟩ := exists_lastExitData
    (G.vertexIsolationRadius_pos (K.edgeFirst e))
    (G.continuous_chartEdgeCurve e).continuousOn
    (G.chartEdgeCurve_zero e) hfinishOutside
  let a := L.parameter
  let q : ℝ → ℝ := fun s => 1 - (1 - a) * s
  let rho : ℝ → Plane := fun s => G.chartEdgeCurve e (q s)
  have hqMaps : Set.MapsTo q (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hqeq : q s = (1 - s) + s * a := by
      dsimp [q]
      ring
    rw [hqeq]
    constructor
    · exact add_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hs.1 L.parameter_mem.1)
    · have hsa : s * a ≤ s * 1 := mul_le_mul_of_nonneg_left L.parameter_mem.2 hs.1
      linarith
  have hqcont : Continuous q := by fun_prop
  have hrhoCont : ContinuousOn rho (Set.Icc (0 : ℝ) 1) :=
    (G.continuous_chartEdgeCurve e).continuousOn.comp hqcont.continuousOn hqMaps
  have hrhoZero : rho 0 = G.vertexImage (K.edgeSecond e) := by
    simp [rho, q]
  have hleftFirstBall : G.chartEdgeCurve e a ∈ G.vertexDisk (K.edgeFirst e) := by
    rw [vertexDisk, Metric.mem_closedBall]
    exact L.on_sphere.le
  have hleftOutsideSecond : rho 1 ∉ G.vertexDisk (K.edgeSecond e) := by
    have hrhoOne : rho 1 = G.chartEdgeCurve e a := by simp [rho, q, a]
    rw [hrhoOne]
    intro hsecond
    exact Set.disjoint_left.mp (G.disjoint_vertexDisks hends)
      hleftFirstBall hsecond
  obtain ⟨R⟩ := exists_lastExitData
    (G.vertexIsolationRadius_pos (K.edgeSecond e)) hrhoCont hrhoZero hleftOutsideSecond
  let b : ℝ := q R.parameter
  have hab : a < b := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_lt_one]
  have hb1 : b < 1 := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_pos]
  refine ⟨{
    left := a
    right := b
    left_pos := L.parameter_pos
    left_lt_right := hab
    right_lt_one := hb1
    left_on_sphere := L.on_sphere
    right_on_sphere := R.on_sphere
    after_left := L.after_exit
    before_right := ?_ }⟩
  intro t ht hat htb
  have ha1 : a < 1 := L.parameter_lt_one
  let s : ℝ := (1 - t) / (1 - a)
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [s]
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha1.le)
    · apply (div_le_one (sub_pos.mpr ha1)).mpr
      linarith
  have hRs : R.parameter < s := by
    dsimp [b, q] at htb
    dsimp [s]
    apply (lt_div_iff₀ (sub_pos.mpr ha1)).mpr
    nlinarith
  have hrhos : rho s = G.chartEdgeCurve e t := by
    dsimp [rho, q, s]
    congr 2
    rw [mul_div_cancel₀ (1 - t) (sub_ne_zero.mpr ha1.ne')]
    ring
  rw [← hrhos]
  exact R.after_exit s hs hRs

/-- A fixed last-exit trim on every locally finite edge. -/
noncomputable def edgeTrim (e : K.Edge) : G.EdgeTrimData e :=
  Classical.choice (G.exists_edgeTrimData e)

namespace EdgeTrimData

variable {G} {e : K.Edge}

/-- The connected compact subarc between the two selected exits. -/
def carrier (T : G.EdgeTrimData e) : Set Plane :=
  G.chartEdgeCurve e '' Set.Icc T.left T.right

theorem isCompact_carrier (T : G.EdgeTrimData e) : IsCompact T.carrier := by
  apply isCompact_Icc.image_of_continuousOn
  exact (G.continuous_chartEdgeCurve e).continuousOn

theorem isPreconnected_carrier (T : G.EdgeTrimData e) : IsPreconnected T.carrier := by
  apply IsPreconnected.image (convex_Icc _ _).isPreconnected
  exact (G.continuous_chartEdgeCurve e).continuousOn

theorem left_mem_carrier (T : G.EdgeTrimData e) :
    G.chartEdgeCurve e T.left ∈ T.carrier :=
  ⟨_, ⟨le_rfl, T.left_lt_right.le⟩, rfl⟩

theorem right_mem_carrier (T : G.EdgeTrimData e) :
    G.chartEdgeCurve e T.right ∈ T.carrier :=
  ⟨_, ⟨T.left_lt_right.le, le_rfl⟩, rfl⟩

theorem carrier_subset_edgeCentralCarrier (T : G.EdgeTrimData e) :
    T.carrier ⊆ G.edgeCentralCarrier e := by
  rintro p ⟨t, ht, rfl⟩
  have htUnit : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨T.left_pos.le.trans ht.1, ht.2.trans T.right_lt_one.le⟩
  have hpEdge : G.chartEdgeCurve e t ∈ G.edgeImage e := by
    rw [G.chartEdgeCurve_eq_of_mem e htUnit]
    exact G.chartEdgePath_mem_edgeImage e ⟨t, htUnit⟩
  refine ⟨hpEdge, ?_⟩
  rw [edgeEndpointNeighborhood, Set.mem_union]
  apply not_or_intro
  · rw [Metric.mem_ball]
    by_cases hlt : T.left < t
    · exact fun hball => T.after_left t htUnit hlt (Metric.mem_closedBall.mpr hball.le)
    · have hteq : t = T.left := le_antisymm (not_lt.mp hlt) ht.1
      rw [hteq, T.left_on_sphere]
      exact lt_irrefl _
  · rw [Metric.mem_ball]
    by_cases hlt : T.left < t
    · by_cases htr : t < T.right
      · exact fun hball => T.before_right t htUnit hlt htr
          (Metric.mem_closedBall.mpr hball.le)
      · have hteq : t = T.right := le_antisymm ht.2 (not_lt.mp htr)
        rw [hteq, T.right_on_sphere]
        exact lt_irrefl _
    · have hteq : t = T.left := le_antisymm (not_lt.mp hlt) ht.1
      intro hball
      have hfirst : G.chartEdgeCurve e T.left ∈ G.vertexDisk (K.edgeFirst e) := by
        rw [vertexDisk, Metric.mem_closedBall, T.left_on_sphere]
      have hsecond : G.chartEdgeCurve e T.left ∈ G.vertexDisk (K.edgeSecond e) := by
        rw [vertexDisk, Metric.mem_closedBall]
        simpa [hteq] using hball.le
      exact Set.disjoint_left.mp (G.disjoint_vertexDisks (K.edgeFirst_ne_edgeSecond e))
        hfirst hsecond

end EdgeTrimData

/-- Ordered exits for an arc whose endpoints lie on boundary circles of possibly different
radii.  The finite graph layer uses one common radius; local finiteness naturally requires a
radius depending on the vertex. -/
structure TwoRadiusBoundaryExitData (gamma : ℝ → Plane)
    (first second : Plane) (firstRadius secondRadius : ℝ) where
  /-- The `left` declaration. -/
  left : ℝ
  /-- The `right` declaration. -/
  right : ℝ
  left_nonneg : 0 ≤ left
  left_lt_right : left < right
  right_le_one : right ≤ 1
  left_on_sphere : dist (gamma left) first = firstRadius
  right_on_sphere : dist (gamma right) second = secondRadius
  after_left : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t →
    gamma t ∉ Metric.closedBall first firstRadius
  before_right : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t → t < right →
    gamma t ∉ Metric.closedBall second secondRadius

theorem exists_twoRadiusBoundaryExitData {gamma : ℝ → Plane} {first second : Plane}
    {firstRadius secondRadius : ℝ}
    (hfirstRadius : 0 < firstRadius) (hsecondRadius : 0 < secondRadius)
    (hcont : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    (hstart : dist (gamma 0) first = firstRadius)
    (hfinish : dist (gamma 1) second = secondRadius)
    (hdisjoint : Disjoint (Metric.closedBall first firstRadius)
      (Metric.closedBall second secondRadius)) :
    Nonempty (TwoRadiusBoundaryExitData gamma first second firstRadius secondRadius) := by
  have hfinishOutside : gamma 1 ∉ Metric.closedBall first firstRadius := by
    intro hfirst
    exact Set.disjoint_left.mp hdisjoint hfirst
      (Metric.mem_closedBall.mpr hfinish.le)
  obtain ⟨L⟩ := exists_weakLastExitData hfirstRadius hcont hstart hfinishOutside
  let a := L.parameter
  let q : ℝ → ℝ := fun s => 1 - (1 - a) * s
  let rho : ℝ → Plane := fun s => gamma (q s)
  have hqMaps : Set.MapsTo q (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hqeq : q s = (1 - s) + s * a := by dsimp [q]; ring
    rw [hqeq]
    constructor
    · exact add_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hs.1 L.parameter_mem.1)
    · have hsa : s * a ≤ s * 1 := mul_le_mul_of_nonneg_left L.parameter_mem.2 hs.1
      linarith
  have hrhoCont : ContinuousOn rho (Set.Icc (0 : ℝ) 1) := by
    exact hcont.comp (by fun_prop) hqMaps
  have hrhoStart : dist (rho 0) second = secondRadius := by
    simp [rho, q, hfinish]
  have hrhoFinishOutside : rho 1 ∉ Metric.closedBall second secondRadius := by
    have hrhoOne : rho 1 = gamma a := by simp [rho, q, a]
    rw [hrhoOne]
    intro hsecond
    exact Set.disjoint_left.mp hdisjoint
      (Metric.mem_closedBall.mpr L.on_sphere.le) hsecond
  obtain ⟨R⟩ := exists_weakLastExitData hsecondRadius hrhoCont hrhoStart hrhoFinishOutside
  let b : ℝ := q R.parameter
  have hab : a < b := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_lt_one]
  have hb1 : b ≤ 1 := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_mem.1]
  refine ⟨{
    left := a
    right := b
    left_nonneg := L.parameter_mem.1
    left_lt_right := hab
    right_le_one := hb1
    left_on_sphere := L.on_sphere
    right_on_sphere := R.on_sphere
    after_left := L.after_exit
    before_right := ?_ }⟩
  intro t ht hat htb
  have ha1 : a < 1 := L.parameter_lt_one
  let s : ℝ := (1 - t) / (1 - a)
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [s]
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha1.le)
    · apply (div_le_one (sub_pos.mpr ha1)).mpr
      linarith
  have hRs : R.parameter < s := by
    dsimp [b, q] at htb
    dsimp [s]
    apply (lt_div_iff₀ (sub_pos.mpr ha1)).mpr
    nlinarith
  have hrhos : rho s = gamma t := by
    dsimp [rho, q, s]
    congr 2
    rw [mul_div_cancel₀ (1 - t) (sub_ne_zero.mpr ha1.ne')]
    ring
  rw [← hrhos]
  exact R.after_exit s hs hRs

/-- A finite PL parameterization of a simple polygonal arc.  The carrier is deliberately
abstract: Chapter 6 can produce it either from a broken line or directly as the PL image of a
finely subdivided source interval. -/
structure PLArcParameterization (carrier : Set Plane) (start finish : Plane) where
  /-- The `length` declaration. -/
  length : ℕ
  length_pos : 0 < length
  /-- The `source` declaration. -/
  source : PlaneComplex
  /-- The `map` declaration. -/
  map : Plane → Plane
  /-- The `curve` declaration. -/
  curve : ℝ → Plane
  source_support : source.support =
    segment ℝ (planePoint 0 0) (planePoint length 0)
  map_isPL : IsPLOn source map
  map_injectiveOn : Set.InjOn map source.support
  map_affineOn : ∀ s ∈ source.simplexes, IsAffineOn map (source.cellCarrier s)
  source_card_le_two : ∀ s ∈ source.simplexes, s.card ≤ 2
  source_vertex_mem : ∀ v, source.position v ∈ source.support
  curve_eq : ∀ t, curve t = map (planePoint (length * t) 0)
  continuousOn : ContinuousOn curve (Set.Icc (0 : ℝ) 1)
  injectiveOn : Set.InjOn curve (Set.Icc (0 : ℝ) 1)
  image_eq : curve '' Set.Icc (0 : ℝ) 1 = carrier
  start_eq : curve 0 = start
  finish_eq : curve 1 = finish

/-- Package a finite PL embedding of the standard unit segment as an abstract PL arc. -/
theorem exists_plArcParameterization_of_unitSegment
    (S : PlaneComplex)
    (hS : S.support = segment ℝ (planePoint 0 0) (planePoint 1 0))
    (hgraph : ∀ s ∈ S.simplexes, s.card ≤ 2)
    {f : Plane → Plane} (hpl : IsPLOn S f) (hinj : Set.InjOn f S.support) :
    ∃ P : PLArcParameterization (f '' S.support)
        (f (planePoint 0 0)) (f (planePoint 1 0)),
      P.length = 1 ∧ P.map = f := by
  have hplS := hpl
  obtain ⟨L, hLsub, hLaffine⟩ := hpl
  let A := PlaneComplex.active L
  let curve : ℝ → Plane := fun t ↦ f (planePoint t 0)
  have haxisLine : (fun t : ℝ ↦ planePoint t 0) =
      AffineMap.lineMap (planePoint 0 0) (planePoint 1 0) := by
    funext t
    ext k
    fin_cases k <;>
      simp [planePoint, AffineMap.lineMap_apply_module]
  have haxisImage : (fun t : ℝ ↦ planePoint t 0) '' Set.Icc (0 : ℝ) 1 =
      segment ℝ (planePoint 0 0) (planePoint 1 0) := by
    rw [haxisLine, segment_eq_image_lineMap]
  have haxisMaps : Set.MapsTo (fun t : ℝ ↦ planePoint t 0)
      (Set.Icc (0 : ℝ) 1) S.support := by
    rw [hS]
    exact Set.mapsTo_iff_image_subset.mpr haxisImage.le
  have hcurveCont : ContinuousOn curve (Set.Icc (0 : ℝ) 1) :=
    hplS.continuousOn.comp
      (by rw [haxisLine]; exact AffineMap.lineMap_continuous.continuousOn) haxisMaps
  have haxisInj : Set.InjOn (fun t : ℝ ↦ planePoint t 0) (Set.Icc (0 : ℝ) 1) := by
    intro x _ y _ hxy
    exact congrArg (fun p : Plane ↦ p 0) hxy
  have hcurveInj : Set.InjOn curve (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply haxisInj hx hy
    exact hinj (haxisMaps hx) (haxisMaps hy) hxy
  refine ⟨{
    length := 1
    length_pos := by norm_num
    source := A
    map := f
    curve := curve
    source_support := by
      change (PlaneComplex.active L).support = _
      rw [L.active_support, hLsub.1, hS]
      norm_num
    map_isPL := by
      refine ⟨A, PlaneComplex.Subdivides.refl A, ?_⟩
      intro s hs
      exact (L.active_cellCarrier s).symm ▸
        hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs)
    map_injectiveOn := by
      intro x hx y hy hxy
      apply hinj
      · rw [← hLsub.1]
        simpa only [A, L.active_support] using hx
      · rw [← hLsub.1]
        simpa only [A, L.active_support] using hy
      · exact hxy
    map_affineOn := by
      intro s hs
      exact (L.active_cellCarrier s).symm ▸
        hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs)
    source_card_le_two := by
      intro s hs
      obtain ⟨t, ht, hst⟩ := (PlaneComplex.active_subdivides_left hLsub).2 s hs
      exact PlaneComplex.card_le_two_of_cellCarrier_subset_face hs ht (hgraph t ht) hst
    source_vertex_mem := by
      intro v
      change L.position v.1 ∈ (PlaneComplex.active L).support
      rw [L.active_support]
      exact v.2
    curve_eq := by intro t; simp [curve, planePoint]
    continuousOn := hcurveCont
    injectiveOn := hcurveInj
    image_eq := by
      rw [show curve '' Set.Icc (0 : ℝ) 1 =
          f '' ((fun t : ℝ ↦ planePoint t 0) '' Set.Icc (0 : ℝ) 1) by
        exact (Set.image_image f (fun t : ℝ ↦ planePoint t 0) _).symm,
        haxisImage, ← hS]
    start_eq := by simp [curve]
    finish_eq := by simp [curve] }, rfl, rfl⟩

/-- A one-edge broken line on the standard unit segment. -/
def unitSegmentChain : BrokenLineData (Set.univ : Set Plane) where
  n := 1
  vertex := ![planePoint 0 0, planePoint 1 0]
  segment_subset := by
    intro i
    fin_cases i
    exact Set.subset_univ _

/-- The canonical finite graph complex supported on the standard unit segment. -/
noncomputable def unitSegmentComplex : PlaneComplex :=
  unitSegmentChain.segmentComplex ⟨0, by simp [unitSegmentChain]⟩

theorem unitSegmentComplex_support :
    unitSegmentComplex.support =
      segment ℝ (planePoint 0 0) (planePoint 1 0) := by
  rw [unitSegmentComplex, unitSegmentChain.segmentComplex_support]
  rfl

theorem unitSegmentComplex_graph (s : Finset unitSegmentComplex.Vertex)
    (hs : s ∈ unitSegmentComplex.simplexes) : s.card ≤ 2 := by
  apply unitSegmentComplex.card_le_two_of_vertices_mem_segment hs
  · intro v hv
    rw [← unitSegmentComplex_support]
    exact unitSegmentComplex.cellCarrier_subset_support hs
      (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)

theorem unitSegment_mem_bounds {p : Plane}
    (hp : p ∈ unitSegmentComplex.support) :
    p 1 = 0 ∧ 0 ≤ p 0 ∧ p 0 ≤ 1 := by
  rw [unitSegmentComplex_support, segment_eq_image_lineMap] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  constructor
  · simp [AffineMap.lineMap_apply_module, planePoint]
  · constructor
    · simpa [AffineMap.lineMap_apply_module, planePoint] using ht.1
    · simpa [AffineMap.lineMap_apply_module, planePoint] using ht.2

theorem planePoint_mem_unitSegment {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    planePoint t 0 ∈ unitSegmentComplex.support := by
  rw [unitSegmentComplex_support, segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  ext i
  fin_cases i <;> simp [AffineMap.lineMap_apply_module, planePoint]

/-- The source vertex at the left endpoint of the unit segment. -/
noncomputable def unitSegmentFirstVertex : unitSegmentComplex.Vertex :=
  unitSegmentChain.arrangementVertex
    (Fin.castSucc ⟨0, by simp [unitSegmentChain]⟩)

/-- The source vertex at the right endpoint of the unit segment. -/
noncomputable def unitSegmentSecondVertex : unitSegmentComplex.Vertex :=
  unitSegmentChain.arrangementVertex
    (Fin.succ ⟨0, by simp [unitSegmentChain]⟩)

theorem unitSegmentFirstVertex_position :
    unitSegmentComplex.position unitSegmentFirstVertex = planePoint 0 0 := by
  change unitSegmentChain.arrangementMesh.toPlaneComplex.position
      (unitSegmentChain.arrangementVertex
        (Fin.castSucc ⟨0, by simp [unitSegmentChain]⟩)) = planePoint 0 0
  simpa [unitSegmentChain] using
    unitSegmentChain.arrangementVertex_position
      (Fin.castSucc ⟨0, by simp [unitSegmentChain]⟩)

theorem unitSegmentSecondVertex_position :
    unitSegmentComplex.position unitSegmentSecondVertex = planePoint 1 0 := by
  change unitSegmentChain.arrangementMesh.toPlaneComplex.position
      (unitSegmentChain.arrangementVertex
        (Fin.succ ⟨0, by simp [unitSegmentChain]⟩)) = planePoint 1 0
  simpa [unitSegmentChain] using
    unitSegmentChain.arrangementVertex_position
      (Fin.succ ⟨0, by simp [unitSegmentChain]⟩)

namespace BrokenLineData

/-- The standard finite PL parameterization carried by a loop-resolved broken line. -/
theorem exists_plArcParameterization {U : Set Plane} (B : BrokenLineData U)
    (hne : B.start ≠ B.finish) :
    Nonempty (PLArcParameterization B.resolvedCarrier B.start B.finish) := by
  obtain ⟨S, F, hSsupport, hpl, hSgraph, hFinj, himage, hstart, hfinish⟩ :=
    B.exists_PL_segment_model
  have hlength : 0 < B.resolvedWalk.length := by
    by_contra hnot
    have hzero : B.resolvedWalk.length = 0 := Nat.eq_zero_of_not_pos hnot
    apply hne
    rw [← B.resolvedVertex_start, ← B.resolvedVertex_finish]
    congr 2
    exact Fin.ext (by simp [hzero])
  have hplS := hpl
  obtain ⟨L, hLsub, hLaffine⟩ := hpl
  let n : ℝ := B.resolvedWalk.length
  let axis : ℝ → Plane := fun t => planePoint (n * t) 0
  let curve : ℝ → Plane := fun t => F (axis t)
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hlength
  have haxisLine : axis = AffineMap.lineMap (planePoint 0 0) (planePoint n 0) := by
    funext t
    ext k
    fin_cases k <;> simp [axis, planePoint, AffineMap.lineMap_apply_module, mul_comm]
  have haxisImage : axis '' Set.Icc (0 : ℝ) 1 =
      segment ℝ (planePoint 0 0) (planePoint n 0) := by
    rw [haxisLine, segment_eq_image_lineMap]
  have haxisMaps : Set.MapsTo axis (Set.Icc (0 : ℝ) 1) S.support := by
    rw [hSsupport]
    simpa [n] using Set.mapsTo_iff_image_subset.mpr haxisImage.le
  have haxisCont : Continuous axis := by
    rw [haxisLine]
    exact AffineMap.lineMap_continuous
  have hcurveCont : ContinuousOn curve (Set.Icc (0 : ℝ) 1) :=
    hplS.continuousOn.comp haxisCont.continuousOn haxisMaps
  have haxisInj : Set.InjOn axis (Set.Icc (0 : ℝ) 1) := by
    intro x _ y _ hxy
    have hcoord := congrArg (fun p : Plane => p 0) hxy
    change n * x = n * y at hcoord
    exact mul_left_cancel₀ hn.ne' hcoord
  have hcurveInj : Set.InjOn curve (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply haxisInj hx hy
    exact hFinj (haxisMaps hx) (haxisMaps hy) hxy
  have hcurveImage : curve '' Set.Icc (0 : ℝ) 1 = B.resolvedCarrier := by
    rw [show curve '' Set.Icc (0 : ℝ) 1 = F '' (axis '' Set.Icc (0 : ℝ) 1) by
      exact (Set.image_image F axis (Set.Icc (0 : ℝ) 1)).symm]
    rw [haxisImage, ← hSsupport, himage]
  refine ⟨{
    length := B.resolvedWalk.length
    length_pos := hlength
    source := PlaneComplex.active L
    map := F
    curve := curve
    source_support := by rw [L.active_support, hLsub.1, hSsupport]
    map_isPL := by
      refine ⟨PlaneComplex.active L, PlaneComplex.Subdivides.refl _, ?_⟩
      intro s hs
      exact (L.active_cellCarrier s).symm ▸
        hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs)
    map_injectiveOn := by
      intro x hx y hy hxy
      apply hFinj
      · rw [← hLsub.1]
        simpa only [L.active_support] using hx
      · rw [← hLsub.1]
        simpa only [L.active_support] using hy
      · exact hxy
    map_affineOn := by
      intro s hs
      exact (L.active_cellCarrier s).symm ▸
        hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs)
    source_card_le_two := by
      intro s hs
      obtain ⟨t, ht, hst⟩ := (PlaneComplex.active_subdivides_left hLsub).2 s hs
      exact PlaneComplex.card_le_two_of_cellCarrier_subset_face hs ht (hSgraph t ht) hst
    source_vertex_mem := by
      intro v
      change L.position v.1 ∈ (PlaneComplex.active L).support
      rw [L.active_support]
      exact v.2
    curve_eq := by intro t; rfl
    continuousOn := hcurveCont
    injectiveOn := hcurveInj
    image_eq := hcurveImage
    start_eq := by simpa [curve, axis, n] using hstart
    finish_eq := by simpa [curve, axis, n] using hfinish }⟩

end BrokenLineData

/-- A simple finite PL replacement for one trimmed central arc, inside its pairwise-disjoint
tube.  The abstract carrier interface also admits the controlled finite approximation used
later in Chapter 6. -/
structure CentralPolygonalArc (e : K.Edge) where
  /-- The `carrier` declaration. -/
  carrier : Set Plane
  /-- The `start` declaration. -/
  start : Plane
  /-- The `finish` declaration. -/
  finish : Plane
  /-- The `parameterizationData` declaration. -/
  parameterizationData : PLArcParameterization carrier start finish
  carrier_subset_tube : carrier ⊆ G.edgeCentralTube e
  carrier_subset_edgeConvexHull : carrier ⊆ convexHull ℝ (G.edgeImage e)
  start_eq : start = G.chartEdgeCurve e (G.edgeTrim e).left
  finish_eq : finish = G.chartEdgeCurve e (G.edgeTrim e).right
  curve_close : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    dist (parameterizationData.curve t)
      (G.chartEdgeCurve e
        ((G.edgeTrim e).left +
          ((G.edgeTrim e).right - (G.edgeTrim e).left) * t)) <
      G.centralTubeRadius e

theorem exists_centralPolygonalArc (e : K.Edge) : Nonempty (G.CentralPolygonalArc e) := by
  let T := G.edgeTrim e
  let q : Plane → ℝ := fun p ↦
    T.left + (T.right - T.left) * p 0
  let h : Plane → Plane := fun p ↦ G.chartEdgeCurve e (q p)
  have hq_cont : Continuous q := by fun_prop
  have hcont : ContinuousOn h unitSegmentComplex.support :=
    ((G.continuous_chartEdgeCurve e).comp hq_cont).continuousOn
  have hq_mem (p : Plane) (hp : p ∈ unitSegmentComplex.support) :
      q p ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨-, hp0, hp1⟩ := unitSegment_mem_bounds hp
    have hslope : 0 ≤ T.right - T.left := sub_nonneg.mpr T.left_lt_right.le
    have hprod0 : 0 ≤ (T.right - T.left) * p 0 := mul_nonneg hslope hp0
    have hprod1 : (T.right - T.left) * p 0 ≤ T.right - T.left := by
      simpa using mul_le_mul_of_nonneg_left hp1 hslope
    constructor <;> dsimp only [q] <;> linarith [T.left_pos, T.right_lt_one]
  have hq_mem_trim (p : Plane) (hp : p ∈ unitSegmentComplex.support) :
      q p ∈ Set.Icc T.left T.right := by
    obtain ⟨-, hp0, hp1⟩ := unitSegment_mem_bounds hp
    have hslope : 0 ≤ T.right - T.left := sub_nonneg.mpr T.left_lt_right.le
    have hprod0 : 0 ≤ (T.right - T.left) * p 0 := mul_nonneg hslope hp0
    have hprod1 : (T.right - T.left) * p 0 ≤ T.right - T.left := by
      simpa using mul_le_mul_of_nonneg_left hp1 hslope
    constructor <;> dsimp only [q] <;> linarith
  have hmem_carrier (p : Plane) (hp : p ∈ unitSegmentComplex.support) :
      h p ∈ T.carrier := by
    exact ⟨q p, hq_mem_trim p hp, rfl⟩
  have hinj : Set.InjOn h unitSegmentComplex.support := by
    intro x hx y hy hxy
    have hpath : G.chartEdgePath e ⟨q x, hq_mem x hx⟩ =
        G.chartEdgePath e ⟨q y, hq_mem y hy⟩ := by
      rw [← G.chartEdgeCurve_eq_of_mem e (hq_mem x hx),
        ← G.chartEdgeCurve_eq_of_mem e (hq_mem y hy)]
      exact hxy
    have hqeq : q x = q y := congrArg Subtype.val
      (G.chartEdgePath_injective e hpath)
    have hxy0 : x 0 = y 0 := by
      dsimp only [q] at hqeq
      nlinarith [T.left_lt_right]
    obtain ⟨hx1, -, -⟩ := unitSegment_mem_bounds hx
    obtain ⟨hy1, -, -⟩ := unitSegment_mem_bounds hy
    ext i
    fin_cases i
    · exact hxy0
    · simp [hx1, hy1]
  obtain ⟨f, hpl, hfinj, hvertex, hclose, hconvex, -⟩ :=
    unitSegmentComplex.exists_graph_PL_approximation_facewise
      unitSegmentComplex_graph hcont hinj (G.centralTubeRadius_pos e)
  obtain ⟨P, hPlength, hPmap⟩ := exists_plArcParameterization_of_unitSegment
    unitSegmentComplex unitSegmentComplex_support unitSegmentComplex_graph hpl hfinj
  refine ⟨{
    carrier := f '' unitSegmentComplex.support
    start := f (planePoint 0 0)
    finish := f (planePoint 1 0)
    parameterizationData := P
    carrier_subset_tube := by
      rintro y ⟨x, hx, rfl⟩
      rw [edgeCentralTube, Metric.mem_thickening_iff]
      refine ⟨h x, T.carrier_subset_edgeCentralCarrier (hmem_carrier x hx), ?_⟩
      simpa [dist_comm] using hclose x hx
    carrier_subset_edgeConvexHull := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      apply convexHull_mono ?_ (hconvex x hx)
      rintro z ⟨x, hx, rfl⟩
      exact (T.carrier_subset_edgeCentralCarrier (hmem_carrier x hx)).1
    start_eq := by
      calc
        f (planePoint 0 0) = h (planePoint 0 0) := by
          rw [← unitSegmentFirstVertex_position]
          exact hvertex unitSegmentFirstVertex
        _ = G.chartEdgeCurve e T.left := by simp [h, q, planePoint]
    finish_eq := by
      calc
        f (planePoint 1 0) = h (planePoint 1 0) := by
          rw [← unitSegmentSecondVertex_position]
          exact hvertex unitSegmentSecondVertex
        _ = G.chartEdgeCurve e T.right := by simp [h, q, planePoint]
    curve_close := by
      intro t ht
      rw [P.curve_eq, hPlength, hPmap]
      have htSupport : planePoint t 0 ∈ unitSegmentComplex.support :=
        planePoint_mem_unitSegment ht
      simpa [h, q, planePoint] using hclose (planePoint t 0) htSupport }⟩

/-- The `centralPolygonalArc` declaration. -/
noncomputable def centralPolygonalArc (e : K.Edge) : G.CentralPolygonalArc e :=
  Classical.choice (G.exists_centralPolygonalArc e)

namespace CentralPolygonalArc

variable {G} {e : K.Edge}

theorem resolvedCarrier_subset (A : G.CentralPolygonalArc e) :
    A.carrier ⊆ G.edgeCentralTube e :=
  A.carrier_subset_tube

/-- The loop-resolved central arc remains in the convex hull of the original edge image. -/
theorem resolvedCarrier_subset_edgeConvexHull (A : G.CentralPolygonalArc e) :
    A.carrier ⊆ convexHull ℝ (G.edgeImage e) :=
  A.carrier_subset_edgeConvexHull

theorem disjoint_resolvedCarriers {d : K.Edge} (A : G.CentralPolygonalArc e)
    (B : G.CentralPolygonalArc d) (hed : e ≠ d) :
    Disjoint A.carrier B.carrier :=
  (G.disjoint_edgeCentralTubes hed).mono A.resolvedCarrier_subset B.resolvedCarrier_subset

/-- Compatibility alias for the finite PL parameterization exposed by a central arc. -/
abbrev Parameterization (A : G.CentralPolygonalArc e) :=
  PLArcParameterization A.carrier A.start A.finish

theorem start_ne_finish (A : G.CentralPolygonalArc e) :
    A.start ≠ A.finish := by
  have hleft : G.chartEdgeCurve e (G.edgeTrim e).left ∈
      G.vertexDisk (K.edgeFirst e) := by
    rw [vertexDisk, Metric.mem_closedBall]
    exact (G.edgeTrim e).left_on_sphere.le
  have hright : G.chartEdgeCurve e (G.edgeTrim e).right ∈
      G.vertexDisk (K.edgeSecond e) := by
    rw [vertexDisk, Metric.mem_closedBall]
    exact (G.edgeTrim e).right_on_sphere.le
  rw [A.start_eq, A.finish_eq]
  intro heq
  exact Set.disjoint_left.mp (G.disjoint_vertexDisks (K.edgeFirst_ne_edgeSecond e))
    hleft (heq ▸ hright)

theorem resolvedWalk_length_pos (A : G.CentralPolygonalArc e) :
    0 < A.parameterizationData.length :=
  A.parameterizationData.length_pos

theorem exists_parameterization (A : G.CentralPolygonalArc e) :
    Nonempty A.Parameterization :=
  ⟨A.parameterizationData⟩

/-- The `parameterization` declaration. -/
noncomputable def parameterization (A : G.CentralPolygonalArc e) : A.Parameterization :=
  A.parameterizationData

/-- Ordered exits of the resolved polygonal arc from the two variable-radius vertex disks. -/
noncomputable def exitData (A : G.CentralPolygonalArc e) :
    TwoRadiusBoundaryExitData A.parameterization.curve
      (G.vertexImage (K.edgeFirst e)) (G.vertexImage (K.edgeSecond e))
      (G.vertexIsolationRadius (K.edgeFirst e))
      (G.vertexIsolationRadius (K.edgeSecond e)) := by
  apply Classical.choice
  apply exists_twoRadiusBoundaryExitData
    (G.vertexIsolationRadius_pos (K.edgeFirst e))
    (G.vertexIsolationRadius_pos (K.edgeSecond e))
    A.parameterization.continuousOn
  · rw [A.parameterization.start_eq, A.start_eq]
    exact (G.edgeTrim e).left_on_sphere
  · rw [A.parameterization.finish_eq, A.finish_eq]
    exact (G.edgeTrim e).right_on_sphere
  · exact G.disjoint_vertexDisks (K.edgeFirst_ne_edgeSecond e)

/-- The `trimmedCarrier` declaration. -/
def trimmedCarrier (A : G.CentralPolygonalArc e) : Set Plane :=
  A.parameterization.curve '' Set.Icc A.exitData.left A.exitData.right

theorem trimmedCarrier_subset_resolvedCarrier (A : G.CentralPolygonalArc e) :
    A.trimmedCarrier ⊆ A.carrier := by
  rw [← A.parameterization.image_eq]
  exact Set.image_mono fun _ ht =>
    ⟨A.exitData.left_nonneg.trans ht.1, ht.2.trans A.exitData.right_le_one⟩

theorem trimmedCarrier_avoids_first (A : G.CentralPolygonalArc e) {x : Plane}
    (hx : x ∈ A.trimmedCarrier)
    (hxleft : x ≠ A.parameterization.curve A.exitData.left) :
    x ∉ G.vertexDisk (K.edgeFirst e) := by
  obtain ⟨t, ht, rfl⟩ := hx
  apply A.exitData.after_left t
  · exact ⟨A.exitData.left_nonneg.trans ht.1,
      ht.2.trans A.exitData.right_le_one⟩
  · exact lt_of_le_of_ne ht.1 fun heq => hxleft (by rw [heq])

theorem trimmedCarrier_avoids_second (A : G.CentralPolygonalArc e) {x : Plane}
    (hx : x ∈ A.trimmedCarrier)
    (hxright : x ≠ A.parameterization.curve A.exitData.right) :
    x ∉ G.vertexDisk (K.edgeSecond e) := by
  obtain ⟨t, ht, rfl⟩ := hx
  by_cases hleft : t = A.exitData.left
  · subst t
    apply Set.disjoint_left.mp (G.disjoint_vertexDisks (K.edgeFirst_ne_edgeSecond e))
    · rw [vertexDisk, Metric.mem_closedBall]
      exact A.exitData.left_on_sphere.le
  · apply A.exitData.before_right t
    · exact ⟨A.exitData.left_nonneg.trans ht.1,
        ht.2.trans A.exitData.right_le_one⟩
    · exact lt_of_le_of_ne ht.1 (Ne.symm hleft)
    · exact lt_of_le_of_ne ht.2 fun heq => hxright (by rw [heq])

/-- The `leftEndpoint` declaration. -/
noncomputable def leftEndpoint (A : G.CentralPolygonalArc e) : Plane :=
  A.parameterization.curve A.exitData.left

/-- The `rightEndpoint` declaration. -/
noncomputable def rightEndpoint (A : G.CentralPolygonalArc e) : Plane :=
  A.parameterization.curve A.exitData.right

/-- The `leftSpoke` declaration. -/
noncomputable def leftSpoke (A : G.CentralPolygonalArc e) : Set Plane :=
  segment ℝ (G.vertexImage (K.edgeFirst e)) A.leftEndpoint

/-- The `rightSpoke` declaration. -/
noncomputable def rightSpoke (A : G.CentralPolygonalArc e) : Set Plane :=
  segment ℝ A.rightEndpoint (G.vertexImage (K.edgeSecond e))

/-- The `completeCarrier` declaration. -/
noncomputable def completeCarrier (A : G.CentralPolygonalArc e) : Set Plane :=
  A.leftSpoke ∪ A.trimmedCarrier ∪ A.rightSpoke

theorem leftEndpoint_on_sphere (A : G.CentralPolygonalArc e) :
    dist A.leftEndpoint (G.vertexImage (K.edgeFirst e)) =
      G.vertexIsolationRadius (K.edgeFirst e) :=
  A.exitData.left_on_sphere

theorem rightEndpoint_on_sphere (A : G.CentralPolygonalArc e) :
    dist A.rightEndpoint (G.vertexImage (K.edgeSecond e)) =
      G.vertexIsolationRadius (K.edgeSecond e) :=
  A.exitData.right_on_sphere

theorem leftEndpoint_mem_trimmedCarrier (A : G.CentralPolygonalArc e) :
    A.leftEndpoint ∈ A.trimmedCarrier :=
  ⟨A.exitData.left, ⟨le_rfl, A.exitData.left_lt_right.le⟩, rfl⟩

theorem rightEndpoint_mem_trimmedCarrier (A : G.CentralPolygonalArc e) :
    A.rightEndpoint ∈ A.trimmedCarrier :=
  ⟨A.exitData.right, ⟨A.exitData.left_lt_right.le, le_rfl⟩, rfl⟩

theorem leftSpoke_subset_vertexDisk (A : G.CentralPolygonalArc e) :
    A.leftSpoke ⊆ G.vertexDisk (K.edgeFirst e) := by
  apply (convex_closedBall _ _).segment_subset
  · exact Metric.mem_closedBall_self (G.vertexIsolationRadius_pos _).le
  · simpa [vertexDisk, Metric.mem_closedBall, dist_comm] using
      A.leftEndpoint_on_sphere.le

theorem rightSpoke_subset_vertexDisk (A : G.CentralPolygonalArc e) :
    A.rightSpoke ⊆ G.vertexDisk (K.edgeSecond e) := by
  apply (convex_closedBall _ _).segment_subset
  · simpa [vertexDisk, Metric.mem_closedBall] using A.rightEndpoint_on_sphere.le
  · exact Metric.mem_closedBall_self (G.vertexIsolationRadius_pos _).le

/-- The complete replacement arc stays in the convex hull of the original embedded edge. -/
theorem completeCarrier_subset_edgeConvexHull (A : G.CentralPolygonalArc e) :
    A.completeCarrier ⊆ convexHull ℝ (G.edgeImage e) := by
  have hconvex : Convex ℝ (convexHull ℝ (G.edgeImage e)) := convex_convexHull ℝ _
  have hfirst : G.vertexImage (K.edgeFirst e) ∈ convexHull ℝ (G.edgeImage e) :=
    subset_convexHull ℝ _ <|
      (G.vertexImage_mem_edgeImage_iff (K.edgeFirst e) e).mpr (K.edgeFirst_mem e)
  have hsecond : G.vertexImage (K.edgeSecond e) ∈ convexHull ℝ (G.edgeImage e) :=
    subset_convexHull ℝ _ <|
      (G.vertexImage_mem_edgeImage_iff (K.edgeSecond e) e).mpr (K.edgeSecond_mem e)
  have hleft : A.leftEndpoint ∈ convexHull ℝ (G.edgeImage e) :=
    A.resolvedCarrier_subset_edgeConvexHull <|
      A.trimmedCarrier_subset_resolvedCarrier A.leftEndpoint_mem_trimmedCarrier
  have hright : A.rightEndpoint ∈ convexHull ℝ (G.edgeImage e) :=
    A.resolvedCarrier_subset_edgeConvexHull <|
      A.trimmedCarrier_subset_resolvedCarrier A.rightEndpoint_mem_trimmedCarrier
  rintro x ((hx | hx) | hx)
  · exact hconvex.segment_subset hfirst hleft hx
  · exact A.resolvedCarrier_subset_edgeConvexHull <|
      A.trimmedCarrier_subset_resolvedCarrier hx
  · exact hconvex.segment_subset hright hsecond hx

/-- Every point of the complete polygonal replacement lies within twice the diameter of the
original charted edge from every point of that edge.  Thus a sufficiently fine source complex
turns the setwise tube construction into a pointwise approximation, without choosing a
parameter-preserving polygonalization. -/
theorem dist_lt_two_mul_edgeImage_diam (A : G.CentralPolygonalArc e)
    {y p : Plane} (hy : y ∈ A.completeCarrier) (hp : p ∈ G.edgeImage e) :
    dist y p < 2 * Metric.diam (G.edgeImage e) := by
  let d := Metric.diam (G.edgeImage e)
  have hd : 0 < d := G.edgeImage_diam_pos e
  have hend : dist (G.vertexImage (K.edgeFirst e))
      (G.vertexImage (K.edgeSecond e)) ≤ d := G.endpointDist_le_edgeImage_diam e
  have hquarter : dist (G.vertexImage (K.edgeFirst e))
      (G.vertexImage (K.edgeSecond e)) / 4 ≤ d / 4 := by
    gcongr
  rcases hy with (hleft | hmiddle) | hright
  · have hyDisk := A.leftSpoke_subset_vertexDisk hleft
    have hyradius : dist y (G.vertexImage (K.edgeFirst e)) ≤
        G.vertexIsolationRadius (K.edgeFirst e) := by
      simpa [vertexDisk] using Metric.mem_closedBall.mp hyDisk
    have hradius : G.vertexIsolationRadius (K.edgeFirst e) ≤ d / 4 :=
      (G.vertexIsolationRadius_le_quarter_dist
        (K.edgeFirst_ne_edgeSecond e).symm).trans hquarter
    have hpdiam : dist (G.vertexImage (K.edgeFirst e)) p ≤ d :=
      Metric.dist_le_diam_of_mem (G.isCompact_edgeImage e).isBounded
        ((G.vertexImage_mem_edgeImage_iff (K.edgeFirst e) e).mpr
          (K.edgeFirst_mem e)) hp
    calc
      dist y p ≤ dist y (G.vertexImage (K.edgeFirst e)) +
          dist (G.vertexImage (K.edgeFirst e)) p := dist_triangle _ _ _
      _ ≤ d / 4 + d := add_le_add (hyradius.trans hradius) hpdiam
      _ < 2 * d := by linarith
  · have hyTube : y ∈ G.edgeCentralTube e :=
      A.trimmedCarrier_subset_resolvedCarrier hmiddle |> A.resolvedCarrier_subset
    obtain ⟨x, hxCentral, hyx⟩ := Metric.mem_thickening_iff.mp hyTube
    have hradius : G.centralTubeRadius e ≤ d / 4 :=
      (G.centralTubeRadius_le_quarter_endpointDist e).trans hquarter
    have hxp : dist x p ≤ d :=
      Metric.dist_le_diam_of_mem (G.isCompact_edgeImage e).isBounded hxCentral.1 hp
    calc
      dist y p ≤ dist y x + dist x p := dist_triangle _ _ _
      _ < d / 4 + d := add_lt_add_of_lt_of_le (hyx.trans_le hradius) hxp
      _ < 2 * d := by linarith
  · have hyDisk := A.rightSpoke_subset_vertexDisk hright
    have hyradius : dist y (G.vertexImage (K.edgeSecond e)) ≤
        G.vertexIsolationRadius (K.edgeSecond e) := by
      simpa [vertexDisk] using Metric.mem_closedBall.mp hyDisk
    have hquarter' : dist (G.vertexImage (K.edgeSecond e))
        (G.vertexImage (K.edgeFirst e)) / 4 ≤ d / 4 := by
      rw [dist_comm]
      exact hquarter
    have hradius : G.vertexIsolationRadius (K.edgeSecond e) ≤ d / 4 :=
      (G.vertexIsolationRadius_le_quarter_dist
        (K.edgeFirst_ne_edgeSecond e)).trans hquarter'
    have hpdiam : dist (G.vertexImage (K.edgeSecond e)) p ≤ d :=
      Metric.dist_le_diam_of_mem (G.isCompact_edgeImage e).isBounded
        ((G.vertexImage_mem_edgeImage_iff (K.edgeSecond e) e).mpr
          (K.edgeSecond_mem e)) hp
    calc
      dist y p ≤ dist y (G.vertexImage (K.edgeSecond e)) +
          dist (G.vertexImage (K.edgeSecond e)) p := dist_triangle _ _ _
      _ ≤ d / 4 + d := add_le_add (hyradius.trans hradius) hpdiam
      _ < 2 * d := by linarith

theorem leftSpoke_inter_trimmedCarrier (A : G.CentralPolygonalArc e) :
    A.leftSpoke ∩ A.trimmedCarrier = {A.leftEndpoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSpoke, hxTrim⟩
    by_contra hx
    exact A.trimmedCarrier_avoids_first hxTrim hx
      (A.leftSpoke_subset_vertexDisk hxSpoke)
  · rintro x rfl
    exact ⟨right_mem_segment ℝ _ _, A.leftEndpoint_mem_trimmedCarrier⟩

theorem rightSpoke_inter_trimmedCarrier (A : G.CentralPolygonalArc e) :
    A.rightSpoke ∩ A.trimmedCarrier = {A.rightEndpoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSpoke, hxTrim⟩
    by_contra hx
    exact A.trimmedCarrier_avoids_second hxTrim hx
      (A.rightSpoke_subset_vertexDisk hxSpoke)
  · rintro x rfl
    exact ⟨left_mem_segment ℝ _ _, A.rightEndpoint_mem_trimmedCarrier⟩

theorem leftSpoke_disjoint_rightSpoke (A : G.CentralPolygonalArc e) :
    Disjoint A.leftSpoke A.rightSpoke :=
  (G.disjoint_vertexDisks (K.edgeFirst_ne_edgeSecond e)).mono
    A.leftSpoke_subset_vertexDisk A.rightSpoke_subset_vertexDisk

/-- The trimmed resolved middle, with its parameter interval normalized to the unit interval. -/
noncomputable def middlePath (A : G.CentralPolygonalArc e) :
    Path A.leftEndpoint A.rightEndpoint where
  toFun t := A.parameterization.curve
    (Path.segment A.exitData.left A.exitData.right t)
  continuous_toFun := by
    apply A.parameterization.continuousOn.comp_continuous
    · exact (Path.segment A.exitData.left A.exitData.right).continuous
    · intro t
      have ht : Path.segment A.exitData.left A.exitData.right t ∈
          segment ℝ A.exitData.left A.exitData.right := by
        rw [← Path.range_segment]
        exact ⟨t, rfl⟩
      rw [segment_eq_Icc A.exitData.left_lt_right.le] at ht
      exact ⟨A.exitData.left_nonneg.trans ht.1,
        ht.2.trans A.exitData.right_le_one⟩
  source' := by simp [leftEndpoint]
  target' := by simp [rightEndpoint]

theorem range_middlePath (A : G.CentralPolygonalArc e) :
    Set.range A.middlePath = A.trimmedCarrier := by
  rw [trimmedCarrier]
  have hsegment : segment ℝ A.exitData.left A.exitData.right =
      Set.Icc A.exitData.left A.exitData.right :=
    segment_eq_Icc A.exitData.left_lt_right.le
  rw [← hsegment, ← Path.range_segment]
  ext x
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Path.segment A.exitData.left A.exitData.right t, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨r, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩

theorem middlePath_injective (A : G.CentralPolygonalArc e) :
    Function.Injective A.middlePath := by
  intro s t hst
  have hs : Path.segment A.exitData.left A.exitData.right s ∈
      Set.Icc A.exitData.left A.exitData.right := by
    rw [← segment_eq_Icc A.exitData.left_lt_right.le, ← Path.range_segment]
    exact ⟨s, rfl⟩
  have ht : Path.segment A.exitData.left A.exitData.right t ∈
      Set.Icc A.exitData.left A.exitData.right := by
    rw [← segment_eq_Icc A.exitData.left_lt_right.le, ← Path.range_segment]
    exact ⟨t, rfl⟩
  have hparam := A.parameterization.injectiveOn
    ⟨A.exitData.left_nonneg.trans hs.1, hs.2.trans A.exitData.right_le_one⟩
    ⟨A.exitData.left_nonneg.trans ht.1, ht.2.trans A.exitData.right_le_one⟩ hst
  exact Path.segment_injective_of_ne A.exitData.left_lt_right.ne hparam

/-- The complete polygonal replacement path of a locally finite abstract edge. -/
noncomputable def completePath (A : G.CentralPolygonalArc e) :
    Path (G.vertexImage (K.edgeFirst e)) (G.vertexImage (K.edgeSecond e)) :=
  (Path.segment (G.vertexImage (K.edgeFirst e)) A.leftEndpoint).trans
    (A.middlePath.trans
      (Path.segment A.rightEndpoint (G.vertexImage (K.edgeSecond e))))

theorem range_completePath (A : G.CentralPolygonalArc e) :
    Set.range A.completePath = A.completeCarrier := by
  rw [completePath, Path.trans_range, Path.trans_range, Path.range_segment,
    Path.range_segment, A.range_middlePath]
  simp [completeCarrier, leftSpoke, rightSpoke, Set.union_assoc]

/-- Each locally finite replacement edge is a simple polygonal path. -/
theorem completePath_injective (A : G.CentralPolygonalArc e) :
    Function.Injective A.completePath := by
  let first := Path.segment (G.vertexImage (K.edgeFirst e)) A.leftEndpoint
  let last := Path.segment A.rightEndpoint (G.vertexImage (K.edgeSecond e))
  have hfirstNe : G.vertexImage (K.edgeFirst e) ≠ A.leftEndpoint := by
    intro heq
    have hs := A.leftEndpoint_on_sphere
    rw [← heq, dist_self] at hs
    linarith [G.vertexIsolationRadius_pos (K.edgeFirst e)]
  have hlastNe : A.rightEndpoint ≠ G.vertexImage (K.edgeSecond e) := by
    intro heq
    have hs := A.rightEndpoint_on_sphere
    rw [heq, dist_self] at hs
    linarith [G.vertexIsolationRadius_pos (K.edgeSecond e)]
  have hfirstInj : Function.Injective first := Path.segment_injective_of_ne hfirstNe
  have hlastInj : Function.Injective last := Path.segment_injective_of_ne hlastNe
  have hmiddleLastInter : Set.range A.middlePath ∩ Set.range last =
      {A.rightEndpoint} := by
    rw [A.range_middlePath, Path.range_segment, Set.inter_comm]
    exact A.rightSpoke_inter_trimmedCarrier
  have htailInj : Function.Injective (A.middlePath.trans last) :=
    Path.trans_injective_of_range_inter A.middlePath last A.middlePath_injective
      hlastInj hmiddleLastInter
  have hfirstMiddleInter : Set.range first ∩ Set.range A.middlePath =
      {A.leftEndpoint} := by
    rw [Path.range_segment, A.range_middlePath]
    exact A.leftSpoke_inter_trimmedCarrier
  have hfirstLast : Disjoint (Set.range first) (Set.range last) := by
    rw [Path.range_segment, Path.range_segment]
    exact A.leftSpoke_disjoint_rightSpoke
  have hfirstTailInter : Set.range first ∩ Set.range (A.middlePath.trans last) =
      {A.leftEndpoint} := by
    rw [Path.trans_range, Set.inter_union_distrib_left, hfirstMiddleInter,
      Set.disjoint_iff_inter_eq_empty.mp hfirstLast, Set.union_empty]
  exact Path.trans_injective_of_range_inter first (A.middlePath.trans last)
    hfirstInj htailInj hfirstTailInter

theorem disjoint_trimmedCarrier {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    Disjoint A.trimmedCarrier B.trimmedCarrier :=
  (A.disjoint_resolvedCarriers B hed).mono
    A.trimmedCarrier_subset_resolvedCarrier B.trimmedCarrier_subset_resolvedCarrier

theorem trimmedCarrier_avoids_nonincident (A : G.CentralPolygonalArc e)
    (v : K.Vertex) (hve : v ∉ e.1) :
    Disjoint (G.vertexDisk v) A.trimmedCarrier :=
  (G.disjoint_edgeCentralTube_nonincidentVertexDisk e v hve).symm.mono_right
    (A.trimmedCarrier_subset_resolvedCarrier.trans A.resolvedCarrier_subset)

theorem leftEndpoint_ne_leftEndpoint {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    A.leftEndpoint ≠ B.leftEndpoint := by
  intro heq
  exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (B := B) hed)
    A.leftEndpoint_mem_trimmedCarrier (heq ▸ B.leftEndpoint_mem_trimmedCarrier)

theorem leftEndpoint_ne_rightEndpoint {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    A.leftEndpoint ≠ B.rightEndpoint := by
  intro heq
  exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (B := B) hed)
    A.leftEndpoint_mem_trimmedCarrier (heq ▸ B.rightEndpoint_mem_trimmedCarrier)

theorem rightEndpoint_ne_leftEndpoint {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    A.rightEndpoint ≠ B.leftEndpoint := by
  intro heq
  exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (B := B) hed)
    A.rightEndpoint_mem_trimmedCarrier (heq ▸ B.leftEndpoint_mem_trimmedCarrier)

theorem rightEndpoint_ne_rightEndpoint {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    A.rightEndpoint ≠ B.rightEndpoint := by
  intro heq
  exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (B := B) hed)
    A.rightEndpoint_mem_trimmedCarrier (heq ▸ B.rightEndpoint_mem_trimmedCarrier)

/-- The `leftOpenSpoke` declaration. -/
noncomputable def leftOpenSpoke (A : G.CentralPolygonalArc e) : Set Plane :=
  A.leftSpoke \ {G.vertexImage (K.edgeFirst e)}

/-- The `rightOpenSpoke` declaration. -/
noncomputable def rightOpenSpoke (A : G.CentralPolygonalArc e) : Set Plane :=
  A.rightSpoke \ {G.vertexImage (K.edgeSecond e)}

/-- The `interiorCarrier` declaration. -/
noncomputable def interiorCarrier (A : G.CentralPolygonalArc e) : Set Plane :=
  A.leftOpenSpoke ∪ A.trimmedCarrier ∪ A.rightOpenSpoke

theorem firstCenter_not_mem_trimmedCarrier (A : G.CentralPolygonalArc e) :
    G.vertexImage (K.edgeFirst e) ∉ A.trimmedCarrier := by
  intro hx
  apply A.trimmedCarrier_avoids_first hx
  · intro heq
    change G.vertexImage (K.edgeFirst e) = A.leftEndpoint at heq
    have hs := A.leftEndpoint_on_sphere
    rw [← heq, dist_self] at hs
    linarith [G.vertexIsolationRadius_pos (K.edgeFirst e)]
  · exact Metric.mem_closedBall_self (G.vertexIsolationRadius_pos _).le

theorem secondCenter_not_mem_trimmedCarrier (A : G.CentralPolygonalArc e) :
    G.vertexImage (K.edgeSecond e) ∉ A.trimmedCarrier := by
  intro hx
  apply A.trimmedCarrier_avoids_second hx
  · intro heq
    change G.vertexImage (K.edgeSecond e) = A.rightEndpoint at heq
    have hs := A.rightEndpoint_on_sphere
    rw [← heq, dist_self] at hs
    linarith [G.vertexIsolationRadius_pos (K.edgeSecond e)]
  · exact Metric.mem_closedBall_self (G.vertexIsolationRadius_pos _).le

theorem firstCenter_not_mem_rightSpoke (A : G.CentralPolygonalArc e) :
    G.vertexImage (K.edgeFirst e) ∉ A.rightSpoke := by
  intro hx
  exact Set.disjoint_left.mp (G.disjoint_vertexDisks (K.edgeFirst_ne_edgeSecond e))
    (Metric.mem_closedBall_self (G.vertexIsolationRadius_pos _).le)
    (A.rightSpoke_subset_vertexDisk hx)

theorem secondCenter_not_mem_leftSpoke (A : G.CentralPolygonalArc e) :
    G.vertexImage (K.edgeSecond e) ∉ A.leftSpoke := by
  intro hx
  exact Set.disjoint_left.mp (G.disjoint_vertexDisks (K.edgeFirst_ne_edgeSecond e))
    (A.leftSpoke_subset_vertexDisk hx)
    (Metric.mem_closedBall_self (G.vertexIsolationRadius_pos _).le)

theorem completeCarrier_sdiff_endpoints (A : G.CentralPolygonalArc e) :
    A.completeCarrier \
        {G.vertexImage (K.edgeFirst e), G.vertexImage (K.edgeSecond e)} =
      A.interiorCarrier := by
  ext x
  simp only [completeCarrier, interiorCarrier, leftOpenSpoke, rightOpenSpoke,
    Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  constructor
  · rintro ⟨(hL | hT) | hR, hne⟩
    · exact Or.inl (Or.inl ⟨hL, fun hx => hne (Or.inl hx)⟩)
    · exact Or.inl (Or.inr hT)
    · exact Or.inr ⟨hR, fun hx => hne (Or.inr hx)⟩
  · rintro ((⟨hL, hx0⟩ | hT) | ⟨hR, hx1⟩)
    · refine ⟨Or.inl (Or.inl hL), ?_⟩
      rintro (hx | hx)
      · exact hx0 hx
      · exact A.secondCenter_not_mem_leftSpoke (hx ▸ hL)
    · refine ⟨Or.inl (Or.inr hT), ?_⟩
      rintro (hx | hx)
      · exact A.firstCenter_not_mem_trimmedCarrier (hx ▸ hT)
      · exact A.secondCenter_not_mem_trimmedCarrier (hx ▸ hT)
    · refine ⟨Or.inr hR, ?_⟩
      rintro (hx | hx)
      · exact A.firstCenter_not_mem_rightSpoke (hx ▸ hR)
      · exact hx1 hx

theorem disjoint_leftSpoke_trimmedCarrier {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    Disjoint A.leftSpoke B.trimmedCarrier := by
  rw [Set.disjoint_left]
  intro x hxSpoke hxTrim
  have hxDisk := A.leftSpoke_subset_vertexDisk hxSpoke
  by_cases hv : K.edgeFirst e ∈ d.1
  · rw [K.edge_eq_pair d] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · have hxEq : x = B.leftEndpoint := by
        by_contra hne
        apply B.trimmedCarrier_avoids_first hxTrim hne
        simpa only [hv] using hxDisk
      have hxSphere : dist x (G.vertexImage (K.edgeFirst e)) =
          G.vertexIsolationRadius (K.edgeFirst e) := by
        rw [hxEq, hv]
        exact B.leftEndpoint_on_sphere
      have hxOwn : x = A.leftEndpoint :=
        eq_endpoint_of_mem_radial_segment
          (G.vertexIsolationRadius_pos (K.edgeFirst e))
          A.leftEndpoint_on_sphere hxSpoke hxSphere
      exact A.leftEndpoint_ne_leftEndpoint (B := B) hed (hxOwn.symm.trans hxEq)
    · have hxEq : x = B.rightEndpoint := by
        by_contra hne
        apply B.trimmedCarrier_avoids_second hxTrim hne
        simpa only [hv] using hxDisk
      have hxSphere : dist x (G.vertexImage (K.edgeFirst e)) =
          G.vertexIsolationRadius (K.edgeFirst e) := by
        rw [hxEq, hv]
        exact B.rightEndpoint_on_sphere
      have hxOwn : x = A.leftEndpoint :=
        eq_endpoint_of_mem_radial_segment
          (G.vertexIsolationRadius_pos (K.edgeFirst e))
          A.leftEndpoint_on_sphere hxSpoke hxSphere
      exact A.leftEndpoint_ne_rightEndpoint (B := B) hed (hxOwn.symm.trans hxEq)
  · exact Set.disjoint_left.mp (B.trimmedCarrier_avoids_nonincident (K.edgeFirst e) hv)
      hxDisk hxTrim

theorem disjoint_rightSpoke_trimmedCarrier {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    Disjoint A.rightSpoke B.trimmedCarrier := by
  rw [Set.disjoint_left]
  intro x hxSpoke hxTrim
  have hxDisk := A.rightSpoke_subset_vertexDisk hxSpoke
  have hxSpoke' : x ∈ segment ℝ (G.vertexImage (K.edgeSecond e)) A.rightEndpoint := by
    rwa [segment_symm]
  by_cases hv : K.edgeSecond e ∈ d.1
  · rw [K.edge_eq_pair d] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · have hxEq : x = B.leftEndpoint := by
        by_contra hne
        apply B.trimmedCarrier_avoids_first hxTrim hne
        simpa only [hv] using hxDisk
      have hxSphere : dist x (G.vertexImage (K.edgeSecond e)) =
          G.vertexIsolationRadius (K.edgeSecond e) := by
        rw [hxEq, hv]
        exact B.leftEndpoint_on_sphere
      have hxOwn : x = A.rightEndpoint :=
        eq_endpoint_of_mem_radial_segment
          (G.vertexIsolationRadius_pos (K.edgeSecond e))
          A.rightEndpoint_on_sphere hxSpoke' hxSphere
      exact A.rightEndpoint_ne_leftEndpoint (B := B) hed (hxOwn.symm.trans hxEq)
    · have hxEq : x = B.rightEndpoint := by
        by_contra hne
        apply B.trimmedCarrier_avoids_second hxTrim hne
        simpa only [hv] using hxDisk
      have hxSphere : dist x (G.vertexImage (K.edgeSecond e)) =
          G.vertexIsolationRadius (K.edgeSecond e) := by
        rw [hxEq, hv]
        exact B.rightEndpoint_on_sphere
      have hxOwn : x = A.rightEndpoint :=
        eq_endpoint_of_mem_radial_segment
          (G.vertexIsolationRadius_pos (K.edgeSecond e))
          A.rightEndpoint_on_sphere hxSpoke' hxSphere
      exact A.rightEndpoint_ne_rightEndpoint (B := B) hed (hxOwn.symm.trans hxEq)
  · exact Set.disjoint_left.mp (B.trimmedCarrier_avoids_nonincident (K.edgeSecond e) hv)
      hxDisk hxTrim

theorem disjoint_leftOpenSpoke_leftOpenSpoke {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    Disjoint A.leftOpenSpoke B.leftOpenSpoke := by
  by_cases hv : K.edgeFirst e = K.edgeFirst d
  · simpa [leftOpenSpoke, leftSpoke, hv] using
      disjoint_radial_segments_away_center
        (G.vertexIsolationRadius_pos (K.edgeFirst e))
        A.leftEndpoint_on_sphere
        (by simpa only [hv] using B.leftEndpoint_on_sphere)
        (A.leftEndpoint_ne_leftEndpoint (B := B) hed)
  · exact (G.disjoint_vertexDisks hv).mono
      (Set.sdiff_subset.trans A.leftSpoke_subset_vertexDisk)
      (Set.sdiff_subset.trans B.leftSpoke_subset_vertexDisk)

theorem disjoint_leftOpenSpoke_rightOpenSpoke {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    Disjoint A.leftOpenSpoke B.rightOpenSpoke := by
  by_cases hv : K.edgeFirst e = K.edgeSecond d
  · simpa [leftOpenSpoke, leftSpoke, rightOpenSpoke, rightSpoke, hv, segment_symm] using
      disjoint_radial_segments_away_center
        (G.vertexIsolationRadius_pos (K.edgeFirst e))
        A.leftEndpoint_on_sphere
        (by simpa only [hv] using B.rightEndpoint_on_sphere)
        (A.leftEndpoint_ne_rightEndpoint (B := B) hed)
  · exact (G.disjoint_vertexDisks hv).mono
      (Set.sdiff_subset.trans A.leftSpoke_subset_vertexDisk)
      (Set.sdiff_subset.trans B.rightSpoke_subset_vertexDisk)

theorem disjoint_rightOpenSpoke_leftOpenSpoke {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    Disjoint A.rightOpenSpoke B.leftOpenSpoke := by
  by_cases hv : K.edgeSecond e = K.edgeFirst d
  · simpa [rightOpenSpoke, rightSpoke, leftOpenSpoke, leftSpoke, hv, segment_symm] using
      disjoint_radial_segments_away_center
        (G.vertexIsolationRadius_pos (K.edgeSecond e))
        A.rightEndpoint_on_sphere
        (by simpa only [hv] using B.leftEndpoint_on_sphere)
        (A.rightEndpoint_ne_leftEndpoint (B := B) hed)
  · exact (G.disjoint_vertexDisks hv).mono
      (Set.sdiff_subset.trans A.rightSpoke_subset_vertexDisk)
      (Set.sdiff_subset.trans B.leftSpoke_subset_vertexDisk)

theorem disjoint_rightOpenSpoke_rightOpenSpoke {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    Disjoint A.rightOpenSpoke B.rightOpenSpoke := by
  by_cases hv : K.edgeSecond e = K.edgeSecond d
  · simpa [rightOpenSpoke, rightSpoke, hv, segment_symm] using
      disjoint_radial_segments_away_center
        (G.vertexIsolationRadius_pos (K.edgeSecond e))
        A.rightEndpoint_on_sphere
        (by simpa only [hv] using B.rightEndpoint_on_sphere)
        (A.rightEndpoint_ne_rightEndpoint (B := B) hed)
  · exact (G.disjoint_vertexDisks hv).mono
      (Set.sdiff_subset.trans A.rightSpoke_subset_vertexDisk)
      (Set.sdiff_subset.trans B.rightSpoke_subset_vertexDisk)

/-- Distinct locally finite replacement edges have disjoint relative interiors. -/
theorem disjoint_interiorCarrier {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    Disjoint A.interiorCarrier B.interiorCarrier := by
  have hLT : Disjoint A.leftOpenSpoke B.trimmedCarrier :=
    (A.disjoint_leftSpoke_trimmedCarrier (B := B) hed).mono_left Set.sdiff_subset
  have hRT : Disjoint A.rightOpenSpoke B.trimmedCarrier :=
    (A.disjoint_rightSpoke_trimmedCarrier (B := B) hed).mono_left Set.sdiff_subset
  have hTL : Disjoint A.trimmedCarrier B.leftOpenSpoke :=
    ((B.disjoint_leftSpoke_trimmedCarrier (B := A) hed.symm).mono_left
      Set.sdiff_subset).symm
  have hTR : Disjoint A.trimmedCarrier B.rightOpenSpoke :=
    ((B.disjoint_rightSpoke_trimmedCarrier (B := A) hed.symm).mono_left
      Set.sdiff_subset).symm
  rw [Set.disjoint_left]
  intro x hx hx'
  change x ∈ (A.leftOpenSpoke ∪ A.trimmedCarrier) ∪ A.rightOpenSpoke at hx
  change x ∈ (B.leftOpenSpoke ∪ B.trimmedCarrier) ∪ B.rightOpenSpoke at hx'
  rcases hx with (hL | hT) | hR <;> rcases hx' with (hL' | hT') | hR'
  · exact Set.disjoint_left.mp (A.disjoint_leftOpenSpoke_leftOpenSpoke (B := B) hed) hL hL'
  · exact Set.disjoint_left.mp hLT hL hT'
  · exact Set.disjoint_left.mp (A.disjoint_leftOpenSpoke_rightOpenSpoke (B := B) hed) hL hR'
  · exact Set.disjoint_left.mp hTL hT hL'
  · exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (B := B) hed) hT hT'
  · exact Set.disjoint_left.mp hTR hT hR'
  · exact Set.disjoint_left.mp (A.disjoint_rightOpenSpoke_leftOpenSpoke (B := B) hed) hR hL'
  · exact Set.disjoint_left.mp hRT hR hT'
  · exact Set.disjoint_left.mp (A.disjoint_rightOpenSpoke_rightOpenSpoke (B := B) hed) hR hR'

theorem completeCarrier_avoids_nonincident (A : G.CentralPolygonalArc e)
    (v : K.Vertex) (hve : v ∉ e.1) :
    Disjoint (G.vertexDisk v) A.completeCarrier := by
  have hvFirst : v ≠ K.edgeFirst e := fun heq => hve (heq ▸ K.edgeFirst_mem e)
  have hvSecond : v ≠ K.edgeSecond e := fun heq => hve (heq ▸ K.edgeSecond_mem e)
  rw [Set.disjoint_left]
  intro x hxDisk hxCarrier
  rcases hxCarrier with (hxLeft | hxTrim) | hxRight
  · exact Set.disjoint_left.mp (G.disjoint_vertexDisks hvFirst)
      hxDisk (A.leftSpoke_subset_vertexDisk hxLeft)
  · exact Set.disjoint_left.mp (A.trimmedCarrier_avoids_nonincident v hve)
      hxDisk hxTrim
  · exact Set.disjoint_left.mp (G.disjoint_vertexDisks hvSecond)
      hxDisk (A.rightSpoke_subset_vertexDisk hxRight)

theorem vertex_mem_completeCarrier (A : G.CentralPolygonalArc e)
    (v : K.Vertex) (hve : v ∈ e.1) :
    G.vertexImage v ∈ A.completeCarrier := by
  rw [K.edge_eq_pair e] at hve
  simp only [Finset.mem_insert, Finset.mem_singleton] at hve
  rcases hve with rfl | rfl
  · exact Or.inl (Or.inl (left_mem_segment ℝ _ _))
  · exact Or.inr (right_mem_segment ℝ _ _)

/-- Distinct complete replacement edges meet only at images of shared abstract vertices. -/
theorem exists_shared_vertex_of_mem_completeCarriers {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d)
    {x : Plane} (hx : x ∈ A.completeCarrier) (hx' : x ∈ B.completeCarrier) :
    ∃ v : K.Vertex, v ∈ (e.1 ∩ d.1 : Finset K.Vertex) ∧ x = G.vertexImage v := by
  have hend : x = G.vertexImage (K.edgeFirst e) ∨
      x = G.vertexImage (K.edgeSecond e) ∨
      x = G.vertexImage (K.edgeFirst d) ∨ x = G.vertexImage (K.edgeSecond d) := by
    by_contra hn
    push Not at hn
    have hxInt : x ∈ A.interiorCarrier := by
      rw [← A.completeCarrier_sdiff_endpoints]
      exact ⟨hx, by simp [hn.1, hn.2.1]⟩
    have hxInt' : x ∈ B.interiorCarrier := by
      rw [← B.completeCarrier_sdiff_endpoints]
      exact ⟨hx', by simp [hn.2.2.1, hn.2.2.2]⟩
    exact Set.disjoint_left.mp (A.disjoint_interiorCarrier (B := B) hed) hxInt hxInt'
  rcases hend with hfirst | hsecond | hfirst' | hsecond'
  · let v := K.edgeFirst e
    have hvd : v ∈ d.1 := by
      by_contra hvd
      have hvDisk : G.vertexImage v ∈ G.vertexDisk v := by
        rw [vertexDisk]
        exact Metric.mem_closedBall_self (G.vertexIsolationRadius_pos v).le
      exact Set.disjoint_left.mp (B.completeCarrier_avoids_nonincident v hvd)
        (hfirst.symm ▸ hvDisk) hx'
    exact ⟨v, Finset.mem_inter.mpr ⟨K.edgeFirst_mem e, hvd⟩, hfirst⟩
  · let v := K.edgeSecond e
    have hvd : v ∈ d.1 := by
      by_contra hvd
      have hvDisk : G.vertexImage v ∈ G.vertexDisk v := by
        rw [vertexDisk]
        exact Metric.mem_closedBall_self (G.vertexIsolationRadius_pos v).le
      exact Set.disjoint_left.mp (B.completeCarrier_avoids_nonincident v hvd)
        (hsecond.symm ▸ hvDisk) hx'
    exact ⟨v, Finset.mem_inter.mpr ⟨K.edgeSecond_mem e, hvd⟩, hsecond⟩
  · let v := K.edgeFirst d
    have hve : v ∈ e.1 := by
      by_contra hve
      have hvDisk : G.vertexImage v ∈ G.vertexDisk v := by
        rw [vertexDisk]
        exact Metric.mem_closedBall_self (G.vertexIsolationRadius_pos v).le
      exact Set.disjoint_left.mp (A.completeCarrier_avoids_nonincident v hve)
        (hfirst'.symm ▸ hvDisk) hx
    exact ⟨v, Finset.mem_inter.mpr ⟨hve, K.edgeFirst_mem d⟩, hfirst'⟩
  · let v := K.edgeSecond d
    have hve : v ∈ e.1 := by
      by_contra hve
      have hvDisk : G.vertexImage v ∈ G.vertexDisk v := by
        rw [vertexDisk]
        exact Metric.mem_closedBall_self (G.vertexIsolationRadius_pos v).le
      exact Set.disjoint_left.mp (A.completeCarrier_avoids_nonincident v hve)
        (hsecond'.symm ▸ hvDisk) hx
    exact ⟨v, Finset.mem_inter.mpr ⟨hve, K.edgeSecond_mem d⟩, hsecond'⟩

theorem completeCarrier_inter_eq_sharedVertices {d : K.Edge}
    {B : G.CentralPolygonalArc d} (A : G.CentralPolygonalArc e) (hed : e ≠ d) :
    A.completeCarrier ∩ B.completeCarrier =
      {x | ∃ v : K.Vertex, v ∈ e.1 ∧ v ∈ d.1 ∧ x = G.vertexImage v} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hx'⟩
    obtain ⟨v, hv, rfl⟩ := A.exists_shared_vertex_of_mem_completeCarriers
      (B := B) hed hx hx'
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2, rfl⟩
  · rintro x ⟨v, hve, hvd, rfl⟩
    exact ⟨A.vertex_mem_completeCarrier v hve, B.vertex_mem_completeCarrier v hvd⟩

end CentralPolygonalArc

/-! ## Strongly-positive edge controls -/

/-- The carrier of an abstract edge, included into the whole source support. -/
def edgeInSupport (e : K.Edge) : Set K.support :=
  Set.range (edgeToSupport (K := K) e)

theorem isCompact_edgeInSupport (e : K.Edge) :
    IsCompact (edgeInSupport (K := K) e) := by
  let : CompactSpace (K.edgeCarrier e) :=
    isCompact_iff_compactSpace.mp (K.isCompact_edgeCarrier e)
  exact isCompact_range (continuous_edgeToSupport (K := K) e)

theorem edgeInSupport_nonempty (e : K.Edge) :
    (edgeInSupport (K := K) e).Nonempty := by
  have he : e.1.Nonempty := Finset.card_pos.mp (by rw [e.2.1]; norm_num)
  let v : {v // v ∈ e.1} := ⟨he.choose, he.choose_spec⟩
  let p : K.edgeCarrier e :=
    ⟨K.edgeMap e (stdSimplex.vertex v), Set.mem_range_self _⟩
  exact ⟨edgeToSupport (K := K) e p, Set.mem_range_self p⟩

/-! ## The assembled locally finite replacement graph -/

/-- The selected complete replacement arc of an abstract edge. -/
noncomputable def replacementArc (e : K.Edge) : G.CentralPolygonalArc e :=
  G.centralPolygonalArc e

theorem edgeInSupport_eq_preimage (e : K.Edge) :
    edgeInSupport (K := K) e = Subtype.val ⁻¹' K.edgeCarrier e := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.2
  · intro hp
    exact ⟨⟨p.1, hp⟩, Subtype.ext rfl⟩

theorem locallyFinite_edgeInSupport :
    LocallyFinite (edgeInSupport (K := K)) := by
  convert K.locallyFinite_edgeCarriers.preimage_continuous
      (continuous_subtype_val : Continuous (Subtype.val : K.support → S)) using 1
  funext e
  exact edgeInSupport_eq_preimage (K := K) e

/-- Any open embedding of the support into the plane gives the relative graph realization needed
by the locally finite Chapter 6 construction.  Local finiteness is transported through the
embedding homeomorphism onto its open range. -/
noncomputable def ofIsOpenEmbedding (f : K.support → Plane)
    (hf : _root_.Topology.IsOpenEmbedding f) : K.PlaneGraphRealization where
  region := Set.range f
  regionOpen := hf.isOpen_range
  map := f
  isEmbedding := hf.isEmbedding
  map_mem_region := fun p ↦ ⟨p, rfl⟩
  vertexApproximationControl := fun _ ↦ 1
  vertexApproximationControl_pos := fun _ ↦ zero_lt_one
  edgeApproximationControl := fun _ ↦ 1
  edgeApproximationControl_pos := fun _ ↦ zero_lt_one
  mapClosedInRegion := by
    have hsurj : Function.Surjective
        (fun p ↦ (⟨f p, ⟨p, rfl⟩⟩ : Set.range f)) := by
      rintro ⟨q, p, rfl⟩
      exact ⟨p, rfl⟩
    rw [hsurj.range_eq]
    exact isClosed_univ
  edgeLocallyFinite := by
    let e : K.support ≃ₜ Set.range f := hf.isEmbedding.toHomeomorph
    have hlocal : LocallyFinite fun a : K.Edge ↦
        e.symm ⁻¹' edgeInSupport (K := K) a :=
      (locallyFinite_edgeInSupport (K := K)).preimage_continuous e.symm.continuous
    convert hlocal using 1
    funext a
    ext q
    constructor
    · intro hq
      change e.symm q ∈ edgeInSupport (K := K) a
      obtain ⟨p, hp, hpq⟩ := hq
      have hpEdge : p ∈ edgeInSupport (K := K) a := by
        rwa [edgeInSupport_eq_preimage (K := K) a]
      have hq : q = e p := by
        apply Subtype.ext
        exact hpq.symm
      rw [hq, e.symm_apply_apply]
      exact hpEdge
    · intro hq
      change e.symm q ∈ edgeInSupport (K := K) a at hq
      change q.1 ∈ f '' {p : K.support | p.1 ∈ K.edgeCarrier a}
      refine ⟨e.symm q, ?_, ?_⟩
      · rw [edgeInSupport_eq_preimage (K := K) a] at hq
        exact hq
      · exact congrArg Subtype.val (e.apply_symm_apply q)

/-- Build a plane graph realization when the source image is closed in a specified open
perturbation region.  Unlike `ofIsOpenEmbedding`, this permits the source image itself to have
boundary, which is the form used on a Rado chart overlap. -/
noncomputable def ofEmbeddingInOpenRegion (V : Set Plane) (hV : IsOpen V)
    (f : K.support → Plane) (hf : _root_.Topology.IsEmbedding f)
    (hmem : ∀ p, f p ∈ V)
    (hclosed : IsClosed (Set.range (fun p ↦ (⟨f p, hmem p⟩ : V)))) :
    K.PlaneGraphRealization where
  region := V
  regionOpen := hV
  map := f
  isEmbedding := hf
  map_mem_region := hmem
  vertexApproximationControl := fun _ ↦ 1
  vertexApproximationControl_pos := fun _ ↦ zero_lt_one
  edgeApproximationControl := fun _ ↦ 1
  edgeApproximationControl_pos := fun _ ↦ zero_lt_one
  mapClosedInRegion := hclosed
  edgeLocallyFinite := by
    let fV : K.support → V := fun p ↦ ⟨f p, hmem p⟩
    have hfV : _root_.Topology.IsEmbedding fV := hf.codRestrict V hmem
    have hlocal : LocallyFinite fun a : K.Edge ↦
        fV '' edgeInSupport (K := K) a :=
      locallyFinite_image_isEmbedding_of_isClosed_range
        (locallyFinite_edgeInSupport (K := K)) hfV hclosed
    convert hlocal using 1
    funext a
    ext q
    constructor
    · rintro ⟨p, hp, hpq⟩
      refine ⟨p, ?_, ?_⟩
      · rw [edgeInSupport_eq_preimage (K := K) a]
        exact hp
      · apply Subtype.ext
        exact hpq
    · rintro ⟨p, hp, hpq⟩
      refine ⟨p, ?_, ?_⟩
      · rw [edgeInSupport_eq_preimage (K := K) a] at hp
        exact hp
      · exact congrArg Subtype.val hpq

theorem range_edgePathInSupport (e : K.Edge) :
    Set.range (edgePathInSupport (K := K) e) = edgeInSupport (K := K) e := by
  apply Set.Subset.antisymm
  · rintro p ⟨r, rfl⟩
    exact ⟨⟨K.edgePath e r, by rw [← K.range_edgePath e]; exact Set.mem_range_self r⟩,
      Subtype.ext rfl⟩
  · rintro p ⟨q, rfl⟩
    have hq : q.1 ∈ Set.range (K.edgePath e) := by
      rw [K.range_edgePath e]
      exact q.2
    obtain ⟨r, hr⟩ := hq
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hr

/-- Restrict the source edge path to its carrier inside the full support. -/
noncomputable def edgePathInSupportToCarrier (e : K.Edge) :
    Set.Icc (0 : ℝ) 1 → edgeInSupport (K := K) e :=
  fun r ↦ ⟨edgePathInSupport (K := K) e r,
    by rw [← range_edgePathInSupport (K := K) e]; exact Set.mem_range_self r⟩

theorem continuous_edgePathInSupportToCarrier (e : K.Edge) :
    Continuous (edgePathInSupportToCarrier (K := K) e) := by
  apply Continuous.subtype_mk
  exact continuous_edgePathInSupport (K := K) e

theorem edgePathInSupportToCarrier_injective (e : K.Edge) :
    Function.Injective (edgePathInSupportToCarrier (K := K) e) := by
  intro r s hrs
  apply edgePathInSupport_injective (K := K) e
  exact congrArg Subtype.val hrs

theorem edgePathInSupportToCarrier_surjective (e : K.Edge) :
    Function.Surjective (edgePathInSupportToCarrier (K := K) e) := by
  rintro ⟨p, hp⟩
  rw [← range_edgePathInSupport (K := K) e] at hp
  obtain ⟨r, rfl⟩ := hp
  exact ⟨r, rfl⟩

/-- The canonical source interval of an edge, inside the support subtype. -/
noncomputable def edgePathInSupportHomeomorph (e : K.Edge) :
    Set.Icc (0 : ℝ) 1 ≃ₜ edgeInSupport (K := K) e := by
  letI : T2Space K.support := G.isEmbedding.t2Space
  exact ((continuous_edgePathInSupportToCarrier (K := K) e).isClosedEmbedding
    (edgePathInSupportToCarrier_injective (K := K) e)).isEmbedding.toHomeomorphOfSurjective
      (edgePathInSupportToCarrier_surjective (K := K) e)

@[simp] theorem edgePathInSupportHomeomorph_apply (e : K.Edge)
    (r : Set.Icc (0 : ℝ) 1) :
    ((G.edgePathInSupportHomeomorph e r).1 : K.support) =
      edgePathInSupport (K := K) e r := rfl

/-- The polygonal replacement map on one closed source edge. -/
noncomputable def replacementEdgeMap (e : K.Edge) :
    edgeInSupport (K := K) e → Plane :=
  fun p ↦ (G.replacementArc e).completePath
    ((G.edgePathInSupportHomeomorph e).symm p)

theorem continuous_replacementEdgeMap (e : K.Edge) :
    Continuous (G.replacementEdgeMap e) :=
  (G.replacementArc e).completePath.continuous.comp
    (G.edgePathInSupportHomeomorph e).symm.continuous

theorem replacementEdgeMap_injective (e : K.Edge) :
    Function.Injective (G.replacementEdgeMap e) :=
  (G.replacementArc e).completePath_injective.comp
    (G.edgePathInSupportHomeomorph e).symm.injective

theorem range_replacementEdgeMap (e : K.Edge) :
    Set.range (G.replacementEdgeMap e) = (G.replacementArc e).completeCarrier := by
  rw [← (G.replacementArc e).range_completePath]
  apply Set.Subset.antisymm
  · rintro y ⟨p, rfl⟩
    exact ⟨(G.edgePathInSupportHomeomorph e).symm p, rfl⟩
  · rintro y ⟨r, rfl⟩
    exact ⟨G.edgePathInSupportHomeomorph e r, by
      simp only [replacementEdgeMap, Homeomorph.symm_apply_apply]⟩

theorem replacementEdgeMap_dist_lt_two_mul_edgeImage_diam (e : K.Edge)
    (p : edgeInSupport (K := K) e) :
    dist (G.replacementEdgeMap e p) (G.map p.1) <
      2 * Metric.diam (G.edgeImage e) := by
  apply (G.replacementArc e).dist_lt_two_mul_edgeImage_diam
  · rw [← G.range_replacementEdgeMap e]
    exact Set.mem_range_self p
  · refine ⟨p.1, ?_, rfl⟩
    change p.1.1 ∈ K.edgeCarrier e
    let q : K.support := p.1
    have hq : q ∈ edgeInSupport (K := K) e := p.2
    have hq' : q ∈ Subtype.val ⁻¹' K.edgeCarrier e := by
      rw [← edgeInSupport_eq_preimage (K := K) e]
      exact hq
    exact hq'

theorem replacementEdgeMap_vertex (e : K.Edge) (v : K.Vertex) (hve : v ∈ e.1) :
    G.replacementEdgeMap e
      ⟨⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩,
        by rw [edgeInSupport_eq_preimage (K := K)]; exact
          (K.vertexPoint_mem_edgeCarrier_iff v e).mpr hve⟩ =
      G.vertexImage v := by
  rw [K.edge_eq_pair e] at hve
  simp only [Finset.mem_insert, Finset.mem_singleton] at hve
  rcases hve with rfl | rfl
  · have hparam : (G.edgePathInSupportHomeomorph e).symm
        ⟨⟨K.vertexPoint (K.edgeFirst e), K.vertexPoint_mem_support _⟩,
          by rw [edgeInSupport_eq_preimage (K := K)]; exact
            (K.vertexPoint_mem_edgeCarrier_iff _ e).mpr (K.edgeFirst_mem e)⟩ =
        ⟨0, by simp⟩ := by
      apply (G.edgePathInSupportHomeomorph e).injective
      rw [(G.edgePathInSupportHomeomorph e).apply_symm_apply]
      apply Subtype.ext
      apply Subtype.ext
      exact (K.edgePath_zero e).symm
    rw [replacementEdgeMap, hparam]
    exact (G.replacementArc e).completePath.source
  · have hparam : (G.edgePathInSupportHomeomorph e).symm
        ⟨⟨K.vertexPoint (K.edgeSecond e), K.vertexPoint_mem_support _⟩,
          by rw [edgeInSupport_eq_preimage (K := K)]; exact
            (K.vertexPoint_mem_edgeCarrier_iff _ e).mpr (K.edgeSecond_mem e)⟩ =
        ⟨1, by simp⟩ := by
      apply (G.edgePathInSupportHomeomorph e).injective
      rw [(G.edgePathInSupportHomeomorph e).apply_symm_apply]
      apply Subtype.ext
      apply Subtype.ext
      exact (K.edgePath_one e).symm
    rw [replacementEdgeMap, hparam]
    exact (G.replacementArc e).completePath.target

/-- The source one-skeleton as a subspace of the complete support. -/
def oneSkeletonInSupport : Set K.support :=
  ⋃ e : K.Edge, edgeInSupport (K := K) e

/-- A chosen source edge carrying a one-skeleton point. -/
noncomputable def containingEdge (p : oneSkeletonInSupport (K := K)) : K.Edge :=
  Classical.choose (Set.mem_iUnion.mp p.2)

theorem mem_edgeInSupport_containingEdge (p : oneSkeletonInSupport (K := K)) :
    p.1 ∈ edgeInSupport (K := K) (containingEdge (K := K) p) :=
  Classical.choose_spec (Set.mem_iUnion.mp p.2)

/-- Simultaneous polygonal replacement of the locally finite source one-skeleton. -/
noncomputable def graphReplacementMap (p : oneSkeletonInSupport (K := K)) : Plane :=
  G.replacementEdgeMap (containingEdge (K := K) p)
    ⟨p.1, mem_edgeInSupport_containingEdge (K := K) p⟩

theorem replacementEdgeMap_eq_on_overlap {e d : K.Edge} (p : K.support)
    (hpe : p ∈ edgeInSupport (K := K) e)
    (hpd : p ∈ edgeInSupport (K := K) d) :
    G.replacementEdgeMap e ⟨p, hpe⟩ = G.replacementEdgeMap d ⟨p, hpd⟩ := by
  by_cases hed : e = d
  · subst d
    rfl
  have hpEdge : p.1 ∈ K.edgeCarrier e ∩ K.edgeCarrier d := by
    rw [edgeInSupport_eq_preimage (K := K)] at hpe hpd
    exact ⟨hpe, hpd⟩
  rw [K.edgeCarrier_inter_eq_sharedVertices hed] at hpEdge
  obtain ⟨v, hve, hvd, hpv⟩ := hpEdge
  let q : K.support := ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩
  have hpq : p = q := Subtype.ext hpv
  calc
    G.replacementEdgeMap e ⟨p, hpe⟩ =
        G.replacementEdgeMap e
          ⟨q, by rw [edgeInSupport_eq_preimage (K := K)]; exact
            (K.vertexPoint_mem_edgeCarrier_iff v e).mpr hve⟩ := by
      subst p
      rfl
    _ = G.vertexImage v := G.replacementEdgeMap_vertex e v hve
    _ = G.replacementEdgeMap d
          ⟨q, by rw [edgeInSupport_eq_preimage (K := K)]; exact
            (K.vertexPoint_mem_edgeCarrier_iff v d).mpr hvd⟩ :=
      (G.replacementEdgeMap_vertex d v hvd).symm
    _ = G.replacementEdgeMap d ⟨p, hpd⟩ := by
      subst p
      rfl

theorem graphReplacementMap_eq (e : K.Edge) (p : oneSkeletonInSupport (K := K))
    (hp : p.1 ∈ edgeInSupport (K := K) e) :
    G.graphReplacementMap p = G.replacementEdgeMap e ⟨p.1, hp⟩ := by
  apply G.replacementEdgeMap_eq_on_overlap

/-- The closed source piece contributed by one edge. -/
def edgePiece (e : K.Edge) : Set (oneSkeletonInSupport (K := K)) :=
  {p | p.1 ∈ edgeInSupport (K := K) e}

theorem locallyFinite_edgePieces : LocallyFinite (edgePiece (K := K)) := by
  convert (locallyFinite_edgeInSupport (K := K)).preimage_continuous
      (continuous_subtype_val : Continuous
        (Subtype.val : oneSkeletonInSupport (K := K) → K.support)) using 1
  funext e
  rfl

theorem isClosed_edgePiece (G : K.PlaneGraphRealization) (e : K.Edge) :
    IsClosed (edgePiece (K := K) e) := by
  let : T2Space K.support := G.isEmbedding.t2Space
  exact (isCompact_edgeInSupport (K := K) e).isClosed.preimage continuous_subtype_val

theorem isCompact_edgePiece (e : K.Edge) :
    IsCompact (edgePiece (K := K) e) := by
  let includeEdge : edgeInSupport (K := K) e →
      oneSkeletonInSupport (K := K) := fun p ↦
    ⟨p.1, Set.mem_iUnion.mpr ⟨e, p.2⟩⟩
  have hinclude : Continuous includeEdge := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hrange : Set.range includeEdge = edgePiece (K := K) e := by
    apply Set.Subset.antisymm
    · rintro p ⟨q, rfl⟩
      exact q.2
    · intro p hp
      exact ⟨⟨p.1, hp⟩, Subtype.ext rfl⟩
  rw [← hrange]
  let : CompactSpace (edgeInSupport (K := K) e) :=
    isCompact_iff_compactSpace.mp (isCompact_edgeInSupport (K := K) e)
  exact isCompact_range hinclude

theorem iUnion_edgePieces :
    (⋃ e : K.Edge, edgePiece (K := K) e) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨e, hpe⟩ := Set.mem_iUnion.mp p.2
  exact Set.mem_iUnion.mpr ⟨e, hpe⟩

theorem continuousOn_graphReplacementMap_edgePiece (e : K.Edge) :
    ContinuousOn G.graphReplacementMap (edgePiece (K := K) e) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let lift : edgePiece (K := K) e → edgeInSupport (K := K) e :=
    fun p ↦ ⟨p.1.1, p.2⟩
  have hlift : Continuous lift := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  have hc : Continuous (G.replacementEdgeMap e ∘ lift) :=
    (G.continuous_replacementEdgeMap e).comp hlift
  convert hc using 1
  funext p
  exact G.graphReplacementMap_eq e p.1 p.2

theorem continuous_graphReplacementMap : Continuous G.graphReplacementMap :=
  (locallyFinite_edgePieces (K := K)).continuous
    (iUnion_edgePieces (K := K)) (G.isClosed_edgePiece)
    (G.continuousOn_graphReplacementMap_edgePiece)

theorem graphReplacementMap_injective : Function.Injective G.graphReplacementMap := by
  intro x y hxy
  let e := containingEdge (K := K) x
  let d := containingEdge (K := K) y
  have hxe : x.1 ∈ edgeInSupport (K := K) e :=
    mem_edgeInSupport_containingEdge (K := K) x
  have hyd : y.1 ∈ edgeInSupport (K := K) d :=
    mem_edgeInSupport_containingEdge (K := K) y
  have hxLocal : G.graphReplacementMap x = G.replacementEdgeMap e ⟨x.1, hxe⟩ :=
    G.graphReplacementMap_eq e x hxe
  have hyLocal : G.graphReplacementMap y = G.replacementEdgeMap d ⟨y.1, hyd⟩ :=
    G.graphReplacementMap_eq d y hyd
  have hlocal : G.replacementEdgeMap e ⟨x.1, hxe⟩ =
      G.replacementEdgeMap d ⟨y.1, hyd⟩ :=
    hxLocal.symm.trans (hxy.trans hyLocal)
  by_cases hed : e = d
  · have hydE : y.1 ∈ edgeInSupport (K := K) e := by
      rw [hed]
      exact hyd
    have hcoh : G.replacementEdgeMap e ⟨y.1, hydE⟩ =
        G.replacementEdgeMap d ⟨y.1, hyd⟩ :=
      G.replacementEdgeMap_eq_on_overlap y.1 hydE hyd
    have hsub := G.replacementEdgeMap_injective e (hlocal.trans hcoh.symm)
    apply Subtype.ext
    exact congrArg (fun z : edgeInSupport (K := K) e ↦ z.1) hsub
  have hxCarrier : G.replacementEdgeMap e ⟨x.1, hxe⟩ ∈
      (G.replacementArc e).completeCarrier := by
    rw [← G.range_replacementEdgeMap e]
    exact Set.mem_range_self (⟨x.1, hxe⟩ : edgeInSupport (K := K) e)
  have hyCarrier : G.replacementEdgeMap d ⟨y.1, hyd⟩ ∈
      (G.replacementArc d).completeCarrier := by
    rw [← G.range_replacementEdgeMap d]
    exact Set.mem_range_self (⟨y.1, hyd⟩ : edgeInSupport (K := K) d)
  have hboth : G.replacementEdgeMap e ⟨x.1, hxe⟩ ∈
      (G.replacementArc e).completeCarrier ∩
        (G.replacementArc d).completeCarrier :=
    ⟨hxCarrier, hlocal ▸ hyCarrier⟩
  rw [(G.replacementArc e).completeCarrier_inter_eq_sharedVertices
    (B := G.replacementArc d) hed] at hboth
  obtain ⟨v, hve, hvd, hvImage⟩ := hboth
  let q : K.support := ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩
  have hxq : ⟨x.1, hxe⟩ =
      (⟨q, by rw [edgeInSupport_eq_preimage (K := K)]; exact
        (K.vertexPoint_mem_edgeCarrier_iff v e).mpr hve⟩ : edgeInSupport (K := K) e) := by
    apply G.replacementEdgeMap_injective e
    rw [G.replacementEdgeMap_vertex e v hve]
    exact hvImage
  have hyq : ⟨y.1, hyd⟩ =
      (⟨q, by rw [edgeInSupport_eq_preimage (K := K)]; exact
        (K.vertexPoint_mem_edgeCarrier_iff v d).mpr hvd⟩ : edgeInSupport (K := K) d) := by
    apply G.replacementEdgeMap_injective d
    rw [G.replacementEdgeMap_vertex d v hvd]
    exact hlocal.symm.trans hvImage
  apply Subtype.ext
  exact (congrArg (fun z : edgeInSupport (K := K) e ↦ z.1) hxq).trans
    (congrArg (fun z : edgeInSupport (K := K) d ↦ z.1) hyq).symm

theorem finite_incidentEdges (G : K.PlaneGraphRealization) (v : K.Vertex) :
    ({e : K.Edge | v ∈ e.1} : Set K.Edge).Finite := by
  let p : G.region := ⟨G.vertexImage v,
    G.map_mem_region ⟨K.vertexPoint v, K.vertexPoint_mem_support v⟩⟩
  apply ((G.locallyFinite_edgeImages).point_finite p).subset
  intro e hve
  exact (G.vertexImage_mem_edgeImage_iff v e).mpr hve

/-- The first radial spoke selected for each abstract edge. -/
noncomputable def leftSpokeFamily (e : K.Edge) : Set Plane :=
  (G.replacementArc e).leftSpoke

/-- The final radial spoke selected for each abstract edge. -/
noncomputable def rightSpokeFamily (e : K.Edge) : Set Plane :=
  (G.replacementArc e).rightSpoke

/-- The trimmed polygonal middle selected for each abstract edge. -/
noncomputable def trimmedCarrierFamily (e : K.Edge) : Set Plane :=
  (G.replacementArc e).trimmedCarrier

/-- The first radial spokes, regarded as subsets of the open chart range. -/
noncomputable def leftSpokeFamilyInRange (e : K.Edge) : Set G.region :=
  {p | p.1 ∈ G.leftSpokeFamily e}

/-- The final radial spokes, regarded as subsets of the open chart range. -/
noncomputable def rightSpokeFamilyInRange (e : K.Edge) : Set G.region :=
  {p | p.1 ∈ G.rightSpokeFamily e}

/-- The trimmed polygonal middles, regarded as subsets of the open chart range. -/
noncomputable def trimmedCarrierFamilyInRange (e : K.Edge) : Set G.region :=
  {p | p.1 ∈ G.trimmedCarrierFamily e}

theorem locallyFinite_leftSpokeFamily : LocallyFinite G.leftSpokeFamilyInRange := by
  intro x
  obtain ⟨U, hUx, hfinite⟩ := G.locallyFinite_vertexDisks x
  refine ⟨U, hUx, ?_⟩
  let V : Set K.Vertex := {v | (G.vertexDiskInRange v ∩ U).Nonempty}
  let E : Set K.Edge := ⋃ v ∈ V, {e : K.Edge | v ∈ e.1}
  have hEfinite : E.Finite := hfinite.biUnion fun v _ ↦ G.finite_incidentEdges v
  apply hEfinite.subset
  intro e he
  obtain ⟨p, hpSpoke, hpU⟩ := he
  have hpDisk := (G.replacementArc e).leftSpoke_subset_vertexDisk hpSpoke
  apply Set.mem_iUnion₂.mpr
  exact ⟨K.edgeFirst e, ⟨p, hpDisk, hpU⟩, K.edgeFirst_mem e⟩

theorem locallyFinite_rightSpokeFamily : LocallyFinite G.rightSpokeFamilyInRange := by
  intro x
  obtain ⟨U, hUx, hfinite⟩ := G.locallyFinite_vertexDisks x
  refine ⟨U, hUx, ?_⟩
  let V : Set K.Vertex := {v | (G.vertexDiskInRange v ∩ U).Nonempty}
  let E : Set K.Edge := ⋃ v ∈ V, {e : K.Edge | v ∈ e.1}
  have hEfinite : E.Finite := hfinite.biUnion fun v _ ↦ G.finite_incidentEdges v
  apply hEfinite.subset
  intro e he
  obtain ⟨p, hpSpoke, hpU⟩ := he
  have hpDisk := (G.replacementArc e).rightSpoke_subset_vertexDisk hpSpoke
  apply Set.mem_iUnion₂.mpr
  exact ⟨K.edgeSecond e, ⟨p, hpDisk, hpU⟩, K.edgeSecond_mem e⟩

theorem locallyFinite_trimmedCarrierFamily :
    LocallyFinite G.trimmedCarrierFamilyInRange := by
  apply G.locallyFinite_edgeCentralTubes.subset
  intro e p hp
  exact (G.replacementArc e).resolvedCarrier_subset
    ((G.replacementArc e).trimmedCarrier_subset_resolvedCarrier hp)

private theorem locallyFinite_union_family {I X : Type*} [TopologicalSpace X]
    {f g : I → Set X} (hf : LocallyFinite f) (hg : LocallyFinite g) :
    LocallyFinite fun i ↦ f i ∪ g i := by
  intro x
  obtain ⟨U, hUx, hUf⟩ := hf x
  obtain ⟨V, hVx, hVg⟩ := hg x
  refine ⟨U ∩ V, Filter.inter_mem hUx hVx, ?_⟩
  apply (hUf.union hVg).subset
  intro i hi
  obtain ⟨p, hpfg, hpUV⟩ := hi
  rcases hpfg with hpf | hpg
  · exact Or.inl ⟨p, hpf, hpUV.1⟩
  · exact Or.inr ⟨p, hpg, hpUV.2⟩

/-- The `completeCarrierInRange` declaration. -/
noncomputable def completeCarrierInRange (e : K.Edge) : Set G.region :=
  {p | p.1 ∈ (G.replacementArc e).completeCarrier}

theorem locallyFinite_completeCarriers : LocallyFinite G.completeCarrierInRange := by
  have hleftMiddle := locallyFinite_union_family
    G.locallyFinite_leftSpokeFamily G.locallyFinite_trimmedCarrierFamily
  have hall := locallyFinite_union_family hleftMiddle G.locallyFinite_rightSpokeFamily
  have heq : (fun e : K.Edge ↦
      G.leftSpokeFamilyInRange e ∪ G.trimmedCarrierFamilyInRange e ∪
        G.rightSpokeFamilyInRange e) = G.completeCarrierInRange := by
    funext e
    ext p
    simp only [CentralPolygonalArc.completeCarrier, leftSpokeFamily,
      trimmedCarrierFamily, rightSpokeFamily, leftSpokeFamilyInRange,
      trimmedCarrierFamilyInRange, rightSpokeFamilyInRange, completeCarrierInRange,
      Set.mem_union, Set.mem_ofPred_eq]
  rw [← heq]
  exact hall

theorem isCompact_completeCarrier (e : K.Edge) :
    IsCompact (G.replacementArc e).completeCarrier := by
  have hleft : IsCompact (G.replacementArc e).leftSpoke := by
    rw [CentralPolygonalArc.leftSpoke, ← Path.range_segment]
    exact isCompact_range (Path.segment _ _).continuous
  have hmiddle : IsCompact (G.replacementArc e).trimmedCarrier := by
    apply (isCompact_Icc : IsCompact
      (Set.Icc (G.replacementArc e).exitData.left
        (G.replacementArc e).exitData.right)).image_of_continuousOn
    exact (G.replacementArc e).parameterization.continuousOn.mono fun t ht ↦
      ⟨(G.replacementArc e).exitData.left_nonneg.trans ht.1,
        ht.2.trans (G.replacementArc e).exitData.right_le_one⟩
  have hright : IsCompact (G.replacementArc e).rightSpoke := by
    rw [CentralPolygonalArc.rightSpoke, ← Path.range_segment]
    exact isCompact_range (Path.segment _ _).continuous
  exact (hleft.union hmiddle).union hright

theorem isClosed_completeCarrier (e : K.Edge) :
    IsClosed (G.replacementArc e).completeCarrier :=
  (G.isCompact_completeCarrier e).isClosed

/-- Every complete replacement arc remains inside the open chart range. -/
theorem completeCarrier_subset_range (e : K.Edge) :
    (G.replacementArc e).completeCarrier ⊆ G.region := by
  intro p hp
  rcases hp with (hpLeft | hpMiddle) | hpRight
  · exact G.vertexDisk_subset_range (K.edgeFirst e)
      ((G.replacementArc e).leftSpoke_subset_vertexDisk hpLeft)
  · exact G.edgeCentralTube_subset_range e
      ((G.replacementArc e).resolvedCarrier_subset
        ((G.replacementArc e).trimmedCarrier_subset_resolvedCarrier hpMiddle))
  · exact G.vertexDisk_subset_range (K.edgeSecond e)
      ((G.replacementArc e).rightSpoke_subset_vertexDisk hpRight)

theorem graphReplacementMap_mem_range (p : oneSkeletonInSupport (K := K)) :
    G.graphReplacementMap p ∈ G.region := by
  let e := containingEdge (K := K) p
  have hp : p.1 ∈ edgeInSupport (K := K) e :=
    mem_edgeInSupport_containingEdge (K := K) p
  apply G.completeCarrier_subset_range e
  rw [G.graphReplacementMap_eq e p hp, ← G.range_replacementEdgeMap e]
  exact Set.mem_range_self (⟨p.1, hp⟩ : edgeInSupport (K := K) e)

/-- The simultaneous replacement map with its natural open chart-range codomain. -/
noncomputable def graphReplacementMapInRange
    (p : oneSkeletonInSupport (K := K)) : G.region :=
  ⟨G.graphReplacementMap p, G.graphReplacementMap_mem_range p⟩

theorem continuous_graphReplacementMapInRange :
    Continuous G.graphReplacementMapInRange := by
  exact G.continuous_graphReplacementMap.subtype_mk _

theorem graphReplacementMapInRange_injective :
    Function.Injective G.graphReplacementMapInRange := by
  intro p q hpq
  apply G.graphReplacementMap_injective
  exact congrArg Subtype.val hpq

/-- The relative image of the part of a source set carried by one edge. -/
private def edgewiseImageInRange (C : Set (oneSkeletonInSupport (K := K)))
    (e : K.Edge) : Set G.region :=
  G.graphReplacementMapInRange '' (C ∩ edgePiece (K := K) e)

private theorem locallyFinite_edgewiseImage
    (C : Set (oneSkeletonInSupport (K := K))) :
    LocallyFinite (G.edgewiseImageInRange C) := by
  apply G.locallyFinite_completeCarriers.subset
  intro e y hy
  obtain ⟨p, hp, rfl⟩ := hy
  change G.graphReplacementMap p ∈ (G.replacementArc e).completeCarrier
  rw [G.graphReplacementMap_eq e p hp.2, ← G.range_replacementEdgeMap e]
  exact Set.mem_range_self
    (⟨p.1, hp.2⟩ : edgeInSupport (K := K) e)

private theorem isClosed_edgewiseImage
    (C : Set (oneSkeletonInSupport (K := K))) (hC : IsClosed C)
    (e : K.Edge) : IsClosed (G.edgewiseImageInRange C e) := by
  have hcompact : IsCompact (C ∩ edgePiece (K := K) e) :=
    (isCompact_edgePiece (K := K) e).inter_left hC
  exact (hcompact.image G.continuous_graphReplacementMapInRange).isClosed

private theorem image_graphReplacementMapInRange_eq_iUnion_edgewiseImage
    (C : Set (oneSkeletonInSupport (K := K))) :
    G.graphReplacementMapInRange '' C =
      ⋃ e : K.Edge, G.edgewiseImageInRange C e := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hpC, rfl⟩
    let e := containingEdge (K := K) p
    exact Set.mem_iUnion.mpr ⟨e, p, ⟨hpC,
      mem_edgeInSupport_containingEdge (K := K) p⟩, rfl⟩
  · intro y hy
    obtain ⟨e, p, hp, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨p, hp.1, rfl⟩

theorem isClosedMap_graphReplacementMapInRange :
    IsClosedMap G.graphReplacementMapInRange := by
  intro C hC
  rw [G.image_graphReplacementMapInRange_eq_iUnion_edgewiseImage C]
  exact (G.locallyFinite_edgewiseImage C).isClosed_iUnion
    (G.isClosed_edgewiseImage C hC)

/-- The simultaneous polygonal replacement is closed in the open chart range. -/
theorem isClosedEmbedding_graphReplacementMapInRange :
    _root_.Topology.IsClosedEmbedding G.graphReplacementMapInRange :=
  _root_.Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    G.continuous_graphReplacementMapInRange G.graphReplacementMapInRange_injective
    G.isClosedMap_graphReplacementMapInRange

/-- The locally finite replacement graph has the source graph topology in the ambient plane. -/
theorem isEmbedding_graphReplacementMap :
    _root_.Topology.IsEmbedding G.graphReplacementMap := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    G.isClosedEmbedding_graphReplacementMapInRange.isEmbedding
  simpa only [Function.comp_def, graphReplacementMapInRange] using h

theorem range_graphReplacementMap :
    Set.range G.graphReplacementMap =
      ⋃ e : K.Edge, (G.replacementArc e).completeCarrier := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, rfl⟩
    let e := containingEdge (K := K) p
    have hp : p.1 ∈ edgeInSupport (K := K) e :=
      mem_edgeInSupport_containingEdge (K := K) p
    apply Set.mem_iUnion.mpr
    refine ⟨e, ?_⟩
    rw [G.graphReplacementMap_eq e p hp, ← G.range_replacementEdgeMap e]
    exact Set.mem_range_self
      (⟨p.1, hp⟩ : edgeInSupport (K := K) e)
  · intro y hy
    obtain ⟨e, hye⟩ := Set.mem_iUnion.mp hy
    rw [← G.range_replacementEdgeMap e] at hye
    obtain ⟨p, rfl⟩ := hye
    let q : oneSkeletonInSupport (K := K) :=
      ⟨p.1, Set.mem_iUnion.mpr ⟨e, p.2⟩⟩
    exact ⟨q, G.graphReplacementMap_eq e q p.2⟩

/-- Pointwise closeness to the original chart realization. -/
def IsPhiApproximation (phi : K.support → ℝ) (f : K.support → Plane) : Prop :=
  ∀ p, dist (f p) (G.map p) < phi p

/-- The edge-mesh condition which converts setwise polygonal tubes into a pointwise control. -/
def EdgeImagesControlled (phi : K.support → ℝ) : Prop :=
  ∀ e : K.Edge, ∀ p ∈ edgeInSupport (K := K) e,
    2 * Metric.diam (G.edgeImage e) < phi p

theorem isPhiApproximation_graphReplacementMap {phi : K.support → ℝ}
    (hsmall : G.EdgeImagesControlled phi) :
    ∀ p : oneSkeletonInSupport (K := K),
      dist (G.graphReplacementMap p) (G.map p.1) < phi p.1 := by
  intro p
  let e := containingEdge (K := K) p
  have hp : p.1 ∈ edgeInSupport (K := K) e :=
    mem_edgeInSupport_containingEdge (K := K) p
  rw [G.graphReplacementMap_eq e p hp]
  exact (G.replacementEdgeMap_dist_lt_two_mul_edgeImage_diam e ⟨p.1, hp⟩).trans
    (hsmall e p.1 hp)

/-- A strongly-positive tolerance has a positive uniform lower bound on each compact edge,
although it need not have a positive lower bound on the whole noncompact complex. -/
theorem exists_edgeControlLowerBound {phi : K.support → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) (e : K.Edge) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ p ∈ edgeInSupport (K := K) e, eps ≤ phi p := by
  exact hphi (edgeInSupport (K := K) e) (isCompact_edgeInSupport (K := K) e)
    (Set.subset_univ _)

/-- A fixed positive edgewise control selected from strong positivity. -/
noncomputable def edgeControlRadius {phi : K.support → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) (e : K.Edge) : ℝ :=
  Classical.choose (exists_edgeControlLowerBound (K := K) hphi e)

theorem edgeControlRadius_pos {phi : K.support → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) (e : K.Edge) :
    0 < edgeControlRadius (K := K) hphi e :=
  (Classical.choose_spec (exists_edgeControlLowerBound (K := K) hphi e)).1

theorem edgeControlRadius_le {phi : K.support → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) (e : K.Edge)
    {p : K.support} (hp : p ∈ edgeInSupport (K := K) e) :
    edgeControlRadius (K := K) hphi e ≤ phi p :=
  (Classical.choose_spec (exists_edgeControlLowerBound (K := K) hphi e)).2 p hp

theorem edgeImagesControlled_of_diam_lt_controlRadius {phi : K.support → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi)
    (hsmall : ∀ e : K.Edge,
      2 * Metric.diam (G.edgeImage e) < edgeControlRadius (K := K) hphi e) :
    G.EdgeImagesControlled phi := by
  intro e p hp
  exact (hsmall e).trans_le (edgeControlRadius_le (K := K) hphi e hp)

/-- Include a maximal face into the whole source support. -/
def faceToSupport (f : K.Face)
    (p : stdSimplex ℝ {v // v ∈ K.faceVertices f}) : K.support :=
  ⟨K.faceMap f p, Set.mem_iUnion.mpr ⟨f, Set.mem_range_self p⟩⟩

theorem continuous_faceToSupport (f : K.Face) :
    Continuous (faceToSupport (K := K) f) := by
  apply Continuous.subtype_mk
  exact K.faceMap_continuous f

/-- A face carrier as a compact subset of the whole source support. -/
def faceInSupport (f : K.Face) : Set K.support :=
  Set.range (faceToSupport (K := K) f)

theorem isCompact_faceInSupport (f : K.Face) :
    IsCompact (faceInSupport (K := K) f) :=
  isCompact_range (continuous_faceToSupport (K := K) f)

theorem exists_faceControlLowerBound {phi : K.support → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) (f : K.Face) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ p ∈ faceInSupport (K := K) f, eps ≤ phi p :=
  hphi (faceInSupport (K := K) f) (isCompact_faceInSupport (K := K) f)
    (Set.subset_univ _)

/-- A fixed positive facewise control selected from strong positivity. -/
noncomputable def faceControlRadius {phi : K.support → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) (f : K.Face) : ℝ :=
  Classical.choose (exists_faceControlLowerBound (K := K) hphi f)

theorem faceControlRadius_pos {phi : K.support → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) (f : K.Face) :
    0 < faceControlRadius (K := K) hphi f :=
  (Classical.choose_spec (exists_faceControlLowerBound (K := K) hphi f)).1

theorem faceControlRadius_le {phi : K.support → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) (f : K.Face)
    {p : K.support} (hp : p ∈ faceInSupport (K := K) f) :
    faceControlRadius (K := K) hphi f ≤ phi p :=
  (Classical.choose_spec (exists_faceControlLowerBound (K := K) hphi f)).2 p hp

end PlaneGraphRealization

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
