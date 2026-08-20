/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalPolyhedron
import LeanPool.ClassificationOfSurfaces.Moise.CommonSubdivision

/-!
# Finite unions of polygonal disks

The cellwise intrinsic approximation produces finitely many polygonal closed disks whose
interiors are compatible.  Independently chosen disk triangulations need not agree on their
common boundary segments.  This file instead cuts one enclosing triangle by every edge line in
the family and retains precisely the chambers lying inside at least one polygon.  The resulting
single triangle mesh has support equal to the union.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace TriangleMesh

/-- The canonical barycentric embedding of a finite plane triangle mesh realization. -/
noncomputable def coordinateEmbed (M : TriangleMesh) :
    GeometricRealization M.Vertex M.triangles → Plane :=
  fun x ↦ M.toPlaneComplex.baryEval x.1

theorem isEmbedding_coordinateEmbed (M : TriangleMesh) :
    _root_.Topology.IsEmbedding M.coordinateEmbed := by
  have hfaces : GeometricRealization M.Vertex M.triangles =
      GeometricRealization M.Vertex M.toPlaneComplex.cells := by
    rw [M.toPlaneComplex_cells]
  let hhomeo := (Homeomorph.setCongr hfaces).trans
    (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2)
  have hhomeo_apply (x : GeometricRealization M.Vertex M.triangles) :
      (hhomeo x).1 = M.coordinateEmbed x := by
    rfl
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp hhomeo.isEmbedding
  have heq : (Subtype.val ∘ hhomeo) = M.coordinateEmbed := by
    funext x
    exact hhomeo_apply x
  rw [heq] at h
  exact h

theorem range_coordinateEmbed (M : TriangleMesh) :
    Set.range M.coordinateEmbed = M.toPlaneComplex.support := by
  have hfaces : GeometricRealization M.Vertex M.triangles =
      GeometricRealization M.Vertex M.toPlaneComplex.cells := by
    rw [M.toPlaneComplex_cells]
  let hhomeo := (Homeomorph.setCongr hfaces).trans
    (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2)
  have hhomeo_apply (x : GeometricRealization M.Vertex M.triangles) :
      (hhomeo x).1 = M.coordinateEmbed x := by
    rfl
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    rw [← hhomeo_apply y]
    exact (hhomeo y).2
  · intro x hx
    obtain ⟨y, hy⟩ := hhomeo.surjective ⟨x, hx⟩
    refine ⟨y, ?_⟩
    rw [← hhomeo_apply y]
    exact congrArg Subtype.val hy

/-- Restrict the coordinate embedding to any plane region containing the mesh support. -/
noncomputable def coordinateEmbedInto (M : TriangleMesh) (W : Set Plane)
    (hW : M.toPlaneComplex.support ⊆ W) :
    GeometricRealization M.Vertex M.triangles → W :=
  fun x ↦ ⟨M.coordinateEmbed x, hW (by
    rw [← M.range_coordinateEmbed]
    exact Set.mem_range_self x)⟩

theorem isEmbedding_coordinateEmbedInto (M : TriangleMesh) (W : Set Plane)
    (hW : M.toPlaneComplex.support ⊆ W) :
    _root_.Topology.IsEmbedding (M.coordinateEmbedInto W hW) :=
  M.isEmbedding_coordinateEmbed.codRestrict W _

end TriangleMesh

namespace PolygonalFamily

variable {ι : Type*} [Fintype ι] (J : ι → PolygonalCircle)

/-- The union of the finitely many closed polygonal disks. -/
def closedRegion : Set Plane :=
  ⋃ i, (J i).closedRegion

omit [Fintype ι] in
theorem isCompact_closedRegion [Finite ι] : IsCompact (closedRegion J) := by
  let := Fintype.ofFinite ι
  exact isCompact_iUnion fun i ↦ (J i).isCompact_closedRegion

/-- A positive radius of a ball containing every disk in the family. -/
noncomputable def enclosingRadius : ℝ :=
  max ((isCompact_closedRegion J).isBounded.subset_closedBall (0 : Plane)).choose 1

theorem enclosingRadius_pos : 0 < enclosingRadius J :=
  lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem closedRegion_subset_enclosingBall :
    closedRegion J ⊆ Metric.closedBall (0 : Plane) (enclosingRadius J) := by
  intro x hx
  have h := ((isCompact_closedRegion J).isBounded.subset_closedBall
    (0 : Plane)).choose_spec hx
  exact Metric.closedBall_subset_closedBall (le_max_left _ _) h

/-- The common enclosing triangle. -/
noncomputable def enclosingMesh : TriangleMesh :=
  TriangleMesh.single (PolygonalCircle.enclosingTriangleVertices (enclosingRadius J))
    (PolygonalCircle.enclosingTriangleVertices_affineIndependent (enclosingRadius_pos J))

theorem closedRegion_subset_enclosingMesh_support :
    closedRegion J ⊆ (enclosingMesh J).toPlaneComplex.support := by
  rw [enclosingMesh, TriangleMesh.single_support]
  exact (closedRegion_subset_enclosingBall J).trans
    (PolygonalCircle.closedBall_subset_enclosingTriangle (enclosingRadius_pos J))

/-- Every supporting line of every polygon in the family. -/
noncomputable def edgeLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset ι).toList.flatMap fun i ↦ (J i).edgeLines

theorem edgeLine_mem_edgeLines (i : ι) (k : ZMod (J i).n) :
    (J i).edgeLine k ∈ edgeLines J := by
  rw [edgeLines, List.mem_flatMap]
  exact ⟨i, by simp, (J i).edgeLine_mem_edgeLines k⟩

/-- The common supporting-line arrangement. -/
noncomputable def arrangementMesh : TriangleMesh :=
  (enclosingMesh J).refineByLines (edgeLines J)

theorem arrangementMesh_support :
    (arrangementMesh J).toPlaneComplex.support =
      (enclosingMesh J).toPlaneComplex.support :=
  (enclosingMesh J).refineByLines_support (edgeLines J)

theorem closedRegion_subset_arrangementMesh_support :
    closedRegion J ⊆ (arrangementMesh J).toPlaneComplex.support := by
  rw [arrangementMesh_support]
  exact closedRegion_subset_enclosingMesh_support J

theorem arrangementMesh_isMonochromatic (i : ι) (k : ZMod (J i).n) :
    (arrangementMesh J).IsMonochromatic ((J i).edgeLine k) :=
  (enclosingMesh J).refineByLines_isMonochromatic_of_mem
    (edgeLines J) (edgeLine_mem_edgeLines J i k)

/-- Carrier of one maximal chamber of the common arrangement. -/
def arrangementTriangleCarrier (t : Finset (arrangementMesh J).Vertex) : Set Plane :=
  convexHull ℝ ((arrangementMesh J).position '' (t : Set _))

theorem convex_arrangementTriangleCarrier
    (t : Finset (arrangementMesh J).Vertex) :
    Convex ℝ (arrangementTriangleCarrier J t) :=
  convex_convexHull ℝ _

theorem isClosed_arrangementTriangleCarrier
    (t : Finset (arrangementMesh J).Vertex) :
    IsClosed (arrangementTriangleCarrier J t) :=
  (t.finite_toSet.image (arrangementMesh J).position).isClosed_convexHull ℝ

theorem arrangementTriangleCarrier_interior_nonempty
    {t : Finset (arrangementMesh J).Vertex} (ht : t ∈ (arrangementMesh J).triangles) :
    (interior (arrangementTriangleCarrier J t)).Nonempty := by
  apply (convex_arrangementTriangleCarrier J t).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [arrangementTriangleCarrier, affineSpan_convexHull]
  have hrange : Set.range (fun v : t ↦ (arrangementMesh J).position v) =
      (arrangementMesh J).position '' (t : Set _) := by
    ext x
    simp
  rw [← hrange]
  apply
    ((arrangementMesh J).affineIndependent_triangle t ht)
      |>.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Fintype.card_coe, (arrangementMesh J).card_triangle t ht]
  simp [Plane]

theorem closure_interior_arrangementTriangleCarrier
    {t : Finset (arrangementMesh J).Vertex} (ht : t ∈ (arrangementMesh J).triangles) :
    closure (interior (arrangementTriangleCarrier J t)) =
      arrangementTriangleCarrier J t := by
  calc
    closure (interior (arrangementTriangleCarrier J t)) =
        closure (arrangementTriangleCarrier J t) :=
      (convex_arrangementTriangleCarrier J t).closure_interior_eq_closure_of_nonempty_interior
        (arrangementTriangleCarrier_interior_nonempty J ht)
    _ = arrangementTriangleCarrier J t :=
      (isClosed_arrangementTriangleCarrier J t).closure_eq

/-- Every open arrangement chamber misses every polygon boundary in the family. -/
theorem arrangementTriangle_interior_disjoint_carrier
    (i : ι) {t : Finset (arrangementMesh J).Vertex}
    (ht : t ∈ (arrangementMesh J).triangles) :
    Disjoint (interior (arrangementTriangleCarrier J t)) (J i).carrier := by
  rw [Set.disjoint_left]
  intro x hxint hxcarrier
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxcarrier
  have hxzero : (J i).edgeLine k x = 0 :=
    (J i).edgeLine_eq_zero_of_mem_edgeSegment k hxk
  rcases arrangementMesh_isMonochromatic J i k t ht with hpos | hneg
  · have hsubset : arrangementTriangleCarrier J t ⊆
        {y | 0 ≤ (J i).edgeLine k y} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hpos v hv
      · exact (convex_Ici (0 : ℝ)).affine_preimage ((J i).edgeLine k)
    have hxstrict := interior_mono hsubset hxint
    rw [(J i).interior_edgeLine_nonneg k] at hxstrict
    change 0 < (J i).edgeLine k x at hxstrict
    linarith
  · have hsubset : arrangementTriangleCarrier J t ⊆
        {y | (J i).edgeLine k y ≤ 0} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact (convex_Iic (0 : ℝ)).affine_preimage ((J i).edgeLine k)
    have hxstrict := interior_mono hsubset hxint
    rw [(J i).interior_edgeLine_nonpos k] at hxstrict
    change (J i).edgeLine k x < 0 at hxstrict
    linarith

theorem arrangementTriangle_interior_side
    (i : ι) {t : Finset (arrangementMesh J).Vertex}
    (ht : t ∈ (arrangementMesh J).triangles) :
    interior (arrangementTriangleCarrier J t) ⊆ (J i).interiorRegion ∨
      interior (arrangementTriangleCarrier J t) ⊆ (J i).exteriorRegion := by
  let s := interior (arrangementTriangleCarrier J t)
  have hsconn : IsPreconnected s :=
    (convex_arrangementTriangleCarrier J t).interior.isPreconnected
  have hsoff : s ⊆ (J i).carrierᶜ := by
    intro x hx
    exact fun hxcarrier ↦ Set.disjoint_left.mp
      (arrangementTriangle_interior_disjoint_carrier J i ht) hx hxcarrier
  have hsunion : s ⊆ (J i).interiorRegion ∪ (J i).exteriorRegion := by
    rw [(J i).interior_union_exterior]
    exact hsoff
  obtain ⟨x, hx⟩ := arrangementTriangleCarrier_interior_nonempty J ht
  rcases hsunion hx with hxin | hxout
  · exact Or.inl <| hsconn.subset_left_of_subset_union
      (J i).isOpen_interiorRegion (J i).isOpen_exteriorRegion
      (J i).disjoint_interior_exterior hsunion ⟨x, hx, hxin⟩
  · exact Or.inr <| hsconn.subset_right_of_subset_union
      (J i).isOpen_interiorRegion (J i).isOpen_exteriorRegion
      (J i).disjoint_interior_exterior hsunion ⟨x, hx, hxout⟩

/-- A chamber is retained when it lies on the bounded side of at least one polygon. -/
def IsInteriorArrangementTriangle
    (t : Finset (arrangementMesh J).Vertex) : Prop :=
  ∃ i, interior (arrangementTriangleCarrier J t) ⊆ (J i).interiorRegion

/-- The common finite mesh of the union of all closed regions. -/
noncomputable def closedRegionMesh : TriangleMesh := by
  classical
  exact (arrangementMesh J).restrictTriangles (IsInteriorArrangementTriangle J)

theorem closedRegionMesh_triangle_mem
    {t : Finset (closedRegionMesh J).Vertex} :
    t ∈ (closedRegionMesh J).triangles ↔
      t ∈ (arrangementMesh J).triangles ∧ IsInteriorArrangementTriangle J t := by
  classical
  exact (arrangementMesh J).mem_restrictTriangles_triangles
    (IsInteriorArrangementTriangle J)

theorem arrangementTriangleCarrier_subset_closedRegion
    {t : Finset (arrangementMesh J).Vertex} (ht : t ∈ (arrangementMesh J).triangles)
    (hinside : IsInteriorArrangementTriangle J t) :
    arrangementTriangleCarrier J t ⊆ closedRegion J := by
  obtain ⟨i, hi⟩ := hinside
  rw [← closure_interior_arrangementTriangleCarrier J ht]
  exact (closure_mono hi).trans fun x hx ↦ Set.mem_iUnion.mpr
    ⟨i, by simpa only [PolygonalCircle.closedRegion] using hx⟩

theorem closedRegionMesh_support_subset :
    (closedRegionMesh J).toPlaneComplex.support ⊆ closedRegion J := by
  rw [TriangleMesh.toPlaneComplex_support]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨htarr, htinside⟩ := (closedRegionMesh_triangle_mem J).mp ht
  exact arrangementTriangleCarrier_subset_closedRegion J htarr htinside hxt

theorem interiorRegion_subset_closedRegionMesh_support (i : ι) :
    (J i).interiorRegion ⊆ (closedRegionMesh J).toPlaneComplex.support := by
  intro x hxinside
  have hxclosed : x ∈ closedRegion J := Set.mem_iUnion.mpr
    ⟨i, by rw [(J i).closedRegion_eq_union]; exact Or.inl hxinside⟩
  have hxsupport := closedRegion_subset_arrangementMesh_support J hxclosed
  rw [TriangleMesh.toPlaneComplex_support] at hxsupport
  simp only [Set.mem_iUnion] at hxsupport
  obtain ⟨t, ht, hxt⟩ := hxsupport
  have hxclosure : x ∈ closure (interior (arrangementTriangleCarrier J t)) := by
    rw [closure_interior_arrangementTriangleCarrier J ht]
    exact hxt
  have hxclosureInter : x ∈ closure
      ((J i).interiorRegion ∩ interior (arrangementTriangleCarrier J t)) :=
    (J i).isOpen_interiorRegion.inter_closure ⟨hxinside, hxclosure⟩
  obtain ⟨y, hyinside, hyt⟩ := Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
  have htinside : interior (arrangementTriangleCarrier J t) ⊆
      (J i).interiorRegion := by
    rcases arrangementTriangle_interior_side J i ht with hin | hout
    · exact hin
    · exact False.elim <| Set.disjoint_left.mp (J i).disjoint_interior_exterior
        hyinside (hout hyt)
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [Set.mem_iUnion]
  exact ⟨t, (closedRegionMesh_triangle_mem J).mpr
    ⟨ht, ⟨i, htinside⟩⟩, hxt⟩

theorem closedRegion_subset_closedRegionMesh_support :
    closedRegion J ⊆ (closedRegionMesh J).toPlaneComplex.support := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  rw [PolygonalCircle.closedRegion] at hxi
  exact closure_minimal (interiorRegion_subset_closedRegionMesh_support J i)
    (closedRegionMesh J).toPlaneComplex.isCompact_support.isClosed hxi

/-- Exact support of the common family mesh. -/
theorem closedRegionMesh_support :
    (closedRegionMesh J).toPlaneComplex.support = closedRegion J :=
  Set.Subset.antisymm (closedRegionMesh_support_subset J)
    (closedRegion_subset_closedRegionMesh_support J)

/-! ## Synchronized submeshes of one family arrangement -/

/-- The union of a selected subfamily of polygonal closed disks. -/
def selectedClosedRegion (p : ι → Prop) : Set Plane :=
  ⋃ i, ⋃ (_ : p i), (J i).closedRegion

/-- An arrangement chamber belongs to the selected submesh when its interior lies on the
bounded side of one selected polygon. -/
def IsSelectedInteriorArrangementTriangle (p : ι → Prop)
    (t : Finset (arrangementMesh J).Vertex) : Prop :=
  ∃ i, p i ∧ interior (arrangementTriangleCarrier J t) ⊆ (J i).interiorRegion

/-- Restrict the common arrangement to the chambers belonging to a selected subfamily.
Different predicates therefore produce meshes with definitionally the same ambient vertex
type and position map. -/
noncomputable def selectedClosedRegionMesh (p : ι → Prop) : TriangleMesh := by
  classical
  exact (arrangementMesh J).restrictTriangles
    (IsSelectedInteriorArrangementTriangle J p)

theorem selectedClosedRegionMesh_triangle_mem (p : ι → Prop)
    {t : Finset (selectedClosedRegionMesh J p).Vertex} :
    t ∈ (selectedClosedRegionMesh J p).triangles ↔
      t ∈ (arrangementMesh J).triangles ∧
        IsSelectedInteriorArrangementTriangle J p t := by
  classical
  exact (arrangementMesh J).mem_restrictTriangles_triangles
    (IsSelectedInteriorArrangementTriangle J p)

theorem arrangementTriangleCarrier_subset_selectedClosedRegion
    (p : ι → Prop) {t : Finset (arrangementMesh J).Vertex}
    (ht : t ∈ (arrangementMesh J).triangles)
    (hinside : IsSelectedInteriorArrangementTriangle J p t) :
    arrangementTriangleCarrier J t ⊆ selectedClosedRegion J p := by
  obtain ⟨i, hpi, hi⟩ := hinside
  rw [← closure_interior_arrangementTriangleCarrier J ht]
  exact (closure_mono hi).trans fun x hx ↦ Set.mem_iUnion.mpr
    ⟨i, Set.mem_iUnion.mpr
      ⟨hpi, by simpa only [PolygonalCircle.closedRegion] using hx⟩⟩

theorem selectedClosedRegionMesh_support_subset (p : ι → Prop) :
    (selectedClosedRegionMesh J p).toPlaneComplex.support ⊆
      selectedClosedRegion J p := by
  rw [TriangleMesh.toPlaneComplex_support]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨htarr, htinside⟩ :=
    (selectedClosedRegionMesh_triangle_mem J p).mp ht
  exact arrangementTriangleCarrier_subset_selectedClosedRegion
    J p htarr htinside hxt

theorem interiorRegion_subset_selectedClosedRegionMesh_support
    (p : ι → Prop) (i : ι) (hpi : p i) :
    (J i).interiorRegion ⊆
      (selectedClosedRegionMesh J p).toPlaneComplex.support := by
  intro x hxinside
  have hxselected : x ∈ selectedClosedRegion J p := Set.mem_iUnion.mpr
    ⟨i, Set.mem_iUnion.mpr
      ⟨hpi, by
        rw [(J i).closedRegion_eq_union]
        exact Or.inl hxinside⟩⟩
  have hxclosed : x ∈ closedRegion J := by
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxselected
    obtain ⟨_, hxi⟩ := Set.mem_iUnion.mp hxi
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  have hxsupport := closedRegion_subset_arrangementMesh_support J hxclosed
  rw [TriangleMesh.toPlaneComplex_support] at hxsupport
  simp only [Set.mem_iUnion] at hxsupport
  obtain ⟨t, ht, hxt⟩ := hxsupport
  have hxclosure : x ∈ closure
      (interior (arrangementTriangleCarrier J t)) := by
    rw [closure_interior_arrangementTriangleCarrier J ht]
    exact hxt
  have hxclosureInter : x ∈ closure
      ((J i).interiorRegion ∩ interior (arrangementTriangleCarrier J t)) :=
    (J i).isOpen_interiorRegion.inter_closure ⟨hxinside, hxclosure⟩
  obtain ⟨y, hyinside, hyt⟩ := Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
  have htinside : interior (arrangementTriangleCarrier J t) ⊆
      (J i).interiorRegion := by
    rcases arrangementTriangle_interior_side J i ht with hin | hout
    · exact hin
    · exact False.elim <| Set.disjoint_left.mp
        (J i).disjoint_interior_exterior hyinside (hout hyt)
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [Set.mem_iUnion]
  exact ⟨t, (selectedClosedRegionMesh_triangle_mem J p).mpr
    ⟨ht, ⟨i, hpi, htinside⟩⟩, hxt⟩

theorem selectedClosedRegion_subset_selectedClosedRegionMesh_support
    (p : ι → Prop) :
    selectedClosedRegion J p ⊆
      (selectedClosedRegionMesh J p).toPlaneComplex.support := by
  intro x hx
  obtain ⟨i, hpi, hxi⟩ := Set.mem_iUnion₂.mp hx
  rw [PolygonalCircle.closedRegion] at hxi
  exact closure_minimal
    (interiorRegion_subset_selectedClosedRegionMesh_support J p i hpi)
    (selectedClosedRegionMesh J p).toPlaneComplex.isCompact_support.isClosed hxi

/-- Every selected subfamily is recovered exactly as a face restriction of the one common
arrangement.  This is the conforming old/new submesh interface used by the Radó weld. -/
theorem selectedClosedRegionMesh_support (p : ι → Prop) :
    (selectedClosedRegionMesh J p).toPlaneComplex.support =
      selectedClosedRegion J p :=
  Set.Subset.antisymm (selectedClosedRegionMesh_support_subset J p)
    (selectedClosedRegion_subset_selectedClosedRegionMesh_support J p)

/-- Taking the union of two selected submeshes is literally the selection by the disjunction
of the two predicates.  All three meshes use the same ambient arrangement vertex type. -/
theorem selectedClosedRegionMesh_triangles_union (p q : ι → Prop) :
    (selectedClosedRegionMesh J p).triangles ∪
        (selectedClosedRegionMesh J q).triangles =
      (selectedClosedRegionMesh J fun i ↦ p i ∨ q i).triangles := by
  classical
  change
    ((arrangementMesh J).triangles.filter
        (IsSelectedInteriorArrangementTriangle J p)) ∪
      ((arrangementMesh J).triangles.filter
        (IsSelectedInteriorArrangementTriangle J q)) =
      (arrangementMesh J).triangles.filter
        (IsSelectedInteriorArrangementTriangle J (fun i ↦ p i ∨ q i))
  ext t
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨ht, i, hpi, hi⟩ | ⟨ht, i, hqi, hi⟩)
    · exact ⟨ht, i, Or.inl hpi, hi⟩
    · exact ⟨ht, i, Or.inr hqi, hi⟩
  · rintro ⟨ht, i, hpi | hqi, hi⟩
    · exact Or.inl ⟨ht, i, hpi, hi⟩
    · exact Or.inr ⟨ht, i, hqi, hi⟩

/-- The two synchronized selected submeshes jointly retain the planar surface incidence bound:
every two-vertex edge belongs to at most two triangles.  This is inherited from the single
ambient arrangement, not proved separately for the two selections. -/
theorem selectedClosedRegionMeshes_joint_edge_valence (p q : ι → Prop)
    (e : Finset (arrangementMesh J).Vertex) (he : e.card = 2) :
    (((selectedClosedRegionMesh J p).triangles ∪
        (selectedClosedRegionMesh J q).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  rw [selectedClosedRegionMesh_triangles_union J p q]
  exact (selectedClosedRegionMesh J fun i ↦ p i ∨ q i).card_incidentTriangles_le_two he

/-! ## Synchronization with an independent finite patch mesh -/

/-- Cut the polygon-family arrangement by all barycentric face lines of a second mesh. -/
noncomputable def synchronizedArrangement (N : TriangleMesh) : TriangleMesh :=
  (arrangementMesh J).refineTo N

/-- A chamber of the synchronized arrangement lies in the selected polygonal region. -/
def IsSelectedSynchronizedTriangle (N : TriangleMesh) (p : ι → Prop)
    (t : Finset (synchronizedArrangement J N).Vertex) : Prop :=
  ∃ i, p i ∧
    interior ((synchronizedArrangement J N).triangleCarrier t) ⊆
      (J i).interiorRegion

/-- The polygonal side of the common old/patch arrangement. -/
noncomputable def selectedSynchronizedMesh (N : TriangleMesh)
    (p : ι → Prop) : TriangleMesh := by
  classical
  exact (synchronizedArrangement J N).restrictTriangles
    (IsSelectedSynchronizedTriangle J N p)

/-- The patch side consists of the synchronized chambers whose interiors meet the patch. -/
def IsTargetSynchronizedTriangle (N : TriangleMesh)
    (t : Finset (synchronizedArrangement J N).Vertex) : Prop :=
  (interior ((synchronizedArrangement J N).triangleCarrier t) ∩
    N.toPlaneComplex.support).Nonempty

/-- The target-mesh side of the common old/patch arrangement. -/
noncomputable def targetSynchronizedMesh (N : TriangleMesh) : TriangleMesh := by
  classical
  exact (synchronizedArrangement J N).restrictTriangles
    (IsTargetSynchronizedTriangle J N)

theorem selectedSynchronizedMesh_triangle_mem (N : TriangleMesh) (p : ι → Prop)
    {t : Finset (selectedSynchronizedMesh J N p).Vertex} :
    t ∈ (selectedSynchronizedMesh J N p).triangles ↔
      t ∈ (synchronizedArrangement J N).triangles ∧
        IsSelectedSynchronizedTriangle J N p t := by
  classical
  exact (synchronizedArrangement J N).mem_restrictTriangles_triangles _

theorem targetSynchronizedMesh_triangle_mem (N : TriangleMesh)
    {t : Finset (targetSynchronizedMesh J N).Vertex} :
    t ∈ (targetSynchronizedMesh J N).triangles ↔
      t ∈ (synchronizedArrangement J N).triangles ∧
        IsTargetSynchronizedTriangle J N t := by
  classical
  exact (synchronizedArrangement J N).mem_restrictTriangles_triangles _

/-- Every synchronized chamber is contained in one chamber of the original polygon-family
arrangement. -/
theorem exists_arrangementTriangle_of_synchronized {N : TriangleMesh}
    {t : Finset (synchronizedArrangement J N).Vertex}
    (ht : t ∈ (synchronizedArrangement J N).triangles) :
    ∃ u ∈ (arrangementMesh J).triangles,
      (synchronizedArrangement J N).triangleCarrier t ⊆
        (arrangementMesh J).triangleCarrier u := by
  let R := synchronizedArrangement J N
  have htFace : t ∈ R.toPlaneComplex.simplexes :=
    R.mem_faces_iff.mpr ⟨by
      have htcard : t.card = 3 := R.card_triangle t ht
      exact Finset.card_pos.mp (by omega), t, ht, subset_rfl⟩
  obtain ⟨s, hs, hts⟩ :=
    ((arrangementMesh J).refineTo_subdivides_left N).2 t htFace
  obtain ⟨-, u, hu, hsu⟩ := (arrangementMesh J).mem_faces_iff.mp hs
  refine ⟨u, hu, ?_⟩
  exact hts.trans (convexHull_mono (Set.image_mono hsu))

/-- Synchronized chambers still lie wholly on one side of every family polygon. -/
theorem synchronizedTriangle_interior_side (N : TriangleMesh) (i : ι)
    {t : Finset (synchronizedArrangement J N).Vertex}
    (ht : t ∈ (synchronizedArrangement J N).triangles) :
    interior ((synchronizedArrangement J N).triangleCarrier t) ⊆
        (J i).interiorRegion ∨
      interior ((synchronizedArrangement J N).triangleCarrier t) ⊆
        (J i).exteriorRegion := by
  obtain ⟨u, hu, htu⟩ := exists_arrangementTriangle_of_synchronized J ht
  have hint := interior_mono htu
  rcases arrangementTriangle_interior_side J i hu with hin | hout
  · exact Or.inl (hint.trans hin)
  · exact Or.inr (hint.trans hout)

/-- Further cutting by the target mesh does not change the selected polygonal support. -/
theorem selectedSynchronizedMesh_support (N : TriangleMesh) (p : ι → Prop) :
    (selectedSynchronizedMesh J N p).toPlaneComplex.support =
      selectedClosedRegion J p := by
  classical
  let R := synchronizedArrangement J N
  let L := selectedSynchronizedMesh J N p
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨htR, i, hpi, hi⟩ :=
      (selectedSynchronizedMesh_triangle_mem J N p).mp ht
    let T : R.Triangle := ⟨t, htR⟩
    have hxClosure : x ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hxt
    have hxRegion : x ∈ closure (J i).interiorRegion :=
      closure_mono hi hxClosure
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨hpi, by simpa only [PolygonalCircle.closedRegion] using hxRegion⟩⟩
  · intro x hx
    obtain ⟨i, hpi, hxi⟩ := Set.mem_iUnion₂.mp hx
    rw [PolygonalCircle.closedRegion] at hxi
    apply closure_minimal _ L.toPlaneComplex.isCompact_support.isClosed hxi
    intro y hy
    have hyFamily : y ∈ closedRegion J := Set.mem_iUnion.mpr
      ⟨i, by rw [(J i).closedRegion_eq_union]; exact Or.inl hy⟩
    have hyArrangement : y ∈ (arrangementMesh J).toPlaneComplex.support :=
      closedRegion_subset_arrangementMesh_support J hyFamily
    have hyR : y ∈ R.toPlaneComplex.support := by
      rw [show R.toPlaneComplex.support =
          (arrangementMesh J).toPlaneComplex.support by
        exact (arrangementMesh J).refineTo_support N]
      exact hyArrangement
    rw [TriangleMesh.toPlaneComplex_support] at hyR
    simp only [Set.mem_iUnion] at hyR
    obtain ⟨t, ht, hyt⟩ := hyR
    let T : R.Triangle := ⟨t, ht⟩
    have hyClosure : y ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hyt
    have hyInterClosure : y ∈ closure
        ((J i).interiorRegion ∩ interior (R.triangleCarrier t)) :=
      (J i).isOpen_interiorRegion.inter_closure ⟨hy, hyClosure⟩
    obtain ⟨z, hzInside, hzT⟩ := Set.Nonempty.of_closure ⟨y, hyInterClosure⟩
    have htInside : interior (R.triangleCarrier t) ⊆
        (J i).interiorRegion := by
      rcases synchronizedTriangle_interior_side J N i ht with hin | hout
      · exact hin
      · exact False.elim <| Set.disjoint_left.mp
          (J i).disjoint_interior_exterior hzInside (hout hzT)
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr
      ⟨(selectedSynchronizedMesh_triangle_mem J N p).mpr
        ⟨ht, i, hpi, htInside⟩, hyt⟩⟩

/-- When the target support lies in the family arrangement's enclosing triangle, the target
side of the synchronized arrangement recovers it exactly. -/
theorem targetSynchronizedMesh_support (N : TriangleMesh)
    (hsub : N.toPlaneComplex.support ⊆
      (arrangementMesh J).toPlaneComplex.support) :
    (targetSynchronizedMesh J N).toPlaneComplex.support =
      N.toPlaneComplex.support := by
  change ((arrangementMesh J).refineToSupport N).toPlaneComplex.support =
    N.toPlaneComplex.support
  exact (arrangementMesh J).refineToSupport_support N hsub

/-- The synchronized old and target submeshes jointly satisfy the planar edge-incidence bound. -/
theorem synchronizedMeshes_joint_edge_valence (N : TriangleMesh) (p : ι → Prop)
    (e : Finset (synchronizedArrangement J N).Vertex) (he : e.card = 2) :
    (((selectedSynchronizedMesh J N p).triangles ∪
        (targetSynchronizedMesh J N).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  apply le_trans (Finset.card_le_card ?_)
    ((synchronizedArrangement J N).card_incidentTriangles_le_two he)
  intro t ht
  obtain ⟨htUnion, het⟩ := Finset.mem_filter.mp ht
  apply (synchronizedArrangement J N).mem_incidentTriangles_iff.mpr
  refine ⟨?_, het⟩
  rcases Finset.mem_union.mp htUnion with htOld | htTarget
  · exact (selectedSynchronizedMesh_triangle_mem J N p).mp htOld |>.1
  · exact (targetSynchronizedMesh_triangle_mem J N).mp htTarget |>.1

omit [Fintype ι] in
/-- A finite union of polygonal closed disks is a finite pure plane polyhedron. -/
theorem closedRegion_is_polyhedron [Finite ι] :
    ∃ K : PlaneComplex, K.support = closedRegion J ∧ K.IsPure2 := by
  let := Fintype.ofFinite ι
  exact ⟨(closedRegionMesh J).toPlaneComplex, closedRegionMesh_support J,
    (closedRegionMesh J).toPlaneComplex_isPure2⟩

end PolygonalFamily

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
