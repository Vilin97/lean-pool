/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalFamilyPolyhedron

/-!
# Synchronized polygonal arrangements with additional finite cuts

The relative Radó weld must cut the common old/new planar arrangement by finitely many
additional lines coming from retained PL face certificates.  Both sides must still be literal
submeshes of one ambient triangle mesh.  This file records that harmless extra-line
generalization of `PolygonalFamily.synchronizedArrangement`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PolygonalFamily

variable {ι : Type*} [Fintype ι] (J : ι → PolygonalCircle)

/-- Cut the polygon-family arrangement simultaneously by a target mesh and by an additional
finite list of affine lines. -/
noncomputable def relativeSynchronizedArrangement (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  (arrangementMesh J).refineByLines (N.coordinateLines ++ lines)

theorem relativeSynchronizedArrangement_support (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    (relativeSynchronizedArrangement J N lines).toPlaneComplex.support =
      (arrangementMesh J).toPlaneComplex.support :=
  (arrangementMesh J).refineByLines_support _

/-- A relative synchronized chamber belongs to the selected polygonal side. -/
def IsSelectedRelativeSynchronizedTriangle (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop)
    (t : Finset (relativeSynchronizedArrangement J N lines).Vertex) : Prop :=
  ∃ i, p i ∧
    interior ((relativeSynchronizedArrangement J N lines).triangleCarrier t) ⊆
      (J i).interiorRegion

/-- The selected polygonal member after all additional cuts. -/
noncomputable def selectedRelativeSynchronizedMesh (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop) : TriangleMesh := by
  classical
  exact (relativeSynchronizedArrangement J N lines).restrictTriangles
    (IsSelectedRelativeSynchronizedTriangle J N lines p)

/-- A relative synchronized chamber belongs to the prescribed target side exactly when its
interior meets the target support. -/
def IsTargetRelativeSynchronizedTriangle (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (t : Finset (relativeSynchronizedArrangement J N lines).Vertex) : Prop :=
  (interior ((relativeSynchronizedArrangement J N lines).triangleCarrier t) ∩
    N.toPlaneComplex.support).Nonempty

/-- The target member after all additional cuts. -/
noncomputable def targetRelativeSynchronizedMesh (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh := by
  classical
  exact (relativeSynchronizedArrangement J N lines).restrictTriangles
    (IsTargetRelativeSynchronizedTriangle J N lines)

theorem selectedRelativeSynchronizedMesh_triangle_mem
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop)
    {t : Finset (selectedRelativeSynchronizedMesh J N lines p).Vertex} :
    t ∈ (selectedRelativeSynchronizedMesh J N lines p).triangles ↔
      t ∈ (relativeSynchronizedArrangement J N lines).triangles ∧
        IsSelectedRelativeSynchronizedTriangle J N lines p t := by
  classical
  exact (relativeSynchronizedArrangement J N lines).mem_restrictTriangles_triangles _

theorem targetRelativeSynchronizedMesh_triangle_mem
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    {t : Finset (targetRelativeSynchronizedMesh J N lines).Vertex} :
    t ∈ (targetRelativeSynchronizedMesh J N lines).triangles ↔
      t ∈ (relativeSynchronizedArrangement J N lines).triangles ∧
        IsTargetRelativeSynchronizedTriangle J N lines t := by
  classical
  exact (relativeSynchronizedArrangement J N lines).mem_restrictTriangles_triangles _

/-- Every chamber after the extra cuts remains inside an original polygon-family arrangement
triangle. -/
theorem exists_arrangementTriangle_of_relativeSynchronized
    {N : TriangleMesh} {lines : List (Plane →ᵃ[ℝ] ℝ)}
    {t : Finset (relativeSynchronizedArrangement J N lines).Vertex}
    (ht : t ∈ (relativeSynchronizedArrangement J N lines).triangles) :
    ∃ u ∈ (arrangementMesh J).triangles,
      (relativeSynchronizedArrangement J N lines).triangleCarrier t ⊆
        (arrangementMesh J).triangleCarrier u := by
  let R := relativeSynchronizedArrangement J N lines
  have htFace : t ∈ R.toPlaneComplex.simplexes :=
    R.mem_faces_iff.mpr ⟨by
      have htcard : t.card = 3 := R.card_triangle t ht
      exact Finset.card_pos.mp (by omega), t, ht, subset_rfl⟩
  obtain ⟨s, hs, hts⟩ :=
    ((arrangementMesh J).refineByLines_subdivides
      (N.coordinateLines ++ lines)).2 t htFace
  obtain ⟨-, u, hu, hsu⟩ := (arrangementMesh J).mem_faces_iff.mp hs
  refine ⟨u, hu, ?_⟩
  exact hts.trans (convexHull_mono (Set.image_mono hsu))

/-- Extra cuts preserve the one-sidedness of every chamber with respect to every polygon in
the family. -/
theorem relativeSynchronizedTriangle_interior_side
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (i : ι)
    {t : Finset (relativeSynchronizedArrangement J N lines).Vertex}
    (ht : t ∈ (relativeSynchronizedArrangement J N lines).triangles) :
    interior ((relativeSynchronizedArrangement J N lines).triangleCarrier t) ⊆
        (J i).interiorRegion ∨
      interior ((relativeSynchronizedArrangement J N lines).triangleCarrier t) ⊆
        (J i).exteriorRegion := by
  obtain ⟨u, hu, htu⟩ :=
    exists_arrangementTriangle_of_relativeSynchronized J ht
  have hint := interior_mono htu
  rcases arrangementTriangle_interior_side J i hu with hin | hout
  · exact Or.inl (hint.trans hin)
  · exact Or.inr (hint.trans hout)

/-- Additional cuts do not alter the selected polygonal support. -/
theorem selectedRelativeSynchronizedMesh_support
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop) :
    (selectedRelativeSynchronizedMesh J N lines p).toPlaneComplex.support =
      selectedClosedRegion J p := by
  classical
  let R := relativeSynchronizedArrangement J N lines
  let L := selectedRelativeSynchronizedMesh J N lines p
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨htR, i, hpi, hi⟩ :=
      (selectedRelativeSynchronizedMesh_triangle_mem J N lines p).mp ht
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
        exact relativeSynchronizedArrangement_support J N lines]
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
      rcases relativeSynchronizedTriangle_interior_side J N lines i ht with
          hin | hout
      · exact hin
      · exact False.elim <| Set.disjoint_left.mp
          (J i).disjoint_interior_exterior hzInside (hout hzT)
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr
      ⟨(selectedRelativeSynchronizedMesh_triangle_mem J N lines p).mpr
        ⟨ht, i, hpi, htInside⟩, hyt⟩⟩

/-- Every retained target chamber lies in a triangle of the prescribed target mesh. -/
theorem exists_targetTriangle_of_targetRelativeSynchronized
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    {t : Finset (targetRelativeSynchronizedMesh J N lines).Vertex}
    (ht : t ∈ (targetRelativeSynchronizedMesh J N lines).triangles) :
    ∃ u ∈ N.triangles,
      (relativeSynchronizedArrangement J N lines).triangleCarrier t ⊆
        N.triangleCarrier u := by
  have htData :=
    (targetRelativeSynchronizedMesh_triangle_mem J N lines).mp ht
  let T : (relativeSynchronizedArrangement J N lines).Triangle :=
    ⟨t, htData.1⟩
  obtain ⟨U, hTU⟩ :=
    (arrangementMesh J).exists_target_triangle_of_refineByLines_of_interior_inter_support
      N (N.coordinateLines ++ lines)
      (fun a ha ↦ List.mem_append_left _ ha) T htData.2
  exact ⟨U.1, U.2, hTU⟩

/-- If the target lies in the polygon-family arrangement, its relative synchronized member has
exactly the prescribed support. -/
theorem targetRelativeSynchronizedMesh_support
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hsub : N.toPlaneComplex.support ⊆
      (arrangementMesh J).toPlaneComplex.support) :
    (targetRelativeSynchronizedMesh J N lines).toPlaneComplex.support =
      N.toPlaneComplex.support := by
  classical
  let R := relativeSynchronizedArrangement J N lines
  let L := targetRelativeSynchronizedMesh J N lines
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨u, hu, htu⟩ :=
      exists_targetTriangle_of_targetRelativeSynchronized J N lines ht
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, htu hxt⟩⟩
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    let U : N.Triangle := ⟨u, hu⟩
    have hinterior : interior (N.triangleCarrier u) ⊆
        L.toPlaneComplex.support := by
      intro y hy
      have hyN : y ∈ N.toPlaneComplex.support := by
        rw [TriangleMesh.toPlaneComplex_support]
        exact Set.mem_iUnion.mpr
          ⟨u, Set.mem_iUnion.mpr ⟨hu, interior_subset hy⟩⟩
      have hyR : y ∈ R.toPlaneComplex.support := by
        rw [relativeSynchronizedArrangement_support]
        exact hsub hyN
      rw [TriangleMesh.toPlaneComplex_support] at hyR
      simp only [Set.mem_iUnion] at hyR
      obtain ⟨t, ht, hyt⟩ := hyR
      let T : R.Triangle := ⟨t, ht⟩
      have hyClosure : y ∈ closure (interior (R.triangleCarrier t)) := by
        rw [R.closure_interior_triangleCarrier T]
        exact hyt
      have hyInterClosure : y ∈ closure
          (interior (N.triangleCarrier u) ∩
            interior (R.triangleCarrier t)) :=
        isOpen_interior.inter_closure ⟨hy, hyClosure⟩
      obtain ⟨z, hzN, hzR⟩ := Set.Nonempty.of_closure ⟨y, hyInterClosure⟩
      have htKeep : t ∈ L.triangles :=
        (targetRelativeSynchronizedMesh_triangle_mem J N lines).mpr
          ⟨ht, ⟨z, hzR, by
            rw [TriangleMesh.toPlaneComplex_support]
            exact Set.mem_iUnion.mpr
              ⟨u, Set.mem_iUnion.mpr ⟨hu, interior_subset hzN⟩⟩⟩⟩
      rw [TriangleMesh.toPlaneComplex_support]
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨htKeep, hyt⟩⟩
    change x ∈ N.triangleCarrier u at hxu
    rw [← N.closure_interior_triangleCarrier U] at hxu
    exact closure_minimal hinterior L.toPlaneComplex.isCompact_support.isClosed hxu

/-- The selected and target members inherit the ambient planar edge-incidence bound. -/
theorem relativeSynchronizedMeshes_joint_edge_valence
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop)
    (e : Finset (relativeSynchronizedArrangement J N lines).Vertex)
    (he : e.card = 2) :
    (((selectedRelativeSynchronizedMesh J N lines p).triangles ∪
        (targetRelativeSynchronizedMesh J N lines).triangles).filter
      fun t ↦ e ⊆ t).card ≤ 2 := by
  apply le_trans (Finset.card_le_card ?_)
    ((relativeSynchronizedArrangement J N lines).card_incidentTriangles_le_two he)
  intro t ht
  obtain ⟨htUnion, het⟩ := Finset.mem_filter.mp ht
  apply (relativeSynchronizedArrangement J N lines).mem_incidentTriangles_iff.mpr
  refine ⟨?_, het⟩
  rcases Finset.mem_union.mp htUnion with htOld | htTarget
  · exact
      (selectedRelativeSynchronizedMesh_triangle_mem J N lines p).mp htOld |>.1
  · exact
      (targetRelativeSynchronizedMesh_triangle_mem J N lines).mp htTarget |>.1

end PolygonalFamily

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
