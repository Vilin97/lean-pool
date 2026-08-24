/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.CommonSubdivision
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicComplex

/-!
# Plane subdivisions as intrinsic subdivisions

The Rado induction uses intrinsic complexes, while all finite cutting and common-refinement
machinery is geometric and planar.  This file is the bridge between those layers.  A pure plane
complex is regarded as the intrinsic complex of its maximal triangles, and a geometric
subdivision induces a faithful intrinsic subdivision through the barycentric realization
homeomorphisms.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex)

/-- Forget the planar placement of a complex, retaining its maximal triangles as an intrinsic
two-complex. -/
@[reducible] def toIntrinsic : IntrinsicTwoComplex where
  Vertex := K.Vertex
  faces := K.cells
  faces_card := fun _ ht => K.card_of_mem_cells ht

@[simp] theorem toIntrinsic_faces : K.toIntrinsic.faces = K.cells := rfl

/-- Barycentric evaluation is an affine map on the ambient coordinate space. -/
noncomputable def baryEvalAffine : (K.Vertex → ℝ) →ᵃ[ℝ] Plane :=
  (∑ v, (LinearMap.proj v).smulRight (K.position v)).toAffineMap

@[simp] theorem baryEvalAffine_apply (x : K.Vertex → ℝ) :
    K.baryEvalAffine x = K.baryEval x := by
  simp [baryEvalAffine, baryEval]

/-- Barycentric coordinates in one maximal triangle, extended by zero to all vertices of the
complex. -/
noncomputable def faceCoords (T : K.toTriangleMesh.Triangle) :
    Plane →ᵃ[ℝ] (K.Vertex → ℝ) := by
  classical
  let b := affineBasisOfTriangle
    (K.toTriangleMesh.position ∘ K.toTriangleMesh.orderedVertex T)
    (K.toTriangleMesh.orderedVertex_affineIndependent T)
  exact AffineMap.pi fun v =>
    if hv : v ∈ T.1 then
      b.coord (K.toTriangleMesh.triangleEquiv T ⟨v, hv⟩)
    else
      AffineMap.const ℝ Plane 0

@[simp] theorem faceCoords_apply_of_mem (T : K.toTriangleMesh.Triangle)
    {v : K.Vertex} (hv : v ∈ T.1) (p : Plane) :
    K.faceCoords T p v =
      (affineBasisOfTriangle
        (K.toTriangleMesh.position ∘ K.toTriangleMesh.orderedVertex T)
        (K.toTriangleMesh.orderedVertex_affineIndependent T)).coord
          (K.toTriangleMesh.triangleEquiv T ⟨v, hv⟩) p := by
  classical
  simp [faceCoords, hv]

@[simp] theorem faceCoords_apply_of_notMem (T : K.toTriangleMesh.Triangle)
    {v : K.Vertex} (hv : v ∉ T.1) (p : Plane) :
    K.faceCoords T p v = 0 := by
  classical
  simp [faceCoords, hv]

theorem faceCoords_support (T : K.toTriangleMesh.Triangle) (p : Plane) :
    ∀ v ∉ T.1, K.faceCoords T p v = 0 :=
  fun _ hv => K.faceCoords_apply_of_notMem T hv p

theorem sum_faceCoords (T : K.toTriangleMesh.Triangle) (p : Plane) :
    ∑ v, K.faceCoords T p v = 1 := by
  classical
  let b := affineBasisOfTriangle
    (K.toTriangleMesh.position ∘ K.toTriangleMesh.orderedVertex T)
    (K.toTriangleMesh.orderedVertex_affineIndependent T)
  rw [K.sum_eq_sum_of_support (K.faceCoords_support T p)]
  calc
    ∑ v ∈ T.1, K.faceCoords T p v =
        ∑ v : T.1, K.faceCoords T p v.1 := (Finset.sum_coe_sort T.1 _).symm
    _ =
        ∑ v : T.1, b.coord (K.toTriangleMesh.triangleEquiv T v) p := by
      apply Finset.sum_congr rfl
      intro v hv
      exact K.faceCoords_apply_of_mem T v.2 p
    _ = ∑ i : Fin 3, b.coord i p :=
      (K.toTriangleMesh.triangleEquiv T).sum_comp (fun i => b.coord i p)
    _ = 1 := b.sum_coord_apply_eq_one p

theorem orderedVertex_triangleEquiv (T : K.toTriangleMesh.Triangle) (v : T.1) :
    K.toTriangleMesh.orderedVertex T (K.toTriangleMesh.triangleEquiv T v) = v.1 := by
  simp [TriangleMesh.orderedVertex]

theorem baryEval_faceCoords (T : K.toTriangleMesh.Triangle) (p : Plane) :
    K.baryEval (K.faceCoords T p) = p := by
  classical
  let b := affineBasisOfTriangle
    (K.toTriangleMesh.position ∘ K.toTriangleMesh.orderedVertex T)
    (K.toTriangleMesh.orderedVertex_affineIndependent T)
  rw [K.baryEval_eq_sum_of_support (K.faceCoords_support T p)]
  calc
    ∑ v ∈ T.1, K.faceCoords T p v • K.position v =
        ∑ v : T.1, K.faceCoords T p v.1 • K.position v.1 :=
      (Finset.sum_coe_sort T.1 _).symm
    _ =
        ∑ v : T.1, b.coord (K.toTriangleMesh.triangleEquiv T v) p •
          K.position v.1 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [K.faceCoords_apply_of_mem T v.2 p]
    _ = ∑ i : Fin 3, b.coord i p •
          K.position (K.toTriangleMesh.orderedVertex T i) := by
      calc
        _ = ∑ v : T.1, b.coord (K.toTriangleMesh.triangleEquiv T v) p •
            K.position (K.toTriangleMesh.orderedVertex T
              (K.toTriangleMesh.triangleEquiv T v)) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [K.orderedVertex_triangleEquiv T v]
        _ = _ :=
          (K.toTriangleMesh.triangleEquiv T).sum_comp
            (fun i => b.coord i p • K.position (K.toTriangleMesh.orderedVertex T i))
    _ = p := by
      change ∑ i : Fin 3, b.coord i p • b i = p
      exact b.linear_combination_coord_eq_self p

/-- The affine coordinates of a geometric triangle vertex are the corresponding unit
barycentric coordinates. -/
theorem faceCoords_position (T : K.toTriangleMesh.Triangle) {v : K.Vertex}
    (hv : v ∈ T.1) :
    K.faceCoords T (K.position v) = Pi.single v 1 := by
  apply K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells T.2)
  · exact K.faceCoords_support T (K.position v)
  · intro w hw
    have hwv : w ≠ v := by
      intro h
      subst w
      exact hw hv
    simp [hwv]
  · exact K.sum_faceCoords T (K.position v)
  · simp
  · rw [K.baryEval_faceCoords]
    simp [PlaneComplex.baryEval]

/-- The inverse barycentric realization map sends a point of a maximal geometric triangle to
the corresponding intrinsic face. -/
theorem realizationHomeomorph_symm_mem_faceCarrier (hpure : K.IsPure2)
    (T : K.toTriangleMesh.Triangle) (p : K.support)
    (hp : p.1 ∈ K.cellCarrier T.1) :
    (K.realizationHomeomorph hpure).symm p ∈ K.toIntrinsic.faceCarrier T.1 := by
  classical
  obtain ⟨x, hxsupp, hx0, hx1, hxeval⟩ := K.exists_weights_of_mem_cellCarrier hp
  let z : K.toIntrinsic.realization :=
    ⟨x, ⟨hx0, hx1⟩, T.1, T.2, hxsupp⟩
  have hz : (K.realizationHomeomorph hpure).symm p = z := by
    have hzimage : K.realizationHomeomorph hpure z = p := by
      apply Subtype.ext
      exact hxeval
    calc
      (K.realizationHomeomorph hpure).symm p =
          (K.realizationHomeomorph hpure).symm
            (K.realizationHomeomorph hpure z) := congrArg _ hzimage.symm
      _ = z := (K.realizationHomeomorph hpure).symm_apply_apply z
  rw [hz]
  exact hxsupp

/-- On a selected maximal triangle, the inverse realization homeomorphism is given by the
explicit affine barycentric-coordinate map for that triangle. -/
theorem realizationHomeomorph_symm_val_eq_faceCoords (hpure : K.IsPure2)
    (T : K.toTriangleMesh.Triangle) (p : K.support)
    (hp : p.1 ∈ K.cellCarrier T.1) :
    ((K.realizationHomeomorph hpure).symm p).1 = K.faceCoords T p.1 := by
  let z := (K.realizationHomeomorph hpure).symm p
  apply K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells T.2)
  · exact K.realizationHomeomorph_symm_mem_faceCarrier hpure T p hp
  · exact K.faceCoords_support T p.1
  · exact z.2.1.2
  · exact K.sum_faceCoords T p.1
  · calc
      K.baryEval z.1 = (K.realizationHomeomorph hpure z).1 := by
        rw [K.realizationHomeomorph_apply]
      _ = p.1 := congrArg Subtype.val
        ((K.realizationHomeomorph hpure).apply_symm_apply p)
      _ = K.baryEval (K.faceCoords T p.1) := (K.baryEval_faceCoords T p.1).symm

/-- Barycentric realization carries every abstract face carrier exactly onto its geometric
convex hull. -/
theorem realizationHomeomorph_image_faceCarrier (hpure : K.IsPure2)
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    (fun x : K.toIntrinsic.realization => (K.realizationHomeomorph hpure x).1) ''
        K.toIntrinsic.faceCarrier s = K.cellCarrier s := by
  classical
  apply Set.Subset.antisymm
  · rintro p ⟨x, hx, rfl⟩
    change (K.realizationHomeomorph hpure x).1 ∈ K.cellCarrier s
    rw [K.realizationHomeomorph_apply]
    exact K.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
  · intro p hp
    obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
    have htcell : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    obtain ⟨x, hxsupp, hx0, hx1, hxeval⟩ := K.exists_weights_of_mem_cellCarrier hp
    have hxt : ∀ v ∉ t, x v = 0 := fun v hv => hxsupp v (fun hvs => hv (hst hvs))
    let z : K.toIntrinsic.realization :=
      ⟨x, ⟨hx0, hx1⟩, ⟨t, htcell, hxt⟩⟩
    refine ⟨z, hxsupp, ?_⟩
    change (K.realizationHomeomorph hpure z).1 = p
    rw [K.realizationHomeomorph_apply]
    exact hxeval

end PlaneComplex

namespace IntrinsicTwoComplex

/-- The intrinsic homeomorphism underlying a geometric subdivision of pure plane complexes. -/
noncomputable def subdivisionHomeomorph {L K : PlaneComplex}
    (hLpure : L.IsPure2) (hKpure : K.IsPure2) (hLK : L.Subdivides K) :
    L.toIntrinsic.realization ≃ₜ K.toIntrinsic.realization :=
  (L.realizationHomeomorph hLpure).trans
    ((Homeomorph.setCongr hLK.1).trans (K.realizationHomeomorph hKpure).symm)

theorem baryEval_subdivisionHomeomorph {L K : PlaneComplex}
    (hLpure : L.IsPure2) (hKpure : K.IsPure2) (hLK : L.Subdivides K)
    (x : L.toIntrinsic.realization) :
    K.baryEval ((subdivisionHomeomorph hLpure hKpure hLK x).1) = L.baryEval x.1 := by
  let q : L.support := L.realizationHomeomorph hLpure x
  let p : K.support := Homeomorph.setCongr hLK.1 q
  have h := congrArg Subtype.val
    ((K.realizationHomeomorph hKpure).apply_symm_apply p)
  change K.baryEval ((K.realizationHomeomorph hKpure).symm p).1 = p.1 at h
  change K.baryEval ((subdivisionHomeomorph hLpure hKpure hLK x).1) =
    L.baryEval x.1
  exact h

/-- A geometric subdivision of pure finite plane complexes is a faithful subdivision of their
intrinsic realizations. -/
noncomputable def subdivisionOfPlaneSubdivision {L K : PlaneComplex}
    (hLpure : L.IsPure2) (hKpure : K.IsPure2) (hLK : L.Subdivides K) :
    K.toIntrinsic.Subdivision where
  refined := L.toIntrinsic
  homeo := subdivisionHomeomorph hLpure hKpure hLK
  affineOnFace := by
    intro s hs
    have hsSimplex : s ∈ L.simplexes := L.mem_simplexes_of_mem_cells hs
    obtain ⟨u, hu, hsu⟩ := hLK.2 s hsSimplex
    obtain ⟨t, ht, hut, htcard⟩ := hKpure u hu
    have htCell : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    let T : K.toTriangleMesh.Triangle := ⟨t, htCell⟩
    refine ⟨(K.faceCoords T).comp L.baryEvalAffine, ?_⟩
    intro x hx
    let y := subdivisionHomeomorph hLpure hKpure hLK x
    have hxGeom : L.baryEval x.1 ∈ L.cellCarrier s :=
      L.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
    have hpGeom : L.baryEval x.1 ∈ K.cellCarrier t :=
      convexHull_mono (Set.image_mono hut) (hsu hxGeom)
    let p : K.support := ⟨L.baryEval x.1, by
      rw [← hLK.1]
      exact L.cellCarrier_subset_support hsSimplex hxGeom⟩
    have hyFace : y ∈ K.toIntrinsic.faceCarrier t := by
      change (K.realizationHomeomorph hKpure).symm p ∈ K.toIntrinsic.faceCarrier t
      exact K.realizationHomeomorph_symm_mem_faceCarrier hKpure T p hpGeom
    have hcoord := K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells htCell)
      hyFace (K.faceCoords_support T (L.baryEval x.1)) y.2.1.2
      (K.sum_faceCoords T (L.baryEval x.1))
      (by rw [baryEval_subdivisionHomeomorph hLpure hKpure hLK,
        K.baryEval_faceCoords])
    rw [AffineMap.comp_apply, PlaneComplex.baryEvalAffine_apply]
    exact hcoord
  subordinate := by
    intro s hs
    have hsSimplex : s ∈ L.simplexes := L.mem_simplexes_of_mem_cells hs
    obtain ⟨u, hu, hsu⟩ := hLK.2 s hsSimplex
    obtain ⟨t, ht, hut, htcard⟩ := hKpure u hu
    have htCell : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    let T : K.toTriangleMesh.Triangle := ⟨t, htCell⟩
    refine ⟨t, htCell, ?_⟩
    intro x hx
    have hxGeom : L.baryEval x.1 ∈ L.cellCarrier s :=
      L.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
    have hpGeom : L.baryEval x.1 ∈ K.cellCarrier t :=
      convexHull_mono (Set.image_mono hut) (hsu hxGeom)
    let p : K.support := ⟨L.baryEval x.1, by
      rw [← hLK.1]
      exact L.cellCarrier_subset_support hsSimplex hxGeom⟩
    change (K.realizationHomeomorph hKpure).symm p ∈ K.toIntrinsic.faceCarrier t
    exact K.realizationHomeomorph_symm_mem_faceCarrier hKpure T p hpGeom

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
