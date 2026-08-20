/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceExtension
import LeanPool.ClassificationOfSurfaces.Moise.PLApproximation

/-!
# PL fillings of intrinsic polygonal face boundaries

The simultaneous intrinsic graph replacement gives every maximal face a canonical map from the
standard triangular frontier onto a simple polygonal circle.  `IntrinsicFaceExtension` proves
that this map is genuinely PL on one named finite subdivision.  Polygonal Schoenflies now fills
it by a finite PL homeomorphism, without changing any shared-edge boundary values.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}

/-- A certified finite PL filling of the canonical polygonal boundary of one intrinsic face. -/
structure FacePLFilling (t : K.Face) where
  /-- The `map` declaration. -/
  map : Plane → Plane
  eqOn_boundary : Set.EqOn map
    (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (frontier standardFaceRegion)
  continuousOn : ContinuousOn map standardFaceRegion
  injectiveOn : Set.InjOn map standardFaceRegion
  image_eq : map '' standardFaceRegion =
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion
  isPLOnSet : IsPLOnSet standardFaceRegion map
  certificate : Nonempty (FinitePLHomeomorphBetween map standardFaceRegion
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion)

/-- Polygonal Schoenflies fills the canonical face boundary by a finite PL homeomorphism. -/
theorem exists_facePLFilling (t : K.Face) :
    Nonempty (K.FacePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) := by
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  obtain ⟨F, hboundary, hcontinuous, hFinj, himage, hpl, hcert⟩ :=
    pl_extension_of_triangle_to_polygon_boundary
      standardTrianglePlaneComplex_isTriangle J
      (K.faceBoundaryMap_isPLOnSet t)
      (K.faceBoundaryMap_injectiveOn t)
      (K.faceBoundaryMap_image_polygon t)
  exact ⟨{
    map := F
    eqOn_boundary := hboundary
    continuousOn := hcontinuous
    injectiveOn := hFinj
    image_eq := himage
    isPLOnSet := hpl
    certificate := hcert
  }⟩

/-- A fixed choice of the certified PL filling for downstream finite gluing. -/
noncomputable def facePLFilling (t : K.Face) :
    K.FacePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) t :=
  Classical.choice (K.exists_facePLFilling t)

/-- Fillings of neighboring faces agree wherever their standard boundary lifts name the same
intrinsic one-skeleton point.  The equality is pointwise because both restrictions are the same
global graph replacement map. -/
theorem facePLFilling_eq_of_boundaryLift_eq
    {t u : K.Face} {p q : StandardFaceBoundary}
    (hpq : (K.faceBoundaryLift t p).1 = (K.faceBoundaryLift u q).1) :
    (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).map p.1 =
      (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) u).map q.1 := by
  rw [(K.facePLFilling t).eqOn_boundary p.2,
    (K.facePLFilling u).eqOn_boundary q.2,
    K.faceBoundaryMap_apply t p, K.faceBoundaryMap_apply u q, hpq]

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
