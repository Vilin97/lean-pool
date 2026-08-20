/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ChartInductionCore

/-!
# The Radó crossing weld and chart induction

This file completes the chart-induction framework developed in `ChartInductionCore`. It constructs
the crossing weld, packages the one-chart induction step, and assembles the final triangulation.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

open PartialTriangulation.PolygonalReplacementSourceAtlas
open PartialTriangulation.RelativeSynchronizedTarget

private theorem extendFaceCoordinates_vertex {V : Type*} [DecidableEq V]
    (F : Finset V) (v : {v // v ∈ F}) :
    extendFaceCoordinates F (stdSimplex.vertex v) = Pi.single v.1 1 := by
  funext w
  by_cases hwv : w = v.1
  · subst w
    simp [extendFaceCoordinates, v.2]
  · by_cases hw : w ∈ F
    · have hsub : (⟨w, hw⟩ : {w // w ∈ F}) ≠ v :=
        fun h ↦ hwv (congrArg Subtype.val h)
      simp [extendFaceCoordinates, hw, hwv, hsub]
    · simp [extendFaceCoordinates, hw, hwv]

private theorem simplex_apply_eq_one_of_extend_eq_single
    {V : Type*} [DecidableEq V] (F : Finset V)
    (x : stdSimplex ℝ {v // v ∈ F}) (v : {v // v ∈ F})
    (h : extendFaceCoordinates F x = Pi.single v.1 1) :
    x v = 1 := by
  have hone := congrFun h v.1
  rw [extendFaceCoordinates_of_mem _ _ v.2] at hone
  simpa only [Pi.single_eq_same] using hone

private theorem barycentricVertex_sum {V K : Type*} [Fintype V] [DecidableEq V]
    (F : Finset V) (v : {v // v ∈ F}) (point : V → K → ℝ) :
    (fun k ↦ ∑ w : V, extendFaceCoordinates F (stdSimplex.vertex v) w * point w k) =
      point v.1 := by
  rw [extendFaceCoordinates_vertex]
  funext k
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro w _ hw
    simp [hw]
  · simp

private def simplexLineMap {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) (r : Set.Icc (0 : ℝ) 1) : stdSimplex ℝ V :=
  ⟨AffineMap.lineMap x.1 y.1 r.1,
    (convex_stdSimplex ℝ V).lineMap_mem x.2 y.2 r.2⟩

private theorem extendFaceCoordinates_simplexLineMap {V : Type*} [DecidableEq V]
    (F : Finset V) (x y : stdSimplex ℝ {v // v ∈ F}) (r : Set.Icc (0 : ℝ) 1) :
    extendFaceCoordinates F (simplexLineMap x y r) =
      (1 - r.1) • extendFaceCoordinates F x + r.1 • extendFaceCoordinates F y := by
  funext v
  by_cases hv : v ∈ F
  · rw [extendFaceCoordinates_of_mem _ _ hv]
    simp only [simplexLineMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [extendFaceCoordinates_of_mem _ _ hv, extendFaceCoordinates_of_mem _ _ hv]
    change
      (AffineMap.lineMap x.1 y.1 r.1) ⟨v, hv⟩ =
        (1 - r.1) * x ⟨v, hv⟩ + r.1 * y ⟨v, hv⟩
    rw [AffineMap.lineMap_apply_module]
    rfl
  · rw [extendFaceCoordinates_of_notMem _ _ hv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [extendFaceCoordinates_of_notMem _ _ hv, extendFaceCoordinates_of_notMem _ _ hv]
    simp

private theorem extendFaceCoordinates_simplexLineMap_vertices_eq
    {V : Type*} [DecidableEq V] (F G : Finset V)
    (a b : {v // v ∈ F}) (c d : {v // v ∈ G})
    (hac : a.1 = c.1) (hbd : b.1 = d.1) (r : Set.Icc (0 : ℝ) 1) :
    extendFaceCoordinates F
        (simplexLineMap (stdSimplex.vertex a) (stdSimplex.vertex b) r) =
      extendFaceCoordinates G
        (simplexLineMap (stdSimplex.vertex c) (stdSimplex.vertex d) r) := by
  rw [extendFaceCoordinates_simplexLineMap, extendFaceCoordinates_simplexLineMap,
    extendFaceCoordinates_vertex, extendFaceCoordinates_vertex,
    extendFaceCoordinates_vertex, extendFaceCoordinates_vertex, hac, hbd]

private theorem map_simplexLineMap_vertices {V W : Type*} [Fintype V] [DecidableEq V]
    (map : stdSimplex ℝ V → W → ℝ) (point : V → W → ℝ)
    (hline : ∀ (x y : stdSimplex ℝ V) (r : Set.Icc (0 : ℝ) 1),
      map (simplexLineMap x y r) = AffineMap.lineMap (map x) (map y) r.1)
    (hvertex : ∀ v, map (stdSimplex.vertex v) = point v)
    (a b : V) (r : Set.Icc (0 : ℝ) 1) :
    map (simplexLineMap (stdSimplex.vertex a) (stdSimplex.vertex b) r) =
      AffineMap.lineMap (point a) (point b) r.1 := by
  rw [hline, hvertex, hvertex]

private theorem mem_faceCarrier_of_val_eq_lineMap {K : IntrinsicTwoComplex}
    (s : Finset K.Vertex) (p₀ p₁ q : K.realization) (r : ℝ)
    (hp₀ : p₀ ∈ K.faceCarrier s) (hp₁ : p₁ ∈ K.faceCarrier s)
    (hq : q.1 = AffineMap.lineMap p₀.1 p₁.1 r) :
    q ∈ K.faceCarrier s := by
  intro k hk
  rw [hq]
  simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hp₀ k hk, hp₁ k hk]
  ring

private theorem edgeParameterValue_eq_lineMap {K : IntrinsicTwoComplex}
    (M : K.EdgeMarking) (e : K.Edge) (p₀ p₁ q : K.realization) (r : ℝ)
    (hp₀ : p₀ ∈ K.faceCarrier e.1) (hp₁ : p₁ ∈ K.faceCarrier e.1)
    (hq : q.1 = AffineMap.lineMap p₀.1 p₁.1 r) :
    M.edgeParameterValue e q =
      (1 - r) * M.edgeParameterValue e p₀ + r * M.edgeParameterValue e p₁ := by
  have hqEdge := mem_faceCarrier_of_val_eq_lineMap e.1 p₀ p₁ q r hp₀ hp₁ hq
  rw [M.edgeParameterValue_eq e hqEdge,
    M.edgeParameterValue_eq e hp₀, M.edgeParameterValue_eq e hp₁,
    K.edgeParameter_eq_secondCoordinate e q hqEdge,
    K.edgeParameter_eq_secondCoordinate e p₀ hp₀,
    K.edgeParameter_eq_secondCoordinate e p₁ hp₁,
    hq, AffineMap.lineMap_apply_module]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem coordinates_eq_of_comparison
    {X Y P C : Type*} (mapX : X → P) (mapY : Y → P)
    (coordinatesX : X → C) (coordinatesY : Y → C)
    (mapX_eq : ∀ {x x'}, mapX x = mapX x' → coordinatesX x = coordinatesX x')
    (mapY_eq : ∀ {y y'}, mapY y = mapY y' → coordinatesY y = coordinatesY y')
    (map_eq_of_coordinates :
      ∀ {x y}, coordinatesX x = coordinatesY y → mapX x = mapY y)
    {x x' : X} {y y' : Y}
    (hxy : mapX x = mapY y)
    (hcomparison : coordinatesX x' = coordinatesY y')
    (hy : mapY y' = mapY y) :
    coordinatesX x = coordinatesY y := by
  have hyCoordinates := mapY_eq hy
  have hcomparisonMap := map_eq_of_coordinates hcomparison
  have hx := mapX_eq (hxy.trans (hy.symm.trans hcomparisonMap.symm))
  exact hx.trans (hcomparison.trans hyCoordinates)

private theorem val_eq_of_pushGeometricRealization_eq
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W] (e : V ↪ W)
    (F G : Finset (Finset V))
    (x : GeometricRealization V F) (y : GeometricRealization V G)
    (h : (pushGeometricRealization e F x).1 =
      (pushGeometricRealization e G y).1) :
    x.1 = y.1 := by
  classical
  funext v
  calc
    x.1 v = (pushGeometricRealization e F x).1 (e v) :=
      (pushGeometricRealization_apply_embedding e F x v).symm
    _ = (pushGeometricRealization e G y).1 (e v) := congrFun h (e v)
    _ = y.1 v := pushGeometricRealization_apply_embedding e G y v

private theorem push_relabel_symm_coordinates_eq
    {V W C : Type*} [Fintype V] [Fintype W] [Fintype C]
    [DecidableEq C] (vToCommon : V ↪ C) (wToCommon : W ↪ C)
    (F : Finset (Finset V)) (G : Finset (Finset W))
    (x : GeometricRealization C (relabelFaceFamily vToCommon F))
    (y : GeometricRealization C (relabelFaceFamily wToCommon G))
    (hxy : x.1 = y.1) :
    (pushGeometricRealization vToCommon F
        ((relabelGeometricRealizationHomeomorph vToCommon F).symm x)).1 =
      (pushGeometricRealization wToCommon G
        ((relabelGeometricRealizationHomeomorph wToCommon G).symm y)).1 := by
  calc
    (pushGeometricRealization vToCommon F
        ((relabelGeometricRealizationHomeomorph vToCommon F).symm x)).1 =
        x.1 := congrArg Subtype.val
          ((relabelGeometricRealizationHomeomorph vToCommon F).apply_symm_apply x)
    _ = y.1 := hxy
    _ =
        (pushGeometricRealization wToCommon G
          ((relabelGeometricRealizationHomeomorph wToCommon G).symm y)).1 :=
      congrArg Subtype.val
        ((relabelGeometricRealizationHomeomorph wToCommon G).apply_symm_apply y).symm

private theorem oldSurfaceEmbed_eq_newSurfaceEmbed_of_val_eq
    {S ι : Type*} [TopologicalSpace S] [Fintype ι] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hold : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion)
    (hnew : N.toPlaneComplex.support ⊆ c.kind.modelRegion)
    (x : GeometricRealization
      (PartialTriangulation.RelativeSynchronizedTarget.oldMesh J N lines).Vertex
      (PartialTriangulation.RelativeSynchronizedTarget.oldMesh J N lines).triangles)
    (y : GeometricRealization
      (PartialTriangulation.RelativeSynchronizedTarget.newMesh J N lines).Vertex
      (PartialTriangulation.RelativeSynchronizedTarget.newMesh J N lines).triangles)
    (hxy : x.1 = y.1) :
    PartialTriangulation.RelativeSynchronizedTarget.oldSurfaceEmbed
        c J N lines hold x =
      PartialTriangulation.RelativeSynchronizedTarget.newSurfaceEmbed
        c J N lines harr hnew y :=
  (PartialTriangulation.RelativeSynchronizedTarget.surfaceEmbed_eq_iff
    c J N lines harr hold hnew x y).mpr hxy

private theorem union_subset_interior_union_of_diff_subset
    {X : Type*} [TopologicalSpace X] (A C P Q : Set X)
    (hA : A ⊆ interior P) (hC : C \ interior P ⊆ interior Q) :
    A ∪ C ⊆ interior (P ∪ Q) := by
  intro x hx
  rcases hx with hxA | hxC
  · exact interior_mono Set.subset_union_left (hA hxA)
  · by_cases hxP : x ∈ interior P
    · exact interior_mono Set.subset_union_left hxP
    · exact interior_mono Set.subset_union_right (hC ⟨hxC, hxP⟩)

private theorem maps_eq_of_common_evaluation
    {X Y W Z R : Type*}
    (oldEval : X → Z) (localEval : Y → Z) (ambient : Z → R)
    (oldMap : X → R) (localMap : Y → R) (targetMap : W → R)
    (hOld : ∀ x, oldMap x = ambient (oldEval x))
    (hLocal : ∀ y, ambient (localEval y) = localMap y)
    {x : X} {y : Y} {w : W} (heval : oldEval x = localEval y)
    (htarget : localMap y = targetMap w) :
    oldMap x = targetMap w := by
  rw [hOld, heval, hLocal, htarget]

private theorem oldTarget_agree_of_local_evaluation
    {X Y W Z C S : Type*}
    (oldEval : X → Z) (localEval : Y → Z)
    (oldCoordinates : X → C) (localCoordinates : Y → C)
    (targetCoordinates : W → C)
    (ambient : Z → S) (oldMap : X → S)
    (localMap : Y → S) (targetMap : W → S)
    (hOldEval : Function.Injective oldEval)
    (hOld : ∀ x, oldMap x = ambient (oldEval x))
    (hLocal : ∀ z, ambient (localEval z) = localMap z)
    (hlift : ∀ z, ∃ x, oldEval x = localEval z ∧
      oldCoordinates x = localCoordinates z)
    (hTarget : ∀ z y, localCoordinates z = targetCoordinates y →
      localMap z = targetMap y)
    {x : X} {y : W} {z : Y}
    (heval : oldEval x = localEval z)
    (hcoords : oldCoordinates x = targetCoordinates y) :
    oldMap x = targetMap y := by
  obtain ⟨xz, hxzEval, hxzCoord⟩ := hlift z
  have hxz : xz = x := hOldEval (hxzEval.trans heval.symm)
  subst xz
  exact maps_eq_of_common_evaluation oldEval localEval ambient
    oldMap localMap targetMap hOld hLocal heval
      (hTarget z y (hxzCoord.symm.trans hcoords))

private theorem exists_facePoint_eq_of_edgeParameter_between
    {K L : IntrinsicTwoComplex} (marking : K.EdgeMarking)
    (point : L.UsedVertex → K.realization)
    (faceMap : (t : L.Face) → stdSimplex ℝ {v // v ∈ t.1} → K.realization)
    (hline : ∀ (t : L.Face) (x y : stdSimplex ℝ {v // v ∈ t.1})
      (r : Set.Icc (0 : ℝ) 1),
      (faceMap t (simplexLineMap x y r)).1 =
        AffineMap.lineMap (faceMap t x).1 (faceMap t y).1 r.1)
    (hvertex : ∀ (t : L.Face) (v : {v // v ∈ t.1}),
      faceMap t (stdSimplex.vertex v) = point ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)
    (t : L.Face) (e : K.Edge) (a b : {v // v ∈ t.1})
    (p : K.realization)
    (haEdge : point ⟨a.1, ⟨t.1, t.2, a.2⟩⟩ ∈ K.faceCarrier e.1)
    (hbEdge : point ⟨b.1, ⟨t.1, t.2, b.2⟩⟩ ∈ K.faceCarrier e.1)
    (hpEdge : p ∈ K.faceCarrier e.1)
    (hap : marking.edgeParameterValue e
        (point ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) ≤ marking.edgeParameterValue e p)
    (hpb : marking.edgeParameterValue e p ≤ marking.edgeParameterValue e
        (point ⟨b.1, ⟨t.1, t.2, b.2⟩⟩))
    (hab : marking.edgeParameterValue e
        (point ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) < marking.edgeParameterValue e
        (point ⟨b.1, ⟨t.1, t.2, b.2⟩⟩)) :
    ∃ z : stdSimplex ℝ {v // v ∈ t.1}, faceMap t z = p := by
  let A := point ⟨a.1, ⟨t.1, t.2, a.2⟩⟩
  let B := point ⟨b.1, ⟨t.1, t.2, b.2⟩⟩
  let ar := marking.edgeParameterValue e A
  let br := marking.edgeParameterValue e B
  let pr := marking.edgeParameterValue e p
  have hden : 0 < br - ar := sub_pos.mpr hab
  let r₀ := (pr - ar) / (br - ar)
  have hr₀ : r₀ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hap) hden.le
    · rw [div_le_one hden]
      linarith
  let r : Set.Icc (0 : ℝ) 1 := ⟨r₀, hr₀⟩
  let z := simplexLineMap (stdSimplex.vertex a) (stdSimplex.vertex b) r
  refine ⟨z, ?_⟩
  let q := faceMap t z
  have hqLine : q.1 = AffineMap.lineMap A.1 B.1 r.1 := by
    change (faceMap t (simplexLineMap
      (stdSimplex.vertex a) (stdSimplex.vertex b) r)).1 = _
    rw [hline, hvertex, hvertex]
  have hqEdge : q ∈ K.faceCarrier e.1 := by
    intro k hk
    rw [hqLine]
    simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [haEdge k hk, hbEdge k hk]
    ring
  have hqParameter : marking.edgeParameterValue e q = pr := by
    rw [marking.edgeParameterValue_eq e hqEdge,
      K.edgeParameter_eq_secondCoordinate, hqLine,
      AffineMap.lineMap_apply_module]
    have haParameter : A.1 (K.edgeSecond e) = ar := by
      change A.1 (K.edgeSecond e) = marking.edgeParameterValue e A
      rw [marking.edgeParameterValue_eq e haEdge,
        K.edgeParameter_eq_secondCoordinate]
    have hbParameter : B.1 (K.edgeSecond e) = br := by
      change B.1 (K.edgeSecond e) = marking.edgeParameterValue e B
      rw [marking.edgeParameterValue_eq e hbEdge,
        K.edgeParameter_eq_secondCoordinate]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [haParameter, hbParameter]
    change (1 - r₀) * ar + r₀ * br = pr
    dsimp only [r₀]
    field_simp
    ring
  exact marking.edgeParameterValue_injOn e hqEdge hpEdge (hqParameter.trans rfl)

/-- An affine subdivision carries a source face map back to the barycentric combination of the
lifts of its vertices.  This isolates the finite-dimensional affine calculation from the chart
construction that supplies the source map. -/
private theorem subdivision_preimage_faceMap_eq_vertex_sum
    {K L : IntrinsicTwoComplex} (R : K.Subdivision)
    (source : L.realization → K.realization)
    (lift : L.UsedVertex → R.refined.realization)
    (parent : L.Face → R.refined.Face)
    (hlift : ∀ u, R.homeo (lift u) = source (L.vertexPoint u))
    (hliftFace : ∀ (t : L.Face) (v : {v // v ∈ t.1}),
      lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈ R.refined.faceCarrier (parent t).1)
    (hface : ∀ (t : L.Face) (x : stdSimplex ℝ {v // v ∈ t.1}),
      R.homeo.symm (source (L.faceStandardMap t x)) ∈
        R.refined.faceCarrier (parent t).1)
    (hsourceSum : ∀ (t : L.Face) (x : stdSimplex ℝ {v // v ∈ t.1}),
      (source (L.faceStandardMap t x)).1 =
        ∑ v : {v // v ∈ t.1}, x v •
          (source (L.vertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1)
    (t : L.Face) (x : stdSimplex ℝ {v // v ∈ t.1}) :
    (R.homeo.symm (source (L.faceStandardMap t x))).1 =
      ∑ v : {v // v ∈ t.1}, x v •
        (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 := by
  classical
  let xg : L.realization := L.faceStandardMap t x
  let s := parent t
  let y : R.refined.realization := R.homeo.symm (source xg)
  have hyFace : y ∈ R.refined.faceCarrier s.1 := hface t x
  let point : {v // v ∈ t.1} → (R.refined.Vertex → ℝ) :=
    fun v ↦ (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1
  let weight : {v // v ∈ t.1} → ℝ := fun v ↦ x v
  have hweight : ∑ v, weight v = 1 := x.2.2
  let zfun : R.refined.Vertex → ℝ :=
    (Finset.univ : Finset {v // v ∈ t.1}).affineCombination ℝ point weight
  have hzlinear : zfun = ∑ v, weight v • point v :=
    Finset.affineCombination_eq_linear_combination Finset.univ point weight hweight
  have hznonneg : ∀ k, 0 ≤ zfun k := by
    intro k
    rw [hzlinear]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (x.2.1 v)
      ((lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).2.1.1 k)
  have hzsum : ∑ k, zfun k = 1 := by
    rw [hzlinear]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    calc
      (∑ v, ∑ k, weight v * (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k) =
          ∑ v, weight v * ∑ k, (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.mul_sum]
      _ = ∑ v, weight v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [(lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).2.1.2, mul_one]
      _ = 1 := hweight
  have hzsupport : ∀ k ∉ s.1, zfun k = 0 := by
    intro k hk
    rw [hzlinear]
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro v _
    change weight v • (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k = 0
    rw [(hliftFace t v) k hk, smul_zero]
  let z : R.refined.realization :=
    ⟨zfun, ⟨hznonneg, hzsum⟩, ⟨s.1, s.2, hzsupport⟩⟩
  obtain ⟨b, hb⟩ := R.affineOnFace s.1 s.2
  have hbz : (R.homeo z).1 = b z.1 := hb z hzsupport
  have hbcomb : b zfun =
      (Finset.univ : Finset {v // v ∈ t.1}).affineCombination ℝ
        (b ∘ point) weight :=
    (Finset.univ : Finset {v // v ∈ t.1}).map_affineCombination
      point weight hweight b
  have hvertex (v : {v // v ∈ t.1}) :
      b (point v) = (source (L.vertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1 := by
    have hbv := hb (lift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) (hliftFace t v)
    rw [← hbv]
    exact congrArg Subtype.val (hlift ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)
  have hzsource : (R.homeo z).1 = (source xg).1 := by
    rw [hbz, hbcomb,
      Finset.affineCombination_eq_linear_combination
        Finset.univ (b ∘ point) weight hweight]
    simp only [Function.comp_apply]
    calc
      ∑ v, weight v • b (point v) =
          ∑ v, x v •
            (source (L.vertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1 := by
        apply Finset.sum_congr rfl
        intro v _
        rw [hvertex v]
      _ = (source (L.faceStandardMap t x)).1 := (hsourceSum t x).symm
  have hyz : y = z := by
    apply R.homeo.injective
    apply Subtype.ext
    rw [R.homeo.apply_symm_apply]
    exact hzsource.symm
  change y.1 = _
  rw [hyz]
  exact hzlinear

/-- A common local realization witnesses equality of coordinates after two finite complexes are
relabelled into the same vertex type. -/
private theorem relabeled_coordinates_eq_of_common_local
    {Old Target Common Z R : Type*}
    [Fintype Old] [Fintype Target] [Fintype Common]
    [DecidableEq Common]
    (oldFaces : Finset (Finset Old)) (localFaces : Finset (Finset Target))
    (targetFaces : Finset (Finset Target))
    (oldToCommon : Old ↪ Common) (targetToCommon : Target ↪ Common)
    (oldMap : GeometricRealization Old oldFaces → R)
    (targetMap : GeometricRealization Target targetFaces → R)
    (oldEval : GeometricRealization Old oldFaces → Z)
    (localEval : GeometricRealization Target localFaces → Z)
    (hOldEval : Function.Injective oldEval)
    (hbridge : ∀ x y, oldMap x = targetMap y →
      ∃ z : GeometricRealization Target localFaces,
        oldEval x = localEval z ∧ z.1 = y.1)
    (hlift : ∀ z : GeometricRealization Target localFaces,
      ∃ x : GeometricRealization Old oldFaces,
        oldEval x = localEval z ∧
          (pushGeometricRealization oldToCommon oldFaces x).1 =
            (pushGeometricRealization targetToCommon localFaces z).1) :
    ∀ (x : GeometricRealization Common (relabelFaceFamily oldToCommon oldFaces))
      (y : GeometricRealization Common (relabelFaceFamily targetToCommon targetFaces)),
      oldMap ((relabelGeometricRealizationHomeomorph oldToCommon oldFaces).symm x) =
          targetMap
            ((relabelGeometricRealizationHomeomorph targetToCommon targetFaces).symm y) →
        x.1 = y.1 := by
  classical
  intro x y hxy
  let xb := (relabelGeometricRealizationHomeomorph oldToCommon oldFaces).symm x
  let yb := (relabelGeometricRealizationHomeomorph targetToCommon targetFaces).symm y
  obtain ⟨z, hzEval, hzy⟩ := hbridge xb yb hxy
  obtain ⟨xz, hxzEval, hxzCoord⟩ := hlift z
  have hxzxb : xz = xb :=
    hOldEval (hxzEval.trans hzEval.symm)
  subst xz
  have htargetCoord :
      (pushGeometricRealization targetToCommon localFaces z).1 =
        (pushGeometricRealization targetToCommon targetFaces yb).1 :=
    pushGeometricRealization_val_eq_of_val_eq targetToCommon
      localFaces targetFaces z yb hzy
  have hxback :
      (relabelGeometricRealizationHomeomorph oldToCommon oldFaces) xb = x :=
    (relabelGeometricRealizationHomeomorph oldToCommon oldFaces).apply_symm_apply x
  have hyback :
      (relabelGeometricRealizationHomeomorph targetToCommon targetFaces) yb = y :=
    (relabelGeometricRealizationHomeomorph targetToCommon targetFaces).apply_symm_apply y
  calc
    x.1 =
        ((relabelGeometricRealizationHomeomorph oldToCommon oldFaces) xb).1 :=
      congrArg Subtype.val hxback.symm
    _ = (pushGeometricRealization oldToCommon oldFaces xb).1 := rfl
    _ = (pushGeometricRealization targetToCommon localFaces z).1 := hxzCoord
    _ = (pushGeometricRealization targetToCommon targetFaces yb).1 := htargetCoord
    _ = ((relabelGeometricRealizationHomeomorph targetToCommon targetFaces) yb).1 := rfl
    _ = y.1 := congrArg Subtype.val hyback

private theorem mem_map_univ {V W : Type*} [Fintype V]
    (e : V ↪ W) (v : V) : e v ∈ (Finset.univ : Finset V).map e :=
  Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩

/-- Introduce an abstraction boundary around a large local record.  Pattern-matching on this
existential leaves the witness abstract, preventing downstream projection reduction from
re-normalizing all fields of the original structure literal. -/
private theorem exists_sealed_copy {X : Sort*} (x : X) : ∃ y : X, y = x :=
  ⟨x, rfl⟩

private theorem mem_finset_map {V W : Type*}
    (e : V ↪ W) (F : Finset V) {v : V} (hv : v ∈ F) : e v ∈ F.map e :=
  Finset.mem_map.mpr ⟨v, hv, rfl⟩

private theorem fanVertexEmbedding_mem_globalFanFaceVertices
    {K : IntrinsicTwoComplex} (M : K.EdgeMarking) (f : M.FanFace)
    (v : {p // p ∈ M.fanFaceVertices f}) :
    M.fanVertexEmbedding f v ∈ M.globalFanFaceVertices f :=
  (M.mem_globalFanFaceVertices_iff f _).mpr v.2

private theorem fanFirstVertexEmbedding_mem_globalFanFaceVertices
    {K : IntrinsicTwoComplex} (M : K.EdgeMarking) (f : M.FanFace) :
    M.fanVertexEmbedding f (M.fanFirstVertex f) ∈ M.globalFanFaceVertices f :=
  fanVertexEmbedding_mem_globalFanFaceVertices M f (M.fanFirstVertex f)

private theorem fanSecondVertexEmbedding_mem_globalFanFaceVertices
    {K : IntrinsicTwoComplex} (M : K.EdgeMarking) (f : M.FanFace) :
    M.fanVertexEmbedding f (M.fanSecondVertex f) ∈ M.globalFanFaceVertices f :=
  fanVertexEmbedding_mem_globalFanFaceVertices M f (M.fanSecondVertex f)

private theorem fanRelabel_relabelFace_relabelUniv_apply
    {K : IntrinsicTwoComplex} (M : K.EdgeMarking) (f : M.FanFace)
    {Old Used : Type*}
    (fanToOld : M.FanVertex ↪ Old)
    (oldToUsed :
      {v // v ∈ (M.globalFanFaceVertices f).map fanToOld} ↪ Used)
    (x : stdSimplex ℝ
      {v // v ∈ (Finset.univ : Finset
        {v // v ∈ (M.globalFanFaceVertices f).map fanToOld}).map oldToUsed})
    (p : {p // p ∈ M.fanFaceVertices f}) :
    (M.fanRelabelSimplex f
      (relabelFaceSimplex fanToOld (M.globalFanFaceVertices f)
        (relabelUnivSimplex oldToUsed x))) p =
      x ⟨oldToUsed
          ⟨fanToOld (M.fanVertexEmbedding f p),
            mem_finset_map fanToOld _
              (fanVertexEmbedding_mem_globalFanFaceVertices M f p)⟩,
        mem_map_univ oldToUsed _⟩ := by
  classical
  let gp := M.fanVertexEmbedding f p
  have hgp : gp ∈ M.globalFanFaceVertices f :=
    fanVertexEmbedding_mem_globalFanFaceVertices M f p
  let op : {v // v ∈ (M.globalFanFaceVertices f).map fanToOld} :=
    ⟨fanToOld gp, mem_finset_map fanToOld _ hgp⟩
  let uv := oldToUsed op
  have huv : uv ∈ (Finset.univ : Finset
      {v // v ∈ (M.globalFanFaceVertices f).map fanToOld}).map oldToUsed :=
    mem_map_univ oldToUsed op
  let wv : {v // v ∈ (Finset.univ : Finset
      {v // v ∈ (M.globalFanFaceVertices f).map fanToOld}).map oldToUsed} :=
    ⟨uv, huv⟩
  calc
    (M.fanRelabelSimplex f
        (relabelFaceSimplex fanToOld (M.globalFanFaceVertices f)
          (relabelUnivSimplex oldToUsed x))) p =
        extendFaceCoordinates (M.fanFaceVertices f)
          (M.fanRelabelSimplex f
            (relabelFaceSimplex fanToOld (M.globalFanFaceVertices f)
              (relabelUnivSimplex oldToUsed x))) gp.1 := by
      change _ = extendFaceCoordinates (M.fanFaceVertices f) _ p.1
      rw [extendFaceCoordinates_of_mem _ _ p.2]
    _ = extendFaceCoordinates (M.globalFanFaceVertices f)
          (relabelFaceSimplex fanToOld (M.globalFanFaceVertices f)
            (relabelUnivSimplex oldToUsed x)) gp :=
      M.fanRelabel_extended_apply f _ gp
    _ = extendFaceCoordinates
          ((M.globalFanFaceVertices f).map fanToOld)
          (relabelUnivSimplex oldToUsed x) (fanToOld gp) :=
      relabelFaceSimplex_extended_apply fanToOld
        (M.globalFanFaceVertices f) _ gp
    _ = (relabelUnivSimplex oldToUsed x) op := by
      rw [extendFaceCoordinates_of_mem _ _ op.2]
    _ = extendFaceCoordinates
          ((Finset.univ : Finset
            {v // v ∈ (M.globalFanFaceVertices f).map fanToOld}).map oldToUsed)
          x uv :=
      relabelUnivSimplex_apply oldToUsed x op
    _ = x wv := by
      rw [extendFaceCoordinates_of_mem _ _ huv]
    _ = _ := rfl

/-- The vertices of an old complex which are not identified with a local target vertex. -/
private abbrev OldVertexComplement {Local Old : Type*} (localToOld : Local ↪ Old) :=
  {v : Old // ¬ ∃ u : Local, localToOld u = v}

/-- A common vertex type obtained by replacing the local part of `Old` by `Target`. -/
private abbrev AmalgamatedVertex {Local Old : Type*} (localToOld : Local ↪ Old)
    (Target : Type*) :=
  Sum (OldVertexComplement localToOld) Target

private noncomputable def oldToAmalgamatedFun {Local Old Target : Type*}
    (localToOld : Local ↪ Old) (localToTarget : Local ↪ Target) :
    Old → AmalgamatedVertex localToOld Target := by
  classical
  exact fun v ↦ if hv : ∃ u : Local, localToOld u = v then
      Sum.inr (localToTarget (Classical.choose hv))
    else
      Sum.inl ⟨v, hv⟩

private theorem oldToAmalgamatedFun_injective {Local Old Target : Type*}
    (localToOld : Local ↪ Old) (localToTarget : Local ↪ Target) :
    Function.Injective (oldToAmalgamatedFun localToOld localToTarget) := by
  intro v w hvw
  by_cases hv : ∃ u : Local, localToOld u = v
  · by_cases hw : ∃ u : Local, localToOld u = w
    · have htarget :
          localToTarget (Classical.choose hv) =
            localToTarget (Classical.choose hw) := by
        have hs :
            (Sum.inr (localToTarget (Classical.choose hv)) :
                AmalgamatedVertex localToOld Target) =
              Sum.inr (localToTarget (Classical.choose hw)) := by
          simpa only [oldToAmalgamatedFun, dite_eq_left hv, dite_eq_left hw] using hvw
        exact Sum.inr_injective (show
          (Sum.inr (localToTarget (Classical.choose hv)) :
              OldVertexComplement localToOld ⊕ Target) =
            Sum.inr (localToTarget (Classical.choose hw)) from
          hs)
      have hlocal : Classical.choose hv = Classical.choose hw :=
        localToTarget.injective htarget
      calc
        v = localToOld (Classical.choose hv) := (Classical.choose_spec hv).symm
        _ = localToOld (Classical.choose hw) := congrArg localToOld hlocal
        _ = w := Classical.choose_spec hw
    · exfalso
      simp only [oldToAmalgamatedFun, dite_eq_left hv, dite_eq_right hw, reduceCtorEq] at hvw
  · by_cases hw : ∃ u : Local, localToOld u = w
    · exfalso
      simp only [oldToAmalgamatedFun, dite_eq_right hv, dite_eq_left hw, reduceCtorEq] at hvw
    · have hextra :
          (⟨v, hv⟩ : OldVertexComplement localToOld) = ⟨w, hw⟩ := by
        have hs :
            (Sum.inl (⟨v, hv⟩ : OldVertexComplement localToOld) :
                AmalgamatedVertex localToOld Target) =
              Sum.inl ⟨w, hw⟩ := by
          simpa only [oldToAmalgamatedFun, dite_eq_right hv, dite_eq_right hw] using hvw
        exact Sum.inl_injective (show
          (Sum.inl (⟨v, hv⟩ : OldVertexComplement localToOld) :
              OldVertexComplement localToOld ⊕ Target) =
            Sum.inl ⟨w, hw⟩ from hs)
      exact congrArg Subtype.val hextra

private noncomputable def oldToAmalgamated {Local Old Target : Type*}
    (localToOld : Local ↪ Old) (localToTarget : Local ↪ Target) :
    Old ↪ AmalgamatedVertex localToOld Target :=
  ⟨oldToAmalgamatedFun localToOld localToTarget,
    oldToAmalgamatedFun_injective localToOld localToTarget⟩

private def targetToAmalgamated {Local Old Target : Type*}
    (localToOld : Local ↪ Old) : Target ↪ AmalgamatedVertex localToOld Target :=
  ⟨Sum.inr, Sum.inr_injective⟩

private theorem oldToAmalgamated_local {Local Old Target : Type*}
    (localToOld : Local ↪ Old) (localToTarget : Local ↪ Target) (u : Local) :
    oldToAmalgamated localToOld localToTarget (localToOld u) =
      targetToAmalgamated localToOld (localToTarget u) := by
  have hlocal : ∃ q, localToOld q = localToOld u := ⟨u, rfl⟩
  change oldToAmalgamatedFun localToOld localToTarget (localToOld u) =
    Sum.inr (localToTarget u)
  rw [show oldToAmalgamatedFun localToOld localToTarget (localToOld u) =
      Sum.inr (localToTarget (Classical.choose hlocal)) by
    simp only [oldToAmalgamatedFun, dite_eq_left hlocal]]
  congr 1
  exact congrArg localToTarget
    (localToOld.injective (Classical.choose_spec hlocal))

/-- Equality of coordinates on an amalgamated vertex type forces every positively weighted old
vertex to come from the local part. -/
private theorem exists_local_of_positive_of_amalgamated_coordinates
    {Local Old Target : Type*}
    (localToOld : Local ↪ Old) (localToTarget : Local ↪ Target)
    (oldWeight : Old → ℝ)
    (oldCoordinates targetCoordinates :
      AmalgamatedVertex localToOld Target → ℝ)
    (hOld : ∀ v, oldCoordinates
      (oldToAmalgamated localToOld localToTarget v) = oldWeight v)
    (hTarget : ∀ v : OldVertexComplement localToOld,
      targetCoordinates (Sum.inl v) = 0)
    (hcoords : oldCoordinates = targetCoordinates)
    (v : Old) (hv : 0 < oldWeight v) :
    ∃ u : Local, localToOld u = v := by
  by_contra hlocal
  have hvCommon :
      oldToAmalgamated localToOld localToTarget v =
        Sum.inl ⟨v, hlocal⟩ := by
    change oldToAmalgamatedFun localToOld localToTarget v =
      Sum.inl ⟨v, hlocal⟩
    simp only [oldToAmalgamatedFun, dite_eq_right hlocal]
  have hzero : oldWeight v = 0 := by
    rw [← hOld v, hvCommon, hcoords]
    exact hTarget ⟨v, hlocal⟩
  linarith

/-- The chart-independent data used to glue a finite local complex to the marked fans in an
ambient intrinsic complex.  Keeping this data in one object prevents the compatibility proof from
inheriting the much larger chart-straightening telescope. -/
private structure MixedLocalFanData where
  ambient : IntrinsicTwoComplex
  localComplex : IntrinsicTwoComplex
  marking : ambient.EdgeMarking
  isOutside : marking.FanFace → Prop
  isOutside_decidable : DecidablePred isOutside
  localVertexPoint : localComplex.UsedVertex → ambient.realization
  localVertexPoint_injective : Function.Injective localVertexPoint
  localFaceMap : (t : localComplex.Face) →
    stdSimplex ℝ {v // v ∈ t.1} → ambient.realization

private abbrev MixedLocalFanData.OutsideFanFace (M : MixedLocalFanData) :=
  {f : M.marking.FanFace // M.isOutside f}

private instance MixedLocalFanData.instDecidablePredIsOutside (M : MixedLocalFanData) :
    DecidablePred M.isOutside := M.isOutside_decidable

private noncomputable abbrev MixedLocalFanData.oldVertexPoints (M : MixedLocalFanData) :
    Finset M.ambient.realization :=
  (Finset.univ : Finset M.localComplex.UsedVertex).image M.localVertexPoint ∪
    M.marking.fanVertices

private abbrev MixedLocalFanData.OldVertex (M : MixedLocalFanData) :=
  {p : M.ambient.realization // p ∈ M.oldVertexPoints}

private noncomputable abbrev MixedLocalFanData.localOldVertexEmbedding (M : MixedLocalFanData) :
    M.localComplex.UsedVertex ↪ M.OldVertex :=
  { toFun := fun v ↦ ⟨M.localVertexPoint v, by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩
    inj' := fun _ _ h ↦ M.localVertexPoint_injective
      (congrArg (fun z : M.OldVertex ↦ z.1) h) }

private noncomputable abbrev MixedLocalFanData.fanOldVertexEmbedding (M : MixedLocalFanData) :
    M.marking.FanVertex ↪ M.OldVertex :=
  { toFun := fun v ↦ ⟨v.1, Finset.mem_union_right _ v.2⟩
    inj' := fun _ _ h ↦ Subtype.ext
      (congrArg (fun z : M.OldVertex ↦ z.1) h) }

private noncomputable abbrev MixedLocalFanData.localFaceOldVertexEmbedding
    (M : MixedLocalFanData) (t : M.localComplex.Face) : {v // v ∈ t.1} ↪ M.OldVertex :=
  { toFun := fun v ↦ M.localOldVertexEmbedding ⟨v.1, ⟨t.1, t.2, v.2⟩⟩
    inj' := by
      intro v w hvw
      apply Subtype.ext
      have hp :
          M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ =
            M.localVertexPoint ⟨w.1, ⟨t.1, t.2, w.2⟩⟩ :=
        congrArg (fun z : M.OldVertex ↦ z.1) hvw
      exact congrArg (fun z : M.localComplex.UsedVertex ↦ z.1)
        (M.localVertexPoint_injective hp) }

private abbrev MixedLocalFanData.MixedOldFace (M : MixedLocalFanData) :=
  Sum M.localComplex.Face M.OutsideFanFace

private noncomputable abbrev MixedLocalFanData.mixedOldFaceVertices
    (M : MixedLocalFanData) : M.MixedOldFace → Finset M.OldVertex
  | Sum.inl t =>
      (Finset.univ : Finset {v // v ∈ t.1}).map (M.localFaceOldVertexEmbedding t)
  | Sum.inr f =>
      (M.marking.globalFanFaceVertices f.1).map M.fanOldVertexEmbedding

private noncomputable abbrev MixedLocalFanData.mixedOldFaceMap
    (M : MixedLocalFanData) (f : M.MixedOldFace) :
    stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f} → M.ambient.realization :=
  match f with
  | Sum.inl t => fun x ↦
      M.localFaceMap t (relabelUnivSimplex (M.localFaceOldVertexEmbedding t) x)
  | Sum.inr f => fun x ↦
      M.marking.globalFanFaceMap f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) x)

private theorem MixedLocalFanData.mixedOldFaceVertices_card_three
    (M : MixedLocalFanData) (f : M.MixedOldFace) :
    (M.mixedOldFaceVertices f).card = 3 := by
  rcases f with t | f
  · change ((Finset.univ : Finset {v // v ∈ t.1}).map
        (M.localFaceOldVertexEmbedding t)).card = 3
    rw [Finset.card_map, Finset.card_univ, Fintype.card_coe,
      M.localComplex.faces_card t.1 t.2]
  · change ((M.marking.globalFanFaceVertices f.1).map M.fanOldVertexEmbedding).card = 3
    rw [Finset.card_map, IntrinsicTwoComplex.EdgeMarking.globalFanFaceVertices,
      Finset.card_map, Finset.card_attach, M.marking.fanFaceVertices_card]

private theorem MixedLocalFanData.mixedOldFaceMap_val_of_local
    (M : MixedLocalFanData)
    (hlocal : ∀ (t : M.localComplex.Face) (x : stdSimplex ℝ {v // v ∈ t.1}),
      (M.localFaceMap t x).1 = ∑ v : {v // v ∈ t.1}, x v •
        (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1)
    (f : M.MixedOldFace)
    (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f}) :
    (M.mixedOldFaceMap f x).1 = fun k ↦ ∑ v : M.OldVertex,
      extendFaceCoordinates (M.mixedOldFaceVertices f) x v * v.1.1 k := by
  rcases f with t | f
  · let x₀ := relabelUnivSimplex (M.localFaceOldVertexEmbedding t) x
    rw [hlocal t x₀]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hsum := sum_extendFaceCoordinates_relabelUnivSimplex
      (M.localFaceOldVertexEmbedding t) x (fun v : M.OldVertex ↦ v.1.1 k)
    exact hsum.symm
  · let y := relabelFaceSimplex M.fanOldVertexEmbedding
      (M.marking.globalFanFaceVertices f.1) x
    rw [M.marking.globalFanFaceMap_val_eq_fanBarycentricAffine]
    funext k
    rw [M.marking.fanBarycentricAffine_apply]
    have hsum := sum_extendFaceCoordinates_relabelFaceSimplex
      M.fanOldVertexEmbedding (M.marking.globalFanFaceVertices f.1) x
      (fun v : M.OldVertex ↦ v.1.1 k)
    exact hsum.symm

private theorem MixedLocalFanData.localMixedExtended_apply
    (M : MixedLocalFanData) (t : M.localComplex.Face)
    (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)})
    (u : M.localComplex.UsedVertex) :
    extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x
        (M.localOldVertexEmbedding u) =
      extendFaceCoordinates t.1
        (relabelUnivSimplex (M.localFaceOldVertexEmbedding t) x) u.1 := by
  by_cases hut : u.1 ∈ t.1
  · let v : {v // v ∈ t.1} := ⟨u.1, hut⟩
    have huv : u = ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ := Subtype.ext rfl
    have hemb :
        M.localOldVertexEmbedding u = M.localFaceOldVertexEmbedding t v := by
      change M.localOldVertexEmbedding u =
        M.localOldVertexEmbedding ⟨v.1, ⟨t.1, t.2, v.2⟩⟩
      exact congrArg M.localOldVertexEmbedding huv
    have hmem :
        M.localFaceOldVertexEmbedding t v ∈
          M.mixedOldFaceVertices (Sum.inl t) :=
      mem_map_univ (M.localFaceOldVertexEmbedding t) v
    rw [hemb, extendFaceCoordinates_of_mem _ _ hmem,
      extendFaceCoordinates_of_mem _ _ hut]
    have hrel :=
      (relabelUnivSimplex_apply (M.localFaceOldVertexEmbedding t) x v).symm
    rw [extendFaceCoordinates_of_mem _ _ hmem] at hrel
    simpa only [v] using hrel
  · have hnot :
        M.localOldVertexEmbedding u ∉ M.mixedOldFaceVertices (Sum.inl t) := by
      intro hu
      change M.localOldVertexEmbedding u ∈
        (Finset.univ : Finset {v // v ∈ t.1}).map
          (M.localFaceOldVertexEmbedding t) at hu
      obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hu
      have hused : u = ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ :=
        M.localOldVertexEmbedding.injective hv.symm
      exact hut (congrArg (fun z : M.localComplex.UsedVertex ↦ z.1) hused ▸ v.2)
    rw [extendFaceCoordinates_of_notMem _ _ hnot,
      extendFaceCoordinates_of_notMem _ _ hut]

private theorem faceStandardMap_comp_eq_iff
    {Z : Type*} (L : IntrinsicTwoComplex) (map : L.realization → Z)
    (hmap : Function.Injective map)
    {t u : L.Face} {x : stdSimplex ℝ {v // v ∈ t.1}}
    {y : stdSimplex ℝ {v // v ∈ u.1}} :
    map (L.faceStandardMap t x) = map (L.faceStandardMap u y) ↔
      extendFaceCoordinates t.1 x = extendFaceCoordinates u.1 y := by
  constructor
  · intro h
    have hrealization := congrArg Subtype.val (hmap h)
    simpa only [L.faceStandardMap_val] using hrealization
  · intro h
    apply congrArg map
    apply Subtype.ext
    simpa only [L.faceStandardMap_val] using h

private theorem MixedLocalFanData.localMixedFaceMap_eq_iff_of_local
    (M : MixedLocalFanData)
    (hlocal : ∀ {t u : M.localComplex.Face}
      {x : stdSimplex ℝ {v // v ∈ t.1}}
      {y : stdSimplex ℝ {v // v ∈ u.1}},
      M.localFaceMap t x = M.localFaceMap u y ↔
        extendFaceCoordinates t.1 x = extendFaceCoordinates u.1 y)
    {t u : M.localComplex.Face}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl u)}} :
    M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inl u) y ↔
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl u)) y := by
  let x₀ := relabelUnivSimplex (M.localFaceOldVertexEmbedding t) x
  let y₀ := relabelUnivSimplex (M.localFaceOldVertexEmbedding u) y
  constructor
  · intro hxy
    have hcoords : extendFaceCoordinates t.1 x₀ =
        extendFaceCoordinates u.1 y₀ := hlocal.mp hxy
    funext p
    by_cases hp : p ∈ Set.range M.localOldVertexEmbedding
    · obtain ⟨v, rfl⟩ := hp
      rw [M.localMixedExtended_apply t x v,
        M.localMixedExtended_apply u y v, congrFun hcoords v.1]
    · have hpt : p ∉ M.mixedOldFaceVertices (Sum.inl t) := by
        intro hpt
        change p ∈ (Finset.univ : Finset {v // v ∈ t.1}).map
          (M.localFaceOldVertexEmbedding t) at hpt
        obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hpt
        exact hp ⟨⟨v.1, ⟨t.1, t.2, v.2⟩⟩, hv⟩
      have hpu : p ∉ M.mixedOldFaceVertices (Sum.inl u) := by
        intro hpu
        change p ∈ (Finset.univ : Finset {v // v ∈ u.1}).map
          (M.localFaceOldVertexEmbedding u) at hpu
        obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hpu
        exact hp ⟨⟨v.1, ⟨u.1, u.2, v.2⟩⟩, hv⟩
      rw [extendFaceCoordinates_of_notMem _ _ hpt,
        extendFaceCoordinates_of_notMem _ _ hpu]
  · intro hcoords
    apply hlocal.mpr
    funext v
    by_cases hvUsed : ∃ q ∈ M.localComplex.faces, v ∈ q
    · let w : M.localComplex.UsedVertex := ⟨v, hvUsed⟩
      have hw := congrFun hcoords (M.localOldVertexEmbedding w)
      rw [M.localMixedExtended_apply t x w,
        M.localMixedExtended_apply u y w] at hw
      exact hw
    · have hvt : v ∉ t.1 := fun hvt ↦ hvUsed ⟨t.1, t.2, hvt⟩
      have hvu : v ∉ u.1 := fun hvu ↦ hvUsed ⟨u.1, u.2, hvu⟩
      rw [extendFaceCoordinates_of_notMem _ _ hvt,
        extendFaceCoordinates_of_notMem _ _ hvu]

/-- The local facts needed by the chart-independent local/fan compatibility argument. -/
private structure MixedLocalFanCertificate (M : MixedLocalFanData) where
  parentFace : M.localComplex.Face → M.ambient.Face
  outside_parent_ne : ∀ (f : M.OutsideFanFace) (t : M.localComplex.Face),
    f.1.1 ≠ parentFace t
  mixedOldFaceVertices_card : ∀ f : M.MixedOldFace,
    (M.mixedOldFaceVertices f).card = 3
  continuous_mixedOldFaceMap : ∀ f : M.MixedOldFace,
    Continuous (M.mixedOldFaceMap f)
  mixedOldFaceMap_val :
    ∀ (f : M.MixedOldFace)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f}),
      (M.mixedOldFaceMap f x).1 = fun k ↦ ∑ v : M.OldVertex,
        extendFaceCoordinates (M.mixedOldFaceVertices f) x v * v.1.1 k
  localMixedFaceMap_eq_iff :
    ∀ {t u : M.localComplex.Face}
      {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
      {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl u)}},
      M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inl u) y ↔
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
          extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl u)) y
  fanMixedFaceMap_eq_iff :
    ∀ {f g : M.OutsideFanFace}
      {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}}
      {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr g)}},
      M.mixedOldFaceMap (Sum.inr f) x = M.mixedOldFaceMap (Sum.inr g) y ↔
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) x =
          extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr g)) y
  mixedOldFaceMap_eq_of_extendedCoordinates :
    ∀ {f g : M.MixedOldFace}
      {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f}}
      {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices g}},
      extendFaceCoordinates (M.mixedOldFaceVertices f) x =
          extendFaceCoordinates (M.mixedOldFaceVertices g) y →
        M.mixedOldFaceMap f x = M.mixedOldFaceMap g y
  localMixedFaceMap_mem_parent :
    ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}),
      M.mixedOldFaceMap (Sum.inl t) x ∈ M.ambient.faceCarrier (parentFace t).1
  localVertexPoint_mem_parent :
    ∀ (t : M.localComplex.Face) (v : {v // v ∈ t.1}),
      M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
        M.ambient.faceCarrier (parentFace t).1
  localVertexPoint_mem_marking :
    ∀ v : M.localComplex.UsedVertex, M.localVertexPoint v ∈ M.marking.points
  positive_localVertex_mem_edge :
    ∀ (t : M.localComplex.Face) (x : stdSimplex ℝ {v // v ∈ t.1})
      (e : M.ambient.Edge),
      M.localFaceMap t x ∈ M.ambient.faceCarrier e.1 →
        ∀ (v : {v // v ∈ t.1}), 0 < x v →
          M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈ M.ambient.faceCarrier e.1
  localFace_edgeParameter_eq_sum :
    ∀ (t : M.localComplex.Face) (x : stdSimplex ℝ {v // v ∈ t.1})
      (e : M.ambient.Edge),
      M.localFaceMap t x ∈ M.ambient.faceCarrier e.1 →
        M.marking.edgeParameterValue e (M.localFaceMap t x) =
          ∑ v : {v // v ∈ t.1}, x v * M.marking.edgeParameterValue e
            (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)
  edge_subset_face_of_openPoint :
    ∀ (e : M.ambient.Edge) (s : M.ambient.Face) (q : M.ambient.realization),
      q ∈ M.ambient.edgePath e '' {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1} →
        q ∈ M.ambient.faceCarrier s.1 → e.1 ⊆ s.1
  edgeMark_lift :
    ∀ (t : M.localComplex.Face) (e : M.ambient.Edge),
      e.1 ⊆ (parentFace t).1 → ∀ p ∈ M.marking.edgeMarks e,
        ∃ u : M.localComplex.UsedVertex, M.localVertexPoint u = p
  markingPoint_lift :
    ∀ (t : M.localComplex.Face) p, p ∈ M.marking.points →
      p ∈ M.ambient.faceCarrier (parentFace t).1 →
        ∃ u : M.localComplex.UsedVertex, M.localVertexPoint u = p
  localUsedVertex_mem_face_of_map_eq :
    ∀ (t : M.localComplex.Face) (z : stdSimplex ℝ {v // v ∈ t.1})
      (u : M.localComplex.UsedVertex),
      M.localFaceMap t z = M.localVertexPoint u → u.1 ∈ t.1
  exists_localFacePoint_eq_of_edgeParameter_between :
    ∀ (t : M.localComplex.Face) (e : M.ambient.Edge) (a b : {v // v ∈ t.1})
      (p : M.ambient.realization),
      M.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩ ∈ M.ambient.faceCarrier e.1 →
      M.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩ ∈ M.ambient.faceCarrier e.1 →
      p ∈ M.ambient.faceCarrier e.1 →
      M.marking.edgeParameterValue e
          (M.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) ≤
        M.marking.edgeParameterValue e p →
      M.marking.edgeParameterValue e p ≤
        M.marking.edgeParameterValue e
          (M.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩) →
      M.marking.edgeParameterValue e
          (M.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) <
        M.marking.edgeParameterValue e
          (M.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩) →
      ∃ z : stdSimplex ℝ {v // v ∈ t.1}, M.localFaceMap t z = p
  mixedOldFaceMap_simplexLineMap :
    ∀ (f : M.MixedOldFace)
      (x y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f})
      (r : Set.Icc (0 : ℝ) 1),
      (M.mixedOldFaceMap f (simplexLineMap x y r)).1 =
        AffineMap.lineMap (M.mixedOldFaceMap f x).1 (M.mixedOldFaceMap f y).1 r.1
  mixedOldFaceMap_vertex :
    ∀ (f : M.MixedOldFace) (v : {v // v ∈ M.mixedOldFaceVertices f}),
      M.mixedOldFaceMap f (stdSimplex.vertex v) = v.1.1
  mixedLocalExtended_eq_single_of_map_eq_localVertex :
    ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)})
      (u : M.localComplex.UsedVertex),
      M.mixedOldFaceMap (Sum.inl t) x = M.localVertexPoint u →
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
          Pi.single (M.localOldVertexEmbedding u) 1
  mixedFanExtended_eq_single_of_map_eq_fanVertex :
    ∀ (f : M.OutsideFanFace)
      (y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)})
      (v : {p // p ∈ M.marking.fanFaceVertices f.1}),
      M.mixedOldFaceMap (Sum.inr f) y = v.1 →
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y =
          Pi.single (M.fanOldVertexEmbedding (M.marking.fanVertexEmbedding f.1 v)) 1

private structure LocalFanIntervalVertices
    (M : MixedLocalFanData) (t : M.localComplex.Face) (f : M.OutsideFanFace) where
  first : M.localComplex.UsedVertex
  second : M.localComplex.UsedVertex
  first_mem : first.1 ∈ t.1
  second_mem : second.1 ∈ t.1
  first_eq : M.localVertexPoint first =
    M.marking.edgeIntervalFirst (M.ambient.faceEdge f.1.1 f.1.2.1) f.1.2.2
  second_eq : M.localVertexPoint second =
    M.marking.edgeIntervalSecond (M.ambient.faceEdge f.1.1 f.1.2.1) f.1.2.2

private theorem MixedLocalFanCertificate.exists_localFanIntervalVertices
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {t : M.localComplex.Face} {f : M.OutsideFanFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}}
    (hxy : M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inr f) y)
    (hyCenter :
      (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanCenterVertex f.1) = 0)
    (hyPos :
      0 < (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanFirstVertex f.1) ∧
      0 < (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanSecondVertex f.1)) :
    Nonempty (LocalFanIntervalVertices M t f) := by
  let x₀ := relabelUnivSimplex (M.localFaceOldVertexEmbedding t) x
  let yG := relabelFaceSimplex M.fanOldVertexEmbedding
    (M.marking.globalFanFaceVertices f.1) y
  let y₀ := M.marking.fanRelabelSimplex f.1 yG
  let e := M.ambient.faceEdge f.1.1 f.1.2.1
  let q := M.mixedOldFaceMap (Sum.inl t) x
  let p₀ := M.marking.edgeIntervalFirst e f.1.2.2
  let p₁ := M.marking.edgeIntervalSecond e f.1.2.2
  let a₀ := M.marking.edgeParameterValue e p₀
  let a₁ := M.marking.edgeParameterValue e p₁
  let z₀ := M.marking.edgeParameterValue e q
  have hfanEq : M.marking.fanFaceMap f.1 y₀ = q := hxy.symm
  have hqOpen :
      q ∈ M.ambient.edgePath e ''
        {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1} := by
    rw [← hfanEq]
    exact M.marking.fanFaceMap_mem_edgePath_image_Ioo_of_center_zero_of_base_weights_pos
      f.1 y₀ hyCenter hyPos.1 hyPos.2
  have hqEdge : q ∈ M.ambient.faceCarrier e.1 := by
    rw [← hfanEq]
    exact M.marking.fanFaceMap_mem_baseEdge_of_center_eq_zero f.1 y₀ hyCenter
  have heSelected : e.1 ⊆ (C.parentFace t).1 :=
    C.edge_subset_face_of_openPoint e (C.parentFace t) q hqOpen
      (C.localMixedFaceMap_mem_parent t x)
  have hzInterval : z₀ ∈ Set.Ioo a₀ a₁ := by
    change M.marking.edgeParameterValue e q ∈
      Set.Ioo
        (M.marking.edgeParameterValue e (M.marking.fanFirstVertex f.1).1)
        (M.marking.edgeParameterValue e (M.marking.fanSecondVertex f.1).1)
    rw [← hfanEq]
    exact M.marking.edgeParameterValue_fanFaceMap_mem_Ioo_of_center_eq_zero
      f.1 y₀ hyCenter hyPos.1 hyPos.2
  have hzAverage :
      z₀ = ∑ v : {v // v ∈ t.1}, x₀ v * M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) :=
    C.localFace_edgeParameter_eq_sum t x₀ e hqEdge
  have hgap (v : {v // v ∈ t.1}) (hvPos : 0 < x₀ v) :
      ¬M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) ∈ Set.Ioo a₀ a₁ := by
    have hvEdge := C.positive_localVertex_mem_edge t x₀ e hqEdge v hvPos
    have hvMark : M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
        M.marking.edgeMarks e :=
      (M.marking.mem_edgeMarks_iff e _).mpr
        ⟨C.localVertexPoint_mem_marking ⟨v.1, ⟨t.1, t.2, v.2⟩⟩, hvEdge⟩
    exact M.marking.not_edgeMark_parameter_mem_Ioo e f.1.2.2 hvMark
  obtain ⟨⟨lo, hloPos, hlo⟩, ⟨hi, hhiPos, hhi⟩⟩ :=
    exists_positive_weight_on_both_sides_of_gap
      (weight := fun v : {v // v ∈ t.1} ↦ x₀ v)
      (value := fun v ↦ M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩))
      a₀ a₁ z₀ x₀.2.1 x₀.2.2 hzAverage hgap hzInterval
  have hloEdge := C.positive_localVertex_mem_edge t x₀ e hqEdge lo hloPos
  have hhiEdge := C.positive_localVertex_mem_edge t x₀ e hqEdge hi hhiPos
  have hp₀Mark : p₀ ∈ M.marking.edgeMarks e :=
    M.marking.edgeIntervalFirst_mem_edgeMarks e f.1.2.2
  have hp₁Mark : p₁ ∈ M.marking.edgeMarks e :=
    M.marking.edgeIntervalSecond_mem_edgeMarks e f.1.2.2
  have hp₀Edge := ((M.marking.mem_edgeMarks_iff e p₀).mp hp₀Mark).2
  have hp₁Edge := ((M.marking.mem_edgeMarks_iff e p₁).mp hp₁Mark).2
  obtain ⟨u₀, hu₀⟩ := C.edgeMark_lift t e heSelected p₀ hp₀Mark
  obtain ⟨u₁, hu₁⟩ := C.edgeMark_lift t e heSelected p₁ hp₁Mark
  have hlohi : M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨lo.1, ⟨t.1, t.2, lo.2⟩⟩) <
      M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨hi.1, ⟨t.1, t.2, hi.2⟩⟩) := by
    calc
      _ ≤ a₀ := hlo
      _ < a₁ := hzInterval.1.trans hzInterval.2
      _ ≤ _ := hhi
  have hp₀hi : M.marking.edgeParameterValue e p₀ ≤
      M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨hi.1, ⟨t.1, t.2, hi.2⟩⟩) :=
    le_trans (hzInterval.1.trans hzInterval.2).le hhi
  have hloP₁ : M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨lo.1, ⟨t.1, t.2, lo.2⟩⟩) ≤
      M.marking.edgeParameterValue e p₁ :=
    le_trans hlo (hzInterval.1.trans hzInterval.2).le
  obtain ⟨zAt, hzAt⟩ := C.exists_localFacePoint_eq_of_edgeParameter_between
    t e lo hi p₀ hloEdge hhiEdge hp₀Edge hlo hp₀hi hlohi
  obtain ⟨zBt, hzBt⟩ := C.exists_localFacePoint_eq_of_edgeParameter_between
    t e lo hi p₁ hloEdge hhiEdge hp₁Edge hloP₁ hhi hlohi
  have hu₀Face : u₀.1 ∈ t.1 :=
    C.localUsedVertex_mem_face_of_map_eq t zAt u₀ (hzAt.trans hu₀.symm)
  have hu₁Face : u₁.1 ∈ t.1 :=
    C.localUsedVertex_mem_face_of_map_eq t zBt u₁ (hzBt.trans hu₁.symm)
  exact ⟨u₀, u₁, hu₀Face, hu₁Face, hu₀, hu₁⟩

private theorem MixedLocalFanCertificate.localFanInterior_extendedCoordinates_eq
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {t : M.localComplex.Face} {f : M.OutsideFanFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}}
    (hxy : M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inr f) y)
    (hyCenter :
      (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanCenterVertex f.1) = 0)
    (hyPos :
      0 < (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanFirstVertex f.1) ∧
      0 < (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))
          (M.marking.fanSecondVertex f.1)) :
    extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y := by
  let yG := relabelFaceSimplex M.fanOldVertexEmbedding
    (M.marking.globalFanFaceVertices f.1) y
  let y₀ := M.marking.fanRelabelSimplex f.1 yG
  let e := M.ambient.faceEdge f.1.1 f.1.2.1
  let q := M.mixedOldFaceMap (Sum.inl t) x
  let p₀ := M.marking.edgeIntervalFirst e f.1.2.2
  let p₁ := M.marking.edgeIntervalSecond e f.1.2.2
  let a₀ := M.marking.edgeParameterValue e p₀
  let a₁ := M.marking.edgeParameterValue e p₁
  let z₀ := M.marking.edgeParameterValue e q
  obtain ⟨D⟩ := C.exists_localFanIntervalVertices M hxy hyCenter hyPos
  let v₀t : {v // v ∈ t.1} := ⟨D.first.1, D.first_mem⟩
  let v₁t : {v // v ∈ t.1} := ⟨D.second.1, D.second_mem⟩
  have hv₀Local : M.localFaceOldVertexEmbedding t v₀t =
      M.localOldVertexEmbedding D.first := Subtype.ext rfl
  have hv₁Local : M.localFaceOldVertexEmbedding t v₁t =
      M.localOldVertexEmbedding D.second := Subtype.ext rfl
  have hw₀LocalMem : M.localOldVertexEmbedding D.first ∈
      M.mixedOldFaceVertices (Sum.inl t) := by
    change M.localOldVertexEmbedding D.first ∈
      (Finset.univ : Finset {v // v ∈ t.1}).map (M.localFaceOldVertexEmbedding t)
    rw [← hv₀Local]
    exact mem_map_univ (M.localFaceOldVertexEmbedding t) v₀t
  have hw₁LocalMem : M.localOldVertexEmbedding D.second ∈
      M.mixedOldFaceVertices (Sum.inl t) := by
    change M.localOldVertexEmbedding D.second ∈
      (Finset.univ : Finset {v // v ∈ t.1}).map (M.localFaceOldVertexEmbedding t)
    rw [← hv₁Local]
    exact mem_map_univ (M.localFaceOldVertexEmbedding t) v₁t
  let w₀Local : {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)} :=
    ⟨M.localOldVertexEmbedding D.first, hw₀LocalMem⟩
  let w₁Local : {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)} :=
    ⟨M.localOldVertexEmbedding D.second, hw₁LocalMem⟩
  let gv₀ : M.marking.FanVertex :=
    M.marking.fanVertexEmbedding f.1 (M.marking.fanFirstVertex f.1)
  let gv₁ : M.marking.FanVertex :=
    M.marking.fanVertexEmbedding f.1 (M.marking.fanSecondVertex f.1)
  have hw₀Raw : M.localOldVertexEmbedding D.first = M.fanOldVertexEmbedding gv₀ :=
    Subtype.ext D.first_eq
  have hw₁Raw : M.localOldVertexEmbedding D.second = M.fanOldVertexEmbedding gv₁ :=
    Subtype.ext D.second_eq
  have hgv₀Mem : gv₀ ∈ M.marking.globalFanFaceVertices f.1 :=
    fanFirstVertexEmbedding_mem_globalFanFaceVertices M.marking f.1
  have hgv₁Mem : gv₁ ∈ M.marking.globalFanFaceVertices f.1 :=
    fanSecondVertexEmbedding_mem_globalFanFaceVertices M.marking f.1
  have hw₀FanMem : M.fanOldVertexEmbedding gv₀ ∈
      M.mixedOldFaceVertices (Sum.inr f) := by
    change M.fanOldVertexEmbedding gv₀ ∈
      (M.marking.globalFanFaceVertices f.1).map M.fanOldVertexEmbedding
    exact mem_finset_map M.fanOldVertexEmbedding _ hgv₀Mem
  have hw₁FanMem : M.fanOldVertexEmbedding gv₁ ∈
      M.mixedOldFaceVertices (Sum.inr f) := by
    change M.fanOldVertexEmbedding gv₁ ∈
      (M.marking.globalFanFaceVertices f.1).map M.fanOldVertexEmbedding
    exact mem_finset_map M.fanOldVertexEmbedding _ hgv₁Mem
  let w₀Fan : {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)} :=
    ⟨M.fanOldVertexEmbedding gv₀, hw₀FanMem⟩
  let w₁Fan : {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)} :=
    ⟨M.fanOldVertexEmbedding gv₁, hw₁FanMem⟩
  let β := y₀ (M.marking.fanSecondVertex f.1)
  let r : Set.Icc (0 : ℝ) 1 := ⟨β, y₀.2.1 _, stdSimplex.le_one y₀ _⟩
  let xLine := simplexLineMap (stdSimplex.vertex w₀Local) (stdSimplex.vertex w₁Local) r
  let yLine := simplexLineMap (stdSimplex.vertex w₀Fan) (stdSimplex.vertex w₁Fan) r
  have hlineCoords :
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) xLine =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) yLine :=
    extendFaceCoordinates_simplexLineMap_vertices_eq
      (M.mixedOldFaceVertices (Sum.inl t)) (M.mixedOldFaceVertices (Sum.inr f))
      w₀Local w₁Local w₀Fan w₁Fan hw₀Raw hw₁Raw r
  have hp₀Edge := M.marking.edgeIntervalFirst_mem_faceCarrier e f.1.2.2
  have hp₁Edge := M.marking.edgeIntervalSecond_mem_faceCarrier e f.1.2.2
  have hyLineVal : (M.mixedOldFaceMap (Sum.inr f) yLine).1 =
      AffineMap.lineMap p₀.1 p₁.1 β := by
    dsimp only [yLine]
    calc
      (M.mixedOldFaceMap (Sum.inr f)
          (simplexLineMap (stdSimplex.vertex w₀Fan) (stdSimplex.vertex w₁Fan) r)).1 =
          AffineMap.lineMap w₀Fan.1.1.1 w₁Fan.1.1.1 r.1 := by
        apply map_simplexLineMap_vertices
          (fun z ↦ (M.mixedOldFaceMap (Sum.inr f) z).1) (fun v ↦ v.1.1)
        · exact fun z w s ↦ C.mixedOldFaceMap_simplexLineMap (Sum.inr f) z w s
        · exact fun v ↦ congrArg Subtype.val (C.mixedOldFaceMap_vertex (Sum.inr f) v)
      _ = AffineMap.lineMap p₀.1 p₁.1 β := by rfl
  have hyLineEdge : M.mixedOldFaceMap (Sum.inr f) yLine ∈ M.ambient.faceCarrier e.1 :=
    mem_faceCarrier_of_val_eq_lineMap e.1 p₀ p₁ _ β hp₀Edge hp₁Edge hyLineVal
  have hfanEq : M.marking.fanFaceMap f.1 y₀ = q := hxy.symm
  have hqEdge : q ∈ M.ambient.faceCarrier e.1 := by
    rw [← hfanEq]
    exact M.marking.fanFaceMap_mem_baseEdge_of_center_eq_zero f.1 y₀ hyCenter
  have hyLineParameter : M.marking.edgeParameterValue e
        (M.mixedOldFaceMap (Sum.inr f) yLine) = (1 - β) * a₀ + β * a₁ :=
    edgeParameterValue_eq_lineMap M.marking e p₀ p₁ _ β hp₀Edge hp₁Edge hyLineVal
  have hqParameter : z₀ = y₀ (M.marking.fanFirstVertex f.1) * a₀ + β * a₁ := by
    change M.marking.edgeParameterValue e q =
      y₀ (M.marking.fanFirstVertex f.1) *
          M.marking.edgeParameterValue e (M.marking.fanFirstVertex f.1).1 +
        y₀ (M.marking.fanSecondVertex f.1) *
          M.marking.edgeParameterValue e (M.marking.fanSecondVertex f.1).1
    rw [← hfanEq]
    exact M.marking.edgeParameterValue_fanFaceMap_of_center_eq_zero f.1 y₀ hyCenter
  have hbaseSum := M.marking.fanBaseWeights_sum_of_center_eq_zero f.1 y₀ hyCenter
  have hfirstCoeff : 1 - β = y₀ (M.marking.fanFirstVertex f.1) := by
    dsimp only [β]
    linarith
  have hyLineEq : M.mixedOldFaceMap (Sum.inr f) yLine = q := by
    apply M.marking.edgeParameterValue_injOn e hyLineEdge hqEdge
    calc
      _ = (1 - β) * a₀ + β * a₁ := hyLineParameter
      _ = y₀ (M.marking.fanFirstVertex f.1) * a₀ + β * a₁ := by rw [hfirstCoeff]
      _ = z₀ := hqParameter.symm
      _ = M.marking.edgeParameterValue e q := rfl
  exact coordinates_eq_of_comparison
    (M.mixedOldFaceMap (Sum.inl t)) (M.mixedOldFaceMap (Sum.inr f))
    (extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)))
    (extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)))
    (fun {_ _} h ↦ C.localMixedFaceMap_eq_iff.mp h)
    (fun {_ _} h ↦ C.fanMixedFaceMap_eq_iff.mp h)
    (fun {z w} h ↦ C.mixedOldFaceMap_eq_of_extendedCoordinates
      (f := Sum.inl t) (g := Sum.inr f) (x := z) (y := w) h)
    hxy hlineCoords (hyLineEq.trans hxy)

private theorem MixedLocalFanCertificate.localFanEndpoint_extendedCoordinates_eq
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {t : M.localComplex.Face} {f : M.OutsideFanFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}}
    (hxy : M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inr f) y)
    (v : {p // p ∈ M.marking.fanFaceVertices f.1})
    (hvMark : v.1 ∈ M.marking.points)
    (hyv : (M.marking.fanFaceMap f.1
      (M.marking.fanRelabelSimplex f.1
        (relabelFaceSimplex M.fanOldVertexEmbedding
          (M.marking.globalFanFaceVertices f.1) y))).1 = v.1.1) :
    extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y := by
  have hyEndpoint : M.mixedOldFaceMap (Sum.inr f) y = v.1 := by
    apply Subtype.ext
    exact hyv
  have hvSelected : v.1 ∈ M.ambient.faceCarrier (C.parentFace t).1 := by
    rw [← hyEndpoint, ← hxy]
    exact C.localMixedFaceMap_mem_parent t x
  obtain ⟨u, hu⟩ := C.markingPoint_lift t v.1 hvMark hvSelected
  have hxLocal :
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
        Pi.single (M.localOldVertexEmbedding u) 1 :=
    C.mixedLocalExtended_eq_single_of_map_eq_localVertex
      t x u (hxy.trans (hyEndpoint.trans hu.symm))
  have hyFan :
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y =
        Pi.single
          (M.fanOldVertexEmbedding (M.marking.fanVertexEmbedding f.1 v)) 1 :=
    C.mixedFanExtended_eq_single_of_map_eq_fanVertex f y v hyEndpoint
  have hvertex :
      M.localOldVertexEmbedding u =
        M.fanOldVertexEmbedding (M.marking.fanVertexEmbedding f.1 v) := by
    apply Subtype.ext
    exact hu
  rw [hxLocal, hyFan, hvertex]

-- The raw straightening witness is kept behind one projection boundary so later phases do not
-- inherit the full dependent telescope produced by the existential straightening statement.
private theorem MixedLocalFanCertificate.localFanMixedFaceMap_eq_iff
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {t : M.localComplex.Face} {f : M.OutsideFanFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}} :
    M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inr f) y ↔
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y := by
  let mixedFaceSimplexLineMap
      (g : M.MixedOldFace)
      (z w : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices g})
      (r : Set.Icc (0 : ℝ) 1) :
      stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices g} :=
    simplexLineMap z w r
  let x₀ := relabelUnivSimplex
    (M.localFaceOldVertexEmbedding t) x
  let yG := relabelFaceSimplex M.fanOldVertexEmbedding
    (M.marking.globalFanFaceVertices f.1) y
  let y₀ := M.marking.fanRelabelSimplex f.1 yG
  constructor
  · intro hxy
    have hyParent :
        M.marking.fanFaceMap f.1 y₀ ∈
          M.ambient.faceCarrier (C.parentFace t).1 := by
      have hlocal := C.localMixedFaceMap_mem_parent t x
      have hfan :
          M.marking.fanFaceMap f.1 y₀ =
            M.mixedOldFaceMap (Sum.inr f) y := rfl
      rw [hfan, ← hxy]
      exact hlocal
    have hparentNe : f.1.1 ≠ C.parentFace t :=
      C.outside_parent_ne f t
    have hyCenter :
        y₀ (M.marking.fanCenterVertex f.1) = 0 :=
      M.marking.fanCenterWeight_eq_zero_of_mem_faceCarrier_of_parent_ne
        f.1 (C.parentFace t) hparentNe y₀ hyParent
    by_cases hyPos :
        0 < y₀ (M.marking.fanFirstVertex f.1) ∧
          0 < y₀ (M.marking.fanSecondVertex f.1)
    · exact C.localFanInterior_extendedCoordinates_eq M hxy hyCenter hyPos
    · let endpointCoordinates := C.localFanEndpoint_extendedCoordinates_eq M hxy
      rcases
          M.marking.fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
            f.1 y₀ hyCenter hyPos with hyFirst | hySecond
      · exact endpointCoordinates
          (M.marking.fanFirstVertex f.1)
          (((M.marking.mem_edgeMarks_iff
            (M.ambient.faceEdge f.1.1 f.1.2.1) _).mp
              (M.marking.edgeIntervalFirst_mem_edgeMarks
                (M.ambient.faceEdge f.1.1 f.1.2.1)
                f.1.2.2)).1)
          hyFirst.1
      · exact endpointCoordinates
          (M.marking.fanSecondVertex f.1)
          (((M.marking.mem_edgeMarks_iff
            (M.ambient.faceEdge f.1.1 f.1.2.1) _).mp
              (M.marking.edgeIntervalSecond_mem_edgeMarks
                (M.ambient.faceEdge f.1.1 f.1.2.1)
                f.1.2.2)).1)
          hySecond.1
  · intro hcoords
    exact C.mixedOldFaceMap_eq_of_extendedCoordinates
      (f := Sum.inl t) (g := Sum.inr f)
      (x := x) (y := y) hcoords

private theorem MixedLocalFanCertificate.mixedOldFaceMap_eq_iff
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {f g : M.MixedOldFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices g}} :
    M.mixedOldFaceMap f x = M.mixedOldFaceMap g y ↔
      extendFaceCoordinates (M.mixedOldFaceVertices f) x =
        extendFaceCoordinates (M.mixedOldFaceVertices g) y := by
  rcases f with t | f <;> rcases g with u | g
  · exact C.localMixedFaceMap_eq_iff
  · exact C.localFanMixedFaceMap_eq_iff
  · constructor
    · intro hxy
      exact C.localFanMixedFaceMap_eq_iff.mp hxy.symm |>.symm
    · intro hcoords
      exact (C.localFanMixedFaceMap_eq_iff.mpr hcoords.symm).symm
  · exact C.fanMixedFaceMap_eq_iff

private noncomputable abbrev MixedLocalFanData.usedOldVertices (M : MixedLocalFanData) :
    Finset M.OldVertex :=
  (Finset.univ : Finset M.MixedOldFace).biUnion M.mixedOldFaceVertices

private abbrev MixedLocalFanData.UsedOldVertex (M : MixedLocalFanData) :=
  {v : M.OldVertex // v ∈ M.usedOldVertices}

private noncomputable abbrev MixedLocalFanData.mixedFaceUsedEmbedding
    (M : MixedLocalFanData) (f : M.MixedOldFace) :
    {v // v ∈ M.mixedOldFaceVertices f} ↪ M.UsedOldVertex :=
  { toFun := fun v ↦ ⟨v.1, Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ f, v.2⟩⟩
    inj' := fun _ _ h ↦ Subtype.ext
      (congrArg (fun z : M.UsedOldVertex ↦ z.1) h) }

private noncomputable abbrev MixedLocalFanData.mixedUsedFaceVertices
    (M : MixedLocalFanData) (f : M.MixedOldFace) : Finset M.UsedOldVertex :=
  (Finset.univ : Finset {v // v ∈ M.mixedOldFaceVertices f}).map
    (M.mixedFaceUsedEmbedding f)

private noncomputable abbrev MixedLocalFanData.mixedUsedFaceMap
    (M : MixedLocalFanData) (f : M.MixedOldFace) :
    stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices f} → M.ambient.realization :=
  fun x ↦ M.mixedOldFaceMap f
    (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x)

private theorem MixedLocalFanCertificate.mixedUsedFaceVertices_card
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) (f : M.MixedOldFace) :
    (M.mixedUsedFaceVertices f).card = 3 := by
  change ((Finset.univ : Finset {v // v ∈ M.mixedOldFaceVertices f}).map
    (M.mixedFaceUsedEmbedding f)).card = 3
  rw [Finset.card_map, Finset.card_univ, Fintype.card_coe,
    C.mixedOldFaceVertices_card]

private theorem MixedLocalFanCertificate.continuous_mixedUsedFaceMap
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) (f : M.MixedOldFace) :
    Continuous (M.mixedUsedFaceMap f) :=
  (C.continuous_mixedOldFaceMap f).comp
    (stdSimplex.continuous_map (univMapSubtypeEquiv (M.mixedFaceUsedEmbedding f)))

private theorem MixedLocalFanData.mixedUsedExtended_apply
    (M : MixedLocalFanData) (f : M.MixedOldFace)
    (x : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices f})
    (p : M.UsedOldVertex) :
    extendFaceCoordinates (M.mixedUsedFaceVertices f) x p =
      extendFaceCoordinates (M.mixedOldFaceVertices f)
        (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) p.1 := by
  by_cases hp : p.1 ∈ M.mixedOldFaceVertices f
  · let v : {v // v ∈ M.mixedOldFaceVertices f} := ⟨p.1, hp⟩
    have hemb : M.mixedFaceUsedEmbedding f v = p := Subtype.ext rfl
    have hmem : M.mixedFaceUsedEmbedding f v ∈ M.mixedUsedFaceVertices f :=
      mem_map_univ (M.mixedFaceUsedEmbedding f) v
    have hpMem : p ∈ M.mixedUsedFaceVertices f := hemb ▸ hmem
    rw [extendFaceCoordinates_of_mem _ _ hpMem,
      extendFaceCoordinates_of_mem _ _ hp]
    have hleft :
        (⟨p, hpMem⟩ : {q // q ∈ M.mixedUsedFaceVertices f}) =
          ⟨M.mixedFaceUsedEmbedding f v, hmem⟩ := Subtype.ext hemb.symm
    have hright :
        (⟨p.1, hp⟩ : {q // q ∈ M.mixedOldFaceVertices f}) = v :=
      Subtype.ext rfl
    rw [hleft, hright]
    have hmapMem :
        M.mixedFaceUsedEmbedding f v ∈
          (Finset.univ : Finset {q // q ∈ M.mixedOldFaceVertices f}).map
            (M.mixedFaceUsedEmbedding f) :=
      mem_map_univ (M.mixedFaceUsedEmbedding f) v
    have hrel := (relabelUnivSimplex_apply (M.mixedFaceUsedEmbedding f) x v).symm
    rw [extendFaceCoordinates_of_mem _ _ hmapMem] at hrel
    exact hrel
  · have hpUsed : p ∉ M.mixedUsedFaceVertices f := by
      intro hpUsed
      obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hpUsed
      exact hp (congrArg (fun z : M.UsedOldVertex ↦ z.1) hv ▸ v.2)
    rw [extendFaceCoordinates_of_notMem _ _ hpUsed,
      extendFaceCoordinates_of_notMem _ _ hp]

private theorem MixedLocalFanCertificate.mixedUsedFaceMap_val
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (f : M.MixedOldFace)
    (x : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices f}) :
    (M.mixedUsedFaceMap f x).1 = fun k ↦ ∑ v : M.UsedOldVertex,
      extendFaceCoordinates (M.mixedUsedFaceVertices f) x v * v.1.1.1 k := by
  rw [show M.mixedUsedFaceMap f x = M.mixedOldFaceMap f
      (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) by rfl,
    C.mixedOldFaceMap_val]
  funext k
  have hused := sum_extendFaceCoordinates_relabelUnivSimplex
    (M.mixedFaceUsedEmbedding f) x (fun v : M.UsedOldVertex ↦ v.1.1.1 k)
  have hold :
      (∑ v : M.OldVertex,
          extendFaceCoordinates (M.mixedOldFaceVertices f)
              (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) v * v.1.1 k) =
        ∑ v ∈ M.mixedOldFaceVertices f,
          extendFaceCoordinates (M.mixedOldFaceVertices f)
              (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) v * v.1.1 k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    rw [extendFaceCoordinates_of_notMem _ _ hv, zero_mul]
  rw [hused, hold,
    ← sum_attach_mul_eq_sum_extendFaceCoordinates
      (M.mixedOldFaceVertices f)
      (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x)
      (fun v : M.OldVertex ↦ v.1.1 k)]
  rfl

private theorem MixedLocalFanCertificate.mixedUsedFaceMap_eq_iff
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    {f g : M.MixedOldFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices f}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices g}} :
    M.mixedUsedFaceMap f x = M.mixedUsedFaceMap g y ↔
      extendFaceCoordinates (M.mixedUsedFaceVertices f) x =
        extendFaceCoordinates (M.mixedUsedFaceVertices g) y := by
  rw [show M.mixedUsedFaceMap f x = M.mixedOldFaceMap f
      (relabelUnivSimplex (M.mixedFaceUsedEmbedding f) x) from rfl,
    show M.mixedUsedFaceMap g y = M.mixedOldFaceMap g
      (relabelUnivSimplex (M.mixedFaceUsedEmbedding g) y) from rfl,
    C.mixedOldFaceMap_eq_iff]
  constructor
  · intro hcoords
    funext p
    rw [M.mixedUsedExtended_apply f x p, M.mixedUsedExtended_apply g y p,
      congrFun hcoords p.1]
  · intro hcoords
    funext p
    by_cases hp : p ∈ M.usedOldVertices
    · let q : M.UsedOldVertex := ⟨p, hp⟩
      have hq := congrFun hcoords q
      rw [M.mixedUsedExtended_apply f x q,
        M.mixedUsedExtended_apply g y q] at hq
      exact hq
    · have hpf : p ∉ M.mixedOldFaceVertices f := fun hpf ↦
        hp (Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ f, hpf⟩)
      have hpg : p ∉ M.mixedOldFaceVertices g := fun hpg ↦
        hp (Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hpg⟩)
      rw [extendFaceCoordinates_of_notMem _ _ hpf,
        extendFaceCoordinates_of_notMem _ _ hpg]

private noncomputable abbrev MixedLocalFanCertificate.mixedOldComplex
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) :
    LocallyFiniteTriangleComplex M.ambient.realization where
  Vertex := M.UsedOldVertex
  Face := M.MixedOldFace
  faceVertices := M.mixedUsedFaceVertices
  faceVertices_card := C.mixedUsedFaceVertices_card
  vertex_used := by
    intro v
    obtain ⟨f, -, hvf⟩ := Finset.mem_biUnion.mp v.2
    have hvMem :
        M.mixedFaceUsedEmbedding f ⟨v.1, hvf⟩ ∈ M.mixedUsedFaceVertices f :=
      mem_map_univ (M.mixedFaceUsedEmbedding f) ⟨v.1, hvf⟩
    refine ⟨f, ?_⟩
    convert hvMem using 1
    exact Subtype.ext rfl
  faceMap := M.mixedUsedFaceMap
  faceMap_continuous := C.continuous_mixedUsedFaceMap
  faceMap_eq_iff := C.mixedUsedFaceMap_eq_iff
  locallyFinite := locallyFinite_of_finite _

/-- The subdivision assembled from the local old faces and the complementary marked fan.
Keeping this construction independent of the chart weld prevents the final weld proof from
re-elaborating the full mixed-face coordinate argument. -/
private noncomputable def MixedLocalFanCertificate.mixedSubdivision
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (hsupport : (C.mixedOldComplex M).support = Set.univ) : M.ambient.Subdivision := by
  let K := C.mixedOldComplex M
  let homeo : K.compactIntrinsic.realization ≃ₜ M.ambient.realization := by
    let e : K.compactIntrinsic.realization ≃ M.ambient.realization :=
      Equiv.ofBijective K.compactEval
        ⟨K.injective_compactEval, by
          intro y
          have hy : y ∈ K.support := by
            rw [hsupport]
            exact Set.mem_univ y
          rw [← K.range_compactEval] at hy
          exact hy⟩
    exact Continuous.homeoOfEquivCompactToT2 (f := e) K.continuous_compactEval
  let barycentricAffine :
      (M.UsedOldVertex → ℝ) →ᵃ[ℝ] (M.ambient.Vertex → ℝ) :=
    (∑ v : M.UsedOldVertex,
      (LinearMap.proj v).smulRight
        (v.1.1.1 : M.ambient.Vertex → ℝ)).toAffineMap
  have barycentricAffine_apply (z : M.UsedOldVertex → ℝ) :
      barycentricAffine z = fun k ↦ ∑ v : M.UsedOldVertex, z v * v.1.1.1 k := by
    funext k
    simp [barycentricAffine, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  letI : Fintype K.Vertex := K.compactIntrinsic.vertexFintype
  exact
    { refined := K.compactIntrinsic
      homeo := homeo
      affineOnFace := by
        intro s hs
        change s ∈ K.compactIntrinsic.faces at hs
        rw [K.compactIntrinsic_faces] at hs
        obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hs
        refine ⟨barycentricAffine, ?_⟩
        intro x hx
        have heval := K.compactEval_eq_faceMap f x hx
        have hhomeo :
            (homeo x).1 = (K.compactEval x).1 :=
          congrArg Subtype.val (show homeo x = K.compactEval x by rfl)
        rw [hhomeo, heval]
        change
          (M.mixedUsedFaceMap f
              (K.restrictToFace (M.mixedUsedFaceVertices f) ⟨x.1, x.2.1⟩ hx)).1 =
            barycentricAffine x.1
        rw [C.mixedUsedFaceMap_val]
        funext k
        rw [congrFun (barycentricAffine_apply x.1) k]
        apply Finset.sum_congr rfl
        intro v _
        apply congrArg (· * v.1.1.1 k)
        by_cases hv : v ∈ M.mixedUsedFaceVertices f
        · rw [extendFaceCoordinates_of_mem _ _ hv]
          rfl
        · simp [extendFaceCoordinates, hv, hx v hv]
      subordinate := by
        intro s hs
        change s ∈ K.compactIntrinsic.faces at hs
        rw [K.compactIntrinsic_faces] at hs
        obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hs
        rcases f with t | f
        · refine ⟨(C.parentFace t).1, (C.parentFace t).2, ?_⟩
          intro x hx
          have heval := K.compactEval_eq_faceMap (Sum.inl t) x hx
          change homeo x ∈ M.ambient.faceCarrier (C.parentFace t).1
          rw [show homeo x = K.compactEval x by rfl, heval]
          change
            M.mixedUsedFaceMap (Sum.inl t)
                (K.restrictToFace (M.mixedUsedFaceVertices (Sum.inl t))
                  ⟨x.1, x.2.1⟩ hx) ∈
              M.ambient.faceCarrier (C.parentFace t).1
          exact C.localMixedFaceMap_mem_parent t _
        · refine ⟨f.1.1.1, f.1.1.2, ?_⟩
          intro x hx
          have heval := K.compactEval_eq_faceMap (Sum.inr f) x hx
          change homeo x ∈ M.ambient.faceCarrier f.1.1.1
          rw [show homeo x = K.compactEval x by rfl, heval]
          change
            M.mixedUsedFaceMap (Sum.inr f)
                (K.restrictToFace (M.mixedUsedFaceVertices (Sum.inr f))
                  ⟨x.1, x.2.1⟩ hx) ∈
              M.ambient.faceCarrier f.1.1.1
          exact M.marking.globalFanFaceMap_mem_faceCarrier f.1 _ }

private theorem MixedLocalFanCertificate.mixedSubdivision_homeo_apply
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (hsupport : (C.mixedOldComplex M).support = Set.univ)
    (x : (C.mixedOldComplex M).compactIntrinsic.realization) :
    (C.mixedSubdivision M hsupport).homeo x = (C.mixedOldComplex M).compactEval x := by
  rfl

private theorem MixedLocalFanCertificate.mixedSubdivision_refined
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (hsupport : (C.mixedOldComplex M).support = Set.univ) :
    (C.mixedSubdivision M hsupport).refined = (C.mixedOldComplex M).compactIntrinsic := by
  rfl

private noncomputable abbrev MixedLocalFanData.localUsedOldEmbedding
    (M : MixedLocalFanData) : M.localComplex.UsedVertex ↪ M.UsedOldVertex :=
  { toFun := fun u ↦ ⟨M.localOldVertexEmbedding u, by
      obtain ⟨t, ht, hut⟩ := u.2
      apply Finset.mem_biUnion.mpr
      refine ⟨Sum.inl (⟨t, ht⟩ : M.localComplex.Face), Finset.mem_univ _, ?_⟩
      apply Finset.mem_map.mpr
      refine ⟨⟨u.1, hut⟩, Finset.mem_univ _, ?_⟩
      exact Subtype.ext rfl⟩
    inj' := fun _ _ h ↦ M.localOldVertexEmbedding.injective
      (congrArg (fun z : M.UsedOldVertex ↦ z.1) h) }

private abbrev MixedLocalFanData.localUsedVertexEmbedding
    (M : MixedLocalFanData) : M.localComplex.UsedVertex ↪ M.localComplex.Vertex :=
  ⟨Subtype.val, Subtype.val_injective⟩

private noncomputable abbrev MixedLocalFanData.CommonVertex (M : MixedLocalFanData) :=
  AmalgamatedVertex M.localUsedOldEmbedding M.localComplex.Vertex

private noncomputable abbrev MixedLocalFanData.oldToCommon (M : MixedLocalFanData) :
    M.UsedOldVertex ↪ M.CommonVertex :=
  oldToAmalgamated M.localUsedOldEmbedding M.localUsedVertexEmbedding

private noncomputable abbrev MixedLocalFanData.targetToCommon (M : MixedLocalFanData) :
    M.localComplex.Vertex ↪ M.CommonVertex :=
  targetToAmalgamated M.localUsedOldEmbedding

private theorem MixedLocalFanData.oldToCommon_local (M : MixedLocalFanData)
    (u : M.localComplex.UsedVertex) :
    M.oldToCommon (M.localUsedOldEmbedding u) = M.targetToCommon u.1 :=
  oldToAmalgamated_local M.localUsedOldEmbedding M.localUsedVertexEmbedding u

private theorem MixedLocalFanData.exists_local_of_oldToCommon_eq_target
    (M : MixedLocalFanData) (v : M.UsedOldVertex) (a : M.localComplex.Vertex)
    (h : M.oldToCommon v = M.targetToCommon a) :
    ∃ u : M.localComplex.UsedVertex, M.localUsedOldEmbedding u = v := by
  by_contra hlocal
  have hleft : M.oldToCommon v = Sum.inl ⟨v, hlocal⟩ := by
    change oldToAmalgamatedFun M.localUsedOldEmbedding M.localUsedVertexEmbedding v =
      Sum.inl ⟨v, hlocal⟩
    simp only [oldToAmalgamatedFun, dite_eq_right hlocal]
  rw [hleft] at h
  have h' :
      (Sum.inl (⟨v, hlocal⟩ : OldVertexComplement M.localUsedOldEmbedding) :
        M.CommonVertex) = Sum.inr a := h
  exact Sum.inl_ne_inr h'

private theorem MixedLocalFanData.oldToCommon_extra
    (M : MixedLocalFanData) (v : OldVertexComplement M.localUsedOldEmbedding) :
    M.oldToCommon v.1 = Sum.inl v := by
  change oldToAmalgamatedFun M.localUsedOldEmbedding M.localUsedVertexEmbedding v.1 =
    Sum.inl v
  simp only [oldToAmalgamatedFun, dite_eq_right v.2]

private noncomputable abbrev MixedLocalFanCertificate.compactVertexEquiv
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) :
    C.mixedOldComplex.compactIntrinsic.Vertex ≃ M.UsedOldVertex :=
  Equiv.refl _

private noncomputable abbrev MixedLocalFanCertificate.oldCompactToCommon
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M) :
    C.mixedOldComplex.compactIntrinsic.Vertex ↪ M.CommonVertex :=
  { toFun := fun v ↦ M.oldToCommon
      (MixedLocalFanCertificate.compactVertexEquiv M C v)
    inj' := fun _ _ h ↦
      (MixedLocalFanCertificate.compactVertexEquiv M C).injective
        (M.oldToCommon.injective h) }

private theorem MixedLocalFanData.localMixedUsedVertex_isLocal
    (M : MixedLocalFanData) (t : M.localComplex.Face) (v : M.UsedOldVertex)
    (hv : v ∈ M.mixedUsedFaceVertices (Sum.inl t)) :
    ∃ u : M.localComplex.UsedVertex, M.localUsedOldEmbedding u = v := by
  change v ∈
    (Finset.univ : Finset {w // w ∈ M.mixedOldFaceVertices (Sum.inl t)}).map
      (M.mixedFaceUsedEmbedding (Sum.inl t)) at hv
  obtain ⟨w, -, hwv⟩ := Finset.mem_map.mp hv
  have hwOld : w.1 ∈ M.mixedOldFaceVertices (Sum.inl t) := w.2
  change w.1 ∈ (Finset.univ : Finset {a // a ∈ t.1}).map
    (M.localFaceOldVertexEmbedding t) at hwOld
  obtain ⟨a, -, haw⟩ := Finset.mem_map.mp hwOld
  let u : M.localComplex.UsedVertex := ⟨a.1, t.1, t.2, a.2⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  calc
    (M.localUsedOldEmbedding u).1 = M.localFaceOldVertexEmbedding t a := rfl
    _ = w.1 := haw
    _ = v.1 := congrArg Subtype.val hwv

private noncomputable def MixedLocalFanCertificate.hasLocalCommonCoordinates
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (x : C.mixedOldComplex.compactIntrinsic.realization)
    (z : M.localComplex.realization) : Prop := by
  classical
  letI : Fintype M.UsedOldVertex :=
    C.mixedOldComplex.compactIntrinsic.vertexFintype
  exact
    (pushGeometricRealization C.oldCompactToCommon
        C.mixedOldComplex.compactIntrinsic.faces x).1 =
      (pushGeometricRealization M.targetToCommon M.localComplex.faces z).1

private theorem MixedLocalFanCertificate.hasLocalCommonCoordinates_iff
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (x : C.mixedOldComplex.compactIntrinsic.realization)
    (z : M.localComplex.realization) :
    C.hasLocalCommonCoordinates M x z ↔
      (pushGeometricRealization C.oldCompactToCommon
          C.mixedOldComplex.compactIntrinsic.faces x).1 =
        (pushGeometricRealization M.targetToCommon M.localComplex.faces z).1 := by
  rfl

/-- A local realization lifts canonically to the compact mixed complex, with the same coordinates
after amalgamating the local vertices. -/
private theorem MixedLocalFanCertificate.exists_oldPoint_of_local
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (localEval : M.localComplex.realization → M.ambient.realization)
    (hlocalFaceMap : ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ t.1}),
      M.localFaceMap t x = localEval (M.localComplex.faceStandardMap t x))
    (z : M.localComplex.realization) :
    ∃ x : C.mixedOldComplex.compactIntrinsic.realization,
      C.mixedOldComplex.compactEval x = localEval z ∧
      C.hasLocalCommonCoordinates M x z := by
  classical
  let : Fintype M.UsedOldVertex :=
    C.mixedOldComplex.compactIntrinsic.vertexFintype
  obtain ⟨t, ht, hzt⟩ := z.2.2
  let tf : M.localComplex.Face := ⟨t, ht⟩
  let x₀ : stdSimplex ℝ {v // v ∈ tf.1} :=
    M.localComplex.restrictToFaceSimplex tf z hzt
  have hx₀ : M.localComplex.faceStandardMap tf x₀ = z :=
    M.localComplex.faceStandardMap_restrictToFaceSimplex tf z hzt
  have hExt₀ : extendFaceCoordinates tf.1 x₀ = z.1 := by
    rw [← M.localComplex.faceStandardMap_val tf x₀, hx₀]
  obtain ⟨x₁, hx₁⟩ :=
    relabelUnivSimplex_surjective (M.localFaceOldVertexEmbedding tf) x₀
  obtain ⟨x₂, hx₂⟩ :=
    relabelUnivSimplex_surjective (M.mixedFaceUsedEmbedding (Sum.inl tf)) x₁
  have hface : M.mixedUsedFaceVertices (Sum.inl tf) ∈
      C.mixedOldComplex.compactIntrinsic.faces :=
    C.mixedOldComplex.compactIntrinsic_face_mem (Sum.inl tf : M.MixedOldFace)
  let cf : C.mixedOldComplex.compactIntrinsic.Face :=
    ⟨M.mixedUsedFaceVertices (Sum.inl tf), hface⟩
  let x : C.mixedOldComplex.compactIntrinsic.realization :=
    C.mixedOldComplex.compactIntrinsic.faceStandardMap cf x₂
  have hxVal : x.1 =
      extendFaceCoordinates (M.mixedUsedFaceVertices (Sum.inl tf)) x₂ :=
    C.mixedOldComplex.compactIntrinsic.faceStandardMap_val cf x₂
  have hxSupp : ∀ v ∉ M.mixedUsedFaceVertices (Sum.inl tf), x.1 v = 0 := by
    intro v hv
    rw [hxVal]
    exact extendFaceCoordinates_of_notMem _ _ hv
  refine ⟨x, ?_, ?_⟩
  · rw [C.mixedOldComplex.compactEval_eq_faceMap (Sum.inl tf) x hxSupp]
    calc
      M.mixedUsedFaceMap (Sum.inl tf)
          (C.mixedOldComplex.restrictToFace
            (M.mixedUsedFaceVertices (Sum.inl tf)) ⟨x.1, x.2.1⟩ hxSupp) =
          M.mixedUsedFaceMap (Sum.inl tf) x₂ := by
        exact (C.mixedUsedFaceMap_eq_iff.mpr (by
          rw [C.mixedOldComplex.extendFaceCoordinates_restrictToFace]
          exact C.mixedOldComplex.compactIntrinsic.faceStandardMap_val cf x₂))
      _ = M.localFaceMap tf
          (relabelUnivSimplex (M.localFaceOldVertexEmbedding tf)
            (relabelUnivSimplex (M.mixedFaceUsedEmbedding (Sum.inl tf)) x₂)) := rfl
      _ = M.localFaceMap tf x₀ := by rw [hx₂, hx₁]
      _ = localEval (M.localComplex.faceStandardMap tf x₀) :=
        hlocalFaceMap tf x₀
      _ = localEval z := congrArg localEval hx₀
  · unfold MixedLocalFanCertificate.hasLocalCommonCoordinates
    change
      (pushGeometricRealization
          (MixedLocalFanCertificate.oldCompactToCommon M C)
          C.mixedOldComplex.compactIntrinsic.faces x).1 =
        (pushGeometricRealization M.targetToCommon M.localComplex.faces z).1
    funext b
    cases b with
    | inl v =>
        let vc : C.mixedOldComplex.compactIntrinsic.Vertex :=
          (MixedLocalFanCertificate.compactVertexEquiv M C).symm v.1
        have hcompact :
            MixedLocalFanCertificate.oldCompactToCommon M C vc = Sum.inl v := by
          change M.oldToCommon ((MixedLocalFanCertificate.compactVertexEquiv M C)
            ((MixedLocalFanCertificate.compactVertexEquiv M C).symm v.1)) = Sum.inl v
          rw [(MixedLocalFanCertificate.compactVertexEquiv M C).apply_symm_apply]
          exact M.oldToCommon_extra v
        have hvNot : v.1 ∉ M.mixedUsedFaceVertices (Sum.inl tf) := by
          intro hv
          exact v.2 (M.localMixedUsedVertex_isLocal tf v.1 hv)
        calc
          (pushGeometricRealization
              (MixedLocalFanCertificate.oldCompactToCommon M C)
              C.mixedOldComplex.compactIntrinsic.faces x).1 (Sum.inl v) =
              (pushGeometricRealization
                (MixedLocalFanCertificate.oldCompactToCommon M C)
                C.mixedOldComplex.compactIntrinsic.faces x).1
                  (MixedLocalFanCertificate.oldCompactToCommon M C vc) := by
            rw [hcompact]
          _ = x.1 vc := pushGeometricRealization_apply_embedding
            (MixedLocalFanCertificate.oldCompactToCommon M C)
            C.mixedOldComplex.compactIntrinsic.faces x vc
          _ = 0 := by
            change x.1 v.1 = 0
            rw [hxVal, extendFaceCoordinates_of_notMem _ _ hvNot]
          _ = (pushGeometricRealization M.targetToCommon
              M.localComplex.faces z).1 (Sum.inl v) := by
            symm
            apply pushGeometricRealization_apply_of_notMem_range
            rintro ⟨a, ha⟩
            have hcontra : (Sum.inr a : M.CommonVertex) = Sum.inl v := ha
            simp at hcontra
    | inr a =>
        have htarget :
            (pushGeometricRealization M.targetToCommon
                M.localComplex.faces z).1 (Sum.inr a) = z.1 a := by
          change (pushGeometricRealization M.targetToCommon
            M.localComplex.faces z).1 (M.targetToCommon a) = z.1 a
          exact pushGeometricRealization_apply_embedding
            M.targetToCommon M.localComplex.faces z a
        refine Eq.trans ?_ htarget.symm
        by_cases haUsed : ∃ s ∈ M.localComplex.faces, a ∈ s
        · let u : M.localComplex.UsedVertex := ⟨a, haUsed⟩
          let vc : C.mixedOldComplex.compactIntrinsic.Vertex :=
            (MixedLocalFanCertificate.compactVertexEquiv M C).symm
              (M.localUsedOldEmbedding u)
          have hcommon :
              MixedLocalFanCertificate.oldCompactToCommon M C vc = Sum.inr a :=
            M.oldToCommon_local u
          calc
            (pushGeometricRealization
                (MixedLocalFanCertificate.oldCompactToCommon M C)
                C.mixedOldComplex.compactIntrinsic.faces x).1 (Sum.inr a) =
                (pushGeometricRealization
                  (MixedLocalFanCertificate.oldCompactToCommon M C)
                  C.mixedOldComplex.compactIntrinsic.faces x).1
                    (MixedLocalFanCertificate.oldCompactToCommon M C vc) := by
              rw [hcommon]
            _ = x.1 vc := pushGeometricRealization_apply_embedding
              (MixedLocalFanCertificate.oldCompactToCommon M C)
              C.mixedOldComplex.compactIntrinsic.faces x vc
            _ = extendFaceCoordinates (M.mixedUsedFaceVertices (Sum.inl tf)) x₂
                (M.localUsedOldEmbedding u) :=
              congrFun hxVal (M.localUsedOldEmbedding u)
            _ = extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl tf))
                (relabelUnivSimplex (M.mixedFaceUsedEmbedding (Sum.inl tf)) x₂)
                (M.localOldVertexEmbedding u) :=
              M.mixedUsedExtended_apply (Sum.inl tf) x₂ (M.localUsedOldEmbedding u)
            _ = extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl tf)) x₁
                (M.localOldVertexEmbedding u) := by rw [hx₂]
            _ = extendFaceCoordinates tf.1 x₀ u.1 := by
              rw [M.localMixedExtended_apply, hx₁]
            _ = z.1 a := congrFun hExt₀ a
        · have haZero : z.1 a = 0 := by
            apply hzt a
            intro hat
            exact haUsed ⟨t, ht, hat⟩
          rw [haZero]
          have hnot : (Sum.inr a : M.CommonVertex) ∉
              Set.range (MixedLocalFanCertificate.oldCompactToCommon M C) := by
            rintro ⟨v, hv⟩
            let vOld : M.UsedOldVertex :=
              MixedLocalFanCertificate.compactVertexEquiv M C v
            have hvOld : M.oldToCommon vOld = Sum.inr a := hv
            obtain ⟨u, huv⟩ :=
              M.exists_local_of_oldToCommon_eq_target vOld a hvOld
            have hraw : (Sum.inr u.1 : M.CommonVertex) = Sum.inr a := by
              calc
                (Sum.inr u.1 : M.CommonVertex) =
                    M.oldToCommon (M.localUsedOldEmbedding u) :=
                  (M.oldToCommon_local u).symm
                _ = M.oldToCommon vOld := congrArg M.oldToCommon huv
                _ = Sum.inr a := hvOld
            have hua : u.1 = a := Sum.inr_injective hraw
            exact haUsed (hua ▸ u.2)
          exact pushGeometricRealization_apply_of_notMem_range
            (MixedLocalFanCertificate.oldCompactToCommon M C)
            C.mixedOldComplex.compactIntrinsic.faces x hnot

private theorem MixedLocalFanCertificate.fanCenter_not_local
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (f : M.OutsideFanFace) :
    ¬ ∃ u : M.localComplex.UsedVertex,
      M.localOldVertexEmbedding u =
        M.fanOldVertexEmbedding
          (M.marking.fanVertexEmbedding f.1 (M.marking.fanCenterVertex f.1)) := by
  rintro ⟨u, hu⟩
  obtain ⟨t, ht, hut⟩ := u.2
  let tf : M.localComplex.Face := ⟨t, ht⟩
  let uv : {v // v ∈ tf.1} := ⟨u.1, hut⟩
  have hlocal : M.localVertexPoint u ∈ M.ambient.faceCarrier (C.parentFace tf).1 := by
    have huv :
        (⟨uv.1, ⟨tf.1, tf.2, uv.2⟩⟩ : M.localComplex.UsedVertex) = u :=
      Subtype.ext rfl
    simpa only [huv] using C.localVertexPoint_mem_parent tf uv
  have hcenterEq : M.localVertexPoint u = M.ambient.faceCenter f.1.1 :=
    congrArg (fun z : M.OldVertex ↦ z.1) hu
  have hcenterMem :
      M.ambient.faceCenter f.1.1 ∈ M.ambient.faceCarrier (C.parentFace tf).1 := by
    rw [← hcenterEq]
    exact hlocal
  let xc : stdSimplex ℝ {p // p ∈ M.marking.fanFaceVertices f.1} :=
    stdSimplex.vertex (M.marking.fanCenterVertex f.1)
  have hxcCarrier :
      M.marking.fanFaceMap f.1 xc ∈ M.ambient.faceCarrier (C.parentFace tf).1 := by
    rw [M.marking.fanFaceMap_vertex f.1 (M.marking.fanCenterVertex f.1)]
    exact hcenterMem
  have hzero := M.marking.fanCenterWeight_eq_zero_of_mem_faceCarrier_of_parent_ne
    f.1 (C.parentFace tf) (C.outside_parent_ne f tf) xc hxcCarrier
  have hone : xc (M.marking.fanCenterVertex f.1) = 1 := by
    simp [xc, stdSimplex.vertex]
  rw [hone] at hzero
  exact one_ne_zero hzero

private theorem MixedLocalFanCertificate.fanFace_oldPoint_mem_baseEdge_of_common
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (f : M.OutsideFanFace)
    (xb : C.mixedOldComplex.compactIntrinsic.realization)
    (yb : GeometricRealization M.localComplex.Vertex targetFaces)
    (hxb : ∀ v ∉ M.mixedUsedFaceVertices (Sum.inr f), xb.1 v = 0)
    (hcoords :
      (pushGeometricRealization
          (MixedLocalFanCertificate.oldCompactToCommon M C)
          C.mixedOldComplex.compactIntrinsic.faces xb).1 =
        (pushGeometricRealization M.targetToCommon targetFaces yb).1) :
    C.mixedOldComplex.compactEval xb ∈ M.ambient.faceCarrier
      (M.ambient.faceEdge f.1.1 f.1.2.1).1 := by
  classical
  let : Fintype M.UsedOldVertex :=
    C.mixedOldComplex.compactIntrinsic.vertexFintype
  let fc := M.marking.fanCenterVertex f.1
  let gc : M.marking.FanVertex := M.marking.fanVertexEmbedding f.1 fc
  have hgc : gc ∈ M.marking.globalFanFaceVertices f.1 :=
    fanVertexEmbedding_mem_globalFanFaceVertices M.marking f.1 fc
  have hoc :
      M.fanOldVertexEmbedding gc ∈ M.mixedOldFaceVertices (Sum.inr f) := by
    exact mem_finset_map M.fanOldVertexEmbedding _ hgc
  let oc : {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)} :=
    ⟨M.fanOldVertexEmbedding gc, hoc⟩
  let uc : M.UsedOldVertex := M.mixedFaceUsedEmbedding (Sum.inr f) oc
  have huc : uc ∈ M.mixedUsedFaceVertices (Sum.inr f) :=
    mem_map_univ (M.mixedFaceUsedEmbedding (Sum.inr f)) oc
  let wc : {v // v ∈ M.mixedUsedFaceVertices (Sum.inr f)} := ⟨uc, huc⟩
  have hnotLocal :
      ¬ ∃ u : M.localComplex.UsedVertex, M.localUsedOldEmbedding u = uc := by
    rintro ⟨u, hu⟩
    apply MixedLocalFanCertificate.fanCenter_not_local M C f
    refine ⟨u, ?_⟩
    exact congrArg (fun z : M.UsedOldVertex ↦ z.1) hu
  have hucCommon : M.oldToCommon uc = Sum.inl ⟨uc, hnotLocal⟩ := by
    change oldToAmalgamatedFun M.localUsedOldEmbedding M.localUsedVertexEmbedding uc =
      Sum.inl ⟨uc, hnotLocal⟩
    simp only [oldToAmalgamatedFun, dite_eq_right hnotLocal]
  let vc : C.mixedOldComplex.compactIntrinsic.Vertex :=
    (MixedLocalFanCertificate.compactVertexEquiv M C).symm uc
  have hvcCommon :
      MixedLocalFanCertificate.oldCompactToCommon M C vc =
        Sum.inl ⟨uc, hnotLocal⟩ := by
    change M.oldToCommon
        (MixedLocalFanCertificate.compactVertexEquiv M C vc) =
      Sum.inl ⟨uc, hnotLocal⟩
    rw [(MixedLocalFanCertificate.compactVertexEquiv M C).apply_symm_apply]
    exact hucCommon
  have htargetZero :
      (pushGeometricRealization M.targetToCommon targetFaces yb).1
          (Sum.inl ⟨uc, hnotLocal⟩) = 0 := by
    apply pushGeometricRealization_apply_of_notMem_range
    rintro ⟨a, ha⟩
    have hcontra :
        (Sum.inr a : M.CommonVertex) = Sum.inl ⟨uc, hnotLocal⟩ := ha
    simp at hcontra
  have hxbCenter : xb.1 vc = 0 := by
    calc
      xb.1 vc =
          (pushGeometricRealization
            (MixedLocalFanCertificate.oldCompactToCommon M C)
            C.mixedOldComplex.compactIntrinsic.faces xb).1
              (MixedLocalFanCertificate.oldCompactToCommon M C vc) :=
        (pushGeometricRealization_apply_embedding
          (MixedLocalFanCertificate.oldCompactToCommon M C)
          C.mixedOldComplex.compactIntrinsic.faces xb vc).symm
      _ = (pushGeometricRealization
            (MixedLocalFanCertificate.oldCompactToCommon M C)
            C.mixedOldComplex.compactIntrinsic.faces xb).1
              (Sum.inl ⟨uc, hnotLocal⟩) := by rw [hvcCommon]
      _ = (pushGeometricRealization M.targetToCommon targetFaces yb).1
              (Sum.inl ⟨uc, hnotLocal⟩) :=
        congrFun hcoords (Sum.inl ⟨uc, hnotLocal⟩)
      _ = 0 := htargetZero
  let x₂ : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices (Sum.inr f)} :=
    C.mixedOldComplex.restrictToFace
      (M.mixedUsedFaceVertices (Sum.inr f)) ⟨xb.1, xb.2.1⟩ hxb
  let x₁ : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)} :=
    relabelUnivSimplex (M.mixedFaceUsedEmbedding (Sum.inr f)) x₂
  let xG : stdSimplex ℝ {v // v ∈ M.marking.globalFanFaceVertices f.1} :=
    relabelFaceSimplex M.fanOldVertexEmbedding
      (M.marking.globalFanFaceVertices f.1) x₁
  let x₀ : stdSimplex ℝ {p // p ∈ M.marking.fanFaceVertices f.1} :=
    M.marking.fanRelabelSimplex f.1 xG
  have hcenter : x₀ fc = 0 := by
    have hweight : x₀ fc = x₂ wc := by
      simpa only [x₀, xG, x₁, wc, uc, oc, gc,
        MixedLocalFanData.mixedOldFaceVertices,
        MixedLocalFanData.mixedUsedFaceVertices] using
        fanRelabel_relabelFace_relabelUniv_apply M.marking f.1
          M.fanOldVertexEmbedding (M.mixedFaceUsedEmbedding (Sum.inr f)) x₂ fc
    exact hweight.trans hxbCenter
  rw [C.mixedOldComplex.compactEval_eq_faceMap (Sum.inr f) xb hxb]
  change M.marking.fanFaceMap f.1 x₀ ∈
    M.ambient.faceCarrier (M.ambient.faceEdge f.1.1 f.1.2.1).1
  exact M.marking.fanFaceMap_mem_baseEdge_of_center_eq_zero f.1 x₀ hcenter

private theorem MixedLocalFanCertificate.positive_usedOld_isLocal_of_common
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (xb : C.mixedOldComplex.compactIntrinsic.realization)
    (yb : GeometricRealization M.localComplex.Vertex targetFaces)
    (hcoords :
      (pushGeometricRealization C.oldCompactToCommon
          C.mixedOldComplex.compactIntrinsic.faces xb).1 =
        (pushGeometricRealization M.targetToCommon targetFaces yb).1)
    (v : M.UsedOldVertex)
    (hv : 0 < xb.1 (C.compactVertexEquiv.symm v)) :
    ∃ u : M.localComplex.UsedVertex, M.localUsedOldEmbedding u = v := by
  classical
  let : Fintype M.UsedOldVertex :=
    C.mixedOldComplex.compactIntrinsic.vertexFintype
  apply exists_local_of_positive_of_amalgamated_coordinates
    M.localUsedOldEmbedding M.localUsedVertexEmbedding
    (fun w ↦ xb.1 (C.compactVertexEquiv.symm w))
    (pushGeometricRealization C.oldCompactToCommon
      C.mixedOldComplex.compactIntrinsic.faces xb).1
    (pushGeometricRealization M.targetToCommon targetFaces yb).1
  · intro w
    rw [← pushGeometricRealization_apply_embedding
      C.oldCompactToCommon C.mixedOldComplex.compactIntrinsic.faces
      xb (C.compactVertexEquiv.symm w)]
    congr 1
  · intro w
    apply pushGeometricRealization_apply_of_notMem_range
    rintro ⟨a, ha⟩
    have hcontra : (Sum.inr a : M.CommonVertex) = Sum.inl w := ha
    simp at hcontra
  · exact hcoords
  · exact hv

/-- The two geometric facts about a selected region needed to absorb an outside fan face. -/
private structure MixedFanSelectionData (M : MixedLocalFanData) where
  selectedSet : Set M.ambient.realization
  localVertex_mem_selected : ∀ u : M.localComplex.UsedVertex,
    M.localVertexPoint u ∈ selectedSet
  baseEdge_mem_selected :
    ∀ (f : M.OutsideFanFace) (p : M.ambient.realization),
      p ∈ M.ambient.faceCarrier (M.ambient.faceEdge f.1.1 f.1.2.1).1 →
      (∃ u : M.localComplex.UsedVertex,
        M.localVertexPoint u = (M.marking.fanFirstVertex f.1).1) →
      (∃ u : M.localComplex.UsedVertex,
        M.localVertexPoint u = (M.marking.fanSecondVertex f.1).1) →
      p ∈ selectedSet

private theorem MixedLocalFanCertificate.fanFace_oldPoint_mem_selected_of_common
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (D : MixedFanSelectionData M)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (f : M.OutsideFanFace)
    (xb : C.mixedOldComplex.compactIntrinsic.realization)
    (yb : GeometricRealization M.localComplex.Vertex targetFaces)
    (hxb : ∀ v ∉ M.mixedUsedFaceVertices (Sum.inr f), xb.1 v = 0)
    (hcoords :
      (pushGeometricRealization C.oldCompactToCommon
          C.mixedOldComplex.compactIntrinsic.faces xb).1 =
        (pushGeometricRealization M.targetToCommon targetFaces yb).1) :
    C.mixedOldComplex.compactEval xb ∈ D.selectedSet := by
  classical
  let : Fintype M.UsedOldVertex :=
    C.mixedOldComplex.compactIntrinsic.vertexFintype
  let x₂ : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices (Sum.inr f)} :=
    C.mixedOldComplex.restrictToFace
      (M.mixedUsedFaceVertices (Sum.inr f)) ⟨xb.1, xb.2.1⟩ hxb
  let x₁ : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)} :=
    relabelUnivSimplex (M.mixedFaceUsedEmbedding (Sum.inr f)) x₂
  let xG : stdSimplex ℝ {v // v ∈ M.marking.globalFanFaceVertices f.1} :=
    relabelFaceSimplex M.fanOldVertexEmbedding
      (M.marking.globalFanFaceVertices f.1) x₁
  let x₀ : stdSimplex ℝ {p // p ∈ M.marking.fanFaceVertices f.1} :=
    M.marking.fanRelabelSimplex f.1 xG
  have hmap :
      C.mixedOldComplex.compactEval xb = M.marking.fanFaceMap f.1 x₀ := by
    rw [C.mixedOldComplex.compactEval_eq_faceMap (Sum.inr f) xb hxb]
    rfl
  have hbase :=
    MixedLocalFanCertificate.fanFace_oldPoint_mem_baseEdge_of_common
      M C targetFaces f xb yb hxb hcoords
  have hcenter : x₀ (M.marking.fanCenterVertex f.1) = 0 := by
    apply M.marking.fanCenterWeight_eq_zero_of_mem_baseEdge
    rwa [← hmap]
  have hpositiveLocal
      (p : {p // p ∈ M.marking.fanFaceVertices f.1})
      (hp : 0 < x₀ p) :
      ∃ u : M.localComplex.UsedVertex, M.localVertexPoint u = p.1 := by
    let gp : M.marking.FanVertex := M.marking.fanVertexEmbedding f.1 p
    have hgp : gp ∈ M.marking.globalFanFaceVertices f.1 :=
      fanVertexEmbedding_mem_globalFanFaceVertices M.marking f.1 p
    have hop :
        M.fanOldVertexEmbedding gp ∈ M.mixedOldFaceVertices (Sum.inr f) := by
      exact mem_finset_map M.fanOldVertexEmbedding _ hgp
    let op : {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)} :=
      ⟨M.fanOldVertexEmbedding gp, hop⟩
    let uv : M.UsedOldVertex := M.mixedFaceUsedEmbedding (Sum.inr f) op
    have huv : uv ∈ M.mixedUsedFaceVertices (Sum.inr f) :=
      mem_map_univ (M.mixedFaceUsedEmbedding (Sum.inr f)) op
    let wv : {v // v ∈ M.mixedUsedFaceVertices (Sum.inr f)} := ⟨uv, huv⟩
    let cv : C.mixedOldComplex.compactIntrinsic.Vertex :=
      C.compactVertexEquiv.symm uv
    have hweight : x₀ p = xb.1 cv := by
      change x₀ p = x₂ wv
      simpa only [x₀, xG, x₁, wv, uv, op, gp,
        MixedLocalFanData.mixedOldFaceVertices,
        MixedLocalFanData.mixedUsedFaceVertices] using
        fanRelabel_relabelFace_relabelUniv_apply M.marking f.1
          M.fanOldVertexEmbedding (M.mixedFaceUsedEmbedding (Sum.inr f)) x₂ p
    have hcv : 0 < xb.1 cv := by rw [← hweight]; exact hp
    obtain ⟨u, hu⟩ :=
      MixedLocalFanCertificate.positive_usedOld_isLocal_of_common
        M C targetFaces xb yb hcoords uv hcv
    refine ⟨u, ?_⟩
    have huOld :
        M.localOldVertexEmbedding u = M.fanOldVertexEmbedding gp :=
      congrArg (fun z : M.UsedOldVertex ↦ z.1) hu
    exact congrArg (fun z : M.OldVertex ↦ z.1) huOld
  have endpointSelected
      (p : {p // p ∈ M.marking.fanFaceVertices f.1})
      (hpoint : (M.marking.fanFaceMap f.1 x₀).1 = p.1.1)
      (hcoordinates :
        extendFaceCoordinates (M.marking.fanFaceVertices f.1) x₀ =
          Pi.single p.1 1) :
      C.mixedOldComplex.compactEval xb ∈ D.selectedSet := by
    have hpOne := simplex_apply_eq_one_of_extend_eq_single
      (M.marking.fanFaceVertices f.1) x₀ p hcoordinates
    obtain ⟨u, hu⟩ := hpositiveLocal p (by rw [hpOne]; norm_num)
    have heq : C.mixedOldComplex.compactEval xb = p.1 := by
      apply Subtype.ext
      rw [hmap]
      exact hpoint
    rw [heq, ← hu]
    exact D.localVertex_mem_selected u
  by_cases hpos :
      0 < x₀ (M.marking.fanFirstVertex f.1) ∧
        0 < x₀ (M.marking.fanSecondVertex f.1)
  · exact D.baseEdge_mem_selected f _ hbase
      (hpositiveLocal (M.marking.fanFirstVertex f.1) hpos.1)
      (hpositiveLocal (M.marking.fanSecondVertex f.1) hpos.2)
  · rcases M.marking.fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
        f.1 x₀ hcenter hpos with hfirst | hsecond
    · exact endpointSelected (M.marking.fanFirstVertex f.1) hfirst.1 hfirst.2
    · exact endpointSelected (M.marking.fanSecondVertex f.1) hsecond.1 hsecond.2


private theorem MixedLocalFanCertificate.localFace_relabel_agree
    {S : Type*} (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (localMap : M.localComplex.realization → M.ambient.realization)
    (local_face_eval :
      ∀ (t : M.localComplex.Face)
        (x : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices (Sum.inl t)}),
        M.mixedUsedFaceMap (Sum.inl t) x =
          localMap (M.localComplex.faceStandardMap t
            (relabelUnivSimplex (M.localFaceOldVertexEmbedding t)
              (relabelUnivSimplex (M.mixedFaceUsedEmbedding (Sum.inl t)) x))))
    (eOld : C.mixedOldComplex.compactIntrinsic.realization → S)
    (eTarget : GeometricRealization M.localComplex.Vertex targetFaces → S)
    (agree_of_local :
      ∀ (xb : C.mixedOldComplex.compactIntrinsic.realization)
        (yb : GeometricRealization M.localComplex.Vertex targetFaces)
        (z : M.localComplex.realization),
        C.mixedOldComplex.compactEval xb = localMap z →
        (pushGeometricRealization C.oldCompactToCommon
              C.mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization M.targetToCommon targetFaces yb).1 →
        eOld xb = eTarget yb)
    (tf : M.localComplex.Face)
    (xb : C.mixedOldComplex.compactIntrinsic.realization)
    (yb : GeometricRealization M.localComplex.Vertex targetFaces)
    (hxb : ∀ v ∉ M.mixedUsedFaceVertices (Sum.inl tf), xb.1 v = 0)
    (hcoords :
      (pushGeometricRealization C.oldCompactToCommon
          C.mixedOldComplex.compactIntrinsic.faces xb).1 =
        (pushGeometricRealization M.targetToCommon targetFaces yb).1) :
    eOld xb = eTarget yb := by
  classical
  let : Fintype M.UsedOldVertex :=
    C.mixedOldComplex.compactIntrinsic.vertexFintype
  let x₂ : stdSimplex ℝ {v // v ∈ M.mixedUsedFaceVertices (Sum.inl tf)} :=
    C.mixedOldComplex.restrictToFace
      (M.mixedUsedFaceVertices (Sum.inl tf)) ⟨xb.1, xb.2.1⟩ hxb
  let x₁ : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl tf)} :=
    relabelUnivSimplex (M.mixedFaceUsedEmbedding (Sum.inl tf)) x₂
  let x₀ : stdSimplex ℝ {v // v ∈ tf.1} :=
    relabelUnivSimplex (M.localFaceOldVertexEmbedding tf) x₁
  let z : M.localComplex.realization := M.localComplex.faceStandardMap tf x₀
  apply agree_of_local xb yb z
  · rw [C.mixedOldComplex.compactEval_eq_faceMap (Sum.inl tf) xb hxb]
    exact local_face_eval tf x₂
  · exact hcoords

private theorem MixedLocalFanCertificate.fanFace_relabel_agree
    {S : Type*} (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    (D : MixedFanSelectionData M) [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (localMap : M.localComplex.realization → M.ambient.realization)
    (selected_lift : ∀ p ∈ D.selectedSet, ∃ z, localMap z = p)
    (eOld : C.mixedOldComplex.compactIntrinsic.realization → S)
    (eTarget : GeometricRealization M.localComplex.Vertex targetFaces → S)
    (agree_of_local :
      ∀ (xb : C.mixedOldComplex.compactIntrinsic.realization)
        (yb : GeometricRealization M.localComplex.Vertex targetFaces)
        (z : M.localComplex.realization),
        C.mixedOldComplex.compactEval xb = localMap z →
        (pushGeometricRealization C.oldCompactToCommon
              C.mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization M.targetToCommon targetFaces yb).1 →
        eOld xb = eTarget yb)
    (f : M.OutsideFanFace)
    (xb : C.mixedOldComplex.compactIntrinsic.realization)
    (yb : GeometricRealization M.localComplex.Vertex targetFaces)
    (hxb : ∀ v ∉ M.mixedUsedFaceVertices (Sum.inr f), xb.1 v = 0)
    (hcoords :
      (pushGeometricRealization C.oldCompactToCommon
          C.mixedOldComplex.compactIntrinsic.faces xb).1 =
        (pushGeometricRealization M.targetToCommon targetFaces yb).1) :
    eOld xb = eTarget yb := by
  have hselected :=
    MixedLocalFanCertificate.fanFace_oldPoint_mem_selected_of_common
      M C D targetFaces f xb yb hxb hcoords
  obtain ⟨z, hz⟩ := selected_lift _ hselected
  exact agree_of_local xb yb z hz.symm hcoords

private theorem MixedLocalFanCertificate.common_relabel_agree_small
    {S : Type*} (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (eOld : C.mixedOldComplex.compactIntrinsic.realization → S)
    (eTarget : GeometricRealization M.localComplex.Vertex targetFaces → S)
    (local_agree :
      ∀ (tf : M.localComplex.Face)
        (xb : C.mixedOldComplex.compactIntrinsic.realization)
        (yb : GeometricRealization M.localComplex.Vertex targetFaces),
        (∀ v ∉ M.mixedUsedFaceVertices (Sum.inl tf), xb.1 v = 0) →
        (pushGeometricRealization C.oldCompactToCommon
              C.mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization M.targetToCommon targetFaces yb).1 →
        eOld xb = eTarget yb)
    (fan_agree :
      ∀ (f : M.OutsideFanFace)
        (xb : C.mixedOldComplex.compactIntrinsic.realization)
        (yb : GeometricRealization M.localComplex.Vertex targetFaces),
        (∀ v ∉ M.mixedUsedFaceVertices (Sum.inr f), xb.1 v = 0) →
        (pushGeometricRealization C.oldCompactToCommon
              C.mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization M.targetToCommon targetFaces yb).1 →
        eOld xb = eTarget yb) :
    ∀ (x : GeometricRealization M.CommonVertex
        (relabelFaceFamily C.oldCompactToCommon
          C.mixedOldComplex.compactIntrinsic.faces))
      (y : GeometricRealization M.CommonVertex
        (relabelFaceFamily M.targetToCommon targetFaces)),
      x.1 = y.1 →
        (eOld ∘ (relabelGeometricRealizationHomeomorph C.oldCompactToCommon
          C.mixedOldComplex.compactIntrinsic.faces).symm) x =
        (eTarget ∘ (relabelGeometricRealizationHomeomorph M.targetToCommon
          targetFaces).symm) y := by
  intro x y hxy
  let xb := (relabelGeometricRealizationHomeomorph C.oldCompactToCommon
    C.mixedOldComplex.compactIntrinsic.faces).symm x
  let yb := (relabelGeometricRealizationHomeomorph M.targetToCommon targetFaces).symm y
  have hcoords := push_relabel_symm_coordinates_eq C.oldCompactToCommon M.targetToCommon
    C.mixedOldComplex.compactIntrinsic.faces targetFaces x y hxy
  obtain ⟨f, hxb⟩ := C.mixedOldComplex.exists_containingFace xb
  change eOld xb = eTarget yb
  rcases f with tf | f
  · exact local_agree tf xb yb hxb hcoords
  · exact fan_agree f xb yb hxb hcoords

private noncomputable def MixedLocalFanCertificate.relabelOldFaces
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex] :=
  relabelFaceFamily C.oldCompactToCommon C.mixedOldComplex.compactIntrinsic.faces

private noncomputable def MixedLocalFanData.relabelTargetFaces
    (M : MixedLocalFanData) [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex)) :=
  relabelFaceFamily M.targetToCommon targetFaces

private noncomputable def MixedLocalFanCertificate.relabelOldMap
    {S : Type*} (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (eOld : C.mixedOldComplex.compactIntrinsic.realization → S) :
    GeometricRealization M.CommonVertex (C.relabelOldFaces M) → S :=
  eOld ∘ (relabelGeometricRealizationHomeomorph C.oldCompactToCommon
    C.mixedOldComplex.compactIntrinsic.faces).symm

private noncomputable def MixedLocalFanData.relabelTargetMap
    {S : Type*} (M : MixedLocalFanData)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (eTarget : GeometricRealization M.localComplex.Vertex targetFaces → S) :
    GeometricRealization M.CommonVertex (M.relabelTargetFaces targetFaces) → S :=
  eTarget ∘ (relabelGeometricRealizationHomeomorph M.targetToCommon targetFaces).symm

private structure RelabeledWeldCertificate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (eOld : C.mixedOldComplex.compactIntrinsic.realization → S)
    (eTarget : GeometricRealization M.localComplex.Vertex targetFaces → S) where
  card : ∀ t ∈ C.relabelOldFaces M ∪ M.relabelTargetFaces targetFaces, t.card = 3
  old_embedding : _root_.Topology.IsEmbedding (C.relabelOldMap M eOld)
  target_embedding : _root_.Topology.IsEmbedding (M.relabelTargetMap targetFaces eTarget)
  old_boundary : PartialTriangulation.BoundaryFacewiseRegularEmbedding
    (C.relabelOldFaces M) (C.relabelOldMap M eOld)
  target_boundary : PartialTriangulation.BoundaryFacewiseRegularEmbedding
    (M.relabelTargetFaces targetFaces) (M.relabelTargetMap targetFaces eTarget)
  range_old : Set.range (C.relabelOldMap M eOld) = Set.range eOld
  range_target : Set.range (M.relabelTargetMap targetFaces eTarget) = Set.range eTarget

private theorem exists_relabeledWeldCertificate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (M : MixedLocalFanData) (C : MixedLocalFanCertificate M)
    [DecidableEq M.CommonVertex]
    (targetFaces : Finset (Finset M.localComplex.Vertex))
    (eOld : C.mixedOldComplex.compactIntrinsic.realization → S)
    (eTarget : GeometricRealization M.localComplex.Vertex targetFaces → S)
    (heOld : _root_.Topology.IsEmbedding eOld)
    (heTarget : _root_.Topology.IsEmbedding eTarget)
    (hOldBoundary : PartialTriangulation.BoundaryFacewiseRegularEmbedding
      C.mixedOldComplex.compactIntrinsic.faces eOld)
    (hTargetBoundary : PartialTriangulation.BoundaryFacewiseRegularEmbedding
      targetFaces eTarget)
    (hTargetCard : ∀ t ∈ targetFaces, t.card = 3) :
    RelabeledWeldCertificate M C targetFaces eOld eTarget := by
  classical
  refine
    { card := ?_
      old_embedding := heOld.comp
        (relabelGeometricRealizationHomeomorph C.oldCompactToCommon
          C.mixedOldComplex.compactIntrinsic.faces).symm.isEmbedding
      target_embedding := heTarget.comp
        (relabelGeometricRealizationHomeomorph M.targetToCommon targetFaces).symm.isEmbedding
      old_boundary := PartialTriangulation.boundaryFacewiseRegularEmbedding_relabel
        C.oldCompactToCommon C.mixedOldComplex.compactIntrinsic.faces eOld hOldBoundary
      target_boundary := PartialTriangulation.boundaryFacewiseRegularEmbedding_relabel
        M.targetToCommon targetFaces eTarget hTargetBoundary
      range_old := ?_
      range_target := ?_ }
  · intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      rw [Finset.card_map]
      exact C.mixedOldComplex.compactIntrinsic.faces_card u hu
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      rw [Finset.card_map]
      exact hTargetCard u hu
  · apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro y ⟨x, rfl⟩
      refine ⟨(relabelGeometricRealizationHomeomorph C.oldCompactToCommon
        C.mixedOldComplex.compactIntrinsic.faces) x, ?_⟩
      exact congrArg eOld ((relabelGeometricRealizationHomeomorph C.oldCompactToCommon
        C.mixedOldComplex.compactIntrinsic.faces).symm_apply_apply x)
  · apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro y ⟨x, rfl⟩
      refine ⟨(relabelGeometricRealizationHomeomorph M.targetToCommon targetFaces) x, ?_⟩
      exact congrArg eTarget
        ((relabelGeometricRealizationHomeomorph M.targetToCommon targetFaces).symm_apply_apply x)

private noncomputable def alignedRelativeExtraLines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ)) : List (Plane →ᵃ[ℝ] ℝ) :=
  let n := A.commonLevel (A.tilesMeeting C hC)
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let alignmentLines := A.relativeLevelAlignmentLines C hC N anchorLines n
  anchorLines ++ baseOldMesh.coordinateLines ++ alignmentLines

private theorem exists_baseTriangle_of_alignedRelativeOldTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle) :
    ∃ u : (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).Triangle,
      (A.tileFacesMeetingRelativeOldMesh C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1 ⊆
        (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1 := by
  classical
  let n := A.commonLevel (A.tilesMeeting C hC)
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let alignmentLines := A.relativeLevelAlignmentLines C hC N anchorLines n
  let extraLines := alignedRelativeExtraLines A C hC N anchorLines
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let localOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let R := PolygonalFamily.relativeSynchronizedArrangement
    (A.tileFacePolygonMeeting C hC) N lines
  have htR : t.1 ∈ R.triangles :=
    (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
      (A.tileFacePolygonMeeting C hC) N lines (fun _ ↦ True)).mp t.2 |>.1
  let tR : R.Triangle := ⟨t.1, htR⟩
  have hBaseLines : ∀ a ∈ baseOldMesh.coordinateLines,
      a ∈ N.coordinateLines ++ lines := by
    intro a ha
    apply List.mem_append_right
    change a ∈ A.tileFaceMeetingCertificateLines C hC N ++ extraLines
    apply List.mem_append_right
    change a ∈ anchorLines ++ baseOldMesh.coordinateLines ++ alignmentLines
    exact List.mem_append_left _ (List.mem_append_right _ ha)
  have hhit :
      (interior (R.triangleCarrier tR.1) ∩
        baseOldMesh.toPlaneComplex.support).Nonempty := by
    obtain ⟨p, hp⟩ := R.interior_triangleCarrier_nonempty tR
    refine ⟨p, hp, ?_⟩
    rw [A.tileFacesMeetingRelativeOldMesh_support C hC N anchorLines,
      ← A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines]
    rw [localOldMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr
      ⟨t.1, Set.mem_iUnion.mpr ⟨t.2, interior_subset hp⟩⟩
  obtain ⟨u, hu⟩ :=
    (PolygonalFamily.arrangementMesh (A.tileFacePolygonMeeting C hC)
      ).exists_target_triangle_of_refineByLines_of_interior_inter_support
        baseOldMesh (N.coordinateLines ++ lines) hBaseLines tR hhit
  exact ⟨u, hu⟩


private theorem alignedRelativeOldTriangle_source_mem_levelFace
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle)
    (u : (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).Triangle)
    (s : {s : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
      s ∈ A.levelFaces (A.tilesMeeting C hC)})
    (p : Plane)
    (hp : p ∈ interior ((A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1))
    (htu : (A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1 ⊆
      (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1)
    (hparent : levelFaceParent K s.1 =
      A.relativeOldTriangleParent C hC N anchorLines u)
    (hmono : ∀ k : Fin 3,
      (A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).IsMonochromatic
        ((levelFaceParentCoord K s.1 k).comp
          (A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u)))
    (hcoordAtP : ∀ k : Fin 3, 0 <
      ((levelFaceParentCoord K s.1 k).comp
        (A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u)) p) :
    ∀ (r : Plane)
      (hr : r ∈ (A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1),
      A.tileFacesMeetingRelativeSourceEmbed C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)
          (A.relativeOldTrianglePoint C hC N
            (alignedRelativeExtraLines A C hC N anchorLines) t ⟨r, hr⟩) ∈
        K.levelFaceCarrier s.1 := by
  classical
  let n := A.commonLevel (A.tilesMeeting C hC)
  let Rlevel := K.safeSubdivision n
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let extraLines := alignedRelativeExtraLines A C hC N anchorLines
  let localOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let source₁ := A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
  let F := A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u
  intro r hr
  let a : Fin 3 → (Plane →ᵃ[ℝ] ℝ) := fun k ↦ (levelFaceParentCoord K s.1 k).comp F
  have hrcoord (k : Fin 3) : 0 ≤ a k r := by
    rcases hmono k t.1 t.2 with hpos | hneg
    · apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage (a k)) hr
      rintro z ⟨v, hv, rfl⟩
      exact hpos v hv
    · have hpNonpos : a k p ≤ 0 := by
        apply convexHull_min ?_ ((convex_Iic (0 : ℝ)).affine_preimage (a k))
          (interior_subset hp)
        rintro z ⟨v, hv, rfl⟩
        exact hneg v hv
      exact False.elim ((not_lt_of_ge hpNonpos) (hcoordAtP k))
  let b := affineBasisOfTriangle
    (levelFaceParentPlaneAffine K s.1 ∘ standardTriangleVertex)
    (affineIndependent_comp_of_injOn_convexHull
      standardTriangleVertex standardTriangleVertex_affineIndependent
      (levelFaceParentPlaneAffine K s.1) (by
        rw [← standardTrianglePlaneComplex_support]
        exact levelFaceParentPlaneAffine_injOn K s.1))
  have hFr : F r ∈ convexHull ℝ (Set.range b) := by
    rw [b.convexHull_eq_nonneg_coord]
    exact fun k ↦ hrcoord k
  have hb : (fun i ↦ b i) =
      levelFaceParentPlaneAffine K s.1 ∘ standardTriangleVertex := by
    funext i
    rfl
  have hFr' : F r ∈ convexHull ℝ
      (Set.range (levelFaceParentPlaneAffine K s.1 ∘ standardTriangleVertex)) := by
    rwa [← congrArg Set.range hb]
  rw [Set.range_comp, ← (levelFaceParentPlaneAffine K s.1).image_convexHull,
    ← standardTrianglePlaneComplex_support] at hFr'
  obtain ⟨z', hz', hz'eq⟩ := hFr'
  let z'Support : standardTrianglePlaneComplex.support := ⟨z', hz'⟩
  let rLocal : {q : Plane // q ∈ localOldMesh.triangleCarrier t.1} := ⟨r, hr⟩
  let rBase : {q : Plane // q ∈ baseOldMesh.triangleCarrier u.1} := ⟨r, htu hr⟩
  let q' : Rlevel.refined.ClosedFace s.1 :=
    (Rlevel.refined.facePlaneHomeomorph s.1).symm z'Support
  refine ⟨q'.1, q'.2, ?_⟩
  have hsourceR :
      A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
          (A.relativeOldTrianglePoint C hC N anchorLines u rBase) =
        source₁ (A.relativeOldTrianglePoint C hC N extraLines t rLocal) := by
    apply A.tileFacesMeetingRelativeSourceEmbed_eq_of_coordinateEmbed_eq C hC N
    rw [A.relativeOldTrianglePoint_coordinateEmbed C hC N anchorLines u rBase,
      A.relativeOldTrianglePoint_coordinateEmbed C hC N extraLines t rLocal]
  have hsourceRMem : source₁ (A.relativeOldTrianglePoint C hC N extraLines t rLocal) ∈
      K.faceCarrier (A.relativeOldTriangleParent C hC N anchorLines u).1 := by
    rw [← hsourceR]
    exact A.relativeOldTriangleParent_contains C hC N anchorLines u _
      (A.relativeOldTrianglePoint_supported C hC N anchorLines u rBase)
  have hq'Parent : Rlevel.homeo q'.1 ∈
      K.faceCarrier (A.relativeOldTriangleParent C hC N anchorLines u).1 := by
    rw [← hparent]
    exact levelFaceParent_contains K s.1 q'.1 q'.2
  have hclosed :
      (⟨Rlevel.homeo q'.1, hq'Parent⟩ :
          K.ClosedFace (A.relativeOldTriangleParent C hC N anchorLines u)) =
        ⟨source₁ (A.relativeOldTrianglePoint C hC N extraLines t rLocal),
          hsourceRMem⟩ := by
    apply (K.facePlaneHomeomorph
      (A.relativeOldTriangleParent C hC N anchorLines u)).injective
    apply Subtype.ext
    have hlevel := levelFaceParentPlaneAffine_eq K s.1 z'Support
    have hbase := A.relativeOldTriangleParentPlaneAffine_eq
      C hC N anchorLines u rBase
    rw [K.facePlaneHomeomorph_val_eq_forwardAffine] at hlevel hbase
    calc
      K.facePlaneForwardAffine (A.relativeOldTriangleParent C hC N anchorLines u)
          (Rlevel.homeo q'.1).1 =
          K.facePlaneForwardAffine (levelFaceParent K s.1) (Rlevel.homeo q'.1).1 := by
        rw [hparent]
      _ = levelFaceParentPlaneAffine K s.1 z' := hlevel.symm
      _ = F r := hz'eq
      _ = K.facePlaneForwardAffine (A.relativeOldTriangleParent C hC N anchorLines u)
          (A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
            (A.relativeOldTrianglePoint C hC N anchorLines u rBase)).1 := hbase
      _ = K.facePlaneForwardAffine (A.relativeOldTriangleParent C hC N anchorLines u)
          (source₁ (A.relativeOldTrianglePoint C hC N extraLines t rLocal)).1 :=
        congrArg (K.facePlaneForwardAffine
          (A.relativeOldTriangleParent C hC N anchorLines u))
          (congrArg Subtype.val hsourceR)
  exact congrArg Subtype.val hclosed

private theorem exists_alignedRelativeOldTriangle_parentWitness
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle) :
    ∃ (u : (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).Triangle)
      (s : {s : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
        s ∈ A.levelFaces (A.tilesMeeting C hC)})
      (htu : (A.tileFacesMeetingRelativeOldMesh C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1 ⊆
        (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1)
      (p : {p : Plane // p ∈ interior
        ((A.tileFacesMeetingRelativeOldMesh C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1)})
      (q : (K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).refined.ClosedFace s.1),
      A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
          (A.relativeOldTrianglePoint C hC N anchorLines u
            ⟨p.1, interior_subset (interior_mono htu p.2)⟩) =
        A.tileFacesMeetingRelativeSourceEmbed C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)
          (A.relativeOldTrianglePoint C hC N
            (alignedRelativeExtraLines A C hC N anchorLines) t
            ⟨p.1, interior_subset p.2⟩) ∧
      A.tileFacesMeetingRelativeSourceEmbed C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)
          (A.relativeOldTrianglePoint C hC N
            (alignedRelativeExtraLines A C hC N anchorLines) t
            ⟨p.1, interior_subset p.2⟩) =
        (K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).homeo q.1 ∧
      levelFaceParent K s.1 = A.relativeOldTriangleParent C hC N anchorLines u := by
  classical
  let n := A.commonLevel (A.tilesMeeting C hC)
  let selectedLevelFaces := A.levelFaces (A.tilesMeeting C hC)
  let Rlevel := K.safeSubdivision n
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let extraLines := alignedRelativeExtraLines A C hC N anchorLines
  let source₁ := A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
  let localOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  have hsource₁Range : Set.range source₁ =
      ⋃ u : {u : K.LevelFace n // u ∈ selectedLevelFaces}, K.levelFaceCarrier u.1 :=
    A.range_tileFacesMeetingRelativeSourceEmbed_eq_levelFaces C hC N extraLines
  obtain ⟨u, htu⟩ :=
    exists_baseTriangle_of_alignedRelativeOldTriangle A C hC N anchorLines t
  obtain ⟨p, hp⟩ := localOldMesh.interior_triangleCarrier_nonempty t
  have hpBase : p ∈ interior (baseOldMesh.triangleCarrier u.1) := interior_mono htu hp
  let pLocal : {q : Plane // q ∈ localOldMesh.triangleCarrier t.1} :=
    ⟨p, interior_subset hp⟩
  let pBase : {q : Plane // q ∈ baseOldMesh.triangleCarrier u.1} :=
    ⟨p, interior_subset hpBase⟩
  let xLocal := A.relativeOldTrianglePoint C hC N extraLines t pLocal
  let xBase := A.relativeOldTrianglePoint C hC N anchorLines u pBase
  have hsourceEq :
      A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines xBase = source₁ xLocal := by
    apply A.tileFacesMeetingRelativeSourceEmbed_eq_of_coordinateEmbed_eq C hC N
    rw [A.relativeOldTrianglePoint_coordinateEmbed C hC N anchorLines u pBase,
      A.relativeOldTrianglePoint_coordinateEmbed C hC N extraLines t pLocal]
  have hxUnion : source₁ xLocal ∈
      ⋃ s : {s : K.LevelFace n // s ∈ selectedLevelFaces}, K.levelFaceCarrier s.1 := by
    rw [← hsource₁Range]
    exact Set.mem_range_self xLocal
  obtain ⟨s, q, hqFace, hqSource⟩ := Set.mem_iUnion.mp hxUnion
  have hbaseMem : source₁ xLocal ∈
      K.faceCarrier (A.relativeOldTriangleParent C hC N anchorLines u).1 := by
    rw [← hsourceEq]
    exact A.relativeOldTriangleParent_contains C hC N anchorLines u xBase
      (A.relativeOldTrianglePoint_supported C hC N anchorLines u pBase)
  have hlevelMem : source₁ xLocal ∈ K.faceCarrier (levelFaceParent K s.1).1 := by
    have h := levelFaceParent_contains K s.1 q hqFace
    rw [hqSource] at h
    exact h
  let F := A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u
  have hFimage : F '' interior (baseOldMesh.triangleCarrier u.1) ⊆
      standardTrianglePlaneComplex.support := by
    rintro z ⟨r, hr, rfl⟩
    let rBase : {q : Plane // q ∈ baseOldMesh.triangleCarrier u.1} :=
      ⟨r, interior_subset hr⟩
    rw [A.relativeOldTriangleParentPlaneAffine_eq C hC N anchorLines u rBase]
    exact (K.facePlaneHomeomorph (A.relativeOldTriangleParent C hC N anchorLines u) _).2
  have hFopen : IsOpen (F '' interior (baseOldMesh.triangleCarrier u.1)) :=
    (F.isOpenMap F.continuous_of_finiteDimensional
      (A.relativeOldTriangleParentPlaneAffine_surjective C hC N anchorLines u))
      (interior (baseOldMesh.triangleCarrier u.1)) isOpen_interior
  have hpFint : F p ∈ interior standardTrianglePlaneComplex.support := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (hFopen.mem_nhds ⟨p, hpBase, rfl⟩) hFimage
  have hpChartInt :
      (K.facePlaneHomeomorph (A.relativeOldTriangleParent C hC N anchorLines u)
        ⟨source₁ xLocal, hbaseMem⟩).1 ∈
        interior standardTrianglePlaneComplex.support := by
    have hbaseMem' : A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines xBase ∈
        K.faceCarrier (A.relativeOldTriangleParent C hC N anchorLines u).1 :=
      A.relativeOldTriangleParent_contains C hC N anchorLines u xBase
        (A.relativeOldTrianglePoint_supported C hC N anchorLines u pBase)
    have hclosed :
        (⟨A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines xBase, hbaseMem'⟩ :
          K.ClosedFace (A.relativeOldTriangleParent C hC N anchorLines u)) =
          ⟨source₁ xLocal, hbaseMem⟩ := Subtype.ext hsourceEq
    have heq :
        (K.facePlaneHomeomorph (A.relativeOldTriangleParent C hC N anchorLines u)
          ⟨source₁ xLocal, hbaseMem⟩).1 = F p := by
      calc
        _ = (K.facePlaneHomeomorph (A.relativeOldTriangleParent C hC N anchorLines u)
              ⟨A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines xBase,
                hbaseMem'⟩).1 :=
          congrArg (fun w ↦ w.1) (congrArg (K.facePlaneHomeomorph
            (A.relativeOldTriangleParent C hC N anchorLines u)) hclosed.symm)
        _ = F p :=
          (A.relativeOldTriangleParentPlaneAffine_eq C hC N anchorLines u pBase).symm
    rw [heq]
    exact hpFint
  have hparent : levelFaceParent K s.1 =
      A.relativeOldTriangleParent C hC N anchorLines u := by
    symm
    exact face_eq_of_mem_faceCarriers_of_facePlane_mem_interior K
      (A.relativeOldTriangleParent C hC N anchorLines u) (levelFaceParent K s.1)
      (source₁ xLocal) hbaseMem hlevelMem hpChartInt
  exact ⟨u, s, htu, ⟨p, hp⟩, ⟨q, hqFace⟩, hsourceEq, hqSource.symm, hparent⟩

private theorem alignedRelativeOldTriangle_planeAt_parentWitness
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle)
    (u : (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).Triangle)
    (s : {s : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
      s ∈ A.levelFaces (A.tilesMeeting C hC)})
    (htu : (A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1 ⊆
      (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1)
    (p : {p : Plane // p ∈ interior
      ((A.tileFacesMeetingRelativeOldMesh C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1)})
    (q : (K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).refined.ClosedFace s.1)
    (hsourceEq : A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
        (A.relativeOldTrianglePoint C hC N anchorLines u
          ⟨p.1, interior_subset (interior_mono htu p.2)⟩) =
      A.tileFacesMeetingRelativeSourceEmbed C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)
        (A.relativeOldTrianglePoint C hC N
          (alignedRelativeExtraLines A C hC N anchorLines) t
          ⟨p.1, interior_subset p.2⟩))
    (hqSource : A.tileFacesMeetingRelativeSourceEmbed C hC N
        (alignedRelativeExtraLines A C hC N anchorLines)
        (A.relativeOldTrianglePoint C hC N
          (alignedRelativeExtraLines A C hC N anchorLines) t
          ⟨p.1, interior_subset p.2⟩) =
      (K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).homeo q.1)
    (hparent : levelFaceParent K s.1 =
      A.relativeOldTriangleParent C hC N anchorLines u) :
    A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u p.1 =
      levelFaceParentPlaneAffine K s.1
        ((K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))).refined
          |>.facePlaneHomeomorph s.1 q).1 := by
  let Rlevel := K.safeSubdivision (A.commonLevel (A.tilesMeeting C hC))
  let pBase : {r : Plane // r ∈
      (A.tileFacesMeetingRelativeOldMesh C hC N anchorLines).triangleCarrier u.1} :=
    ⟨p.1, interior_subset (interior_mono htu p.2)⟩
  let z : standardTrianglePlaneComplex.support := Rlevel.refined.facePlaneHomeomorph s.1 q
  have hbase := A.relativeOldTriangleParentPlaneAffine_eq C hC N anchorLines u pBase
  have hlevel := levelFaceParentPlaneAffine_eq K s.1 z
  rw [K.facePlaneHomeomorph_val_eq_forwardAffine] at hbase hlevel
  have hqback : ((Rlevel.refined.facePlaneHomeomorph s.1).symm z).1 = q.1 :=
    congrArg Subtype.val ((Rlevel.refined.facePlaneHomeomorph s.1).symm_apply_apply q)
  have hlevel' : levelFaceParentPlaneAffine K s.1 z.1 =
      K.facePlaneForwardAffine (levelFaceParent K s.1) (Rlevel.homeo q.1).1 := by
    calc
      _ = K.facePlaneForwardAffine (levelFaceParent K s.1)
          (Rlevel.homeo ((Rlevel.refined.facePlaneHomeomorph s.1).symm z).1).1 := hlevel
      _ = _ := congrArg (K.facePlaneForwardAffine (levelFaceParent K s.1))
        (congrArg Subtype.val (congrArg Rlevel.homeo hqback))
  calc
    _ = K.facePlaneForwardAffine (A.relativeOldTriangleParent C hC N anchorLines u)
        (A.tileFacesMeetingRelativeSourceEmbed C hC N anchorLines
          (A.relativeOldTrianglePoint C hC N anchorLines u pBase)).1 := hbase
    _ = K.facePlaneForwardAffine (levelFaceParent K s.1) (Rlevel.homeo q.1).1 := by
      rw [hparent]
      exact congrArg (K.facePlaneForwardAffine
        (A.relativeOldTriangleParent C hC N anchorLines u))
        (congrArg Subtype.val (hsourceEq.trans hqSource))
    _ = _ := hlevel'.symm

private theorem exists_levelFace_of_alignedRelativeOldTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PartialTriangulation.PolygonalReplacementPresentation U V}
    (A : PartialTriangulation.PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh C hC N
      (alignedRelativeExtraLines A C hC N anchorLines)).Triangle) :
    ∃ s : {s : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
        s ∈ A.levelFaces (A.tilesMeeting C hC)},
      ∀ (p : Plane)
        (hp : p ∈ (A.tileFacesMeetingRelativeOldMesh C hC N
          (alignedRelativeExtraLines A C hC N anchorLines)).triangleCarrier t.1),
        A.tileFacesMeetingRelativeSourceEmbed C hC N
            (alignedRelativeExtraLines A C hC N anchorLines)
            (A.relativeOldTrianglePoint C hC N
              (alignedRelativeExtraLines A C hC N anchorLines) t ⟨p, hp⟩) ∈
          K.levelFaceCarrier s.1 := by
  classical
  let n := A.commonLevel (A.tilesMeeting C hC)
  let selectedLevelFaces := A.levelFaces (A.tilesMeeting C hC)
  let Rlevel := K.safeSubdivision n
  let baseOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N anchorLines
  let alignmentLines := A.relativeLevelAlignmentLines C hC N anchorLines n
  let extraLines := alignedRelativeExtraLines A C hC N anchorLines
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let J := A.tileFacePolygonMeeting C hC
  let source₁ := A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
  let localOldMesh := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  obtain ⟨u, s, htu, p, q, hsourceEq, hqSource, hparent⟩ :=
    exists_alignedRelativeOldTriangle_parentWitness A C hC N anchorLines t
  let F := A.relativeOldTriangleParentPlaneAffine C hC N anchorLines u
  let z : standardTrianglePlaneComplex.support :=
    Rlevel.refined.facePlaneHomeomorph s.1 q
  have hplaneAtP : F p.1 = levelFaceParentPlaneAffine K s.1 z.1 :=
    alignedRelativeOldTriangle_planeAt_parentWitness
      A C hC N anchorLines t u s htu p q hsourceEq hqSource hparent
  have hmono (k : Fin 3) :
      localOldMesh.IsMonochromatic
        ((levelFaceParentCoord K s.1 k).comp F) := by
    have haAlign :
        (levelFaceParentCoord K s.1 k).comp F ∈
          alignmentLines := by
      exact A.relativeLevelAlignmentLine_mem
        C hC N anchorLines n u s.1 hparent k
    have haExtra :
        (levelFaceParentCoord K s.1 k).comp F ∈
          extraLines :=
      List.mem_append_right _ haAlign
    have haLines :
        (levelFaceParentCoord K s.1 k).comp F ∈ lines :=
      List.mem_append_right _ haExtra
    have haAll :
        (levelFaceParentCoord K s.1 k).comp F ∈
          N.coordinateLines ++ lines :=
      List.mem_append_right _ haLines
    have hR :=
      (PolygonalFamily.arrangementMesh J
        ).refineByLines_isMonochromatic_of_mem
          (N.coordinateLines ++ lines) haAll
    intro w hw
    apply hR w
    exact
      (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
        J N lines (fun _ ↦ True)).mp hw |>.1
  have hcoordAtP (k : Fin 3) :
      0 <
        ((levelFaceParentCoord K s.1 k).comp F) p.1 := by
    let a := (levelFaceParentCoord K s.1 k).comp F
    have hnonneg : 0 ≤ a p.1 := by
      change 0 ≤ levelFaceParentCoord K s.1 k (F p.1)
      rw [hplaneAtP]
      exact levelFaceParentCoord_nonneg K s.1 k z
    rcases hmono k t.1 t.2 with hpos | hneg
    · have hsub :
          localOldMesh.triangleCarrier t.1 ⊆ {r | 0 ≤ a r} := by
        apply convexHull_min
        · rintro r ⟨v, hv, rfl⟩
          exact hpos v hv
        · exact ((convex_Ici (0 : ℝ)).affine_preimage a)
      have hpHalf := interior_mono hsub p.2
      rw [TriangleMesh.interior_affine_nonneg_of_surjective a
        (A.relativeLevelAlignmentLine_surjective
          C hC N anchorLines u s.1 k)] at hpHalf
      exact hpHalf
    · have hsub :
          localOldMesh.triangleCarrier t.1 ⊆ {r | a r ≤ 0} := by
        apply convexHull_min
        · rintro r ⟨v, hv, rfl⟩
          exact hneg v hv
        · exact ((convex_Iic (0 : ℝ)).affine_preimage a)
      have hpHalf := interior_mono hsub p.2
      rw [TriangleMesh.interior_affine_nonpos_of_surjective a
        (A.relativeLevelAlignmentLine_surjective
          C hC N anchorLines u s.1 k)] at hpHalf
      exact False.elim ((not_lt_of_ge hnonneg) hpHalf)
  exact ⟨s, alignedRelativeOldTriangle_source_mem_levelFace
    A C hC N anchorLines t u s p.1 p.2 htu hparent hmono hcoordAtP⟩


private structure CrossingWeldStraighteningContext
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (c : MoiseChart S)
    (T : PartialTriangulation S) (A : Set S) where
  C : Set S
  hCclosed : IsClosed C
  hAC : A ⊆ interior C
  hCT : C ⊆ interior T.support
  U : Set T.toIntrinsic.realization
  hU : IsOpen U
  V : Set Plane
  hV : IsOpen V
  Q : PartialTriangulation.PolygonalReplacementPresentation U V
  Qatlas : PartialTriangulation.PolygonalReplacementSourceAtlas T.toIntrinsic U V Q
  g' : U → c.kind.modelRegion
  g : T.toIntrinsic.realization → S
  hVsub : V ⊆ c.kind.perturbationRegion
  hVavoid : ∀ z : c.kind.modelRegion, (z : Plane) ∉ V → (c.chart.symm z).1 ∈ C
  hVprotected : ∀ y : T.chartOverlap c, T.embed y.1 ∈ C → T.chartOverlapMap c y ∉ V
  hUprotected : ∀ y : T.chartOverlap c, y.1 ∉ U → T.embed y.1 ∈ C
  hgcoord : ∀ y : U, (g' y : Plane) = (Q.sourceHomeomorph y).1.1
  hUsub : U ⊆ T.chartOverlap c
  hgval : ∀ y : U, g y.1 = (c.chart.symm (g' y)).1
  hgfix : ∀ x, T.embed x ∈ C → g x = T.embed x
  hgmatch : MatchesAtFrontier U g T.embed
  hgcont : ContinuousOn g U
  hginj : Set.InjOn g U
  hcross : Disjoint (g '' U) (T.embed '' Uᶜ)
  hembed : _root_.Topology.IsEmbedding (frontierGlue U g T.embed)
  hBoundaryPreservation : PreservesManifoldBoundary S (frontierGlue U g T.embed) T.embed

private noncomputable abbrev CrossingWeldStraighteningContext.adjusted
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S}
    {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : PartialTriangulation S :=
  T.replaceOnOpen W.U W.g W.hembed

private noncomputable def CrossingWeldStraighteningContext.remainder
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : Set S :=
  c.core \ interior W.adjusted.support

private noncomputable def CrossingWeldStraighteningContext.remainderToDomain
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : W.remainder → c.domain :=
  fun x ↦ ⟨x.1, c.core_subset_domain x.2.1⟩

private noncomputable def CrossingWeldStraighteningContext.remainderModel
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : W.remainder → c.kind.modelRegion :=
  fun x ↦ c.chart (W.remainderToDomain x)

private noncomputable def CrossingWeldStraighteningContext.remainderCoordinate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) : W.remainder → Plane :=
  fun x ↦ W.remainderModel x

-- The compact chart patch and its adaptive source neighborhood form the first persistent stage.
private structure CrossingWeldPatchContext
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (c : MoiseChart S) (T : PartialTriangulation S) (A : Set S) where
  straightening : CrossingWeldStraighteningContext S c T A
  N : TriangleMesh
  hN_V : N.toPlaneComplex.support ⊆ straightening.V
  hN_patch : N.toPlaneComplex.support ⊆ c.kind.patchComplex.support
  hRemainderInterior : Set.range straightening.remainderModel ⊆
    interior {p : c.kind.modelRegion | (p : Plane) ∈ N.toPlaneComplex.support}
  CN : Set straightening.V
  hCN_support : CN = {p : straightening.V | p.1 ∈ N.toPlaneComplex.support}
  hCNcompact : IsCompact CN
  hN_arrangement : N.toPlaneComplex.support ⊆
    (PolygonalFamily.arrangementMesh
      (straightening.Qatlas.tileFacePolygonMeeting CN hCNcompact)).toPlaneComplex.support
  hN_model : N.toPlaneComplex.support ⊆ c.kind.modelRegion
  hA_adjusted : A ⊆ interior straightening.adjusted.support

omit [ConnectedSpace S] in
private theorem exists_crossingWeldStraighteningContext
    (c : MoiseChart S) {T : PartialTriangulation S} {A : Set S}
    (hT : RadoInvariant T A)
    (hstraight : PartialTriangulation.BoundaryPreservingStraightening S T c) :
    Nonempty (CrossingWeldStraighteningContext S c T A) := by
  obtain ⟨C, hCclosed, hAC, hCT⟩ := hT.exists_closedBuffer
  obtain ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
      hUprotected, hgcoord, hUsub, hgval, hgfix, hgmatch, hgcont, hginj, hcross,
      hembed, hBoundaryPreservation⟩ :=
    hstraight C hCclosed
  exact ⟨⟨C, hCclosed, hAC, hCT, U, hU, V, hV, Q, Qatlas, g', g,
    hVsub, hVavoid, hVprotected, hUprotected, hgcoord, hUsub, hgval, hgfix,
    hgmatch, hgcont, hginj, hcross, hembed, hBoundaryPreservation⟩⟩

omit [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
-- A boundary-faithful chart core protected by the old support stays interior after the
-- frontier-glued straightening.  The two manifold strata require different local arguments.
private theorem chartCore_inter_protected_subset_interior_frontierGlue
    (c : MoiseChart S) (hc : c.BoundaryFaithful)
    (T : PartialTriangulation S) (C : Set S)
    (U : Set T.toIntrinsic.realization)
    (g : T.toIntrinsic.realization → S)
    (hCT : C ⊆ interior T.support)
    (hgfix : ∀ x, T.embed x ∈ C → g x = T.embed x)
    (hembed : _root_.Topology.IsEmbedding (frontierGlue U g T.embed))
    (hBoundaryPreservation : PreservesManifoldBoundary S
      (frontierGlue U g T.embed) T.embed) :
    c.core ∩ C ⊆ interior (Set.range (frontierGlue U g T.embed)) := by
  have hProtectedInteriorPoint :
      c.core ∩ C ∩
          (modelWithCornersEuclideanHalfSpace 2).interior S ⊆
        interior (Set.range (frontierGlue U g T.embed)) := by
    rintro x ⟨⟨hxCore, hxC⟩, hxi⟩
    apply
      T.subset_interior_range_frontierGlue_of_fixedOn_of_isInteriorPoint
        U g hembed (A := {x})
    · simpa only [Set.singleton_subset_iff] using hCT hxC
    · intro z hz
      have hzx : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact hxi
    · intro y hy
      apply hgfix y
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hxC
    · exact Set.mem_singleton x
  have hProtectedBoundaryPoint :
      c.core ∩ C ∩
          (modelWithCornersEuclideanHalfSpace 2).boundary S ⊆
        interior (Set.range (frontierGlue U g T.embed)) := by
    rintro x ⟨⟨hxCore, hxC⟩, hxBoundary⟩
    obtain ⟨y, hy⟩ := interior_subset (hCT hxC)
    change T.toIntrinsic.realization at y
    have hyFixed :
        frontierGlue U g T.embed y = T.embed y := by
      by_cases hyU : y ∈ U
      · rw [frontierGlue_of_mem hyU, hgfix y]
        simpa only [hy] using hxC
      · rw [frontierGlue_of_notMem hyU]
    cases hk : c.kind with
    | disk =>
        exact False.elim <|
          (hc.1 hk x (c.core_subset_domain hxCore)) hxBoundary
    | halfDisk =>
        have hmodel :
            c.kind.modelRegion = ChartKind.halfDisk.modelRegion := by
          rw [hk]
        let chartHalf :
            c.domain ≃ₜ ChartKind.halfDisk.modelRegion :=
          c.chart.trans (Homeomorph.setCongr hmodel)
        have hchartHalfBoundary :
            ∀ z (hz : z ∈ c.domain),
              z ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
                ((chartHalf ⟨z, hz⟩ : Plane) 0 = 0) := by
          intro z hz
          have h := hc.2 hk z hz
          have hcoord :
              (((Homeomorph.setCongr hmodel)
                (c.chart ⟨z, hz⟩) :
                  ChartKind.halfDisk.modelRegion) : Plane) =
                (c.chart ⟨z, hz⟩ : Plane) := by
            exact congrArg Subtype.val
              (Equiv.setCongr_apply hmodel (c.chart ⟨z, hz⟩))
          change
            z ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
              (((Homeomorph.setCongr hmodel)
                (c.chart ⟨z, hz⟩) :
                  ChartKind.halfDisk.modelRegion) : Plane) 0 = 0
          rw [hcoord]
          exact h
        have hopen :=
          mem_interior_range_of_fixed_boundary_preserving_in_halfDiskChart
            c.domain c.isOpen_domain
            chartHalf hchartHalfBoundary
            T.isEmbedding hembed hBoundaryPreservation
            (x := y) (by
              rw [hy]
              exact hCT hxC)
            (by
              rw [hy]
              exact c.core_subset_domain hxCore)
            hyFixed
        rwa [hy] at hopen
  rintro x ⟨hxCore, hxC⟩
  rcases
      (modelWithCornersEuclideanHalfSpace 2).isInteriorPoint_or_isBoundaryPoint x with
    hxi | hxb
  · exact hProtectedInteriorPoint ⟨⟨hxCore, hxC⟩, hxi⟩
  · exact hProtectedBoundaryPoint ⟨⟨hxCore, hxC⟩, hxb⟩

omit [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
-- A compact part of the chart model has a finite patch submesh whose relative interior covers it.
private theorem exists_patchSubmesh_covering_compact
    (c : MoiseChart S) (V : Set Plane) (D : Set c.kind.modelRegion)
    (hV : IsOpen V) (hDcompact : IsCompact D)
    (hDtarget : D ⊆
      {p : c.kind.modelRegion | (p : Plane) ∈ V} ∩
        interior {p : c.kind.modelRegion |
          (p : Plane) ∈ c.kind.patchComplex.support}) :
    ∃ N : TriangleMesh,
      N.toPlaneComplex.support ⊆ V ∧
      N.toPlaneComplex.support ⊆ c.kind.patchComplex.support ∧
      D ⊆ interior {p : c.kind.modelRegion |
        (p : Plane) ∈ N.toPlaneComplex.support} := by
  let Vmodel : Set c.kind.modelRegion := {p | (p : Plane) ∈ V}
  let patchModel : Set c.kind.modelRegion :=
    {p | (p : Plane) ∈ c.kind.patchComplex.support}
  have hVmodelOpen : IsOpen Vmodel :=
    hV.preimage continuous_subtype_val
  have htargetOpen : IsOpen (Vmodel ∩ interior patchModel) :=
    hVmodelOpen.inter isOpen_interior
  let : LocallyCompactSpace c.kind.modelRegion :=
    c.kind.modelRegionLocallyCompactSpace
  obtain ⟨E, hEcompact, hDinterior, hEtarget⟩ :=
    exists_compact_between hDcompact htargetOpen hDtarget
  let Ecoord : Set Plane := Subtype.val '' E
  have hEcoordCompact : IsCompact Ecoord :=
    hEcompact.image continuous_subtype_val
  have hEcoordPatch : Ecoord ⊆ c.kind.patchComplex.support := by
    rintro p ⟨q, hqE, rfl⟩
    have hqPatch : q ∈ patchModel :=
      interior_subset (hEtarget hqE).2
    exact hqPatch
  have hEcoordV : Ecoord ⊆ V := by
    rintro p ⟨q, hqE, rfl⟩
    exact (hEtarget hqE).1
  let L : c.kind.patchComplex.OpenSubmesh Ecoord V :=
    Classical.choice
      (c.kind.patchComplex.exists_openSubmesh c.kind.patchComplex_pure
        hEcoordCompact hEcoordPatch hV hEcoordV)
  refine ⟨L.mesh, L.contained, L.support_subset_original, ?_⟩
  apply hDinterior.trans
  apply interior_mono
  intro p hpE
  exact L.covers ⟨p, hpE, rfl⟩

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem exists_crossingWeldPatchContext
    (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {T : PartialTriangulation S} {A : Set S}
    (W : CrossingWeldStraighteningContext S c T A) :
    Nonempty (CrossingWeldPatchContext S c T A) := by
  classical
  let T₀ := W.adjusted
  have hA₀ : A ⊆ interior T₀.support := by
    change A ⊆ interior (Set.range (frontierGlue W.U W.g T.embed))
    exact T.subset_interior_range_frontierGlue_of_fixedOn W.U W.g W.hAC
      (W.hCT.trans interior_subset) W.hgfix
  have hProtectedCore : c.core ∩ W.C ⊆ interior T₀.support := by
    change c.core ∩ W.C ⊆ interior (Set.range (frontierGlue W.U W.g T.embed))
    exact chartCore_inter_protected_subset_interior_frontierGlue
      S c hc T W.C W.U W.g W.hCT W.hgfix W.hembed W.hBoundaryPreservation
  let D := W.remainder
  have hDcompact : IsCompact D :=
    c.isCompact_core.diff isOpen_interior
  let : CompactSpace D := isCompact_iff_compactSpace.mp hDcompact
  let dToDomain := W.remainderToDomain
  let dModel := W.remainderModel
  let dCoord := W.remainderCoordinate
  have hdCoord_cont : Continuous dCoord := by
    exact continuous_subtype_val.comp
      (c.chart.continuous.comp
        (Continuous.subtype_mk continuous_subtype_val _))
  let Dcoord : Set Plane := Set.range dCoord
  have hDcoordCompact : IsCompact Dcoord :=
    isCompact_range hdCoord_cont
  have hdModel_cont : Continuous dModel :=
    c.chart.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _)
  let Dmodel : Set c.kind.modelRegion := Set.range dModel
  have hDmodelCompact : IsCompact Dmodel :=
    isCompact_range hdModel_cont
  have hDcoordPatch : Dcoord ⊆ c.kind.patchComplex.support := by
    rintro p ⟨x, rfl⟩
    apply c.kind.modelCore_subset_patchComplex_support
    obtain ⟨hxDomain, hxCore⟩ := c.mem_core_iff.mp x.2.1
    have hdomain :
        (⟨x.1, hxDomain⟩ : c.domain) = dToDomain x :=
      Subtype.ext rfl
    simpa [dCoord, dModel, CrossingWeldStraighteningContext.remainderCoordinate,
      CrossingWeldStraighteningContext.remainderModel, hdomain] using hxCore
  have hDcoordV : Dcoord ⊆ W.V := by
    rintro p ⟨x, rfl⟩
    by_contra hpV
    have hxC : (c.chart.symm (c.chart (dToDomain x))).1 ∈ W.C := by
      apply W.hVavoid (c.chart (dToDomain x))
      simpa [dCoord, dModel, CrossingWeldStraighteningContext.remainderCoordinate,
        CrossingWeldStraighteningContext.remainderModel] using hpV
    have hxC' : x.1 ∈ W.C := by
      rw [c.chart.symm_apply_apply] at hxC
      have hdval : (dToDomain x).1 = x.1 := by
        rfl
      rwa [hdval] at hxC
    exact x.2.2 (hProtectedCore ⟨x.2.1, hxC'⟩)
  let Vmodel : Set c.kind.modelRegion := {p | (p : Plane) ∈ W.V}
  let patchModel : Set c.kind.modelRegion :=
    {p | (p : Plane) ∈ c.kind.patchComplex.support}
  have hDmodelTarget : Dmodel ⊆ Vmodel ∩ interior patchModel := by
    rintro p ⟨x, rfl⟩
    constructor
    · exact hDcoordV ⟨x, rfl⟩
    · apply c.kind.modelCore_subset_interior_patchInRegion
      obtain ⟨hxDomain, hxCore⟩ := c.mem_core_iff.mp x.2.1
      have hdomain :
          (⟨x.1, hxDomain⟩ : c.domain) = dToDomain x :=
        Subtype.ext rfl
      simpa [dModel, patchModel,
        CrossingWeldStraighteningContext.remainderModel, hdomain] using hxCore
  obtain ⟨N, hN_V, hN_patch, hDmodelInteriorN⟩ :=
    exists_patchSubmesh_covering_compact S c W.V Dmodel W.hV hDmodelCompact
      hDmodelTarget
  let CN : Set W.V := {p | p.1 ∈ N.toPlaneComplex.support}
  have hCNcompact : IsCompact CN := by
    apply _root_.Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      N.toPlaneComplex.isCompact_support
    intro p hp
    exact ⟨⟨p, hN_V hp⟩, rfl⟩
  have hN_arrangement :
      N.toPlaneComplex.support ⊆
        (PolygonalFamily.arrangementMesh
          (W.Qatlas.tileFacePolygonMeeting CN hCNcompact)).toPlaneComplex.support :=
    hN_patch.trans
      (PartialTriangulation.SynchronizedPatch.patchComplex_support_subset_arrangementMesh
        c.kind (W.Qatlas.tileFacePolygonMeeting CN hCNcompact))
  have hN_model : N.toPlaneComplex.support ⊆ c.kind.modelRegion :=
    hN_patch.trans c.kind.patchComplex_support_subset_modelRegion
  exact ⟨⟨W, N, hN_V, hN_patch, hDmodelInteriorN, CN, rfl, hCNcompact,
    hN_arrangement, hN_model, hA₀⟩⟩

private noncomputable def ChartInductionGeometry.n
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) : ℕ :=
  P.straightening.Qatlas.commonLevel
    (P.straightening.Qatlas.tilesMeeting P.CN P.hCNcompact)

private noncomputable def ChartInductionGeometry.subdivision
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) : T.toIntrinsic.Subdivision :=
  T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)

private noncomputable def ChartInductionGeometry.selectedFaces
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :=
  P.straightening.Qatlas.levelFaces
    (P.straightening.Qatlas.tilesMeeting P.CN P.hCNcompact)

private noncomputable def ChartInductionGeometry.extraLines
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ)) :=
  alignedRelativeExtraLines P.straightening.Qatlas P.CN P.hCNcompact
    P.N anchorLines

private noncomputable def ChartInductionGeometry.localComplex
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ)) :=
  P.straightening.Qatlas.tileFacesMeetingRelativeSourceComplex
    P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P anchorLines)

private noncomputable def ChartInductionGeometry.source
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ)) :
    (ChartInductionGeometry.localComplex P anchorLines).realization →
      T.toIntrinsic.realization :=
  P.straightening.Qatlas.tileFacesMeetingRelativeSourceEmbed
    P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P anchorLines)

@[simp]
private theorem ChartInductionGeometry.source_apply
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (anchorLines : List (Plane →ᵃ[ℝ] ℝ))
    (x : (ChartInductionGeometry.localComplex P anchorLines).realization) :
    ChartInductionGeometry.source P anchorLines x =
      P.straightening.Qatlas.tileFacesMeetingRelativeSourceEmbed
        P.CN P.hCNcompact P.N
          (ChartInductionGeometry.extraLines P anchorLines) x := rfl

private structure ChartInductionGeometry
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (c : MoiseChart S) (T : PartialTriangulation S) (A : Set S)
    (P : CrossingWeldPatchContext S c T A) where
  anchorLines : List (Plane →ᵃ[ℝ] ℝ)
  localFaceParent :
    (ChartInductionGeometry.localComplex P anchorLines).Face →
      {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
        s ∈ ChartInductionGeometry.selectedFaces P}
  localVertexPoint :
    (ChartInductionGeometry.localComplex P anchorLines).UsedVertex →
      (ChartInductionGeometry.subdivision P).refined.realization
  localVertexPoint_injective : Function.Injective localVertexPoint
  localVertex_source : ∀ u,
    ChartInductionGeometry.source P anchorLines
        ((ChartInductionGeometry.localComplex P anchorLines).vertexPoint u) =
      (ChartInductionGeometry.subdivision P).homeo (localVertexPoint u)
  source_injective : Function.Injective (ChartInductionGeometry.source P anchorLines)
  localFaceMap_val : ∀
      (t : (ChartInductionGeometry.localComplex P anchorLines).Face)
      (x : stdSimplex ℝ {v // v ∈ t.1}),
    ((ChartInductionGeometry.subdivision P).homeo.symm
      (ChartInductionGeometry.source P anchorLines
        ((ChartInductionGeometry.localComplex P anchorLines).faceStandardMap t x))).1 =
      ∑ v : {v // v ∈ t.1}, x v •
        (localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1
  source_range : Set.range (ChartInductionGeometry.source P anchorLines) =
    ⋃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
        s ∈ ChartInductionGeometry.selectedFaces P},
      T.toIntrinsic.levelFaceCarrier s.1
  subdivision_surface :
    (ChartInductionGeometry.subdivision P).refined.HasSurfaceEdgeValence

private abbrev ChartInductionGeometry.LevelAnchor
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :=
  Σ u : {u : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
      u ∈ ChartInductionGeometry.selectedFaces P},
    Sum {v // v ∈ u.1.1} (ZMod 3)

private noncomputable instance ChartInductionGeometry.levelAnchorFintype
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    Fintype (ChartInductionGeometry.LevelAnchor P) := by
  classical
  unfold ChartInductionGeometry.LevelAnchor
  infer_instance

private noncomputable def ChartInductionGeometry.anchorLevelPoint
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    ChartInductionGeometry.LevelAnchor P →
      (ChartInductionGeometry.subdivision P).refined.realization :=
  fun a ↦ match a.2 with
    | Sum.inl v => (ChartInductionGeometry.subdivision P).refined.facePoint a.1.1 v
    | Sum.inr i => (ChartInductionGeometry.subdivision P).refined.edgePath
        ((ChartInductionGeometry.subdivision P).refined.faceEdge a.1.1 i)
        ⟨1 / 2, by constructor <;> norm_num⟩

private noncomputable def ChartInductionGeometry.anchorSourcePoint
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    ChartInductionGeometry.LevelAnchor P → T.toIntrinsic.realization :=
  fun a ↦ (ChartInductionGeometry.subdivision P).homeo
    (ChartInductionGeometry.anchorLevelPoint P a)

private theorem ChartInductionGeometry.anchorSourcePoint_mem_selected
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (a : ChartInductionGeometry.LevelAnchor P) :
    ChartInductionGeometry.anchorSourcePoint P a ∈
      ⋃ u : {u : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
          u ∈ ChartInductionGeometry.selectedFaces P},
        T.toIntrinsic.levelFaceCarrier u.1 := by
  rcases a with ⟨s, v | i⟩
  · apply Set.mem_iUnion.mpr
    refine ⟨s, (ChartInductionGeometry.subdivision P).refined.facePoint s.1 v, ?_, rfl⟩
    exact (ChartInductionGeometry.subdivision P).refined.facePoint_mem_faceCarrier s.1 v
  · let edgeHalf : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
    have hedge : (ChartInductionGeometry.subdivision P).refined.edgePath
        ((ChartInductionGeometry.subdivision P).refined.faceEdge s.1 i) edgeHalf ∈
      (ChartInductionGeometry.subdivision P).refined.faceCarrier
        ((ChartInductionGeometry.subdivision P).refined.faceEdge s.1 i).1 := by
      rw [← (ChartInductionGeometry.subdivision P).refined.range_edgePath]
      exact ⟨edgeHalf, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨s, (ChartInductionGeometry.subdivision P).refined.edgePath
      ((ChartInductionGeometry.subdivision P).refined.faceEdge s.1 i) edgeHalf, ?_, rfl⟩
    intro v hv
    exact hedge v (fun hve ↦ hv
      ((ChartInductionGeometry.subdivision P).refined.faceEdge_subset_face s.1 i hve))

private theorem ChartInductionGeometry.anchorSourcePoint_mem_open
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (a : ChartInductionGeometry.LevelAnchor P) :
    ChartInductionGeometry.anchorSourcePoint P a ∈ P.straightening.U := by
  apply P.straightening.Qatlas.sourceTileFacesMeeting_subset_open P.CN P.hCNcompact
  rw [P.straightening.Qatlas.sourceTileFacesMeeting_eq_levelFaces P.CN P.hCNcompact]
  exact ChartInductionGeometry.anchorSourcePoint_mem_selected P a

private noncomputable def ChartInductionGeometry.anchorCoordinate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) : ChartInductionGeometry.LevelAnchor P → Plane :=
  fun a ↦ (P.straightening.Q.sourceHomeomorph
    ⟨ChartInductionGeometry.anchorSourcePoint P a,
      ChartInductionGeometry.anchorSourcePoint_mem_open P a⟩).1.1

private noncomputable def ChartInductionGeometry.canonicalAnchorLines
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) : List (Plane →ᵃ[ℝ] ℝ) :=
  PartialTriangulation.PolygonalReplacementSourceAtlas.coordinateAnchorLines
    (ChartInductionGeometry.anchorCoordinate P)

private noncomputable def ChartInductionGeometry.canonicalLocalFaceParent
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face) :
    {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
      s ∈ ChartInductionGeometry.selectedFaces P} :=
  Classical.choose (exists_levelFace_of_alignedRelativeOldTriangle
    P.straightening.Qatlas P.CN P.hCNcompact P.N
      (ChartInductionGeometry.canonicalAnchorLines P)
    (⟨t.1, t.2⟩ : (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
      P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
        (ChartInductionGeometry.canonicalAnchorLines P))).Triangle))

private theorem ChartInductionGeometry.canonicalLocalFaceParent_contains
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face)
    (p : Plane)
    (hp : p ∈ (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
      P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
        (ChartInductionGeometry.canonicalAnchorLines P))).triangleCarrier t.1) :
    ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)
        (P.straightening.Qatlas.relativeOldTrianglePoint P.CN P.hCNcompact P.N
          (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
          (⟨t.1, t.2⟩ : (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
            P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
              (ChartInductionGeometry.canonicalAnchorLines P))).Triangle) ⟨p, hp⟩) ∈
      T.toIntrinsic.levelFaceCarrier
        (ChartInductionGeometry.canonicalLocalFaceParent P t).1 :=
  Classical.choose_spec (exists_levelFace_of_alignedRelativeOldTriangle
    P.straightening.Qatlas P.CN P.hCNcompact P.N
      (ChartInductionGeometry.canonicalAnchorLines P)
      (⟨t.1, t.2⟩ : (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
        P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
          (ChartInductionGeometry.canonicalAnchorLines P))).Triangle)) p hp

private theorem ChartInductionGeometry.canonicalLocalFaceParent_contains_realization
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face)
    (x : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).realization)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P) x ∈
      T.toIntrinsic.levelFaceCarrier
        (ChartInductionGeometry.canonicalLocalFaceParent P t).1 := by
  let localOldMesh := P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
    P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
  let p : Plane := localOldMesh.coordinateEmbed x
  have hp : p ∈ localOldMesh.triangleCarrier t.1 := by
    apply localOldMesh.toPlaneComplex.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
  let y := P.straightening.Qatlas.relativeOldTrianglePoint P.CN P.hCNcompact P.N
    (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
    (⟨t.1, t.2⟩ : localOldMesh.Triangle) ⟨p, hp⟩
  have hyx : y = x := by
    apply localOldMesh.isEmbedding_coordinateEmbed.injective
    rw [P.straightening.Qatlas.relativeOldTrianglePoint_coordinateEmbed
      P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
      (⟨t.1, t.2⟩ : localOldMesh.Triangle) ⟨p, hp⟩]
  rw [← hyx]
  exact ChartInductionGeometry.canonicalLocalFaceParent_contains P t p hp

private noncomputable def ChartInductionGeometry.canonicalLocalVertexPoint
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).UsedVertex →
      (ChartInductionGeometry.subdivision P).refined.realization :=
  fun v ↦ (ChartInductionGeometry.subdivision P).homeo.symm
    (P.straightening.Qatlas.tileFacesMeetingRelativeSourceVertexPoint
      P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P)) v)

private theorem ChartInductionGeometry.canonicalLocalVertexPoint_mem_face
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face) (v : {v // v ∈ t.1}) :
    ChartInductionGeometry.canonicalLocalVertexPoint P ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
      (ChartInductionGeometry.subdivision P).refined.faceCarrier
        (ChartInductionGeometry.canonicalLocalFaceParent P t).1.1 := by
  let localComplex := ChartInductionGeometry.localComplex P
    (ChartInductionGeometry.canonicalAnchorLines P)
  let uv : localComplex.UsedVertex := ⟨v.1, ⟨t.1, t.2, v.2⟩⟩
  let xv : localComplex.realization := localComplex.vertexPoint uv
  have hxv : ∀ w ∉ t.1, xv.1 w = 0 := by
    intro w hw
    change Pi.single v.1 1 w = 0
    have hwv : w ≠ v.1 := fun h ↦ hw (h ▸ v.2)
    simp [hwv]
  obtain ⟨q, hq, hqeq⟩ :=
    ChartInductionGeometry.canonicalLocalFaceParent_contains_realization P t xv hxv
  have hlocal : (ChartInductionGeometry.subdivision P).homeo
      (ChartInductionGeometry.canonicalLocalVertexPoint P uv) =
        ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P) xv :=
    (ChartInductionGeometry.subdivision P).homeo.apply_symm_apply _
  have heq : ChartInductionGeometry.canonicalLocalVertexPoint P uv = q :=
    (ChartInductionGeometry.subdivision P).homeo.injective (hlocal.trans hqeq.symm)
  rwa [heq]

private theorem ChartInductionGeometry.canonicalSource_isEmbedding
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    _root_.Topology.IsEmbedding
      (ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)) :=
  P.straightening.Qatlas.isEmbedding_tileFacesMeetingRelativeSourceEmbed
    P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))

private theorem ChartInductionGeometry.canonicalLocalFaceMap_val
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face)
    (x : stdSimplex ℝ {v // v ∈ t.1}) :
    ((ChartInductionGeometry.subdivision P).homeo.symm
      (ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)
        ((ChartInductionGeometry.localComplex P
          (ChartInductionGeometry.canonicalAnchorLines P)).faceStandardMap t x))).1 =
      ∑ v : {v // v ∈ t.1}, x v •
        (ChartInductionGeometry.canonicalLocalVertexPoint P
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 := by
  let Rlevel := ChartInductionGeometry.subdivision P
  let localComplex := ChartInductionGeometry.localComplex P
    (ChartInductionGeometry.canonicalAnchorLines P)
  let source₁ := ChartInductionGeometry.source P
    (ChartInductionGeometry.canonicalAnchorLines P)
  let localVertexLevelPoint := ChartInductionGeometry.canonicalLocalVertexPoint P
  let localFaceLevelFace := ChartInductionGeometry.canonicalLocalFaceParent P
  apply subdivision_preimage_faceMap_eq_vertex_sum
    Rlevel source₁ localVertexLevelPoint (fun u ↦ (localFaceLevelFace u).1)
  · exact fun u ↦ Rlevel.homeo.apply_symm_apply _
  · exact ChartInductionGeometry.canonicalLocalVertexPoint_mem_face P
  · intro u y
    let yg : localComplex.realization := localComplex.faceStandardMap u y
    have hyg : ∀ v ∉ u.1, yg.1 v = 0 := by
      intro v hv
      rw [localComplex.faceStandardMap_val]
      exact extendFaceCoordinates_of_notMem u.1 y hv
    obtain ⟨q, hq, hqeq⟩ :=
      ChartInductionGeometry.canonicalLocalFaceParent_contains_realization P u yg hyg
    have hyq : Rlevel.homeo.symm (source₁ yg) = q := by
      change (T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)).homeo.symm
        (ChartInductionGeometry.source P
          (ChartInductionGeometry.canonicalAnchorLines P) yg) = q
      calc
        _ = (T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)).homeo.symm
            ((T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)).homeo q) :=
          congrArg
            (T.toIntrinsic.safeSubdivision (ChartInductionGeometry.n P)).homeo.symm hqeq.symm
        _ = q :=
          (T.toIntrinsic.safeSubdivision
            (ChartInductionGeometry.n P)).homeo.symm_apply_apply q
    rwa [hyq]
  · intro u y
    let yg : localComplex.realization := localComplex.faceStandardMap u y
    have hyg : ∀ v ∉ u.1, yg.1 v = 0 := by
      intro v hv
      rw [localComplex.faceStandardMap_val]
      exact extendFaceCoordinates_of_notMem u.1 y hv
    change (ChartInductionGeometry.source P
      (ChartInductionGeometry.canonicalAnchorLines P) yg).1 = _
    dsimp only [ChartInductionGeometry.source, source₁]
    rw [P.straightening.Qatlas.relativeSourceFaceMap_eq_vertex_sum
      P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
      (⟨u.1, u.2⟩ : (P.straightening.Qatlas.tileFacesMeetingRelativeOldMesh
        P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
          (ChartInductionGeometry.canonicalAnchorLines P))).Triangle) yg hyg]
    apply Finset.sum_congr rfl
    intro v _
    have hcoord : yg.1 v.1 = y v := by
      rw [show yg.1 = extendFaceCoordinates u.1 y from localComplex.faceStandardMap_val u y,
        extendFaceCoordinates_of_mem u.1 y v.2]
      exact congrArg y (Subtype.ext rfl)
    rw [hcoord]
    rfl

private theorem ChartInductionGeometry.canonicalLocalVertexPoint_injective
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) :
    Function.Injective (ChartInductionGeometry.canonicalLocalVertexPoint P) := by
  intro v w hvw
  let localComplex := ChartInductionGeometry.localComplex P
    (ChartInductionGeometry.canonicalAnchorLines P)
  apply localComplex.injective_vertexPoint
  apply (ChartInductionGeometry.canonicalSource_isEmbedding P).injective
  change P.straightening.Qatlas.tileFacesMeetingRelativeSourceVertexPoint
      P.CN P.hCNcompact P.N
        (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P)) v =
    P.straightening.Qatlas.tileFacesMeetingRelativeSourceVertexPoint
      P.CN P.hCNcompact P.N
        (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P)) w
  have h := congrArg (ChartInductionGeometry.subdivision P).homeo hvw
  simpa only [ChartInductionGeometry.canonicalLocalVertexPoint,
    (ChartInductionGeometry.subdivision P).homeo.apply_symm_apply] using h

private noncomputable def ChartInductionGeometry.canonical
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A) :
    ChartInductionGeometry S c T A P where
  anchorLines := ChartInductionGeometry.canonicalAnchorLines P
  localFaceParent := ChartInductionGeometry.canonicalLocalFaceParent P
  localVertexPoint := ChartInductionGeometry.canonicalLocalVertexPoint P
  localVertexPoint_injective := ChartInductionGeometry.canonicalLocalVertexPoint_injective P
  localVertex_source := fun _ ↦
    (ChartInductionGeometry.subdivision P).homeo.apply_symm_apply _ |>.symm
  source_injective := (ChartInductionGeometry.canonicalSource_isEmbedding P).injective
  localFaceMap_val := ChartInductionGeometry.canonicalLocalFaceMap_val P
  source_range := P.straightening.Qatlas.range_tileFacesMeetingRelativeSourceEmbed_eq_levelFaces
    P.CN P.hCNcompact P.N
      (ChartInductionGeometry.extraLines P (ChartInductionGeometry.canonicalAnchorLines P))
  subdivision_surface := by
    apply T.toIntrinsic.hasSurfaceEdgeValence_iteratedMidpointSubdivision
    exact fun e he ↦ hT.combSurface e he

private theorem ChartInductionGeometry.canonicalLocalFaceMap_simplexLineMap
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face)
    (x y : stdSimplex ℝ {v // v ∈ t.1}) (r : Set.Icc (0 : ℝ) 1) :
    ((ChartInductionGeometry.subdivision P).homeo.symm
      (ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)
        ((ChartInductionGeometry.localComplex P
          (ChartInductionGeometry.canonicalAnchorLines P)).faceStandardMap t
          (simplexLineMap x y r)))).1 =
      AffineMap.lineMap
        ((ChartInductionGeometry.subdivision P).homeo.symm
          (ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)
            ((ChartInductionGeometry.localComplex P
              (ChartInductionGeometry.canonicalAnchorLines P)).faceStandardMap t x))).1
        ((ChartInductionGeometry.subdivision P).homeo.symm
          (ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)
            ((ChartInductionGeometry.localComplex P
              (ChartInductionGeometry.canonicalAnchorLines P)).faceStandardMap t y))).1 r.1 := by
  rw [ChartInductionGeometry.canonicalLocalFaceMap_val P t (simplexLineMap x y r),
    ChartInductionGeometry.canonicalLocalFaceMap_val P t x,
    ChartInductionGeometry.canonicalLocalFaceMap_val P t y]
  funext k
  simp only [simplexLineMap, AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]
  change (∑ v, ((1 - r.1) * x v + r.1 * y v) *
      (ChartInductionGeometry.canonicalLocalVertexPoint P
        ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k) =
    (1 - r.1) * ∑ v, x v * (ChartInductionGeometry.canonicalLocalVertexPoint P
      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k +
    r.1 * ∑ v, y v * (ChartInductionGeometry.canonicalLocalVertexPoint P
      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k
  calc
    _ = ∑ v, ((1 - r.1) * (x v * (ChartInductionGeometry.canonicalLocalVertexPoint P
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k) +
        r.1 * (y v * (ChartInductionGeometry.canonicalLocalVertexPoint P
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k)) := by
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private theorem ChartInductionGeometry.canonicalLocalFaceMap_vertex
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (t : (ChartInductionGeometry.localComplex P
      (ChartInductionGeometry.canonicalAnchorLines P)).Face) (v : {v // v ∈ t.1}) :
    (ChartInductionGeometry.subdivision P).homeo.symm
      (ChartInductionGeometry.source P (ChartInductionGeometry.canonicalAnchorLines P)
        ((ChartInductionGeometry.localComplex P
          (ChartInductionGeometry.canonicalAnchorLines P)).faceStandardMap t
            (stdSimplex.vertex v))) =
      ChartInductionGeometry.canonicalLocalVertexPoint P
        ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ := by
  apply Subtype.ext
  rw [ChartInductionGeometry.canonicalLocalFaceMap_val]
  funext k
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    simp [stdSimplex.vertex, hw]
  · simp

private theorem ChartInductionGeometry.exists_canonicalLocalVertex_eq_anchor
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (a : ChartInductionGeometry.LevelAnchor P) :
    ∃ v : (ChartInductionGeometry.localComplex P
        (ChartInductionGeometry.canonicalAnchorLines P)).UsedVertex,
      P.straightening.Qatlas.tileFacesMeetingRelativeSourceVertexPoint
          P.CN P.hCNcompact P.N
          (ChartInductionGeometry.extraLines P
            (ChartInductionGeometry.canonicalAnchorLines P)) v =
        ChartInductionGeometry.anchorSourcePoint P a := by
  let Qatlas := P.straightening.Qatlas
  let Q := P.straightening.Q
  let anchorCoordinate := ChartInductionGeometry.anchorCoordinate P
  let anchorLines := ChartInductionGeometry.canonicalAnchorLines P
  let extraLines := ChartInductionGeometry.extraLines P anchorLines
  let lines := Qatlas.tileFaceMeetingLines P.CN P.hCNcompact P.N extraLines
  let J := Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact
  let localOldMesh := Qatlas.tileFacesMeetingRelativeOldMesh
    P.CN P.hCNcompact P.N extraLines
  have hAnchorCoordinateSupport : anchorCoordinate a ∈ localOldMesh.toPlaneComplex.support := by
    rw [Qatlas.tileFacesMeetingRelativeOldMesh_support P.CN P.hCNcompact P.N extraLines]
    have haSelected : ChartInductionGeometry.anchorSourcePoint P a ∈
        ⋃ f : Qatlas.TileFacesMeeting P.CN P.hCNcompact, Q.sourceFaceSet f.1 := by
      rw [Qatlas.sourceTileFacesMeeting_eq_levelFaces P.CN P.hCNcompact]
      exact ChartInductionGeometry.anchorSourcePoint_mem_selected P a
    rw [Qatlas.sourceTileFacesMeeting_eq_coordinatePreimage P.CN P.hCNcompact] at haSelected
    simpa only [anchorCoordinate, ChartInductionGeometry.anchorCoordinate] using haSelected.2
  have hmono (line : Plane →ᵃ[ℝ] ℝ) (hline : line ∈ anchorLines) :
      localOldMesh.IsMonochromatic line := by
    have hExtra : line ∈ extraLines := by
      apply List.mem_append_left
      apply List.mem_append_left
      exact hline
    have hAll : line ∈ P.N.coordinateLines ++ lines :=
      List.mem_append_right _ (List.mem_append_right _ hExtra)
    have hR := (PolygonalFamily.arrangementMesh J).refineByLines_isMonochromatic_of_mem
      (P.N.coordinateLines ++ lines) hAll
    intro t ht
    exact hR t ((PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
      J P.N lines (fun _ ↦ True)).mp ht).1
  have hVertical := hmono (BrokenLineData.verticalLine (anchorCoordinate a))
    (PartialTriangulation.PolygonalReplacementSourceAtlas.verticalLine_mem_coordinateAnchorLines
      anchorCoordinate a)
  have hHorizontal := hmono (BrokenLineData.horizontalLine (anchorCoordinate a))
    (horizontalLine_mem_coordinateAnchorLines anchorCoordinate a)
  obtain ⟨v, hvPosition, hvSimplex⟩ :=
    localOldMesh.exists_vertex_position_eq_of_monochromatic_coordinates
      (anchorCoordinate a) hAnchorCoordinateSupport hVertical hHorizontal
  obtain ⟨-, t, ht, hvt⟩ := localOldMesh.mem_faces_iff.mp hvSimplex
  let localComplex := ChartInductionGeometry.localComplex P anchorLines
  let v' : localComplex.UsedVertex := ⟨v, ⟨t, ht, hvt (by simp)⟩⟩
  refine ⟨v', ?_⟩
  let pLocal : P.straightening.U :=
    Qatlas.tileFacesMeetingRelativeSourceVertexPointInOpen
      P.CN P.hCNcompact P.N extraLines v'
  let pAnchor : P.straightening.U :=
    ⟨ChartInductionGeometry.anchorSourcePoint P a,
      ChartInductionGeometry.anchorSourcePoint_mem_open P a⟩
  have hcoordLocal : (Q.sourceHomeomorph pLocal).1.1 = localOldMesh.position v :=
    Qatlas.sourceHomeomorph_relativeSourceVertexPointInOpen
      P.CN P.hCNcompact P.N extraLines v'
  have hq : Q.sourceHomeomorph pLocal = Q.sourceHomeomorph pAnchor := by
    apply Subtype.ext
    apply Subtype.ext
    exact hcoordLocal.trans hvPosition
  exact congrArg Subtype.val (Q.sourceHomeomorph.injective hq)

private theorem ChartInductionGeometry.canonicalAnchor_mem_localVertexPoints
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (a : ChartInductionGeometry.LevelAnchor P) :
    ChartInductionGeometry.anchorLevelPoint P a ∈
      ((Finset.univ : Finset (ChartInductionGeometry.localComplex P
          (ChartInductionGeometry.canonicalAnchorLines P)).UsedVertex).image
        (ChartInductionGeometry.canonicalLocalVertexPoint P)) := by
  obtain ⟨v, hv⟩ := ChartInductionGeometry.exists_canonicalLocalVertex_eq_anchor P a
  apply Finset.mem_image.mpr
  refine ⟨v, Finset.mem_univ v, ?_⟩
  change (ChartInductionGeometry.subdivision P).homeo.symm
      (P.straightening.Qatlas.tileFacesMeetingRelativeSourceVertexPoint
        P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P
          (ChartInductionGeometry.canonicalAnchorLines P)) v) =
    ChartInductionGeometry.anchorLevelPoint P a
  rw [hv]
  exact (ChartInductionGeometry.subdivision P).homeo.symm_apply_apply _

/-- The source realization map stored by a chart-induction geometry certificate is injective. -/
private theorem ChartInductionGeometry.source_injective_of_geometry
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :
    Function.Injective (ChartInductionGeometry.source P G.anchorLines) :=
  G.source_injective

private noncomputable def ChartInductionGeometry.localVertexPoints
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :=
  (Finset.univ : Finset (ChartInductionGeometry.localComplex P G.anchorLines).UsedVertex
    ).image G.localVertexPoint

private noncomputable def ChartInductionGeometry.edgeMidpointPoints
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (_G : ChartInductionGeometry S c T A P) :=
  (Finset.univ : Finset (ChartInductionGeometry.subdivision P).refined.Edge).image
    (fun e ↦ (ChartInductionGeometry.subdivision P).refined.edgePath e
      ⟨1 / 2, by constructor <;> norm_num⟩)

private noncomputable def ChartInductionGeometry.marking
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :=
  IntrinsicTwoComplex.EdgeMarking.ofFinset
    (ChartInductionGeometry.subdivision P).refined
    (G.localVertexPoints ∪ G.edgeMidpointPoints)

@[reducible]
private noncomputable def ChartInductionGeometry.mixedData
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) : MixedLocalFanData where
  ambient := (ChartInductionGeometry.subdivision P).refined
  localComplex := ChartInductionGeometry.localComplex P G.anchorLines
  marking := G.marking
  isOutside := fun f ↦ f.1 ∉ ChartInductionGeometry.selectedFaces P
  isOutside_decidable := fun _ ↦ Classical.propDecidable _
  localVertexPoint := G.localVertexPoint
  localVertexPoint_injective := G.localVertexPoint_injective
  localFaceMap := fun t x ↦ (ChartInductionGeometry.subdivision P).homeo.symm
    (ChartInductionGeometry.source P G.anchorLines
      ((ChartInductionGeometry.localComplex P G.anchorLines).faceStandardMap t x))

private noncomputable def ChartInductionGeometry.lines
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :=
  P.straightening.Qatlas.tileFaceMeetingLines P.CN P.hCNcompact P.N
    (ChartInductionGeometry.extraLines P G.anchorLines)

private noncomputable def ChartInductionGeometry.targetMesh
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :=
  PartialTriangulation.RelativeSynchronizedTarget.newMesh
    (P.straightening.Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact)
    P.N G.lines

private noncomputable def ChartInductionGeometry.targetEmbed
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P) :
    GeometricRealization G.targetMesh.Vertex G.targetMesh.triangles → S :=
  PartialTriangulation.RelativeSynchronizedTarget.newSurfaceEmbed c
    (P.straightening.Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact)
    P.N G.lines P.hN_arrangement P.hN_model

private noncomputable def ChartInductionGeometry.mixedOldComplex
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P)
    (C : MixedLocalFanCertificate G.mixedData) := C.mixedOldComplex G.mixedData

private noncomputable def ChartInductionGeometry.oldEmbed
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (G : ChartInductionGeometry S c T A P)
    (C : MixedLocalFanCertificate G.mixedData) :
      (C.mixedOldComplex G.mixedData).compactIntrinsic.realization → S :=
  fun x ↦ P.straightening.adjusted.embed
    ((ChartInductionGeometry.subdivision P).homeo
      (G.mixedOldComplex C |>.compactEval x))

private structure ChartInductionFinishContext
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (c : MoiseChart S) (T : PartialTriangulation S) (A : Set S)
    (P : CrossingWeldPatchContext S c T A) where
  geometry : ChartInductionGeometry S c T A P
  chart_boundary : c.BoundaryFaithful
  triangulation_boundary : T.BoundaryFacewiseRegular
  certificate : MixedLocalFanCertificate geometry.mixedData
  fan_surface :
    geometry.marking.markedFanLocallyFiniteTriangleComplex.compactIntrinsic
      |>.HasSurfaceEdgeValence
  selectedFace_of_fanInterval_endpoints_local :
    ∀ (f : geometry.mixedData.OutsideFanFace),
      geometry.marking.edgeIntervalFirst
          ((ChartInductionGeometry.subdivision P).refined.faceEdge f.1.1 f.1.2.1)
          f.1.2.2 ∈ geometry.localVertexPoints →
      geometry.marking.edgeIntervalSecond
          ((ChartInductionGeometry.subdivision P).refined.faceEdge f.1.1 f.1.2.1)
          f.1.2.2 ∈ geometry.localVertexPoints →
      ∃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
          s ∈ ChartInductionGeometry.selectedFaces P},
        ((ChartInductionGeometry.subdivision P).refined.faceEdge
          f.1.1 f.1.2.1).1 ⊆ s.1.1

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_mixedOldComplex_support
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P) :
    (MixedLocalFanCertificate.mixedOldComplex
      F.geometry.mixedData F.certificate).support = Set.univ := by
  classical
  let G := F.geometry
  let M := G.mixedData
  let C := F.certificate
  let R := ChartInductionGeometry.subdivision P
  let selected := ChartInductionGeometry.selectedFaces P
  let source : M.localComplex.realization → T.toIntrinsic.realization :=
    ChartInductionGeometry.source P G.anchorLines
  let OutsideFace := M.OutsideFanFace
  let outsideMap (f : OutsideFace) :
      stdSimplex ℝ {v // v ∈ M.marking.globalFanFaceVertices f.1} →
        T.toIntrinsic.realization :=
    fun x ↦ R.homeo (M.marking.globalFanFaceMap f.1 x)
  let K := C.mixedOldComplex M
  have cover :
      Set.range source ∪ ⋃ f : OutsideFace, Set.range (outsideMap f) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    let q : R.refined.realization := R.homeo.symm p
    obtain ⟨t, ht, hqt⟩ := q.2.2
    let tf : R.refined.Face := ⟨t, ht⟩
    by_cases htSelected : tf ∈ selected
    · apply Set.mem_union_left
      change p ∈ Set.range (ChartInductionGeometry.source P G.anchorLines)
      rw [G.source_range]
      apply Set.mem_iUnion.mpr
      let u : {u : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
          u ∈ ChartInductionGeometry.selectedFaces P} := ⟨tf, htSelected⟩
      exact ⟨u, q, hqt, R.homeo.apply_symm_apply p⟩
    · apply Set.mem_union_right
      obtain ⟨i, j, x, hx⟩ :=
        M.marking.exists_fanFaceMap_eq_of_mem_faceCarrier tf hqt
      let f : M.marking.FanFace := ⟨tf, i, j⟩
      have hqRange : q ∈ Set.range (M.marking.globalFanFaceMap f) := by
        rw [M.marking.range_globalFanFaceMap f]
        exact ⟨x, hx⟩
      obtain ⟨y, hy⟩ := hqRange
      let fo : OutsideFace := ⟨f, htSelected⟩
      apply Set.mem_iUnion.mpr
      refine ⟨fo, y, ?_⟩
      change R.homeo (M.marking.globalFanFaceMap f y) = p
      rw [hy, R.homeo.apply_symm_apply]
  apply Set.eq_univ_of_forall
  intro p
  have hpCover :
      R.homeo p ∈ Set.range source ∪
        ⋃ f : OutsideFace, Set.range (outsideMap f) := by
    rw [cover]
    exact Set.mem_univ _
  rcases hpCover with hpLocal | hpFan
  · obtain ⟨z, hz⟩ := hpLocal
    obtain ⟨t, ht, hzt⟩ := z.2.2
    let tf : M.localComplex.Face := ⟨t, ht⟩
    let x₀ : stdSimplex ℝ {v // v ∈ tf.1} :=
      M.localComplex.restrictToFaceSimplex tf z hzt
    have hx₀ : M.localComplex.faceStandardMap tf x₀ = z :=
      M.localComplex.faceStandardMap_restrictToFaceSimplex tf z hzt
    obtain ⟨x₁, hx₁⟩ :=
      relabelUnivSimplex_surjective (M.localFaceOldVertexEmbedding tf) x₀
    obtain ⟨x₂, hx₂⟩ :=
      relabelUnivSimplex_surjective (M.mixedFaceUsedEmbedding (Sum.inl tf)) x₁
    change p ∈ ⋃ f, Set.range (M.mixedUsedFaceMap f)
    apply Set.mem_iUnion.mpr
    refine ⟨Sum.inl tf, x₂, ?_⟩
    change R.homeo.symm
      (source
        (M.localComplex.faceStandardMap tf
          (relabelUnivSimplex (M.localFaceOldVertexEmbedding tf)
            (relabelUnivSimplex (M.mixedFaceUsedEmbedding (Sum.inl tf)) x₂)))) = p
    rw [hx₂, hx₁, hx₀, hz, R.homeo.symm_apply_apply]
  · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hpFan
    obtain ⟨z, hz⟩ := hf
    have hz' : M.marking.globalFanFaceMap f.1 z = p := by
      apply R.homeo.injective
      exact hz
    obtain ⟨x₁, hx₁⟩ :=
      relabelFaceSimplex_surjective M.fanOldVertexEmbedding
        (M.marking.globalFanFaceVertices f.1) z
    obtain ⟨x₂, hx₂⟩ :=
      relabelUnivSimplex_surjective (M.mixedFaceUsedEmbedding (Sum.inr f)) x₁
    change p ∈ ⋃ f, Set.range (M.mixedUsedFaceMap f)
    apply Set.mem_iUnion.mpr
    refine ⟨Sum.inr f, x₂, ?_⟩
    change M.marking.globalFanFaceMap f.1
      (relabelFaceSimplex M.fanOldVertexEmbedding
        (M.marking.globalFanFaceVertices f.1)
        (relabelUnivSimplex (M.mixedFaceUsedEmbedding (Sum.inr f)) x₂)) = p
    rw [hx₂, hx₁, hz']

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_oldTarget_eq_implies_local
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P)
    (x : F.geometry.mixedOldComplex F.certificate |>.compactIntrinsic.realization)
    (y : GeometricRealization F.geometry.targetMesh.Vertex
      F.geometry.targetMesh.triangles)
    (hxy : F.geometry.oldEmbed F.certificate x = F.geometry.targetEmbed y) :
    ∃ z : F.geometry.mixedData.localComplex.realization,
      ChartInductionGeometry.source P F.geometry.anchorLines z =
          (ChartInductionGeometry.subdivision P).homeo
            (F.geometry.mixedOldComplex F.certificate |>.compactEval x) ∧
        z.1 = y.1 := by
  classical
  let G := F.geometry
  let M := G.mixedData
  let K := G.mixedOldComplex F.certificate
  let W := P.straightening
  let U := W.U
  let V := W.V
  let Q := W.Q
  let Qatlas := W.Qatlas
  let g' := W.g'
  let g := W.g
  let T₀ := W.adjusted
  let N := P.N
  let CN := P.CN
  let J := Qatlas.tileFacePolygonMeeting CN P.hCNcompact
  let R := ChartInductionGeometry.subdivision P
  let source : M.localComplex.realization → T.toIntrinsic.realization :=
    ChartInductionGeometry.source P G.anchorLines
  let lines := G.lines
  let e₂ := G.targetEmbed
  let e₁local := PartialTriangulation.RelativeSynchronizedTarget.oldSurfaceEmbed
    c J N lines (Qatlas.tileFacePolygonMeeting_closedRegion_subset_modelRegion
      c CN P.hCNcompact g' W.hgcoord)
  let q : T.toIntrinsic.realization := R.homeo (K.compactEval x)
  let p : Plane := G.targetMesh.coordinateEmbed y
  have hpNew : p ∈ G.targetMesh.toPlaneComplex.support := by
    rw [← G.targetMesh.range_coordinateEmbed]
    exact Set.mem_range_self y
  have hpN : p ∈ N.toPlaneComplex.support := by
    rw [ChartInductionGeometry.targetMesh] at hpNew
    rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
      J N lines P.hN_arrangement] at hpNew
    exact hpNew
  have hpV : p ∈ V := P.hN_V hpN
  have hqSurface : T₀.embed q = e₂ y := hxy
  have hqU : q ∈ U := by
    by_contra hqU
    have hqOld : T.embed q = e₂ y := by
      calc
        T.embed q = T₀.embed q := by
          change T.embed q = frontierGlue U g T.embed q
          rw [frontierGlue_of_notMem hqU]
        _ = e₂ y := hqSurface
    have hqDomain : T.embed q ∈ c.domain := by
      rw [hqOld]
      exact (c.chart.symm
        (G.targetMesh.coordinateEmbedInto c.kind.modelRegion (by
          rw [ChartInductionGeometry.targetMesh]
          rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
            J N lines P.hN_arrangement]
          exact P.hN_model) y)).2
    let qChart : T.chartOverlap c := ⟨q, hqDomain⟩
    have hqC : T.embed q ∈ W.C := W.hUprotected qChart hqU
    have hqNotV : T.chartOverlapMap c qChart ∉ V := W.hVprotected qChart hqC
    apply hqNotV
    have hdomain :
        T.chartOverlapToDomain c qChart =
          c.chart.symm
            (G.targetMesh.coordinateEmbedInto c.kind.modelRegion (by
              rw [ChartInductionGeometry.targetMesh]
              rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
                J N lines P.hN_arrangement]
              exact P.hN_model) y) := by
      apply Subtype.ext
      exact hqOld
    have hmodel := congrArg c.chart hdomain
    rw [c.chart.apply_symm_apply] at hmodel
    change T.chartOverlapMap c qChart ∈ V
    change ((c.chart (T.chartOverlapToDomain c qChart) :
      c.kind.modelRegion) : Plane) ∈ V
    rw [hmodel]
    exact hpV
  let qU : U := ⟨q, hqU⟩
  have hqTarget : g q = e₂ y := by
    calc
      g q = T₀.embed q := by
        change g q = frontierGlue U g T.embed q
        rw [frontierGlue_of_mem hqU]
      _ = e₂ y := hqSurface
  have hmodel :
      g' qU = G.targetMesh.coordinateEmbedInto c.kind.modelRegion (by
        rw [ChartInductionGeometry.targetMesh]
        rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
          J N lines P.hN_arrangement]
        exact P.hN_model) y := by
    apply c.chart.symm.injective
    apply Subtype.ext
    rw [← W.hgval qU]
    exact hqTarget
  have hqCN : (Q.sourceHomeomorph qU).1 ∈ CN := by
    change (Q.sourceHomeomorph qU).1 ∈ P.CN
    rw [P.hCN_support]
    change (Q.sourceHomeomorph qU).1.1 ∈ N.toPlaneComplex.support
    rw [← W.hgcoord qU]
    change (g' qU : Plane) ∈ N.toPlaneComplex.support
    rw [hmodel]
    exact hpN
  have hqSelected :
      q ∈ ⋃ f : Qatlas.TileFacesMeeting CN P.hCNcompact, Q.sourceFaceSet f.1 :=
    Qatlas.coordinatePreimage_subset_sourceTileFacesMeeting
      CN P.hCNcompact ⟨hqU, hqCN⟩
  rw [Qatlas.sourceTileFacesMeeting_eq_levelFaces CN P.hCNcompact] at hqSelected
  have hsourceRange := G.source_range
  simp only [ChartInductionGeometry.n, ChartInductionGeometry.selectedFaces] at hsourceRange
  rw [← hsourceRange] at hqSelected
  obtain ⟨z, hz⟩ := hqSelected
  refine ⟨z, hz, ?_⟩
  apply (PartialTriangulation.RelativeSynchronizedTarget.surfaceEmbed_eq_iff
    c J N lines P.hN_arrangement
      (Qatlas.tileFacePolygonMeeting_closedRegion_subset_modelRegion
        c CN P.hCNcompact g' W.hgcoord) P.hN_model z y).mp
  change e₁local z = e₂ y
  have hlocalOldEq : T₀.embed (source z) = e₁local z := by
    change frontierGlue U g T.embed (source z) = _
    rw [frontierGlue_of_mem]
    · let r : Q.complex.support :=
        Qatlas.tileFacesMeetingRelativeOldCoordinateSupport CN P.hCNcompact N
          (ChartInductionGeometry.extraLines P G.anchorLines) z
      let zU : U := ⟨source z, by
        exact (Q.sourceHomeomorph.symm r).2⟩
      have hzU : zU = Q.sourceHomeomorph.symm r := Subtype.ext rfl
      change W.g zU.1 = _
      rw [W.hgval zU]
      unfold e₁local
      apply congrArg Subtype.val
      apply congrArg c.chart.symm
      apply Subtype.ext
      rw [W.hgcoord zU, hzU, Q.sourceHomeomorph.apply_symm_apply]
      rfl
    · exact (Q.sourceHomeomorph.symm
        (Qatlas.tileFacesMeetingRelativeOldCoordinateSupport CN P.hCNcompact N
          (ChartInductionGeometry.extraLines P G.anchorLines) z)).2
  calc
    e₁local z = T₀.embed (source z) := hlocalOldEq.symm
    _ = T₀.embed q := congrArg T₀.embed hz
    _ = e₂ y := hqSurface

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_target_embedding
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P) :
    _root_.Topology.IsEmbedding F.geometry.targetEmbed := by
  unfold ChartInductionGeometry.targetEmbed
  exact PartialTriangulation.RelativeSynchronizedTarget.isEmbedding_newSurfaceEmbed
    c (P.straightening.Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact) P.N
      F.geometry.lines
      P.hN_arrangement P.hN_model

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_target_boundary
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P) :
    PartialTriangulation.BoundaryFacewiseRegularEmbedding
      F.geometry.targetMesh.triangles F.geometry.targetEmbed := by
  let G := F.geometry
  let J := P.straightening.Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact
  let lines := G.lines
  have hmeshModel : G.targetMesh.toPlaneComplex.support ⊆ c.kind.modelRegion := by
    rw [ChartInductionGeometry.targetMesh]
    rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
      J P.N lines P.hN_arrangement]
    exact P.hN_model
  apply PartialTriangulation.boundaryFacewiseRegularEmbedding_congr
    (PartialTriangulation.TriangleMesh.boundaryFacewiseRegularEmbedding_chart
      G.targetMesh c F.chart_boundary hmeshModel)
  intro x
  have heq :
      G.targetEmbed x =
        (c.chart.symm
          (G.targetMesh.coordinateEmbedInto c.kind.modelRegion hmeshModel x)).1 := by
    rfl
  rw [heq]

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_remainder_subset_target_interior
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P) :
    P.straightening.remainder ⊆ interior (Set.range F.geometry.targetEmbed) := by
  let G := F.geometry
  let J := P.straightening.Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact
  let lines := G.lines
  intro x hx
  let xD : P.straightening.remainder := ⟨x, hx⟩
  have hpInterior :
      P.straightening.remainderModel xD ∈
        interior {p : c.kind.modelRegion | (p : Plane) ∈ P.N.toPlaneComplex.support} :=
    P.hRemainderInterior ⟨xD, rfl⟩
  apply modelInterior_subset_interior_range_newSurfaceEmbed
    c J P.N lines P.hN_arrangement P.hN_model
  refine ⟨c.chart.symm (P.straightening.remainderModel xD),
    ⟨P.straightening.remainderModel xD, hpInterior, rfl⟩, ?_⟩
  change (c.chart.symm (c.chart (P.straightening.remainderToDomain xD))).1 = x
  rw [c.chart.symm_apply_apply]
  rfl

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_old_embedding
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P) :
    _root_.Topology.IsEmbedding (F.geometry.oldEmbed F.certificate) := by
  let G := F.geometry
  let K := G.mixedOldComplex F.certificate
  have heCompactEval : _root_.Topology.IsEmbedding K.compactEval :=
    (K.continuous_compactEval.isClosedEmbedding K.injective_compactEval).isEmbedding
  unfold ChartInductionGeometry.oldEmbed
  exact P.straightening.adjusted.isEmbedding.comp
    ((ChartInductionGeometry.subdivision P).homeo.isEmbedding.comp heCompactEval)

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_old_boundary
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P) :
    PartialTriangulation.BoundaryFacewiseRegularEmbedding
      (F.geometry.mixedOldComplex F.certificate).compactIntrinsic.faces
      (F.geometry.oldEmbed F.certificate) := by
  let G := F.geometry
  let M := G.mixedData
  let C := F.certificate
  let K := G.mixedOldComplex C
  let R := ChartInductionGeometry.subdivision P
  have hsupport : K.support = Set.univ :=
    chartInduction_mixedOldComplex_support (S := S) P F
  let mixedSubdivision : R.refined.Subdivision :=
    MixedLocalFanCertificate.mixedSubdivision M C hsupport
  have hRBoundary : (T.refine R).BoundaryFacewiseRegular :=
    PartialTriangulation.boundaryFacewiseRegular_refine
      T F.triangulation_boundary R
  have hMixedBoundary :
      ((T.refine R).refine mixedSubdivision).BoundaryFacewiseRegular :=
    PartialTriangulation.boundaryFacewiseRegular_refine
      (T.refine R) hRBoundary mixedSubdivision
  have hMixedBoundaryEmbedding :
      PartialTriangulation.BoundaryFacewiseRegularEmbedding
        K.compactIntrinsic.faces
        (fun x ↦ T.embed (R.homeo (K.compactEval x))) := by
    change PartialTriangulation.BoundaryFacewiseRegularEmbedding
      K.compactIntrinsic.faces (fun x ↦ T.embed (R.homeo (K.compactEval x)))
      at hMixedBoundary
    exact hMixedBoundary
  apply PartialTriangulation.boundaryFacewiseRegularEmbedding_congr
    hMixedBoundaryEmbedding
  intro x
  unfold ChartInductionGeometry.oldEmbed
  exact P.straightening.hBoundaryPreservation (R.homeo (K.compactEval x))

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_old_range
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P) :
    Set.range (F.geometry.oldEmbed F.certificate) =
      P.straightening.adjusted.support := by
  let G := F.geometry
  let K := G.mixedOldComplex F.certificate
  let R := ChartInductionGeometry.subdivision P
  have hsupport : K.support = Set.univ :=
    chartInduction_mixedOldComplex_support (S := S) P F
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨R.homeo (K.compactEval x), rfl⟩
  · rintro y ⟨q, rfl⟩
    let p : R.refined.realization := R.homeo.symm q
    have hp : p ∈ K.support := by
      rw [hsupport]
      exact Set.mem_univ _
    rw [← K.range_compactEval] at hp
    obtain ⟨x, hx⟩ := hp
    refine ⟨x, ?_⟩
    unfold ChartInductionGeometry.oldEmbed
    rw [hx]
    change P.straightening.adjusted.embed (R.homeo p) =
      P.straightening.adjusted.embed q
    rw [R.homeo.apply_symm_apply]

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_relabeled_certificate
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P)
    [DecidableEq F.geometry.mixedData.CommonVertex] :
    RelabeledWeldCertificate F.geometry.mixedData F.certificate
      F.geometry.targetMesh.triangles (F.geometry.oldEmbed F.certificate)
      F.geometry.targetEmbed := by
  exact exists_relabeledWeldCertificate
    F.geometry.mixedData F.certificate F.geometry.targetMesh.triangles
    (F.geometry.oldEmbed F.certificate) F.geometry.targetEmbed
    (chartInduction_old_embedding (S := S) P F)
    (chartInduction_target_embedding (S := S) P F)
    (chartInduction_old_boundary (S := S) P F)
    (chartInduction_target_boundary (S := S) P F)
    F.geometry.targetMesh.card_triangle

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_local_old_eq
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P)
    (z : F.geometry.mixedData.localComplex.realization) :
    P.straightening.adjusted.embed
        (ChartInductionGeometry.source P F.geometry.anchorLines z) =
      PartialTriangulation.RelativeSynchronizedTarget.oldSurfaceEmbed c
        (P.straightening.Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact)
        P.N F.geometry.lines
        (P.straightening.Qatlas.tileFacePolygonMeeting_closedRegion_subset_modelRegion
          c P.CN P.hCNcompact P.straightening.g' P.straightening.hgcoord) z := by
  let G := F.geometry
  let W := P.straightening
  let Q := W.Q
  let Qatlas := W.Qatlas
  let source := ChartInductionGeometry.source P G.anchorLines
  have hzU : source z ∈ W.U := by
    change
      (Q.sourceHomeomorph.symm
        (Qatlas.tileFacesMeetingRelativeOldCoordinateSupport
          P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P G.anchorLines) z)).1 ∈ W.U
    exact
      (Q.sourceHomeomorph.symm
        (Qatlas.tileFacesMeetingRelativeOldCoordinateSupport
          P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P G.anchorLines) z)).2
  change frontierGlue W.U W.g T.embed (source z) = _
  rw [frontierGlue_of_mem hzU]
  let q : Q.complex.support :=
    Qatlas.tileFacesMeetingRelativeOldCoordinateSupport
      P.CN P.hCNcompact P.N (ChartInductionGeometry.extraLines P G.anchorLines) z
  let zU : W.U := ⟨source z, hzU⟩
  have hzUq : zU = Q.sourceHomeomorph.symm q := Subtype.ext rfl
  change W.g zU.1 = _
  rw [W.hgval zU]
  apply congrArg Subtype.val
  apply congrArg c.chart.symm
  apply Subtype.ext
  rw [W.hgcoord zU, hzUq, Q.sourceHomeomorph.apply_symm_apply]
  rfl

private noncomputable def ChartInductionFinishContext.fanSelectionData
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    {P : CrossingWeldPatchContext S c T A}
    (F : ChartInductionFinishContext S c T A P) : MixedFanSelectionData F.geometry.mixedData := by
  classical
  let G := F.geometry
  let M := G.mixedData
  let R := ChartInductionGeometry.subdivision P
  exact {
    selectedSet := {p | R.homeo p ∈
      ⋃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
          s ∈ ChartInductionGeometry.selectedFaces P},
        T.toIntrinsic.levelFaceCarrier s.1}
    localVertex_mem_selected := by
      intro u
      change R.homeo (G.localVertexPoint u) ∈
        ⋃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
            s ∈ ChartInductionGeometry.selectedFaces P},
          T.toIntrinsic.levelFaceCarrier s.1
      rw [← G.source_range]
      refine ⟨M.localComplex.vertexPoint u, ?_⟩
      exact G.localVertex_source u
    baseEdge_mem_selected := by
      intro f p hp ⟨u₀, hu₀⟩ ⟨u₁, hu₁⟩
      have hfirstLocal :
          (M.marking.fanFirstVertex f.1).1 ∈ G.localVertexPoints := by
        rw [← hu₀]
        exact Finset.mem_image.mpr ⟨u₀, Finset.mem_univ u₀, rfl⟩
      have hsecondLocal :
          (M.marking.fanSecondVertex f.1).1 ∈ G.localVertexPoints := by
        rw [← hu₁]
        exact Finset.mem_image.mpr ⟨u₁, Finset.mem_univ u₁, rfl⟩
      obtain ⟨s, hes⟩ :=
        F.selectedFace_of_fanInterval_endpoints_local f hfirstLocal hsecondLocal
      apply Set.mem_iUnion.mpr
      refine ⟨s, p, ?_, rfl⟩
      intro v hv
      exact hp v (fun hve ↦ hv (hes hve)) }

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_selected_lift
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P)
    (p : F.geometry.mixedData.ambient.realization)
    (hp : p ∈ F.fanSelectionData.selectedSet) :
    ∃ z : F.geometry.mixedData.localComplex.realization,
      (ChartInductionGeometry.subdivision P).homeo.symm
        (ChartInductionGeometry.source P F.geometry.anchorLines z) = p := by
  let G := F.geometry
  let R := ChartInductionGeometry.subdivision P
  change R.homeo p ∈
    ⋃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
        s ∈ ChartInductionGeometry.selectedFaces P},
      T.toIntrinsic.levelFaceCarrier s.1 at hp
  rw [← G.source_range] at hp
  obtain ⟨z, hz⟩ := hp
  refine ⟨z, ?_⟩
  rw [hz, R.homeo.symm_apply_apply]

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_oldTarget_agree_of_evaluation
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P)
    [DecidableEq F.geometry.mixedData.CommonVertex]
    (xb : (F.geometry.mixedOldComplex F.certificate).compactIntrinsic.realization)
    (yb : GeometricRealization F.geometry.targetMesh.Vertex F.geometry.targetMesh.triangles)
    (z : F.geometry.mixedData.localComplex.realization)
    (heval : (F.geometry.mixedOldComplex F.certificate).compactEval xb =
      (ChartInductionGeometry.subdivision P).homeo.symm
        (ChartInductionGeometry.source P F.geometry.anchorLines z))
    (hcoords :
      (pushGeometricRealization F.certificate.oldCompactToCommon
          (F.geometry.mixedOldComplex F.certificate).compactIntrinsic.faces xb).1 =
        (pushGeometricRealization F.geometry.mixedData.targetToCommon
          F.geometry.targetMesh.triangles yb).1) :
    F.geometry.oldEmbed F.certificate xb = F.geometry.targetEmbed yb := by
  classical
  let G := F.geometry
  let M := G.mixedData
  let C := F.certificate
  let K := G.mixedOldComplex C
  let R := ChartInductionGeometry.subdivision P
  let source := ChartInductionGeometry.source P G.anchorLines
  let J := P.straightening.Qatlas.tileFacePolygonMeeting P.CN P.hCNcompact
  have hJmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion :=
    P.straightening.Qatlas.tileFacePolygonMeeting_closedRegion_subset_modelRegion
      c P.CN P.hCNcompact P.straightening.g' P.straightening.hgcoord
  let localMap := PartialTriangulation.RelativeSynchronizedTarget.oldSurfaceEmbed
    c J P.N G.lines hJmodel
  apply oldTarget_agree_of_local_evaluation
    K.compactEval (fun w ↦ R.homeo.symm (source w))
    (fun x ↦ (pushGeometricRealization C.oldCompactToCommon
      K.compactIntrinsic.faces x).1)
    (fun w ↦ (pushGeometricRealization M.targetToCommon M.localComplex.faces w).1)
    (fun y ↦ (pushGeometricRealization M.targetToCommon G.targetMesh.triangles y).1)
    (fun p ↦ P.straightening.adjusted.embed (R.homeo p))
    (G.oldEmbed C) localMap G.targetEmbed
  · exact K.injective_compactEval
  · intro x
    rfl
  · intro w
    rw [R.homeo.apply_symm_apply]
    exact chartInduction_local_old_eq (S := S) P F w
  · intro w
    obtain ⟨x, hxEval, hxCoord⟩ :=
      MixedLocalFanCertificate.exists_oldPoint_of_local
        M C (fun v ↦ R.homeo.symm (source v)) (fun _ _ ↦ rfl) w
    refine ⟨x, hxEval, ?_⟩
    exact (MixedLocalFanCertificate.hasLocalCommonCoordinates_iff M C x w).mp hxCoord
  · intro w y hpush
    have hwy : w.1 = y.1 :=
      val_eq_of_pushGeometricRealization_eq M.targetToCommon
        M.localComplex.faces G.targetMesh.triangles w y hpush
    unfold localMap ChartInductionGeometry.targetEmbed
    exact oldSurfaceEmbed_eq_newSurfaceEmbed_of_val_eq
      c J P.N G.lines P.hN_arrangement hJmodel P.hN_model w y hwy
  · exact heval
  · exact hcoords

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_relabel_agree
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P)
    [DecidableEq F.geometry.mixedData.CommonVertex] :
    ∀ (x : GeometricRealization F.geometry.mixedData.CommonVertex
        (F.certificate.relabelOldFaces F.geometry.mixedData))
      (y : GeometricRealization F.geometry.mixedData.CommonVertex
        (F.geometry.mixedData.relabelTargetFaces F.geometry.targetMesh.triangles)),
      x.1 = y.1 →
        F.certificate.relabelOldMap F.geometry.mixedData
            (F.geometry.oldEmbed F.certificate) x =
          F.geometry.mixedData.relabelTargetMap F.geometry.targetMesh.triangles
            F.geometry.targetEmbed y := by
  let G := F.geometry
  let M := G.mixedData
  let C := F.certificate
  let R := ChartInductionGeometry.subdivision P
  let source := ChartInductionGeometry.source P G.anchorLines
  intro x y hxy
  change
    (G.oldEmbed C ∘ (relabelGeometricRealizationHomeomorph C.oldCompactToCommon
      (G.mixedOldComplex C).compactIntrinsic.faces).symm) x =
    (G.targetEmbed ∘ (relabelGeometricRealizationHomeomorph M.targetToCommon
      G.targetMesh.triangles).symm) y
  exact MixedLocalFanCertificate.common_relabel_agree_small
    M C G.targetMesh.triangles (G.oldEmbed C) G.targetEmbed
    (fun tf xb yb hxb hcoords ↦
      MixedLocalFanCertificate.localFace_relabel_agree
        M C G.targetMesh.triangles
        (fun z ↦ R.homeo.symm (source z)) (fun _ _ ↦ rfl)
        (G.oldEmbed C) G.targetEmbed
        (chartInduction_oldTarget_agree_of_evaluation (S := S) P F)
        tf xb yb hxb hcoords)
    (fun f xb yb hxb hcoords ↦
      MixedLocalFanCertificate.fanFace_relabel_agree
        M C F.fanSelectionData G.targetMesh.triangles
        (fun z ↦ R.homeo.symm (source z))
        (chartInduction_selected_lift (S := S) P F)
        (G.oldEmbed C) G.targetEmbed
        (chartInduction_oldTarget_agree_of_evaluation (S := S) P F)
        f xb yb hxb hcoords)
    x y hxy

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem chartInduction_relabel_separate
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P)
    [DecidableEq F.geometry.mixedData.CommonVertex] :
    ∀ (x : GeometricRealization F.geometry.mixedData.CommonVertex
        (F.certificate.relabelOldFaces F.geometry.mixedData))
      (y : GeometricRealization F.geometry.mixedData.CommonVertex
        (F.geometry.mixedData.relabelTargetFaces F.geometry.targetMesh.triangles)),
      F.certificate.relabelOldMap F.geometry.mixedData
          (F.geometry.oldEmbed F.certificate) x =
        F.geometry.mixedData.relabelTargetMap F.geometry.targetMesh.triangles
          F.geometry.targetEmbed y →
      x.1 = y.1 := by
  let G := F.geometry
  let M := G.mixedData
  let C := F.certificate
  let K := G.mixedOldComplex C
  let R := ChartInductionGeometry.subdivision P
  let source : M.localComplex.realization → T.toIntrinsic.realization :=
    ChartInductionGeometry.source P G.anchorLines
  have heCompactEval : Function.Injective K.compactEval :=
    K.injective_compactEval
  apply relabeled_coordinates_eq_of_common_local
    K.compactIntrinsic.faces M.localComplex.faces G.targetMesh.triangles
    C.oldCompactToCommon M.targetToCommon (G.oldEmbed C) G.targetEmbed
    K.compactEval (fun z ↦ R.homeo.symm (source z)) heCompactEval
  · intro xb yb hbase
    obtain ⟨z, hz, hzy⟩ :=
      chartInduction_oldTarget_eq_implies_local (S := S) P F xb yb hbase
    refine ⟨z, ?_, hzy⟩
    change @Eq (ChartInductionGeometry.subdivision P).refined.realization
      ((F.geometry.mixedOldComplex F.certificate).compactEval xb)
      ((ChartInductionGeometry.subdivision P).homeo.symm
        (ChartInductionGeometry.source P F.geometry.anchorLines z))
    simpa only [(ChartInductionGeometry.subdivision P).homeo.symm_apply_apply] using
      (congrArg (ChartInductionGeometry.subdivision P).homeo.symm hz).symm
  · intro z
    obtain ⟨xz, hxzEval, hxzCoord⟩ :=
      MixedLocalFanCertificate.exists_oldPoint_of_local
        M C (fun w ↦ R.homeo.symm (source w)) (fun _ _ ↦ rfl) z
    refine ⟨xz, hxzEval, ?_⟩
    exact (MixedLocalFanCertificate.hasLocalCommonCoordinates_iff
      M C xz z).mp hxzCoord

omit [T2Space S] [ConnectedSpace S] [CompactSpace S] in
private theorem finish_crossing_weld
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A)
    (F : ChartInductionFinishContext S c T A P) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S) (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₁ e₁ ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₂ e₂ ∧
      A ∪ c.core ⊆ interior (Set.range e₁ ∪ Set.range e₂) := by
  classical
  let G := F.geometry
  let M := G.mixedData
  let C := F.certificate
  let cert := chartInduction_relabeled_certificate (S := S) P F
  refine ⟨M.CommonVertex, inferInstance, inferInstance,
    C.relabelOldFaces M, M.relabelTargetFaces G.targetMesh.triangles,
    C.relabelOldMap M (G.oldEmbed C),
    M.relabelTargetMap G.targetMesh.triangles G.targetEmbed,
    cert.card, cert.old_embedding, cert.target_embedding,
    chartInduction_relabel_agree (S := S) P F,
    chartInduction_relabel_separate (S := S) P F,
    cert.old_boundary, cert.target_boundary, ?_⟩
  rw [cert.range_old, cert.range_target, chartInduction_old_range (S := S) P F]
  exact union_subset_interior_union_of_diff_subset
    A c.core P.straightening.adjusted.support (Set.range G.targetEmbed)
    P.hA_adjusted (chartInduction_remainder_subset_target_interior (S := S) P F)



-- Opaque geometry and compatibility certificates keep this final assembly below the default
-- heartbeat budget without exposing the synchronized mesh construction to reduction.
private theorem edge_subset_face_of_halfpoint_mem
    (K : IntrinsicTwoComplex) (d : K.Edge) (s : Finset K.Vertex)
    (hmid : K.edgePath d ⟨1 / 2, by constructor <;> norm_num⟩ ∈ K.faceCarrier s) :
    d.1 ⊆ s := by
  intro v hv
  by_contra hvs
  have hzero : (K.edgePath d ⟨1 / 2, by constructor <;> norm_num⟩).1 v = 0 :=
    hmid v hvs
  have hpos : 0 < (K.edgePath d ⟨1 / 2, by constructor <;> norm_num⟩).1 v := by
    rw [K.edge_eq_pair d] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [K.edgePath_apply_first]
      norm_num
    · rw [K.edgePath_apply_second]
      norm_num
  linarith

private theorem ChartInductionGeometry.canonicalInterfaceEdgeMarks_subset_local
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A) :
    let G := ChartInductionGeometry.canonical P hT
    ∀ (s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
        s ∈ ChartInductionGeometry.selectedFaces P})
      (e : (ChartInductionGeometry.subdivision P).refined.Edge), e.1 ⊆ s.1.1 →
      ∀ p ∈ G.marking.edgeMarks e, p ∈ G.localVertexPoints := by
  classical
  dsimp only
  let G := ChartInductionGeometry.canonical P hT
  let R := ChartInductionGeometry.subdivision P
  intro s e hes p hp
  have hpData := (G.marking.mem_edgeMarks_iff e p).mp hp
  have hpPoints := hpData.1
  have hpEdge := hpData.2
  change p ∈ (G.localVertexPoints ∪ G.edgeMidpointPoints) ∪
      (Finset.univ : Finset R.refined.Edge).image R.refined.edgeFirstPoint ∪
        (Finset.univ : Finset R.refined.Edge).image R.refined.edgeSecondPoint at hpPoints
  rcases Finset.mem_union.mp hpPoints with hpLeft | hpSecond
  · rcases Finset.mem_union.mp hpLeft with hpPrimary | hpFirst
    · rcases Finset.mem_union.mp hpPrimary with hpLocal | hpMid
      · exact hpLocal
      · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpMid
        have hdSubset : d.1 ⊆ e.1 := by
          apply edge_subset_face_of_halfpoint_mem R.refined d e.1
          rw [hdp]
          exact hpEdge
        have hde : d = e := by
          apply Subtype.ext
          exact Finset.eq_of_subset_of_card_le hdSubset (by
            rw [R.refined.card_of_mem_edges d.2, R.refined.card_of_mem_edges e.2])
        subst d
        obtain ⟨i, hi⟩ := R.refined.exists_faceEdge_eq_of_subset s.1 e hes
        let a : ChartInductionGeometry.LevelAnchor P := ⟨s, Sum.inr i⟩
        have ha := ChartInductionGeometry.canonicalAnchor_mem_localVertexPoints P a
        have hpoint : ChartInductionGeometry.anchorLevelPoint P a =
            R.refined.edgePath e ⟨1 / 2, by constructor <;> norm_num⟩ := by
          change ChartInductionGeometry.anchorLevelPoint P ⟨s, Sum.inr i⟩ = _
          simp only [ChartInductionGeometry.anchorLevelPoint]
          rw [hi]
        rw [← hdp, ← hpoint]
        exact ha
    · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpFirst
      have hfirstEdge : R.refined.edgeFirst d ∈ e.1 := by
        let w := R.refined.edgeFirstUsed d
        exact (R.refined.vertexPoint_mem_faceCarrier_iff w e.1).mp (by
          rw [R.refined.vertexPoint_edgeFirstUsed d, hdp]
          exact hpEdge)
      let v : s.1.1 := ⟨R.refined.edgeFirst d, hes hfirstEdge⟩
      let a : ChartInductionGeometry.LevelAnchor P := ⟨s, Sum.inl v⟩
      have ha := ChartInductionGeometry.canonicalAnchor_mem_localVertexPoints P a
      have heq : R.refined.edgeFirstPoint d = R.refined.facePoint s.1 v := Subtype.ext rfl
      rw [← hdp, heq]
      exact ha
  · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpSecond
    have hsecondEdge : R.refined.edgeSecond d ∈ e.1 := by
      let w := R.refined.edgeSecondUsed d
      exact (R.refined.vertexPoint_mem_faceCarrier_iff w e.1).mp (by
        rw [R.refined.vertexPoint_edgeSecondUsed d, hdp]
        exact hpEdge)
    let v : s.1.1 := ⟨R.refined.edgeSecond d, hes hsecondEdge⟩
    let a : ChartInductionGeometry.LevelAnchor P := ⟨s, Sum.inl v⟩
    have ha := ChartInductionGeometry.canonicalAnchor_mem_localVertexPoints P a
    have heq : R.refined.edgeSecondPoint d = R.refined.facePoint s.1 v := Subtype.ext rfl
    rw [← hdp, heq]
    exact ha

private theorem ChartInductionGeometry.canonicalSelectedFace_marking_subset_local
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A) :
    let G := ChartInductionGeometry.canonical P hT
    ∀ (s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
        s ∈ ChartInductionGeometry.selectedFaces P})
      (p : (ChartInductionGeometry.subdivision P).refined.realization),
      p ∈ G.marking.points →
      p ∈ (ChartInductionGeometry.subdivision P).refined.faceCarrier s.1.1 →
      p ∈ G.localVertexPoints := by
  classical
  dsimp only
  let G := ChartInductionGeometry.canonical P hT
  let R := ChartInductionGeometry.subdivision P
  intro s p hpMark hpFace
  change p ∈ (G.localVertexPoints ∪ G.edgeMidpointPoints) ∪
      (Finset.univ : Finset R.refined.Edge).image R.refined.edgeFirstPoint ∪
        (Finset.univ : Finset R.refined.Edge).image R.refined.edgeSecondPoint at hpMark
  rcases Finset.mem_union.mp hpMark with hpLeft | hpSecond
  · rcases Finset.mem_union.mp hpLeft with hpPrimary | hpFirst
    · rcases Finset.mem_union.mp hpPrimary with hpLocal | hpMid
      · exact hpLocal
      · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpMid
        have hdSubset : d.1 ⊆ s.1.1 := by
          apply edge_subset_face_of_halfpoint_mem R.refined d s.1.1
          rw [hdp]
          exact hpFace
        obtain ⟨i, hi⟩ := R.refined.exists_faceEdge_eq_of_subset s.1 d hdSubset
        let a : ChartInductionGeometry.LevelAnchor P := ⟨s, Sum.inr i⟩
        have ha := ChartInductionGeometry.canonicalAnchor_mem_localVertexPoints P a
        have hpoint : ChartInductionGeometry.anchorLevelPoint P a =
            R.refined.edgePath d ⟨1 / 2, by constructor <;> norm_num⟩ := by
          change ChartInductionGeometry.anchorLevelPoint P ⟨s, Sum.inr i⟩ = _
          simp only [ChartInductionGeometry.anchorLevelPoint]
          rw [hi]
        rw [← hdp, ← hpoint]
        exact ha
    · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpFirst
      have hfirstFace : R.refined.edgeFirst d ∈ s.1.1 := by
        let w := R.refined.edgeFirstUsed d
        exact (R.refined.vertexPoint_mem_faceCarrier_iff w s.1.1).mp (by
          rw [R.refined.vertexPoint_edgeFirstUsed d, hdp]
          exact hpFace)
      let v : s.1.1 := ⟨R.refined.edgeFirst d, hfirstFace⟩
      let a : ChartInductionGeometry.LevelAnchor P := ⟨s, Sum.inl v⟩
      have ha := ChartInductionGeometry.canonicalAnchor_mem_localVertexPoints P a
      have heq : R.refined.edgeFirstPoint d = R.refined.facePoint s.1 v := Subtype.ext rfl
      rw [← hdp, heq]
      exact ha
  · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpSecond
    have hsecondFace : R.refined.edgeSecond d ∈ s.1.1 := by
      let w := R.refined.edgeSecondUsed d
      exact (R.refined.vertexPoint_mem_faceCarrier_iff w s.1.1).mp (by
        rw [R.refined.vertexPoint_edgeSecondUsed d, hdp]
        exact hpFace)
    let v : s.1.1 := ⟨R.refined.edgeSecond d, hsecondFace⟩
    let a : ChartInductionGeometry.LevelAnchor P := ⟨s, Sum.inl v⟩
    have ha := ChartInductionGeometry.canonicalAnchor_mem_localVertexPoints P a
    have heq : R.refined.edgeSecondPoint d = R.refined.facePoint s.1 v := Subtype.ext rfl
    rw [← hdp, heq]
    exact ha

private theorem edge_subset_face_of_open_edgePoint
    (K : IntrinsicTwoComplex) (e : K.Edge) (s : K.Face) (q : K.realization)
    (hqOpen : q ∈ K.edgePath e '' {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1})
    (hqFace : q ∈ K.faceCarrier s.1) : e.1 ⊆ s.1 := by
  rintro v hv
  obtain ⟨r, hr, hqr⟩ := hqOpen
  by_contra hvs
  have hzero : q.1 v = 0 := hqFace v hvs
  have hpositive : 0 < (K.edgePath e r).1 v := by
    rw [K.edge_eq_pair e] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [K.edgePath_apply_first]
      exact sub_pos.mpr hr.2
    · rw [K.edgePath_apply_second]
      exact hr.1
  rw [hqr] at hpositive
  linarith

private theorem ChartInductionGeometry.canonicalLocalMark_endpoint_or_selectedEdge
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A)
    (e : (ChartInductionGeometry.subdivision P).refined.Edge)
    (p : (ChartInductionGeometry.subdivision P).refined.realization)
    (hpEdge : p ∈ (ChartInductionGeometry.subdivision P).refined.faceCarrier e.1)
    (hpLocal : p ∈ (ChartInductionGeometry.canonical P hT).localVertexPoints) :
    (∃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
        s ∈ ChartInductionGeometry.selectedFaces P}, e.1 ⊆ s.1.1) ∨
      p = (ChartInductionGeometry.subdivision P).refined.edgeFirstPoint e ∨
      p = (ChartInductionGeometry.subdivision P).refined.edgeSecondPoint e := by
  classical
  let G := ChartInductionGeometry.canonical P hT
  let R := ChartInductionGeometry.subdivision P
  let localComplex := ChartInductionGeometry.localComplex P G.anchorLines
  obtain ⟨u, -, hup⟩ := Finset.mem_image.mp hpLocal
  obtain ⟨t, ht, hut⟩ := u.2
  let tf : localComplex.Face := ⟨t, ht⟩
  let uv : {v // v ∈ tf.1} := ⟨u.1, hut⟩
  have huFace : G.localVertexPoint u ∈ R.refined.faceCarrier (G.localFaceParent tf).1.1 := by
    have huv : (⟨uv.1, ⟨tf.1, tf.2, uv.2⟩⟩ : localComplex.UsedVertex) = u :=
      Subtype.ext rfl
    change ChartInductionGeometry.canonicalLocalVertexPoint P u ∈
      (ChartInductionGeometry.subdivision P).refined.faceCarrier
        (ChartInductionGeometry.canonicalLocalFaceParent P tf).1.1
    rw [← huv]
    exact ChartInductionGeometry.canonicalLocalVertexPoint_mem_face P tf uv
  have hpFace : p ∈ R.refined.faceCarrier (G.localFaceParent tf).1.1 := by
    rw [← hup]
    exact huFace
  by_cases hes : e.1 ⊆ (G.localFaceParent tf).1.1
  · exact Or.inl ⟨G.localFaceParent tf, hes⟩
  · let r := R.refined.edgeParameter e p hpEdge
    have hpath : R.refined.edgePath e r = p := R.refined.edgePath_edgeParameter e p hpEdge
    by_cases hr0 : r.1 = 0
    · exact Or.inr (Or.inl (calc
        p = R.refined.edgePath e r := hpath.symm
        _ = R.refined.edgePath e ⟨0, by simp⟩ := by
          apply congrArg (R.refined.edgePath e)
          exact Subtype.ext hr0
        _ = R.refined.edgeFirstPoint e := R.refined.edgePath_zero e))
    · by_cases hr1 : r.1 = 1
      · exact Or.inr (Or.inr (calc
          p = R.refined.edgePath e r := hpath.symm
          _ = R.refined.edgePath e ⟨1, by simp⟩ := by
            apply congrArg (R.refined.edgePath e)
            exact Subtype.ext hr1
          _ = R.refined.edgeSecondPoint e := R.refined.edgePath_one e))
      · have hrOpen : 0 < r.1 ∧ r.1 < 1 :=
          ⟨lt_of_le_of_ne r.2.1 (Ne.symm hr0), lt_of_le_of_ne r.2.2 hr1⟩
        exact (hes (edge_subset_face_of_open_edgePoint R.refined e
          (G.localFaceParent tf).1 p ⟨r, hrOpen, hpath⟩ hpFace)).elim

private theorem ChartInductionGeometry.canonicalSelectedFace_of_fanInterval_endpoints_local
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A) :
    let G := ChartInductionGeometry.canonical P hT
    ∀ (f : G.mixedData.OutsideFanFace),
      G.marking.edgeIntervalFirst
          ((ChartInductionGeometry.subdivision P).refined.faceEdge f.1.1 f.1.2.1)
          f.1.2.2 ∈ G.localVertexPoints →
      G.marking.edgeIntervalSecond
          ((ChartInductionGeometry.subdivision P).refined.faceEdge f.1.1 f.1.2.1)
          f.1.2.2 ∈ G.localVertexPoints →
      ∃ s : {s : T.toIntrinsic.LevelFace (ChartInductionGeometry.n P) //
          s ∈ ChartInductionGeometry.selectedFaces P},
        ((ChartInductionGeometry.subdivision P).refined.faceEdge f.1.1 f.1.2.1).1 ⊆
          s.1.1 := by
  classical
  dsimp only
  let G := ChartInductionGeometry.canonical P hT
  let R := ChartInductionGeometry.subdivision P
  intro f hp₀ hp₁
  let e := R.refined.faceEdge f.1.1 f.1.2.1
  let p₀ := G.marking.edgeIntervalFirst e f.1.2.2
  let p₁ := G.marking.edgeIntervalSecond e f.1.2.2
  have hp₀Edge : p₀ ∈ R.refined.faceCarrier e.1 :=
    G.marking.edgeIntervalFirst_mem_faceCarrier e f.1.2.2
  have hp₁Edge : p₁ ∈ R.refined.faceCarrier e.1 :=
    G.marking.edgeIntervalSecond_mem_faceCarrier e f.1.2.2
  rcases ChartInductionGeometry.canonicalLocalMark_endpoint_or_selectedEdge
      P hT e p₀ hp₀Edge hp₀ with hs | hp₀End
  · exact hs
  rcases ChartInductionGeometry.canonicalLocalMark_endpoint_or_selectedEdge
      P hT e p₁ hp₁Edge hp₁ with hs | hp₁End
  · exact hs
  have hparamPath (r : Set.Icc (0 : ℝ) 1) :
      G.marking.edgeParameterValue e (R.refined.edgePath e r) = r.1 := by
    rw [G.marking.edgeParameterValue_eq e (by
        rw [← R.refined.range_edgePath e]
        exact ⟨r, rfl⟩),
      R.refined.edgeParameter_eq_secondCoordinate, R.refined.edgePath_apply_second]
  have hfirstParam : G.marking.edgeParameterValue e (R.refined.edgeFirstPoint e) = 0 := by
    rw [← R.refined.edgePath_zero e, hparamPath]
  have hsecondParam : G.marking.edgeParameterValue e (R.refined.edgeSecondPoint e) = 1 := by
    rw [← R.refined.edgePath_one e, hparamPath]
  let edgeHalf : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
  have hmidPoint : R.refined.edgePath e edgeHalf ∈ G.marking.points := by
    apply IntrinsicTwoComplex.EdgeMarking.subset_points_ofFinset
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
  have hmidMark : R.refined.edgePath e edgeHalf ∈ G.marking.edgeMarks e := by
    rw [G.marking.mem_edgeMarks_iff e]
    refine ⟨hmidPoint, ?_⟩
    rw [← R.refined.range_edgePath e]
    exact ⟨edgeHalf, rfl⟩
  have hmidParam : G.marking.edgeParameterValue e
      (R.refined.edgePath e edgeHalf) = 1 / 2 := by rw [hparamPath]
  rcases hp₀End with hp₀First | hp₀Second <;>
    rcases hp₁End with hp₁First | hp₁Second
  · exact False.elim (G.marking.edgeIntervalFirst_ne_second e f.1.2.2
      (hp₀First.trans hp₁First.symm))
  · exfalso
    apply G.marking.not_edgeMark_parameter_mem_Ioo e f.1.2.2 hmidMark
    change G.marking.edgeParameterValue e (R.refined.edgePath e edgeHalf) ∈
      Set.Ioo (G.marking.edgeParameterValue e p₀) (G.marking.edgeParameterValue e p₁)
    rw [hp₀First, hp₁Second, hfirstParam, hsecondParam, hmidParam]
    norm_num
  · have hlt := G.marking.edgeInterval_parameter_lt e f.1.2.2
    change G.marking.edgeParameterValue e p₀ < G.marking.edgeParameterValue e p₁ at hlt
    rw [hp₀Second, hp₁First, hsecondParam, hfirstParam] at hlt
    norm_num at hlt
  · exact False.elim (G.marking.edgeIntervalFirst_ne_second e f.1.2.2
      (hp₀Second.trans hp₁Second.symm))

private structure MixedMapCertificate (M : MixedLocalFanData) where
  mixedOldFaceVertices_card : ∀ f : M.MixedOldFace, (M.mixedOldFaceVertices f).card = 3
  continuous_mixedOldFaceMap : ∀ f : M.MixedOldFace, Continuous (M.mixedOldFaceMap f)
  mixedOldFaceMap_val : ∀ (f : M.MixedOldFace)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f}),
    (M.mixedOldFaceMap f x).1 = fun k ↦ ∑ v : M.OldVertex,
      extendFaceCoordinates (M.mixedOldFaceVertices f) x v * v.1.1 k
  localMixedFaceMap_eq_iff : ∀ {t u : M.localComplex.Face}
      {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}}
      {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl u)}},
    M.mixedOldFaceMap (Sum.inl t) x = M.mixedOldFaceMap (Sum.inl u) y ↔
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl u)) y
  fanMixedFaceMap_eq_iff : ∀ {f g : M.OutsideFanFace}
      {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)}}
      {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr g)}},
    M.mixedOldFaceMap (Sum.inr f) x = M.mixedOldFaceMap (Sum.inr g) y ↔
      extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) x =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr g)) y
  mixedOldFaceMap_simplexLineMap : ∀ (f : M.MixedOldFace)
      (x y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f})
      (r : Set.Icc (0 : ℝ) 1),
    (M.mixedOldFaceMap f (simplexLineMap x y r)).1 =
      AffineMap.lineMap (M.mixedOldFaceMap f x).1 (M.mixedOldFaceMap f y).1 r.1
  mixedOldFaceMap_vertex : ∀ (f : M.MixedOldFace)
      (v : {v // v ∈ M.mixedOldFaceVertices f}),
    M.mixedOldFaceMap f (stdSimplex.vertex v) = v.1.1

private theorem exists_canonicalMixedMapCertificate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A) :
    Nonempty (MixedMapCertificate (ChartInductionGeometry.canonical P hT).mixedData) := by
  classical
  let geometry : ChartInductionGeometry S c T A P :=
    ChartInductionGeometry.canonical P hT
  let Rlevel := ChartInductionGeometry.subdivision P
  let selectedLevelFaces := ChartInductionGeometry.selectedFaces P
  let source₁ := ChartInductionGeometry.source P geometry.anchorLines
  have hsource₁Embedding : _root_.Topology.IsEmbedding source₁ :=
    ChartInductionGeometry.canonicalSource_isEmbedding P
  let localSourceComplex := ChartInductionGeometry.localComplex P geometry.anchorLines
  let localFaceLevelFace := geometry.localFaceParent
  have localFaceLevelFace_contains_realization :=
    ChartInductionGeometry.canonicalLocalFaceParent_contains_realization P
  let localVertexLevelPoint := geometry.localVertexPoint
  have localVertexLevelPoint_mem_face :=
    ChartInductionGeometry.canonicalLocalVertexPoint_mem_face P
  have localFaceLevelMap_val := geometry.localFaceMap_val
  have localFaceLevelMap_simplexLineMap :=
    ChartInductionGeometry.canonicalLocalFaceMap_simplexLineMap P
  have localFaceLevelMap_vertex := ChartInductionGeometry.canonicalLocalFaceMap_vertex P
  let localVertexLevelPoints := geometry.localVertexPoints
  let boundaryMarking := geometry.marking
  let OutsideFanFace := {f : boundaryMarking.FanFace // f.1 ∉ selectedLevelFaces}
  have interfaceEdgeMarks_subset_local :=
    ChartInductionGeometry.canonicalInterfaceEdgeMarks_subset_local P hT
  have selectedFace_marking_subset_local :=
    ChartInductionGeometry.canonicalSelectedFace_marking_subset_local P hT
  let mixedData : MixedLocalFanData := geometry.mixedData
  let oldVertexPoints := mixedData.oldVertexPoints
  let OldVertex := mixedData.OldVertex
  let localOldVertexEmbedding := mixedData.localOldVertexEmbedding
  let fanOldVertexEmbedding := mixedData.fanOldVertexEmbedding
  let localFaceOldVertexEmbedding := mixedData.localFaceOldVertexEmbedding
  let MixedOldFace := mixedData.MixedOldFace
  let mixedOldFaceVertices := mixedData.mixedOldFaceVertices
  let mixedOldFaceMap := mixedData.mixedOldFaceMap
  have mixedOldFaceVertices_card (f : MixedOldFace) :
      (mixedOldFaceVertices f).card = 3 :=
    mixedData.mixedOldFaceVertices_card_three f
  have continuous_mixedOldFaceMap (f : MixedOldFace) :
      Continuous (mixedOldFaceMap f) := by
    rcases f with t | f
    · exact Rlevel.homeo.symm.continuous.comp
        (hsource₁Embedding.continuous.comp
          (localSourceComplex.continuous_faceStandardMap t |>.comp
            (stdSimplex.continuous_map
              (univMapSubtypeEquiv
                (localFaceOldVertexEmbedding t)))))
    · exact boundaryMarking.continuous_globalFanFaceMap f.1 |>.comp
        (stdSimplex.continuous_map
          (finsetMapSubtypeEquiv fanOldVertexEmbedding
            (boundaryMarking.globalFanFaceVertices f.1)).symm)
  have localMixedExtended_apply
      (t : localSourceComplex.Face)
      (x : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inl t)})
      (u : localSourceComplex.UsedVertex) :
      extendFaceCoordinates
          (mixedOldFaceVertices (Sum.inl t)) x
          (localOldVertexEmbedding u) =
        extendFaceCoordinates t.1
          (relabelUnivSimplex
            (localFaceOldVertexEmbedding t) x) u.1 :=
    mixedData.localMixedExtended_apply t x u
  have localMixedFaceMap_eq_iff
      {t u : localSourceComplex.Face}
      {x : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inl t)}}
      {y : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inl u)}} :
      mixedOldFaceMap (Sum.inl t) x =
          mixedOldFaceMap (Sum.inl u) y ↔
        extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inl t)) x =
          extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inl u)) y := by
    apply mixedData.localMixedFaceMap_eq_iff_of_local
    intro t u x y
    change
      (Rlevel.homeo.symm ∘
          ChartInductionGeometry.source P geometry.anchorLines)
          (mixedData.localComplex.faceStandardMap t x) =
        (Rlevel.homeo.symm ∘
          ChartInductionGeometry.source P geometry.anchorLines)
          (mixedData.localComplex.faceStandardMap u y) ↔ _
    exact faceStandardMap_comp_eq_iff mixedData.localComplex
      (Rlevel.homeo.symm ∘ ChartInductionGeometry.source P geometry.anchorLines)
      (Rlevel.homeo.symm.injective.comp geometry.source_injective)
  have fanMixedFaceMap_eq_iff
      {f g : OutsideFanFace}
      {x : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inr f)}}
      {y : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inr g)}} :
      mixedOldFaceMap (Sum.inr f) x =
          mixedOldFaceMap (Sum.inr g) y ↔
        extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inr f)) x =
          extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inr g)) y := by
    change
      boundaryMarking.globalFanFaceMap f.1
          (relabelFaceSimplex fanOldVertexEmbedding
            (boundaryMarking.globalFanFaceVertices f.1) x) =
        boundaryMarking.globalFanFaceMap g.1
          (relabelFaceSimplex fanOldVertexEmbedding
            (boundaryMarking.globalFanFaceVertices g.1) y) ↔ _
    rw [boundaryMarking.globalFanFaceMap_eq_iff]
    exact relabelFaceSimplex_extended_eq_iff
      fanOldVertexEmbedding
  have mixedOldFaceMap_val
      (f : MixedOldFace)
      (x : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f}) :
      (mixedOldFaceMap f x).1 =
        fun k ↦ ∑ v : OldVertex,
          extendFaceCoordinates (mixedOldFaceVertices f) x v *
            v.1.1 k :=
    mixedData.mixedOldFaceMap_val_of_local geometry.localFaceMap_val f x
  let mixedFaceSimplexLineMap
      (f : MixedOldFace)
      (x y : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f})
      (r : Set.Icc (0 : ℝ) 1) :
      stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f} :=
    simplexLineMap x y r
  have extend_mixedFaceSimplexLineMap
      (f : MixedOldFace)
      (x y : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f})
      (r : Set.Icc (0 : ℝ) 1) :
      extendFaceCoordinates (mixedOldFaceVertices f)
          (mixedFaceSimplexLineMap f x y r) =
        (1 - r.1) •
            extendFaceCoordinates (mixedOldFaceVertices f) x +
          r.1 •
            extendFaceCoordinates (mixedOldFaceVertices f) y := by
    exact extendFaceCoordinates_simplexLineMap
      (mixedOldFaceVertices f) x y r
  have mixedOldFaceMap_simplexLineMap
      (f : MixedOldFace)
      (x y : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f})
      (r : Set.Icc (0 : ℝ) 1) :
      (mixedOldFaceMap f (mixedFaceSimplexLineMap f x y r)).1 =
        AffineMap.lineMap
          (mixedOldFaceMap f x).1 (mixedOldFaceMap f y).1 r.1 := by
    rw [mixedOldFaceMap_val,
      extend_mixedFaceSimplexLineMap,
      mixedOldFaceMap_val, mixedOldFaceMap_val]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      AffineMap.lineMap_apply_module]
    calc
      (∑ v,
          ((1 - r.1) *
                extendFaceCoordinates (mixedOldFaceVertices f) x v +
              r.1 *
                extendFaceCoordinates (mixedOldFaceVertices f) y v) *
            v.1.1 k) =
          ∑ v,
            ((1 - r.1) *
                (extendFaceCoordinates
                    (mixedOldFaceVertices f) x v * v.1.1 k) +
              r.1 *
                (extendFaceCoordinates
                    (mixedOldFaceVertices f) y v * v.1.1 k)) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have extend_mixedOldFace_vertex
      (f : MixedOldFace)
      (v : {v // v ∈ mixedOldFaceVertices f}) :
      extendFaceCoordinates (mixedOldFaceVertices f)
          (stdSimplex.vertex v) =
        Pi.single v.1 1 :=
    extendFaceCoordinates_vertex (mixedOldFaceVertices f) v
  have mixedOldFaceMap_vertex
      (f : MixedOldFace)
      (v : {v // v ∈ mixedOldFaceVertices f}) :
      mixedOldFaceMap f (stdSimplex.vertex v) = v.1.1 := by
    apply Subtype.ext
    rw [mixedOldFaceMap_val]
    exact barycentricVertex_sum
      (mixedOldFaceVertices f) v (fun w k ↦ w.1.1 k)
  exact ⟨⟨mixedOldFaceVertices_card, continuous_mixedOldFaceMap, mixedOldFaceMap_val,
    localMixedFaceMap_eq_iff, fanMixedFaceMap_eq_iff,
    mixedOldFaceMap_simplexLineMap, mixedOldFaceMap_vertex⟩⟩

private theorem MixedMapCertificate.localExtended_eq_single
    {M : MixedLocalFanData} (C : MixedMapCertificate M)
    (t : M.localComplex.Face)
    (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)})
    (u : M.localComplex.UsedVertex)
    (hxu : M.mixedOldFaceMap (Sum.inl t) x = M.localVertexPoint u) :
    extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
      Pi.single (M.localOldVertexEmbedding u) 1 := by
  let tu : M.localComplex.Face :=
    ⟨Classical.choose u.2, (Classical.choose_spec u.2).1⟩
  let uv : {v // v ∈ tu.1} :=
    ⟨u.1, (Classical.choose_spec u.2).2⟩
  have huv : M.localFaceOldVertexEmbedding tu uv = M.localOldVertexEmbedding u := by
    apply Subtype.ext
    rfl
  have huMem : M.localOldVertexEmbedding u ∈
      M.mixedOldFaceVertices (Sum.inl tu) := by
    change M.localOldVertexEmbedding u ∈
      (Finset.univ : Finset {v // v ∈ tu.1}).map
        (M.localFaceOldVertexEmbedding tu)
    rw [← huv]
    exact mem_map_univ (M.localFaceOldVertexEmbedding tu) uv
  let w : {v // v ∈ M.mixedOldFaceVertices (Sum.inl tu)} :=
    ⟨M.localOldVertexEmbedding u, huMem⟩
  have hmapw : M.mixedOldFaceMap (Sum.inl tu) (stdSimplex.vertex w) =
      M.localVertexPoint u := by
    calc
      M.mixedOldFaceMap (Sum.inl tu) (stdSimplex.vertex w) =
          w.1.1 := C.mixedOldFaceMap_vertex (Sum.inl tu) w
      _ = M.localVertexPoint u := rfl
  have hcoords := C.localMixedFaceMap_eq_iff.mp (hxu.trans hmapw.symm)
  calc
    extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl t)) x =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inl tu))
          (stdSimplex.vertex w) := hcoords
    _ = Pi.single w.1 1 :=
      extendFaceCoordinates_vertex (M.mixedOldFaceVertices (Sum.inl tu)) w
    _ = Pi.single (M.localOldVertexEmbedding u) 1 := by rfl

private theorem MixedMapCertificate.fanExtended_eq_single
    {M : MixedLocalFanData} (C : MixedMapCertificate M)
    (f : M.OutsideFanFace)
    (y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)})
    (v : {p // p ∈ M.marking.fanFaceVertices f.1})
    (hyv : M.mixedOldFaceMap (Sum.inr f) y = v.1) :
    extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y =
      Pi.single
        (M.fanOldVertexEmbedding (M.marking.fanVertexEmbedding f.1 v)) 1 := by
  let gv : M.marking.FanVertex := M.marking.fanVertexEmbedding f.1 v
  have hgvMem : gv ∈ M.marking.globalFanFaceVertices f.1 :=
    fanVertexEmbedding_mem_globalFanFaceVertices M.marking f.1 v
  have hOldMem : M.fanOldVertexEmbedding gv ∈
      M.mixedOldFaceVertices (Sum.inr f) := by
    change M.fanOldVertexEmbedding gv ∈
      (M.marking.globalFanFaceVertices f.1).map M.fanOldVertexEmbedding
    exact mem_finset_map M.fanOldVertexEmbedding _ hgvMem
  let w : {v // v ∈ M.mixedOldFaceVertices (Sum.inr f)} :=
    ⟨M.fanOldVertexEmbedding gv, hOldMem⟩
  have hmapw : M.mixedOldFaceMap (Sum.inr f) (stdSimplex.vertex w) = v.1 := by
    calc
      M.mixedOldFaceMap (Sum.inr f) (stdSimplex.vertex w) =
          w.1.1 := C.mixedOldFaceMap_vertex (Sum.inr f) w
      _ = v.1 := rfl
  have hcoords := C.fanMixedFaceMap_eq_iff.mp (hyv.trans hmapw.symm)
  calc
    extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f)) y =
        extendFaceCoordinates (M.mixedOldFaceVertices (Sum.inr f))
          (stdSimplex.vertex w) := hcoords
    _ = Pi.single w.1 1 :=
      extendFaceCoordinates_vertex (M.mixedOldFaceVertices (Sum.inr f)) w
    _ = Pi.single
        (M.fanOldVertexEmbedding (M.marking.fanVertexEmbedding f.1 v)) 1 := by rfl

private theorem MixedMapCertificate.map_eq_of_extendedCoordinates
    {M : MixedLocalFanData} (C : MixedMapCertificate M)
    {f g : M.MixedOldFace}
    {x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices f}}
    {y : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices g}}
    (hxy : extendFaceCoordinates (M.mixedOldFaceVertices f) x =
      extendFaceCoordinates (M.mixedOldFaceVertices g) y) :
    M.mixedOldFaceMap f x = M.mixedOldFaceMap g y := by
  apply Subtype.ext
  rw [C.mixedOldFaceMap_val f x, C.mixedOldFaceMap_val g y, hxy]

private structure MixedLocalBarycentricCertificate
    (M : MixedLocalFanData) (parentFace : M.localComplex.Face → M.ambient.Face) where
  localMixedFaceMap_mem_parent : ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}),
    M.mixedOldFaceMap (Sum.inl t) x ∈ M.ambient.faceCarrier (parentFace t).1
  localVertexPoint_mem_marking : ∀ v : M.localComplex.UsedVertex,
    M.localVertexPoint v ∈ M.marking.points
  positive_localVertex_mem_edge : ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ t.1}) (e : M.ambient.Edge),
    M.localFaceMap t x ∈ M.ambient.faceCarrier e.1 →
      ∀ (v : {v // v ∈ t.1}), 0 < x v →
        M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈ M.ambient.faceCarrier e.1
  localFace_edgeParameter_eq_sum : ∀ (t : M.localComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ t.1}) (e : M.ambient.Edge),
    M.localFaceMap t x ∈ M.ambient.faceCarrier e.1 →
      M.marking.edgeParameterValue e (M.localFaceMap t x) =
        ∑ v : {v // v ∈ t.1}, x v * M.marking.edgeParameterValue e
          (M.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)

private theorem exists_canonicalMixedLocalBarycentricCertificate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A) :
    let G := ChartInductionGeometry.canonical P hT
    Nonempty (MixedLocalBarycentricCertificate G.mixedData
      (fun t ↦ (G.localFaceParent t).1)) := by
  classical
  dsimp only
  let G : ChartInductionGeometry S c T A P := ChartInductionGeometry.canonical P hT
  let R := ChartInductionGeometry.subdivision P
  let L := ChartInductionGeometry.localComplex P G.anchorLines
  let source := ChartInductionGeometry.source P G.anchorLines
  let M := G.mixedData
  have hcontains := ChartInductionGeometry.canonicalLocalFaceParent_contains_realization P
  have hlocalFaceMap := G.localFaceMap_val
  have hmemParent (t : L.Face)
      (x : stdSimplex ℝ {v // v ∈ M.mixedOldFaceVertices (Sum.inl t)}) :
      M.mixedOldFaceMap (Sum.inl t) x ∈
        R.refined.faceCarrier (G.localFaceParent t).1.1 := by
    let x₀ := relabelUnivSimplex (M.localFaceOldVertexEmbedding t) x
    let z := L.faceStandardMap t x₀
    have hzSupport : ∀ v ∉ t.1, z.1 v = 0 := by
      intro v hv
      rw [L.faceStandardMap_val]
      exact extendFaceCoordinates_of_notMem t.1 x₀ hv
    obtain ⟨q, hqFace, hq⟩ := hcontains t z hzSupport
    change R.homeo.symm (source z) ∈ R.refined.faceCarrier (G.localFaceParent t).1.1
    have heq : R.homeo.symm (source z) = q := by
      apply R.homeo.injective
      rw [R.homeo.apply_symm_apply]
      exact hq.symm
    rwa [heq]
  have hmemMarking (v : L.UsedVertex) : G.localVertexPoint v ∈ G.marking.points := by
    apply IntrinsicTwoComplex.EdgeMarking.subset_points_ofFinset
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  have hpositive (t : L.Face) (x : stdSimplex ℝ {v // v ∈ t.1})
      (e : R.refined.Edge) (hqEdge : M.localFaceMap t x ∈ R.refined.faceCarrier e.1)
      (v : {v // v ∈ t.1}) (hv : 0 < x v) :
      G.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈ R.refined.faceCarrier e.1 := by
    intro k hk
    have hmap := congrFun (hlocalFaceMap t x) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hmap
    have hsumZero : (∑ w : {w // w ∈ t.1}, x w *
        (G.localVertexPoint ⟨w.1, ⟨t.1, t.2, w.2⟩⟩).1 k) = 0 := by
      rw [← hmap]
      exact hqEdge k hk
    have htermNonneg : 0 ≤ x v *
        (G.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k :=
      mul_nonneg (x.2.1 v)
        ((G.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).2.1.1 k)
    have htermLe : x v *
          (G.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k ≤
        ∑ w : {w // w ∈ t.1}, x w *
          (G.localVertexPoint ⟨w.1, ⟨t.1, t.2, w.2⟩⟩).1 k := by
      simpa only using (Finset.single_le_sum
        (s := (Finset.univ : Finset {w // w ∈ t.1})) (a := v)
        (f := fun w ↦ x w *
          (G.localVertexPoint ⟨w.1, ⟨t.1, t.2, w.2⟩⟩).1 k)
        (by
          intro w _
          exact mul_nonneg (x.2.1 w)
            ((G.localVertexPoint ⟨w.1, ⟨t.1, t.2, w.2⟩⟩).2.1.1 k))
        (Finset.mem_univ v))
    have hprod : x v *
        (G.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k = 0 := by
      apply le_antisymm
      · rw [hsumZero] at htermLe
        exact htermLe
      · exact htermNonneg
    exact (mul_eq_zero.mp hprod).resolve_left hv.ne'
  have hparameter (t : L.Face) (x : stdSimplex ℝ {v // v ∈ t.1})
      (e : R.refined.Edge) (hqEdge : M.localFaceMap t x ∈ R.refined.faceCarrier e.1) :
      G.marking.edgeParameterValue e (M.localFaceMap t x) =
        ∑ v : {v // v ∈ t.1}, x v * G.marking.edgeParameterValue e
          (G.localVertexPoint ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) := by
    rw [G.marking.edgeParameterValue_eq e hqEdge,
      R.refined.edgeParameter_eq_secondCoordinate]
    have hmap := congrFun (hlocalFaceMap t x) (R.refined.edgeSecond e)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hmap
    rw [hmap]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hvZero : x v = 0
    · rw [hvZero, zero_mul, zero_mul]
    · have hvPos : 0 < x v := lt_of_le_of_ne (x.2.1 v) (Ne.symm hvZero)
      have hvEdge := hpositive t x e hqEdge v hvPos
      rw [G.marking.edgeParameterValue_eq e hvEdge,
        R.refined.edgeParameter_eq_secondCoordinate]
  exact ⟨⟨hmemParent, hmemMarking, hpositive, hparameter⟩⟩

private structure MixedLocalInterpolationCertificate (M : MixedLocalFanData) where
  localUsedVertex_mem_face_of_map_eq : ∀ (t : M.localComplex.Face)
      (z : stdSimplex ℝ {v // v ∈ t.1}) (u : M.localComplex.UsedVertex),
    M.localFaceMap t z = M.localVertexPoint u → u.1 ∈ t.1
  exists_localFacePoint_eq_of_edgeParameter_between : ∀
      (t : M.localComplex.Face) (e : M.ambient.Edge) (a b : {v // v ∈ t.1})
      (p : M.ambient.realization),
    M.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩ ∈ M.ambient.faceCarrier e.1 →
    M.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩ ∈ M.ambient.faceCarrier e.1 →
    p ∈ M.ambient.faceCarrier e.1 →
    M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) ≤
      M.marking.edgeParameterValue e p →
    M.marking.edgeParameterValue e p ≤ M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩) →
    M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) <
      M.marking.edgeParameterValue e
        (M.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩) →
    ∃ z : stdSimplex ℝ {v // v ∈ t.1}, M.localFaceMap t z = p

private theorem exists_canonicalMixedLocalInterpolationCertificate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A) :
    Nonempty (MixedLocalInterpolationCertificate
      (ChartInductionGeometry.canonical P hT).mixedData) := by
  classical
  let G : ChartInductionGeometry S c T A P := ChartInductionGeometry.canonical P hT
  let R := ChartInductionGeometry.subdivision P
  let L := ChartInductionGeometry.localComplex P G.anchorLines
  let source := ChartInductionGeometry.source P G.anchorLines
  let M := G.mixedData
  have hsourceEmbedding := ChartInductionGeometry.canonicalSource_isEmbedding P
  have hlineMap := ChartInductionGeometry.canonicalLocalFaceMap_simplexLineMap P
  have hvertex := ChartInductionGeometry.canonicalLocalFaceMap_vertex P
  have hused (t : L.Face) (z : stdSimplex ℝ {v // v ∈ t.1})
      (u : L.UsedVertex) (hzu : M.localFaceMap t z = G.localVertexPoint u) :
      u.1 ∈ t.1 := by
    have hsource : source (L.faceStandardMap t z) = source (L.vertexPoint u) := by
      apply R.homeo.symm.injective
      exact hzu
    have hlocal : L.faceStandardMap t z = L.vertexPoint u :=
      hsourceEmbedding.injective hsource
    by_contra hut
    have hcoord := congrArg (fun q : L.realization ↦ q.1 u.1) hlocal
    rw [L.faceStandardMap_val, extendFaceCoordinates_of_notMem t.1 z hut] at hcoord
    have hone : (L.vertexPoint u).1 u.1 = (1 : ℝ) := by
      simp [IntrinsicTwoComplex.vertexPoint]
    rw [hone] at hcoord
    exact zero_ne_one hcoord
  have hinterpolate (t : L.Face) (e : R.refined.Edge) (a b : {v // v ∈ t.1})
      (p : R.refined.realization)
      (haEdge : G.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩ ∈
        R.refined.faceCarrier e.1)
      (hbEdge : G.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩ ∈
        R.refined.faceCarrier e.1)
      (hpEdge : p ∈ R.refined.faceCarrier e.1)
      (hap : G.marking.edgeParameterValue e
          (G.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) ≤
        G.marking.edgeParameterValue e p)
      (hpb : G.marking.edgeParameterValue e p ≤ G.marking.edgeParameterValue e
          (G.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩))
      (hab : G.marking.edgeParameterValue e
          (G.localVertexPoint ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) <
        G.marking.edgeParameterValue e
          (G.localVertexPoint ⟨b.1, ⟨t.1, t.2, b.2⟩⟩)) :
      ∃ z : stdSimplex ℝ {v // v ∈ t.1}, M.localFaceMap t z = p := by
    apply exists_facePoint_eq_of_edgeParameter_between G.marking G.localVertexPoint
      (fun u y ↦ M.localFaceMap u y)
    · intro u x y r
      exact hlineMap u x y r
    · intro u v
      exact hvertex u v
    · exact haEdge
    · exact hbEdge
    · exact hpEdge
    · exact hap
    · exact hpb
    · exact hab
  exact ⟨⟨hused, hinterpolate⟩⟩

private theorem exists_canonicalMixedLocalFanCertificate
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    {c : MoiseChart S} {T : PartialTriangulation S} {A : Set S}
    (P : CrossingWeldPatchContext S c T A) (hT : RadoInvariant T A) :
    Nonempty (MixedLocalFanCertificate
      (ChartInductionGeometry.canonical P hT).mixedData) := by
  classical
  -- Assemble the full certificate from the separately checked map phase.
  let geometry : ChartInductionGeometry S c T A P :=
    ChartInductionGeometry.canonical P hT
  let localFaceLevelFace := geometry.localFaceParent
  have localVertexLevelPoint_mem_face :=
    ChartInductionGeometry.canonicalLocalVertexPoint_mem_face P
  have interfaceEdgeMarks_subset_local :=
    ChartInductionGeometry.canonicalInterfaceEdgeMarks_subset_local P hT
  have selectedFace_marking_subset_local :=
    ChartInductionGeometry.canonicalSelectedFace_marking_subset_local P hT
  let mixedData : MixedLocalFanData := geometry.mixedData
  obtain ⟨mapCertificate⟩ := exists_canonicalMixedMapCertificate P hT
  obtain ⟨barycentricCertificate⟩ :=
    exists_canonicalMixedLocalBarycentricCertificate P hT
  obtain ⟨interpolationCertificate⟩ :=
    exists_canonicalMixedLocalInterpolationCertificate P hT
  obtain ⟨mixedCertificate, -⟩ :=
    exists_sealed_copy (X := MixedLocalFanCertificate mixedData)
    { parentFace := fun t ↦ (localFaceLevelFace t).1
      outside_parent_ne := by
        intro f t h
        apply f.2
        rw [h]
        exact (localFaceLevelFace t).2
      mixedOldFaceVertices_card := mapCertificate.mixedOldFaceVertices_card
      continuous_mixedOldFaceMap := mapCertificate.continuous_mixedOldFaceMap
      mixedOldFaceMap_val := mapCertificate.mixedOldFaceMap_val
      localMixedFaceMap_eq_iff := mapCertificate.localMixedFaceMap_eq_iff
      fanMixedFaceMap_eq_iff := mapCertificate.fanMixedFaceMap_eq_iff
      mixedOldFaceMap_eq_of_extendedCoordinates :=
        mapCertificate.map_eq_of_extendedCoordinates
      localMixedFaceMap_mem_parent :=
        barycentricCertificate.localMixedFaceMap_mem_parent
      localVertexPoint_mem_parent := localVertexLevelPoint_mem_face
      localVertexPoint_mem_marking :=
        barycentricCertificate.localVertexPoint_mem_marking
      positive_localVertex_mem_edge :=
        barycentricCertificate.positive_localVertex_mem_edge
      localFace_edgeParameter_eq_sum :=
        barycentricCertificate.localFace_edgeParameter_eq_sum
      edge_subset_face_of_openPoint :=
        edge_subset_face_of_open_edgePoint mixedData.ambient
      edgeMark_lift := by
        intro t e he p hp
        have hpLocal := interfaceEdgeMarks_subset_local
          (localFaceLevelFace t) e he p hp
        obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hpLocal
        exact ⟨u, hu⟩
      markingPoint_lift := by
        intro t p hpMark hpFace
        have hpLocal := selectedFace_marking_subset_local
          (localFaceLevelFace t) p hpMark hpFace
        obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hpLocal
        exact ⟨u, hu⟩
      localUsedVertex_mem_face_of_map_eq :=
        interpolationCertificate.localUsedVertex_mem_face_of_map_eq
      exists_localFacePoint_eq_of_edgeParameter_between :=
        interpolationCertificate.exists_localFacePoint_eq_of_edgeParameter_between
      mixedOldFaceMap_simplexLineMap := mapCertificate.mixedOldFaceMap_simplexLineMap
      mixedOldFaceMap_vertex := mapCertificate.mixedOldFaceMap_vertex
      mixedLocalExtended_eq_single_of_map_eq_localVertex :=
        mapCertificate.localExtended_eq_single
      mixedFanExtended_eq_single_of_map_eq_fanVertex :=
        mapCertificate.fanExtended_eq_single }
  exact ⟨mixedCertificate⟩

/-- Shared implementation of the Moise crossing weld once the chart straightening is certified
to preserve the ambient manifold-boundary stratum.

In the genuine crossing case (the chart core is not yet covered, and the absorbed region is not
inside the chart patch), the adjusted old complex and the chart patch admit a common welded
presentation: a common vertex type carrying both face families, with embeddings that agree
exactly on the shared realization, satisfy the combinatorial-surface bound jointly, and whose
united image contains `A ∪ c.core` in its topological interior.

The proof straightens the old complex over the
chart overlap by the locally finite controlled polygonal replacement over
`adaptiveOverlapGraphRealization` with tolerance vanishing at the overlap frontier
(`replaceOnOpen`/`frontierGlue`), refine the straightened trace and the fixed patch complex to
a common plane subdivision (`CommonSubdivision`, Moise's conditions (e)-(h)), and read off the
welded presentation. The finite compact-collar theorem cannot replace this vanishing-tolerance
construction, because continuity across the overlap frontier depends on the error tending to
zero there. -/
theorem MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening
    (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A)
    (hstraight :
      PartialTriangulation.BoundaryPreservingStraightening S T c) :
    let _ := (inferInstance : ConnectedSpace S)
    let _ := (inferInstance : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S)
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S) (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₁ e₁ ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₂ e₂ ∧
      A ∪ c.core ⊆ interior (Set.range e₁ ∪ Set.range e₂) := by
  dsimp
  classical
  let : SecondCountableTopology S := moise_secondCountableTopology S
  obtain ⟨W⟩ := exists_crossingWeldStraighteningContext S c hT hstraight
  obtain ⟨P⟩ := exists_crossingWeldPatchContext S c hc W
  let geometry : ChartInductionGeometry S c T A P :=
    ChartInductionGeometry.canonical P hT
  have hboundaryFanSurface :
      geometry.marking.markedFanLocallyFiniteTriangleComplex.compactIntrinsic
        |>.HasSurfaceEdgeValence :=
    geometry.marking.markedFanCompactIntrinsic_hasSurfaceEdgeValence
      geometry.subdivision_surface
  obtain ⟨mixedCertificate⟩ := exists_canonicalMixedLocalFanCertificate P hT
  have selectedFace_of_fanInterval_endpoints_local :=
    ChartInductionGeometry.canonicalSelectedFace_of_fanInterval_endpoints_local P hT
  let finishContextRaw : ChartInductionFinishContext S c T A P :=
    { geometry := geometry
      chart_boundary := hc
      triangulation_boundary := hT.boundaryFacewiseRegular
      certificate := mixedCertificate
      fan_surface := hboundaryFanSurface
      selectedFace_of_fanInterval_endpoints_local :=
        selectedFace_of_fanInterval_endpoints_local }
  obtain ⟨finishContext, -⟩ := exists_sealed_copy finishContextRaw
  exact finish_crossing_weld (S := S) P finishContext

/-- The bordered crossing weld.  The relative straightening preserves the ambient boundary
stratum, and the synchronized source/target presentations retain it as a simplicial face. -/
theorem MoiseChart.exists_crossing_weld (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S) (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₁ e₁ ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₂ e₂ ∧
      A ∪ c.core ⊆ interior (Set.range e₁ ∪ Set.range e₂) :=
  MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening
    S c hc hT
      (PartialTriangulation.exists_boundaryPreservingStraightening S T c hc
        hT.boundaryFacewiseRegular)

/-- **Theorem boundary** (Moise Ch. 8, Thm. 3, the induction step; bordered version).

Given a partial triangulation satisfying the Radó invariant for the absorbed region `A`, and one
more boundary-faithful chart, the chart's core can be absorbed: there is a partial triangulation
satisfying the invariant for `A ∪ c.core`.

Moise's proof of the step: work in the chart's model coordinates; take a polyhedral neighborhood
of the part of the built complex meeting the chart (Thm. 8.2); adjust it by a PL approximation of
the chart-transition homeomorphism (Thm. 6.3, `pl_approximation_two_manifold`) so that it meets a
fine complex containing the model core simplicially (conditions (a)-(h)); glue (Thm. 7.6).  The
polygonal Jordan and Schoenflies theorems enter through Thm. 6.3.

Hypothesis refinement is expected here (see `RadoInvariant`); conclusion weakening is not. -/
theorem moise_induction_step (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A) :
    ∃ T' : PartialTriangulation S, RadoInvariant T' (A ∪ c.core) := by
  classical
  by_cases hcore : c.core ⊆ interior T.support
  · exact ⟨T, hT.absorb_of_subset c.isCompact_core hcore⟩
  by_cases hA : A ⊆ interior c.patchPartialTriangulation.support
  · exact ⟨c.patchPartialTriangulation,
      radoInvariant_chartPatch_absorb c hc hT.coresCompact hA⟩
  · -- the crossing case: weld the adjusted old complex and the chart patch, then glue
    obtain ⟨V, _, _, F₁, F₂, e₁, e₂, hcard, he₁, he₂, hagree, hsep,
        hboundary₁, hboundary₂, hcover⟩ :=
      MoiseChart.exists_crossing_weld S c hc hT
    obtain ⟨T', _vertexEquiv, _hfaces, hsupport, hsurf', hboundary'⟩ :=
      PartialTriangulation.exists_glued V F₁ F₂ hcard e₁ e₂ he₁ he₂
        hagree hsep hboundary₁ hboundary₂
    refine ⟨T', ?_, hsurf', hboundary', ?_⟩
    · exact (hT.coresCompact.union c.isCompact_core)
    · rw [hsupport]
      exact hcover

omit [T2Space S] [ConnectedSpace S]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- Shared finite Radó induction assembler.  It turns any clean one-chart absorption step with the
full `RadoInvariant` conclusion into an end-to-end geometric triangulation. -/
theorem moise_triangulation_of_induction
    (hstep : ∀ (c : MoiseChart S), c.BoundaryFaithful →
      ∀ {T : PartialTriangulation S} {A : Set S}, RadoInvariant T A →
        ∃ T' : PartialTriangulation S, RadoInvariant T' (A ∪ c.core)) :
    Nonempty (GeometricTriangulation S) := by
  classical
  obtain ⟨m, charts, hcover, hbd⟩ := moise_finite_chart_cover S
  -- Absorb the first `k` cores.
  have Hrec : ∀ k : ℕ,
      ∃ T : PartialTriangulation S,
        RadoInvariant T (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) := by
    intro k
    induction k with
    | zero =>
        refine ⟨PartialTriangulation.empty S, ?_⟩
        have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < 0), (charts i).core) = (∅ : Set S) := by
          simp
        rw [hA]
        exact radoInvariant_empty S
    | succ k ih =>
        rcases ih with ⟨T, hT⟩
        by_cases hk : k < m
        · obtain ⟨T', hT'⟩ :=
            hstep (charts ⟨k, hk⟩) (hbd ⟨k, hk⟩) hT
          refine ⟨T', ?_⟩
          have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k + 1), (charts i).core) =
              (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) ∪
                (charts ⟨k, hk⟩).core := by
            ext x
            simp only [Set.mem_iUnion, Set.mem_union]
            constructor
            · rintro ⟨i, hik, hx⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hik with hik' | hik'
              · exact Or.inl ⟨i, hik', hx⟩
              · refine Or.inr ?_
                have : i = ⟨k, hk⟩ := Fin.ext hik'
                rwa [← this]
            · rintro (⟨i, hik, hx⟩ | hx)
              · exact ⟨i, Nat.lt_succ_of_lt hik, hx⟩
              · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hx⟩
          rw [hA]
          exact hT'
        · refine ⟨T, ?_⟩
          have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k + 1), (charts i).core) =
              (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) := by
            ext x
            simp only [Set.mem_iUnion]
            constructor
            · rintro ⟨i, hik, hx⟩
              have : (i : ℕ) < k := by
                have := i.isLt
                omega
              exact ⟨i, this, hx⟩
            · rintro ⟨i, hik, hx⟩
              exact ⟨i, Nat.lt_succ_of_lt hik, hx⟩
          rw [hA]
          exact hT
  obtain ⟨T, hT⟩ := Hrec m
  have hall : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < m), (charts i).core) = Set.univ := by
    rw [← hcover]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, -, hx⟩
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨i, i.isLt, hx⟩
  have hsupport : T.support = Set.univ := by
    have huniv : (Set.univ : Set S) ⊆ T.support := by
      rw [← hall]
      exact hT.coresCovered
    exact Set.eq_univ_of_univ_subset huniv
  exact ⟨T.toGeometricTriangulation hsupport⟩

/-- The bordered Radó induction assembled from its boundary-preserving one-chart step. -/
theorem moise_triangulation_of_boundaries :
    Nonempty (GeometricTriangulation S) :=
  moise_triangulation_of_induction S (moise_induction_step S)

end EvalHypotheses

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
