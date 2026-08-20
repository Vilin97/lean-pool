/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveTileComplex

/-!
# Conforming fan maps on adaptive midpoint tiles

Each first-safe adaptive triangle has finitely many resolved vertices on its boundary.  Coning
successive boundary vertices to the positive barycentric center gives a locally finite family
of parametrized triangles in the open subpolyhedron.  This file constructs those maps before
proving the global face-to-face intersection theorem.
-/

open scoped BigOperators

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PolygonalCircle

variable (J : PolygonalCircle)

/-- A preconnected subset of a polygonal circle which avoids every polygon vertex cannot pass
from one open edge to another.  Thus meeting one edge forces the whole set to lie in that edge.
This is the elementary component fact used to compare hanging-edge subdivisions. -/
theorem isPreconnected_subset_edgeSegment_of_avoids_vertices
    (A : Set Plane) (i : ZMod J.n) (hA : IsPreconnected A)
    (hcarrier : A ⊆ J.carrier)
    (hvertices : ∀ j : ZMod J.n, J.vertex j ∉ A)
    (hmeet : (A ∩ J.edgeSegment i).Nonempty) :
    A ⊆ J.edgeSegment i := by
  have hcover : A ⊆ J.edgeSegment i ∪ J.otherEdges i := by
    intro x hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hcarrier hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hxj)
    · exact Or.inr (Set.mem_iUnion.mpr
        ⟨j, Set.mem_iUnion.mpr ⟨hji, hxj⟩⟩)
  have hinter : A ∩ (J.edgeSegment i ∩ J.otherEdges i) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, hx⟩
    obtain ⟨j, hji, hxj⟩ := Set.mem_iUnion₂.mp hx.2.2
    rcases J.edgeSegment_inter_subset_endpoints (Ne.symm hji) ⟨hx.2.1, hxj⟩ with
      hxi | hxi
    · exact hvertices i (hxi ▸ hx.1)
    · exact hvertices (i + 1) (hxi ▸ hx.1)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hA)
      (J.edgeSegment i) (J.otherEdges i) (J.isClosed_edgeSegment i)
      (J.isClosed_otherEdges i) hcover hinter with hAi | hAo
  · exact hAi
  · obtain ⟨x, hxA, hxi⟩ := hmeet
    have hx : x ∈ A ∩ (J.edgeSegment i ∩ J.otherEdges i) :=
      ⟨hxA, hxi, hAo hxA⟩
    rw [hinter] at hx
    exact hx.elim

end PolygonalCircle

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)
variable [K.AdaptiveSafety U]
variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

theorem adaptiveFanVertex_mem_carrier (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) {p : K.realization}
    (hp : p ∈ K.adaptiveFanFaceVertices U hU f) :
    p ∈ K.adaptiveFaceCarrier U f.1 := by
  simp only [adaptiveFanFaceVertices, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact K.adaptiveFaceCenter_mem_carrier U f.1
  · have hpEdge := K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU
      f.1 f.2.1 f.2.2
    have hpBoundary : K.adaptiveEdgeIntervalFirst U hU f.1 f.2.1 f.2.2 ∈
        K.boundaryVertices U hU f.1 :=
      ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp hpEdge).1
    exact ((K.mem_boundaryVertices_iff U hU f.1 _).mp hpBoundary).1
  · have hpEdge := K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU
      f.1 f.2.1 f.2.2
    have hpBoundary : K.adaptiveEdgeIntervalSecond U hU f.1 f.2.1 f.2.2 ∈
        K.boundaryVertices U hU f.1 :=
      ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp hpEdge).1
    exact ((K.mem_boundaryVertices_iff U hU f.1 _).mp hpBoundary).1

theorem homeo_symm_mem_levelFaceCarrier {n : ℕ} (t : K.LevelFace n)
    {p : K.realization} (hp : p ∈ K.levelFaceCarrier t) :
    (K.safeSubdivision n).homeo.symm p ∈
      (K.safeSubdivision n).refined.faceCarrier t.1 := by
  obtain ⟨x, hx, hxp⟩ := hp
  have heq : (K.safeSubdivision n).homeo.symm p = x := by
    rw [← hxp]
    exact (K.safeSubdivision n).homeo.symm_apply_apply x
  rwa [heq]

/-- The source point of a geometric fan vertex in the refined realization carrying its tile. -/
noncomputable def adaptiveFanVertexSource (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (p : {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    (K.safeSubdivision f.1.1).refined.realization :=
  (K.safeSubdivision f.1.1).homeo.symm p.1

theorem adaptiveFanVertexSource_mem_carrier (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (p : {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    K.adaptiveFanVertexSource U hU f p ∈
      (K.safeSubdivision f.1.1).refined.faceCarrier f.1.2.1.1 := by
  apply K.homeo_symm_mem_levelFaceCarrier f.1.2.1
  exact K.adaptiveFanVertex_mem_carrier U hU f p.2

/-- The distinguished cone-center vertex of a fan triangle. -/
noncomputable def adaptiveFanCenterVertex (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    {p // p ∈ K.adaptiveFanFaceVertices U hU f} :=
  ⟨K.adaptiveFaceCenter U f.1, by
    simp [adaptiveFanFaceVertices]⟩

/-- The first base vertex of a fan triangle. -/
noncomputable def adaptiveFanFirstVertex (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    {p // p ∈ K.adaptiveFanFaceVertices U hU f} :=
  ⟨K.adaptiveEdgeIntervalFirst U hU f.1 f.2.1 f.2.2, by
    simp [adaptiveFanFaceVertices]⟩

/-- The second base vertex of a fan triangle. -/
noncomputable def adaptiveFanSecondVertex (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    {p // p ∈ K.adaptiveFanFaceVertices U hU f} :=
  ⟨K.adaptiveEdgeIntervalSecond U hU f.1 f.2.1 f.2.2, by
    simp [adaptiveFanFaceVertices]⟩

theorem adaptiveFanVertex_univ (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    (Finset.univ : Finset {p // p ∈ K.adaptiveFanFaceVertices U hU f}) =
      {K.adaptiveFanCenterVertex U hU f,
        K.adaptiveFanFirstVertex U hU f,
        K.adaptiveFanSecondVertex U hU f} := by
  classical
  ext p
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  have hp := p.2
  simp only [adaptiveFanFaceVertices, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hp | hp | hp
  · exact Or.inl (Subtype.ext hp)
  · exact Or.inr (Or.inl (Subtype.ext hp))
  · exact Or.inr (Or.inr (Subtype.ext hp))

theorem adaptiveFanCenterVertex_ne_first (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    K.adaptiveFanCenterVertex U hU f ≠ K.adaptiveFanFirstVertex U hU f := by
  intro h
  have hp := K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU
    f.1 f.2.1 f.2.2
  exact K.adaptiveFaceCenter_ne_boundaryVertex U hU f.1
    ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp hp).1
    (congrArg Subtype.val h)

theorem adaptiveFanCenterVertex_ne_second (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    K.adaptiveFanCenterVertex U hU f ≠ K.adaptiveFanSecondVertex U hU f := by
  intro h
  have hp := K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU
    f.1 f.2.1 f.2.2
  exact K.adaptiveFaceCenter_ne_boundaryVertex U hU f.1
    ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp hp).1
    (congrArg Subtype.val h)

theorem adaptiveFanFirstVertex_ne_second (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    K.adaptiveFanFirstVertex U hU f ≠ K.adaptiveFanSecondVertex U hU f := by
  intro h
  exact K.adaptiveEdgeIntervalFirst_ne_second U hU f.1 f.2.1 f.2.2
    (congrArg Subtype.val h)

/-- The three distinguished fan weights sum to one. -/
theorem adaptiveFanWeights_sum (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    x.1 (K.adaptiveFanCenterVertex U hU f) +
        x.1 (K.adaptiveFanFirstVertex U hU f) +
      x.1 (K.adaptiveFanSecondVertex U hU f) = 1 := by
  classical
  let c := K.adaptiveFanCenterVertex U hU f
  let p := K.adaptiveFanFirstVertex U hU f
  let q := K.adaptiveFanSecondVertex U hU f
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, K.adaptiveFanCenterVertex_ne_first U hU f,
      K.adaptiveFanCenterVertex_ne_second U hU f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, K.adaptiveFanFirstVertex_ne_second U hU f]
  have hsum := x.2.2
  rw [K.adaptiveFanVertex_univ U hU f] at hsum
  rw [Finset.sum_insert hcNot, Finset.sum_insert hpNot,
    Finset.sum_singleton] at hsum
  simpa only [add_assoc] using hsum

/-- The canonical interval parametrization of the resolved base of a fan triangle. -/
noncomputable def adaptiveFanBaseSimplexPath (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) (r : Set.Icc (0 : ℝ) 1) :
    stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f} := by
  let a := K.adaptiveFanFirstVertex U hU f
  let b := K.adaptiveFanSecondVertex U hU f
  let x := AffineMap.lineMap (stdSimplex.vertex a :
      {p // p ∈ K.adaptiveFanFaceVertices U hU f} → ℝ)
    (stdSimplex.vertex b :
      {p // p ∈ K.adaptiveFanFaceVertices U hU f} → ℝ) r.1
  exact ⟨x, (convex_stdSimplex ℝ _).lineMap_mem
    (stdSimplex.vertex a).2 (stdSimplex.vertex b).2 r.2⟩

theorem continuous_adaptiveFanBaseSimplexPath (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Continuous (K.adaptiveFanBaseSimplexPath U hU f) := by
  apply Continuous.subtype_mk
  exact (AffineMap.lineMap (k := ℝ)
    (stdSimplex.vertex (K.adaptiveFanFirstVertex U hU f) :
      {p // p ∈ K.adaptiveFanFaceVertices U hU f} → ℝ)
    (stdSimplex.vertex (K.adaptiveFanSecondVertex U hU f) :
      {p // p ∈ K.adaptiveFanFaceVertices U hU f} → ℝ)).continuous_of_finiteDimensional.comp
        continuous_subtype_val

@[simp] theorem adaptiveFanBaseSimplexPath_apply_first (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) (r : Set.Icc (0 : ℝ) 1) :
    K.adaptiveFanBaseSimplexPath U hU f r
        (K.adaptiveFanFirstVertex U hU f) = 1 - r.1 := by
  let a := K.adaptiveFanFirstVertex U hU f
  let b := K.adaptiveFanSecondVertex U hU f
  have hab : a ≠ b := K.adaptiveFanFirstVertex_ne_second U hU f
  change (K.adaptiveFanBaseSimplexPath U hU f r).1 a = 1 - r.1
  dsimp only [adaptiveFanBaseSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  simp [a, b, hab]

@[simp] theorem adaptiveFanBaseSimplexPath_apply_second (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) (r : Set.Icc (0 : ℝ) 1) :
    K.adaptiveFanBaseSimplexPath U hU f r
        (K.adaptiveFanSecondVertex U hU f) = r.1 := by
  let a := K.adaptiveFanFirstVertex U hU f
  let b := K.adaptiveFanSecondVertex U hU f
  have hab : a ≠ b := K.adaptiveFanFirstVertex_ne_second U hU f
  change (K.adaptiveFanBaseSimplexPath U hU f r).1 b = r.1
  dsimp only [adaptiveFanBaseSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  simp [a, b, hab]

@[simp] theorem adaptiveFanBaseSimplexPath_apply_center (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) (r : Set.Icc (0 : ℝ) 1) :
    K.adaptiveFanBaseSimplexPath U hU f r
        (K.adaptiveFanCenterVertex U hU f) = 0 := by
  let a := K.adaptiveFanFirstVertex U hU f
  let b := K.adaptiveFanSecondVertex U hU f
  let c := K.adaptiveFanCenterVertex U hU f
  have hca : c ≠ a := K.adaptiveFanCenterVertex_ne_first U hU f
  have hcb : c ≠ b := K.adaptiveFanCenterVertex_ne_second U hU f
  change (K.adaptiveFanBaseSimplexPath U hU f r).1 c = 0
  dsimp only [adaptiveFanBaseSimplexPath]
  rw [AffineMap.lineMap_apply_module]
  simp [a, b, c, hca, hcb]

/-- The normalized parameter of the boundary point obtained by radially projecting a noncenter
fan point away from the cone center. -/
noncomputable def adaptiveFanNormalizedBaseParameter (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x.1 (K.adaptiveFanCenterVertex U hU f) < 1) :
    Set.Icc (0 : ℝ) 1 := by
  let d := 1 - x.1 (K.adaptiveFanCenterVertex U hU f)
  have hd : 0 < d := sub_pos.mpr hxCenter
  have hsum := K.adaptiveFanWeights_sum U hU f x
  have hsecondNonneg := x.2.1 (K.adaptiveFanSecondVertex U hU f)
  have hfirstNonneg := x.2.1 (K.adaptiveFanFirstVertex U hU f)
  refine ⟨x.1 (K.adaptiveFanSecondVertex U hU f) / d, ?_, ?_⟩
  · exact div_nonneg hsecondNonneg hd.le
  · apply (div_le_one hd).mpr
    dsimp only [d]
    change x.1 (K.adaptiveFanSecondVertex U hU f) ≤
      1 - x.1 (K.adaptiveFanCenterVertex U hU f)
    linarith

/-- The radial projection of a noncenter fan point to its resolved base interval. -/
noncomputable def adaptiveFanNormalizedBasePoint (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x.1 (K.adaptiveFanCenterVertex U hU f) < 1) :
    stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f} :=
  K.adaptiveFanBaseSimplexPath U hU f
    (K.adaptiveFanNormalizedBaseParameter U hU f x hxCenter)

@[simp] theorem adaptiveFanNormalizedBasePoint_apply_center (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x.1 (K.adaptiveFanCenterVertex U hU f) < 1) :
    K.adaptiveFanNormalizedBasePoint U hU f x hxCenter
        (K.adaptiveFanCenterVertex U hU f) = 0 := by
  exact K.adaptiveFanBaseSimplexPath_apply_center U hU f _

@[simp] theorem adaptiveFanNormalizedBasePoint_apply_second (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x.1 (K.adaptiveFanCenterVertex U hU f) < 1) :
    K.adaptiveFanNormalizedBasePoint U hU f x hxCenter
        (K.adaptiveFanSecondVertex U hU f) =
      x.1 (K.adaptiveFanSecondVertex U hU f) /
        (1 - x.1 (K.adaptiveFanCenterVertex U hU f)) := by
  rw [adaptiveFanNormalizedBasePoint,
    K.adaptiveFanBaseSimplexPath_apply_second U hU f]
  rfl

@[simp] theorem adaptiveFanNormalizedBasePoint_apply_first (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x.1 (K.adaptiveFanCenterVertex U hU f) < 1) :
    K.adaptiveFanNormalizedBasePoint U hU f x hxCenter
        (K.adaptiveFanFirstVertex U hU f) =
      x.1 (K.adaptiveFanFirstVertex U hU f) /
        (1 - x.1 (K.adaptiveFanCenterVertex U hU f)) := by
  rw [adaptiveFanNormalizedBasePoint,
    K.adaptiveFanBaseSimplexPath_apply_first U hU f]
  change 1 - x.1 (K.adaptiveFanSecondVertex U hU f) /
      (1 - x.1 (K.adaptiveFanCenterVertex U hU f)) =
    x.1 (K.adaptiveFanFirstVertex U hU f) /
      (1 - x.1 (K.adaptiveFanCenterVertex U hU f))
  have hsum := K.adaptiveFanWeights_sum U hU f x
  have hxCenter' : x.1 (K.adaptiveFanCenterVertex U hU f) < 1 := hxCenter
  have hden : 1 - x.1 (K.adaptiveFanCenterVertex U hU f) ≠ 0 :=
    (sub_pos.mpr hxCenter').ne'
  have hnum :
      (1 - x.1 (K.adaptiveFanCenterVertex U hU f)) -
          x.1 (K.adaptiveFanSecondVertex U hU f) =
        x.1 (K.adaptiveFanFirstVertex U hU f) := by
    linarith
  field_simp [hden]
  linarith

theorem adaptiveFanBaseSimplexPath_injective (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Function.Injective (K.adaptiveFanBaseSimplexPath U hU f) := by
  intro r s hrs
  apply Subtype.ext
  have hcoord := congrArg
    (fun x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f} ↦
      x (K.adaptiveFanSecondVertex U hU f)) hrs
  simpa using hcoord

/-- Barycentric combination of a fan face's three geometric vertices, formed in the faithful
refined realization before transporting back to the original complex. -/
noncomputable def adaptiveFanSourcePoint (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    (K.safeSubdivision f.1.1).refined.realization := by
  classical
  let z : (K.safeSubdivision f.1.1).refined.Vertex → ℝ := fun v ↦
    ∑ p, x p * (K.adaptiveFanVertexSource U hU f p).1 v
  refine ⟨z, ⟨?_, ?_⟩, ⟨f.1.2.1.1, f.1.2.1.2, ?_⟩⟩
  · intro v
    dsimp only [z]
    exact Finset.sum_nonneg fun p _ ↦
      mul_nonneg (x.2.1 p) ((K.adaptiveFanVertexSource U hU f p).2.1.1 v)
  · dsimp only [z]
    calc
      ∑ v, ∑ p, x p * (K.adaptiveFanVertexSource U hU f p).1 v =
          ∑ p, ∑ v, x p * (K.adaptiveFanVertexSource U hU f p).1 v :=
        Finset.sum_comm
      _ = ∑ p, x p * ∑ v, (K.adaptiveFanVertexSource U hU f p).1 v := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
      _ = ∑ p, x p := by
        apply Finset.sum_congr rfl
        intro p _
        rw [(K.adaptiveFanVertexSource U hU f p).2.1.2, mul_one]
      _ = 1 := x.2.2
  · intro v hv
    dsimp only [z]
    apply Finset.sum_eq_zero
    intro p _
    rw [(K.adaptiveFanVertexSource_mem_carrier U hU f p) v hv, mul_zero]

theorem adaptiveFanSourcePoint_mem_carrier (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    K.adaptiveFanSourcePoint U hU f x ∈
      (K.safeSubdivision f.1.1).refined.faceCarrier f.1.2.1.1 :=
  by
    classical
    intro v hv
    change (∑ p, x p * (K.adaptiveFanVertexSource U hU f p).1 v) = 0
    apply Finset.sum_eq_zero
    intro p _
    rw [(K.adaptiveFanVertexSource_mem_carrier U hU f p) v hv, mul_zero]

/-- The canonical line segment between two barycentric points of one fan face. -/
noncomputable def adaptiveFanSimplexLineMap (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (r : Set.Icc (0 : ℝ) 1) :
    stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f} :=
  ⟨AffineMap.lineMap x.1 y.1 r.1,
    (convex_stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}).lineMap_mem
      x.2 y.2 r.2⟩

-- The affine source calculation expands three dependent finite sums.
theorem adaptiveFanSourcePoint_simplexLineMap (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (r : Set.Icc (0 : ℝ) 1) :
    (K.adaptiveFanSourcePoint U hU f
      (K.adaptiveFanSimplexLineMap U hU f x y r)).1 =
        AffineMap.lineMap (K.adaptiveFanSourcePoint U hU f x).1
          (K.adaptiveFanSourcePoint U hU f y).1 r.1 := by
  classical
  funext v
  simp only [adaptiveFanSourcePoint, adaptiveFanSimplexLineMap,
    AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ p, (((1 - r.1) • x.1 + r.1 • y.1) p) *
      (K.adaptiveFanVertexSource U hU f p).1 v) =
    (1 - r.1) * ∑ p, x p * (K.adaptiveFanVertexSource U hU f p).1 v +
      r.1 * ∑ p, y p * (K.adaptiveFanVertexSource U hU f p).1 v
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ p, ((1 - r.1) * x p + r.1 * y p) *
        (K.adaptiveFanVertexSource U hU f p).1 v) =
        ∑ p, ((1 - r.1) *
            (x p * (K.adaptiveFanVertexSource U hU f p).1 v) +
          r.1 * (y p * (K.adaptiveFanVertexSource U hU f p).1 v)) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

-- An affine fan combination sends a simplex vertex to the corresponding source vertex.
theorem adaptiveFanSourcePoint_vertex (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (p : {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    K.adaptiveFanSourcePoint U hU f (stdSimplex.vertex p) =
      K.adaptiveFanVertexSource U hU f p := by
  classical
  apply Subtype.ext
  funext v
  change (∑ q, (stdSimplex.vertex p :
        stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}) q *
      (K.adaptiveFanVertexSource U hU f q).1 v) =
        (K.adaptiveFanVertexSource U hU f p).1 v
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    simp [hqp]
  · simp

/-- Pulling an edge point back through the faithful subdivision gives zero in every coordinate
outside that edge. -/
theorem homeo_symm_apply_eq_zero_of_mem_levelFaceEdgeCarrier {n : ℕ}
    (t : K.LevelFace n) (i : ZMod 3) {p : K.realization}
    (hp : p ∈ K.levelFaceEdgeCarrier t i)
    {v : (K.safeSubdivision n).refined.Vertex}
    (hv : v ∉ ((K.safeSubdivision n).refined.faceEdge t i).1) :
    ((K.safeSubdivision n).homeo.symm p).1 v = 0 := by
  obtain ⟨x, hx, rfl⟩ := hp
  rw [(K.safeSubdivision n).homeo.symm_apply_apply]
  exact hx v hv

theorem faceVertex_add_two_not_mem_faceEdge {n : ℕ} (t : K.LevelFace n)
    (i : ZMod 3) :
    (K.safeSubdivision n).refined.faceVertex t (i + 2) ∉
      ((K.safeSubdivision n).refined.faceEdge t i).1 := by
  simp only [(K.safeSubdivision n).refined.faceEdge_val,
    Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  · exact ((K.safeSubdivision n).refined.faceVertex_ne_add_two t i).symm h
  · have hne : (K.safeSubdivision n).refined.faceVertex t (i + 2) ≠
        (K.safeSubdivision n).refined.faceVertex t (i + 1) := by
      simpa only [add_assoc, one_add_one_eq_two] using
        ((K.safeSubdivision n).refined.faceVertex_ne_next t (i + 1)).symm
    exact hne h

theorem adaptiveEdgeIntervalFirst_source_opposite (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    ((K.safeSubdivision t.1).homeo.symm
      (K.adaptiveEdgeIntervalFirst U hU t i j)).1
        ((K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 2)) = 0 := by
  apply K.homeo_symm_apply_eq_zero_of_mem_levelFaceEdgeCarrier t.2.1 i
  · exact ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
      (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU t i j)).2
  · exact K.faceVertex_add_two_not_mem_faceEdge t.2.1 i

theorem adaptiveEdgeIntervalSecond_source_opposite (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    ((K.safeSubdivision t.1).homeo.symm
      (K.adaptiveEdgeIntervalSecond U hU t i j)).1
        ((K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 2)) = 0 := by
  apply K.homeo_symm_apply_eq_zero_of_mem_levelFaceEdgeCarrier t.2.1 i
  · exact ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
      (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU t i j)).2
  · exact K.faceVertex_add_two_not_mem_faceEdge t.2.1 i

omit [AdaptiveSafety.IsAdmissible K U] in
theorem adaptiveFaceCenter_source_apply (t : K.AdaptiveFace U)
    (i : ZMod 3) :
    ((K.safeSubdivision t.1).homeo.symm (K.adaptiveFaceCenter U t)).1
        ((K.safeSubdivision t.1).refined.faceVertex t.2.1 i) = 1 / 3 := by
  rw [adaptiveFaceCenter, (K.safeSubdivision t.1).homeo.symm_apply_apply,
    (K.safeSubdivision t.1).refined.faceStandardMap_val,
    extendFaceCoordinates_of_mem t.2.1.1 _
      ((K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 i)]
  exact (K.safeSubdivision t.1).refined.faceCenterSimplex_apply t.2.1 _

/-- The coordinate opposite a fan triangle's base edge is exactly one third of its cone-center
weight. -/
theorem adaptiveFanSourcePoint_opposite (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    (K.adaptiveFanSourcePoint U hU f x).1
      ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 (f.2.1 + 2)) =
      x.1 (K.adaptiveFanCenterVertex U hU f) / 3 := by
  classical
  let c := K.adaptiveFanCenterVertex U hU f
  change (∑ p, x p * (K.adaptiveFanVertexSource U hU f p).1
      ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 (f.2.1 + 2))) = x c / 3
  rw [Finset.sum_eq_single c]
  · have hc :
        (K.adaptiveFanVertexSource U hU f c).1
            ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 (f.2.1 + 2)) =
          1 / 3 := by
      simpa only [c, adaptiveFanCenterVertex, adaptiveFanVertexSource] using
        K.adaptiveFaceCenter_source_apply U f.1 (f.2.1 + 2)
    rw [hc]
    ring
  · intro p _ hpc
    have hp := p.2
    simp only [adaptiveFanFaceVertices, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp
    · exact False.elim (hpc (Subtype.ext hp))
    · rw [mul_eq_zero]
      exact Or.inr (by
        simpa only [adaptiveFanVertexSource, hp] using
          K.adaptiveEdgeIntervalFirst_source_opposite U hU f.1 f.2.1 f.2.2)
    · rw [mul_eq_zero]
      exact Or.inr (by
        simpa only [adaptiveFanVertexSource, hp] using
          K.adaptiveEdgeIntervalSecond_source_opposite U hU f.1 f.2.1 f.2.2)
  · intro hcNot
    simp at hcNot

/-- The cone-center contribution is a lower bound for every barycentric coordinate of a fan
point in its ambient refined face.  At the coordinate opposite the fan base this bound is an
equality. -/
theorem adaptiveFanSourcePoint_faceVertex_lower_bound (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (i : ZMod 3) :
    x.1 (K.adaptiveFanCenterVertex U hU f) / 3 ≤
      (K.adaptiveFanSourcePoint U hU f x).1
        ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 i) := by
  classical
  let c := K.adaptiveFanCenterVertex U hU f
  let p := K.adaptiveFanFirstVertex U hU f
  let q := K.adaptiveFanSecondVertex U hU f
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, K.adaptiveFanCenterVertex_ne_first U hU f,
      K.adaptiveFanCenterVertex_ne_second U hU f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, K.adaptiveFanFirstVertex_ne_second U hU f]
  have hcValue : (K.adaptiveFanVertexSource U hU f c).1
      ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 i) = 1 / 3 := by
    simpa only [c, adaptiveFanCenterVertex, adaptiveFanVertexSource] using
      K.adaptiveFaceCenter_source_apply U f.1 i
  have hpNonneg : 0 ≤ x p * (K.adaptiveFanVertexSource U hU f p).1
      ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 i) :=
    mul_nonneg (x.2.1 p) ((K.adaptiveFanVertexSource U hU f p).2.1.1 _)
  have hqNonneg : 0 ≤ x q * (K.adaptiveFanVertexSource U hU f q).1
      ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 i) :=
    mul_nonneg (x.2.1 q) ((K.adaptiveFanVertexSource U hU f q).2.1.1 _)
  change x c / 3 ≤ ∑ r, x r * (K.adaptiveFanVertexSource U hU f r).1
    ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 i)
  rw [K.adaptiveFanVertex_univ U hU f,
    Finset.sum_insert hcNot, Finset.sum_insert hpNot, Finset.sum_singleton,
    hcValue]
  nlinarith

/-- A noncenter fan point is the affine combination of the cone center and its normalized
radial projection to the base. -/
theorem adaptiveFanSourcePoint_eq_lineMap_normalizedBase (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x.1 (K.adaptiveFanCenterVertex U hU f) < 1) :
    (K.adaptiveFanSourcePoint U hU f x).1 =
      AffineMap.lineMap
        (K.adaptiveFanVertexSource U hU f
          (K.adaptiveFanCenterVertex U hU f)).1
        (K.adaptiveFanSourcePoint U hU f
          (K.adaptiveFanNormalizedBasePoint U hU f x hxCenter)).1
        (1 - x.1 (K.adaptiveFanCenterVertex U hU f)) := by
  classical
  let c := K.adaptiveFanCenterVertex U hU f
  let p := K.adaptiveFanFirstVertex U hU f
  let q := K.adaptiveFanSecondVertex U hU f
  let d := 1 - x.1 c
  have hd : d ≠ 0 := (sub_pos.mpr hxCenter).ne'
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, K.adaptiveFanCenterVertex_ne_first U hU f,
      K.adaptiveFanCenterVertex_ne_second U hU f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, K.adaptiveFanFirstVertex_ne_second U hU f]
  funext v
  change (∑ r, x r * (K.adaptiveFanVertexSource U hU f r).1 v) = _
  rw [K.adaptiveFanVertex_univ U hU f,
    Finset.sum_insert hcNot, Finset.sum_insert hpNot, Finset.sum_singleton,
    AffineMap.lineMap_apply_module]
  change x.1 c * _ + (x.1 p * _ + x.1 q * _) =
    (1 - d) * (K.adaptiveFanVertexSource U hU f c).1 v +
      d * (∑ r,
        K.adaptiveFanNormalizedBasePoint U hU f x hxCenter r *
          (K.adaptiveFanVertexSource U hU f r).1 v)
  rw [K.adaptiveFanVertex_univ U hU f,
    Finset.sum_insert hcNot, Finset.sum_insert hpNot, Finset.sum_singleton,
    K.adaptiveFanNormalizedBasePoint_apply_center U hU f x hxCenter,
    K.adaptiveFanNormalizedBasePoint_apply_first U hU f x hxCenter,
    K.adaptiveFanNormalizedBasePoint_apply_second U hU f x hxCenter]
  dsimp only [d, c, p, q]
  dsimp only [d, c] at hd
  field_simp [hd]
  ring

/-- A vertex of a triangular intrinsic face outside one cyclic edge is the opposite vertex. -/
theorem eq_faceVertex_add_two_of_mem_face_not_mem_faceEdge {n : ℕ}
    (t : K.LevelFace n) (i : ZMod 3)
    {v : (K.safeSubdivision n).refined.Vertex}
    (hvt : v ∈ t.1)
    (hve : v ∉ ((K.safeSubdivision n).refined.faceEdge t i).1) :
    v = (K.safeSubdivision n).refined.faceVertex t (i + 2) := by
  obtain ⟨j, rfl⟩ :=
    (K.safeSubdivision n).refined.exists_faceVertex_eq_of_mem t hvt
  have hji0 : j ≠ i := by
    intro h
    apply hve
    rw [h, (K.safeSubdivision n).refined.faceEdge_val]
    simp
  have hjnext : j ≠ i + 1 := by
    intro h
    apply hve
    rw [h, (K.safeSubdivision n).refined.faceEdge_val]
    simp
  have hji : j = i + 2 :=
    (by decide : ∀ a b : ZMod 3, b ≠ a → b ≠ a + 1 → b = a + 2)
      i j hji0 hjnext
  exact congrArg ((K.safeSubdivision n).refined.faceVertex t) hji

/-- The three cyclic edges of a triangular level face are pairwise distinct. -/
theorem levelFace_faceEdge_injective {n : ℕ} (t : K.LevelFace n) :
    Function.Injective fun i : ZMod 3 ↦
      (K.safeSubdivision n).refined.faceEdge t i := by
  intro i j hij
  have hnot : (K.safeSubdivision n).refined.faceVertex t (j + 2) ∉
      ((K.safeSubdivision n).refined.faceEdge t i).1 := by
    rw [congrArg Subtype.val hij]
    exact K.faceVertex_add_two_not_mem_faceEdge t j
  have hv := K.eq_faceVertex_add_two_of_mem_face_not_mem_faceEdge t i
    ((K.safeSubdivision n).refined.faceVertex_mem t (j + 2)) hnot
  have hindex : j + 2 = i + 2 :=
    (K.safeSubdivision n).refined.faceVertex_injective t hv
  exact (add_right_cancel hindex).symm

/-- Earlier resolved intervals on one ordered tile edge end no later than later intervals begin. -/
theorem adaptiveEdgeIntervalSecond_parameter_le_first_of_lt
    (hU : IsOpen U) (t : K.AdaptiveFace U) (i : ZMod 3)
    (a b : K.AdaptiveEdgeInterval U hU t i) (hab : a.1 < b.1) :
    K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalSecond U hU t i a) ≤
      K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalFirst U hU t i b) := by
  let L := K.boundaryEdgeVertexList U hU t i
  let ka : Fin L.length := ⟨a.1 + 1, by
    have ha := a.2
    dsimp only [L]
    omega⟩
  let kb : Fin L.length := ⟨b.1, by
    have hb := b.2
    dsimp only [L]
    omega⟩
  have hle : ka ≤ kb := by
    change a.1 + 1 ≤ b.1
    omega
  rcases hle.eq_or_lt with heq | hlt
  · change K.levelFaceEdgeParameter t.2.1 i (L.get ka) ≤
      K.levelFaceEdgeParameter t.2.1 i (L.get kb)
    rw [heq]
  · have hp :=
      (K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i).rel_get_of_lt hlt
    simpa only [adaptiveEdgeIntervalSecond, adaptiveEdgeIntervalFirst,
      L, ka, kb] using hp

/-- Zero cone-center weight places a fan source point on its resolved base edge. -/
theorem adaptiveFanSourcePoint_mem_baseEdge_of_center_eq_zero
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0) :
    K.adaptiveFanSourcePoint U hU f x ∈
      (K.safeSubdivision f.1.1).refined.faceCarrier
        ((K.safeSubdivision f.1.1).refined.faceEdge f.1.2.1 f.2.1).1 := by
  intro v hve
  by_cases hvt : v ∈ f.1.2.1.1
  · have hxCenter' : x.1 (K.adaptiveFanCenterVertex U hU f) = 0 := hxCenter
    rw [K.eq_faceVertex_add_two_of_mem_face_not_mem_faceEdge f.1.2.1 f.2.1 hvt hve,
      K.adaptiveFanSourcePoint_opposite U hU f x, hxCenter']
    norm_num
  · exact (K.adaptiveFanSourcePoint_mem_carrier U hU f x) v hvt

/-- When the cone-center weight vanishes, the two ordered base weights sum to one. -/
theorem adaptiveFanBaseWeights_sum_of_center_eq_zero
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0) :
    x (K.adaptiveFanFirstVertex U hU f) +
      x (K.adaptiveFanSecondVertex U hU f) = 1 := by
  let xf : {p // p ∈ K.adaptiveFanFaceVertices U hU f} → ℝ := x.1
  change xf (K.adaptiveFanFirstVertex U hU f) +
    xf (K.adaptiveFanSecondVertex U hU f) = 1
  have hsum : ∑ p, xf p = 1 := x.2.2
  rw [K.adaptiveFanVertex_univ U hU f] at hsum
  have hcNot : K.adaptiveFanCenterVertex U hU f ∉
      ({K.adaptiveFanFirstVertex U hU f,
        K.adaptiveFanSecondVertex U hU f} : Finset _) := by
    simp [K.adaptiveFanCenterVertex_ne_first U hU f,
      K.adaptiveFanCenterVertex_ne_second U hU f]
  have hpNot : K.adaptiveFanFirstVertex U hU f ∉
      ({K.adaptiveFanSecondVertex U hU f} : Finset _) := by
    simp [K.adaptiveFanFirstVertex_ne_second U hU f]
  rw [Finset.sum_insert hcNot, Finset.sum_insert hpNot,
    Finset.sum_singleton] at hsum
  have hxCenter' : xf (K.adaptiveFanCenterVertex U hU f) = 0 := hxCenter
  rw [hxCenter', zero_add] at hsum
  exact hsum

theorem adaptiveFanVertexSource_val_injective (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) : Function.Injective
      (fun p : {p // p ∈ K.adaptiveFanFaceVertices U hU f} ↦
        (K.adaptiveFanVertexSource U hU f p).1) := by
  intro p q hpq
  apply Subtype.ext
  have hsource : K.adaptiveFanVertexSource U hU f p =
      K.adaptiveFanVertexSource U hU f q := Subtype.ext hpq
  have himage := congrArg (K.safeSubdivision f.1.1).homeo hsource
  simpa only [adaptiveFanVertexSource,
    (K.safeSubdivision f.1.1).homeo.apply_symm_apply] using himage

/-- The three pulled-back vertices of a fan face are affinely independent.  The two boundary
vertices lie in the affine coordinate hyperplane opposite their common edge, while the positive
center does not. -/
theorem affineIndependent_adaptiveFanVertexSource_val (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    AffineIndependent ℝ
      (fun p : {p // p ∈ K.adaptiveFanFaceVertices U hU f} ↦
        (K.adaptiveFanVertexSource U hU f p).1) := by
  classical
  let c : {p // p ∈ K.adaptiveFanFaceVertices U hU f} :=
    ⟨K.adaptiveFaceCenter U f.1, by
      simp [adaptiveFanFaceVertices]⟩
  let p : {p // p ∈ K.adaptiveFanFaceVertices U hU f} :=
    ⟨K.adaptiveEdgeIntervalFirst U hU f.1 f.2.1 f.2.2, by
      simp [adaptiveFanFaceVertices]⟩
  let q : {p // p ∈ K.adaptiveFanFaceVertices U hU f} :=
    ⟨K.adaptiveEdgeIntervalSecond U hU f.1 f.2.1 f.2.2, by
      simp [adaptiveFanFaceVertices]⟩
  let opposite :=
    (K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 (f.2.1 + 2)
  let H : AffineSubspace ℝ
      ((K.safeSubdivision f.1.1).refined.Vertex → ℝ) :=
    (LinearMap.ker (LinearMap.proj opposite)).toAffineSubspace
  have hpH : (K.adaptiveFanVertexSource U hU f p).1 ∈ H := by
    change (K.adaptiveFanVertexSource U hU f p).1 opposite = 0
    simpa only [p, opposite, adaptiveFanVertexSource] using
      K.adaptiveEdgeIntervalFirst_source_opposite U hU f.1 f.2.1 f.2.2
  have hqH : (K.adaptiveFanVertexSource U hU f q).1 ∈ H := by
    change (K.adaptiveFanVertexSource U hU f q).1 opposite = 0
    simpa only [q, opposite, adaptiveFanVertexSource] using
      K.adaptiveEdgeIntervalSecond_source_opposite U hU f.1 f.2.1 f.2.2
  have hcH : (K.adaptiveFanVertexSource U hU f c).1 ∉ H := by
    intro hc
    have hzero : (K.adaptiveFanVertexSource U hU f c).1 opposite = 0 := hc
    have hone : (K.adaptiveFanVertexSource U hU f c).1 opposite = 1 / 3 := by
      simpa only [c, opposite, adaptiveFanVertexSource] using
        K.adaptiveFaceCenter_source_apply U f.1 (f.2.1 + 2)
    linarith
  have hpq : (K.adaptiveFanVertexSource U hU f p).1 ≠
      (K.adaptiveFanVertexSource U hU f q).1 := by
    intro heq
    have hpqSubtype := K.adaptiveFanVertexSource_val_injective U hU f heq
    exact K.adaptiveEdgeIntervalFirst_ne_second U hU f.1 f.2.1 f.2.2
      (congrArg Subtype.val hpqSubtype)
  have hthree : AffineIndependent ℝ ![
      (K.adaptiveFanVertexSource U hU f p).1,
      (K.adaptiveFanVertexSource U hU f q).1,
      (K.adaptiveFanVertexSource U hU f c).1] :=
    affineIndependent_of_ne_of_mem_of_mem_of_notMem hpq hpH hqH hcH
  let source := fun r : {r // r ∈ K.adaptiveFanFaceVertices U hU f} ↦
    (K.adaptiveFanVertexSource U hU f r).1
  have hrange : Set.range source = Set.range ![source p, source q, source c] := by
    ext z
    constructor
    · rintro ⟨r, rfl⟩
      have hr := r.2
      simp only [adaptiveFanFaceVertices, Finset.mem_insert,
        Finset.mem_singleton] at hr
      rcases hr with hr | hr | hr
      · have hrc : r = c := Subtype.ext hr
        subst r
        exact ⟨2, by simp⟩
      · have hrp : r = p := Subtype.ext hr
        subst r
        exact ⟨0, by simp⟩
      · have hrq : r = q := Subtype.ext hr
        subst r
        exact ⟨1, by simp⟩
    · rintro ⟨r, rfl⟩
      fin_cases r
      · exact ⟨p, by simp⟩
      · exact ⟨q, by simp⟩
      · exact ⟨c, by simp⟩
  apply AffineIndependent.of_set_of_injective
  · rw [hrange]
    exact hthree.range
  · exact K.adaptiveFanVertexSource_val_injective U hU f

/-- The affine combination map is injective when its source points are affinely independent. -/
theorem affineCombination_injective_of_affineIndependent
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (source : ι → E) (hsource : AffineIndependent ℝ source) :
    Function.Injective (fun x : stdSimplex ℝ ι ↦
      Finset.univ.affineCombination ℝ source x) := by
  intro x y hxy
  have hweights := (hsource.affineCombination_eq_iff_eq x.2.2 y.2.2).mp hxy
  exact Subtype.ext (funext fun i ↦ hweights i (Finset.mem_univ i))

theorem simplex_eq_of_weighted_sum_eq_of_affineIndependent
    {ι α : Type*} [Fintype ι]
    (source : ι → α → ℝ) (hsource : AffineIndependent ℝ source)
    {x y : stdSimplex ℝ ι}
    (hxy : (fun v ↦ ∑ p, x p * source p v) =
      (fun v ↦ ∑ p, y p * source p v)) :
    x = y := by
  apply affineCombination_injective_of_affineIndependent source hsource
  change Finset.univ.affineCombination ℝ source x =
    Finset.univ.affineCombination ℝ source y
  rw [Finset.univ.affineCombination_eq_linear_combination source x x.2.2,
    Finset.univ.affineCombination_eq_linear_combination source y y.2.2]
  funext v
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hxy v

/-- The coordinate function underlying an adaptive fan source point. -/
theorem adaptiveFanSourcePoint_val (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    (K.adaptiveFanSourcePoint U hU f x).1 =
      (fun v ↦ ∑ p, x p * (K.adaptiveFanVertexSource U hU f p).1 v) := by
  rfl

/-- The standard simplex parametrizing one adaptive fan face. -/
abbrev adaptiveFanSimplex (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :=
  stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}

/-- The coordinate-valued source-point map used for injectivity. -/
noncomputable def adaptiveFanSourcePointVal (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    K.adaptiveFanSimplex U hU f →
      (K.safeSubdivision f.1.1).refined.Vertex → ℝ :=
  fun x ↦ (K.adaptiveFanSourcePoint U hU f x).1

theorem adaptiveFanSourcePoint_val_injective (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Function.Injective (K.adaptiveFanSourcePointVal U hU f) := by
  intro x y hxy
  let source : {p // p ∈ K.adaptiveFanFaceVertices U hU f} →
      (K.safeSubdivision f.1.1).refined.Vertex → ℝ :=
    fun p ↦ (K.adaptiveFanVertexSource U hU f p).1
  apply simplex_eq_of_weighted_sum_eq_of_affineIndependent source
    (K.affineIndependent_adaptiveFanVertexSource_val U hU f)
  change (fun v ↦ ∑ p, x p * (K.adaptiveFanVertexSource U hU f p).1 v) =
    (fun v ↦ ∑ p, y p * (K.adaptiveFanVertexSource U hU f p).1 v) at hxy
  simpa only [source, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hxy

/-- One parametrized fan triangle in the open subspace. -/
noncomputable def adaptiveFanFaceMap (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    K.adaptiveFanSimplex U hU f → U :=
  fun x ↦ ⟨(K.safeSubdivision f.1.1).homeo
      (K.adaptiveFanSourcePoint U hU f x),
    K.adaptiveFaceCarrier_subset U f.1
      ⟨K.adaptiveFanSourcePoint U hU f x,
        K.adaptiveFanSourcePoint_mem_carrier U hU f x, rfl⟩⟩

/-- A fan parametrization sends each abstract vertex to its declared geometric point. -/
theorem adaptiveFanFaceMap_vertex (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (p : {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    K.adaptiveFanFaceMap U hU f (stdSimplex.vertex p) = ⟨p.1,
      K.adaptiveFaceCarrier_subset U f.1
        (K.adaptiveFanVertex_mem_carrier U hU f p.2)⟩ := by
  apply Subtype.ext
  change (K.safeSubdivision f.1.1).homeo
      (K.adaptiveFanSourcePoint U hU f (stdSimplex.vertex p)) = p.1
  rw [K.adaptiveFanSourcePoint_vertex U hU f p]
  exact (K.safeSubdivision f.1.1).homeo.apply_symm_apply p.1

theorem adaptiveFanFaceMap_injective (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Function.Injective (K.adaptiveFanFaceMap U hU f) := by
  intro x y hxy
  apply K.adaptiveFanSourcePoint_val_injective U hU f
  exact congrArg Subtype.val ((K.safeSubdivision f.1.1).homeo.injective
    (congrArg Subtype.val hxy))

/-- Within one adaptive tile, a geometric point determines its cone-center weight.  This is the
minimum-coordinate characterization of radial coordinates in a triangle. -/
theorem adaptiveFanCenterWeight_eq_of_faceMap_eq_of_tile_eq
    (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i j : ZMod 3) (a : K.AdaptiveEdgeInterval U hU t i)
    (b : K.AdaptiveEdgeInterval U hU t j)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩}}
    (hxy : K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x =
      K.adaptiveFanFaceMap U hU ⟨t, j, b⟩ y) :
    x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) =
      y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) := by
  have hsource :
      K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x =
        K.adaptiveFanSourcePoint U hU ⟨t, j, b⟩ y := by
    apply (K.safeSubdivision t.1).homeo.injective
    exact congrArg Subtype.val hxy
  have hsourceVal := congrArg Subtype.val hsource
  have hxOpp := K.adaptiveFanSourcePoint_opposite U hU ⟨t, i, a⟩ x
  have hyAtX := K.adaptiveFanSourcePoint_faceVertex_lower_bound U hU
    ⟨t, j, b⟩ y (i + 2)
  have hyOpp := K.adaptiveFanSourcePoint_opposite U hU ⟨t, j, b⟩ y
  have hxAtY := K.adaptiveFanSourcePoint_faceVertex_lower_bound U hU
    ⟨t, i, a⟩ x (j + 2)
  have hleYX : y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) ≤
      x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) := by
    have hcoord := congrFun hsourceVal
      ((K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 2))
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).mp
    calc
      y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) / 3 ≤
          (K.adaptiveFanSourcePoint U hU ⟨t, j, b⟩ y).1
            ((K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 2)) := hyAtX
      _ = (K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x).1
            ((K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 2)) := hcoord.symm
      _ = x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) / 3 := by
        simpa only using hxOpp
  have hleXY : x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) ≤
      y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) := by
    have hcoord := congrFun hsourceVal
      ((K.safeSubdivision t.1).refined.faceVertex t.2.1 (j + 2))
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).mp
    calc
      x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) / 3 ≤
          (K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x).1
            ((K.safeSubdivision t.1).refined.faceVertex t.2.1 (j + 2)) := hxAtY
      _ = (K.adaptiveFanSourcePoint U hU ⟨t, j, b⟩ y).1
            ((K.safeSubdivision t.1).refined.faceVertex t.2.1 (j + 2)) := hcoord
      _ = y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) / 3 := by
        simpa only using hyOpp
  exact le_antisymm hleXY hleYX

/-- After removing the common cone-center contribution, equal points in one tile have equal
radial projections to the tile boundary.  The shared tile is explicit to avoid dependent
transport through the two interval types. -/
theorem adaptiveFanNormalizedBaseFaceMap_eq_of_same_tile
    (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i j : ZMod 3) (a : K.AdaptiveEdgeInterval U hU t i)
    (b : K.AdaptiveEdgeInterval U hU t j)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩}}
    (hxy : K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x =
      K.adaptiveFanFaceMap U hU ⟨t, j, b⟩ y)
    (hxCenter : x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) < 1)
    (hyCenter : y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) < 1) :
    K.adaptiveFanFaceMap U hU ⟨t, i, a⟩
        (K.adaptiveFanNormalizedBasePoint U hU ⟨t, i, a⟩ x hxCenter) =
      K.adaptiveFanFaceMap U hU ⟨t, j, b⟩
        (K.adaptiveFanNormalizedBasePoint U hU ⟨t, j, b⟩ y hyCenter) := by
  let cx := x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩)
  let cy := y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩)
  have hc : cx = cy :=
    K.adaptiveFanCenterWeight_eq_of_faceMap_eq_of_tile_eq U hU t i j a b hxy
  have hsource :
      K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x =
        K.adaptiveFanSourcePoint U hU ⟨t, j, b⟩ y := by
    apply (K.safeSubdivision t.1).homeo.injective
    exact congrArg Subtype.val hxy
  have hxLine := K.adaptiveFanSourcePoint_eq_lineMap_normalizedBase
    U hU ⟨t, i, a⟩ x hxCenter
  have hyLine := K.adaptiveFanSourcePoint_eq_lineMap_normalizedBase
    U hU ⟨t, j, b⟩ y hyCenter
  have hcenterSource :
      (K.adaptiveFanVertexSource U hU ⟨t, i, a⟩
          (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩)).1 =
        (K.adaptiveFanVertexSource U hU ⟨t, j, b⟩
          (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩)).1 := by
    rfl
  have hbaseVal :
      (K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩
        (K.adaptiveFanNormalizedBasePoint U hU ⟨t, i, a⟩ x hxCenter)).1 =
      (K.adaptiveFanSourcePoint U hU ⟨t, j, b⟩
        (K.adaptiveFanNormalizedBasePoint U hU ⟨t, j, b⟩ y hyCenter)).1 := by
    funext v
    have hline :
        AffineMap.lineMap
            (K.adaptiveFanVertexSource U hU ⟨t, i, a⟩
              (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩)).1
            (K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩
              (K.adaptiveFanNormalizedBasePoint U hU ⟨t, i, a⟩ x hxCenter)).1
            (1 - cx) =
          AffineMap.lineMap
            (K.adaptiveFanVertexSource U hU ⟨t, j, b⟩
              (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩)).1
            (K.adaptiveFanSourcePoint U hU ⟨t, j, b⟩
              (K.adaptiveFanNormalizedBasePoint U hU ⟨t, j, b⟩ y hyCenter)).1
            (1 - cy) := by
      rw [← hxLine, ← hyLine]
      exact congrArg Subtype.val hsource
    have hcoord := congrFun hline v
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module,
      ← hc, ← hcenterSource] at hcoord
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    have hd : 1 - cx ≠ 0 := (sub_pos.mpr hxCenter).ne'
    apply mul_left_cancel₀ hd
    nlinarith
  apply Subtype.ext
  change (K.safeSubdivision t.1).homeo
      (K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩
        (K.adaptiveFanNormalizedBasePoint U hU ⟨t, i, a⟩ x hxCenter)) =
    (K.safeSubdivision t.1).homeo
      (K.adaptiveFanSourcePoint U hU ⟨t, j, b⟩
        (K.adaptiveFanNormalizedBasePoint U hU ⟨t, j, b⟩ y hyCenter))
  apply congrArg (K.safeSubdivision t.1).homeo
  exact Subtype.ext hbaseVal

theorem continuous_adaptiveFanSourcePoint (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Continuous (K.adaptiveFanSourcePoint U hU f) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  apply continuous_finsetSum
  intro p _
  exact ((continuous_apply p).comp continuous_subtype_val).mul continuous_const

theorem continuous_adaptiveFanFaceMap (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Continuous (K.adaptiveFanFaceMap U hU f) := by
  apply Continuous.subtype_mk
  exact (K.safeSubdivision f.1.1).homeo.continuous.comp
    (K.continuous_adaptiveFanSourcePoint U hU f)

/-- The geometric interval path along a resolved fan base. -/
noncomputable def adaptiveFanBasePath (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) : Set.Icc (0 : ℝ) 1 → U :=
  K.adaptiveFanFaceMap U hU f ∘ K.adaptiveFanBaseSimplexPath U hU f

theorem continuous_adaptiveFanBasePath (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Continuous (K.adaptiveFanBasePath U hU f) :=
  (K.continuous_adaptiveFanFaceMap U hU f).comp
    (K.continuous_adaptiveFanBaseSimplexPath U hU f)

theorem adaptiveFanBasePath_injective (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Function.Injective (K.adaptiveFanBasePath U hU f) :=
  (K.adaptiveFanFaceMap_injective U hU f).comp
    (K.adaptiveFanBaseSimplexPath_injective U hU f)

/-- In refined barycentric coordinates, the canonical fan-base path is the line segment between
the two pulled-back endpoint vertices. -/
theorem adaptiveFanSourcePoint_baseSimplexPath_val (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) (r : Set.Icc (0 : ℝ) 1) :
    (K.adaptiveFanSourcePoint U hU f
        (K.adaptiveFanBaseSimplexPath U hU f r)).1 =
      AffineMap.lineMap
        (K.adaptiveFanVertexSource U hU f
          (K.adaptiveFanFirstVertex U hU f)).1
        (K.adaptiveFanVertexSource U hU f
          (K.adaptiveFanSecondVertex U hU f)).1 r.1 := by
  classical
  let c := K.adaptiveFanCenterVertex U hU f
  let p := K.adaptiveFanFirstVertex U hU f
  let q := K.adaptiveFanSecondVertex U hU f
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, K.adaptiveFanCenterVertex_ne_first U hU f,
      K.adaptiveFanCenterVertex_ne_second U hU f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, K.adaptiveFanFirstVertex_ne_second U hU f]
  funext v
  change (∑ z, K.adaptiveFanBaseSimplexPath U hU f r z *
      (K.adaptiveFanVertexSource U hU f z).1 v) = _
  rw [K.adaptiveFanVertex_univ U hU f,
    Finset.sum_insert hcNot, Finset.sum_insert hpNot, Finset.sum_singleton]
  rw [K.adaptiveFanBaseSimplexPath_apply_center U hU f r,
    K.adaptiveFanBaseSimplexPath_apply_first U hU f r,
    K.adaptiveFanBaseSimplexPath_apply_second U hU f r]
  simp only [zero_mul, zero_add, AffineMap.lineMap_apply_module, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Faithfulness of the iterated subdivision makes every geometric fan-base path the literal
ambient affine segment between its two declared endpoints. -/
theorem adaptiveFanBasePath_val_eq_lineMap (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) (r : Set.Icc (0 : ℝ) 1) :
    (K.adaptiveFanBasePath U hU f r).1.1 =
      AffineMap.lineMap
        (K.adaptiveFanFirstVertex U hU f).1.1
        (K.adaptiveFanSecondVertex U hU f).1.1 r.1 := by
  let R := K.safeSubdivision f.1.1
  obtain ⟨a, ha⟩ := R.affineOnFace f.1.2.1.1 f.1.2.1.2
  let z := K.adaptiveFanSourcePoint U hU f
    (K.adaptiveFanBaseSimplexPath U hU f r)
  let p := K.adaptiveFanVertexSource U hU f
    (K.adaptiveFanFirstVertex U hU f)
  let q := K.adaptiveFanVertexSource U hU f
    (K.adaptiveFanSecondVertex U hU f)
  have hz : z.1 = AffineMap.lineMap p.1 q.1 r.1 :=
    K.adaptiveFanSourcePoint_baseSimplexPath_val U hU f r
  have hpCarrier : p ∈ R.refined.faceCarrier f.1.2.1.1 :=
    K.adaptiveFanVertexSource_mem_carrier U hU f
      (K.adaptiveFanFirstVertex U hU f)
  have hqCarrier : q ∈ R.refined.faceCarrier f.1.2.1.1 :=
    K.adaptiveFanVertexSource_mem_carrier U hU f
      (K.adaptiveFanSecondVertex U hU f)
  have hzCarrier : z ∈ R.refined.faceCarrier f.1.2.1.1 :=
    K.adaptiveFanSourcePoint_mem_carrier U hU f _
  have hpImage : a p.1 = (K.adaptiveFanFirstVertex U hU f).1.1 := by
    rw [← ha p hpCarrier]
    change (R.homeo (R.homeo.symm (K.adaptiveFanFirstVertex U hU f).1)).1 = _
    rw [R.homeo.apply_symm_apply]
  have hqImage : a q.1 = (K.adaptiveFanSecondVertex U hU f).1.1 := by
    rw [← ha q hqCarrier]
    change (R.homeo (R.homeo.symm (K.adaptiveFanSecondVertex U hU f).1)).1 = _
    rw [R.homeo.apply_symm_apply]
  change (R.homeo z).1 = _
  rw [ha z hzCarrier, hz, AffineMap.apply_lineMap, hpImage, hqImage]

theorem adaptiveFanBaseSimplexPath_zero (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    K.adaptiveFanBaseSimplexPath U hU f ⟨0, by simp⟩ =
      stdSimplex.vertex (K.adaptiveFanFirstVertex U hU f) := by
  apply Subtype.ext
  simp [adaptiveFanBaseSimplexPath, AffineMap.lineMap_apply_module]

theorem adaptiveFanBaseSimplexPath_one (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    K.adaptiveFanBaseSimplexPath U hU f ⟨1, by simp⟩ =
      stdSimplex.vertex (K.adaptiveFanSecondVertex U hU f) := by
  apply Subtype.ext
  simp [adaptiveFanBaseSimplexPath, AffineMap.lineMap_apply_module]

theorem adaptiveFanBasePath_zero (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    K.adaptiveFanBasePath U hU f ⟨0, by simp⟩ =
      ⟨(K.adaptiveFanFirstVertex U hU f).1,
        K.adaptiveFaceCarrier_subset U f.1
          (K.adaptiveFanVertex_mem_carrier U hU f
            (K.adaptiveFanFirstVertex U hU f).2)⟩ := by
  rw [adaptiveFanBasePath, Function.comp_apply,
    K.adaptiveFanBaseSimplexPath_zero U hU f,
    K.adaptiveFanFaceMap_vertex U hU f]

theorem adaptiveFanBasePath_one (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    K.adaptiveFanBasePath U hU f ⟨1, by simp⟩ =
      ⟨(K.adaptiveFanSecondVertex U hU f).1,
        K.adaptiveFaceCarrier_subset U f.1
          (K.adaptiveFanVertex_mem_carrier U hU f
            (K.adaptiveFanSecondVertex U hU f).2)⟩ := by
  rw [adaptiveFanBasePath, Function.comp_apply,
    K.adaptiveFanBaseSimplexPath_one U hU f,
    K.adaptiveFanFaceMap_vertex U hU f]

/-- A zero-center barycentric point is determined by its second base weight. -/
theorem adaptiveFanBaseSimplexPath_eq_of_secondWeight (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (r : Set.Icc (0 : ℝ) 1)
    (hr : r.1 = x (K.adaptiveFanSecondVertex U hU f))
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0) :
    K.adaptiveFanBaseSimplexPath U hU f r = x := by
  have hsum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU f x hxCenter
  apply Subtype.ext
  funext p
  have hp := p.2
  simp only [adaptiveFanFaceVertices, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hp | hp | hp
  · have hpc : p = K.adaptiveFanCenterVertex U hU f := Subtype.ext hp
    subst p
    exact (K.adaptiveFanBaseSimplexPath_apply_center U hU f r).trans hxCenter.symm
  · have hpf : p = K.adaptiveFanFirstVertex U hU f := Subtype.ext hp
    subst p
    calc
      (K.adaptiveFanBaseSimplexPath U hU f r).1
          (K.adaptiveFanFirstVertex U hU f) = 1 - r.1 :=
        K.adaptiveFanBaseSimplexPath_apply_first U hU f r
      _ = x (K.adaptiveFanFirstVertex U hU f) := by
        rw [hr]
        linarith
  · have hps : p = K.adaptiveFanSecondVertex U hU f := Subtype.ext hp
    subst p
    exact (K.adaptiveFanBaseSimplexPath_apply_second U hU f r).trans hr

/-- Every zero-center barycentric point has its declared second base weight as the canonical
base-path parameter. -/
theorem adaptiveFanBaseSimplexPath_secondWeight (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0) :
    K.adaptiveFanBaseSimplexPath U hU f
      ⟨x (K.adaptiveFanSecondVertex U hU f), ⟨x.2.1 _, by
        have hsum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU f x hxCenter
        have hxFirst := x.2.1 (K.adaptiveFanFirstVertex U hU f)
        exact (le_add_of_nonneg_left hxFirst).trans_eq hsum⟩⟩ = x := by
  apply K.adaptiveFanBaseSimplexPath_eq_of_secondWeight U hU f x
  · rfl
  · exact hxCenter

theorem adaptiveFanBasePath_mem_baseEdge (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) (r : Set.Icc (0 : ℝ) 1) :
    (K.adaptiveFanBasePath U hU f r).1 ∈
      K.levelFaceEdgeCarrier f.1.2.1 f.2.1 := by
  refine ⟨K.adaptiveFanSourcePoint U hU f
      (K.adaptiveFanBaseSimplexPath U hU f r), ?_, rfl⟩
  apply K.adaptiveFanSourcePoint_mem_baseEdge_of_center_eq_zero U hU
  exact K.adaptiveFanBaseSimplexPath_apply_center U hU f r

theorem range_adaptiveFanFaceMap_subset_tile (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    Set.range (K.adaptiveFanFaceMap U hU f) ⊆
      K.adaptiveFaceCarrierInOpen U f.1 := by
  rintro p ⟨x, rfl⟩
  exact ⟨K.adaptiveFanSourcePoint U hU f x,
    K.adaptiveFanSourcePoint_mem_carrier U hU f x, rfl⟩

omit [AdaptiveSafety.IsAdmissible K U] in
/-- The adaptive face chart takes a transported cyclic edge to the matching standard edge. -/
theorem adaptiveFacePlaneHomeomorph_mem_edge
    (t : K.AdaptiveFace U) (i : ZMod 3) {p : K.realization}
    (hpEdge : p ∈ K.levelFaceEdgeCarrier t.2.1 i) :
    (K.adaptiveFacePlaneHomeomorph U t
      ⟨p, K.levelFaceEdgeCarrier_subset t.2.1 i hpEdge⟩).1 ∈
      standardTriangleCircle.edgeSegment i := by
  rw [← (K.safeSubdivision t.1).refined.facePlaneHomeomorph_image_edge t.2.1 i]
  let x : (K.safeSubdivision t.1).refined.ClosedFace t.2.1 :=
    ⟨(K.safeSubdivision t.1).homeo.symm p,
      K.levelFaceHomeoSymm_mem_carrier t.2.1
        (K.levelFaceEdgeCarrier_subset t.2.1 i hpEdge)⟩
  refine ⟨x, K.homeo_symm_mem_levelFaceEdgeCarrier t.2.1 i hpEdge, ?_⟩
  rfl

omit [AdaptiveSafety.IsAdmissible K U] in
theorem adaptiveFacePlaneHomeomorph_mem_edge_iff
    (t : K.AdaptiveFace U) (i : ZMod 3) {p : K.realization}
    (hp : p ∈ K.adaptiveFaceCarrier U t) :
    (K.adaptiveFacePlaneHomeomorph U t ⟨p, hp⟩).1 ∈
        standardTriangleCircle.edgeSegment i ↔
      p ∈ K.levelFaceEdgeCarrier t.2.1 i := by
  constructor
  · intro hchart
    rw [← (K.safeSubdivision t.1).refined.facePlaneHomeomorph_image_edge t.2.1 i]
      at hchart
    obtain ⟨x, hxEdge, hxchart⟩ := hchart
    let y : (K.safeSubdivision t.1).refined.ClosedFace t.2.1 :=
      K.adaptiveFaceSourceHomeomorph U t ⟨p, hp⟩
    have hyx : y = x := by
      apply (K.safeSubdivision t.1).refined.facePlaneHomeomorph t.2.1 |>.injective
      apply Subtype.ext
      exact hxchart.symm
    refine ⟨x.1, hxEdge, ?_⟩
    rw [← hyx]
    exact (K.safeSubdivision t.1).homeo.apply_symm_apply p
  · intro hpEdge
    simpa only using K.adaptiveFacePlaneHomeomorph_mem_edge U t i hpEdge

omit [AdaptiveSafety.IsAdmissible K U] in
/-- The adaptive tile barycenter is an interior point in the standard plane chart. -/
theorem adaptiveFacePlaneCenter_mem_interior (t : K.AdaptiveFace U) :
    (K.adaptiveFacePlaneHomeomorph U t
      ⟨K.adaptiveFaceCenter U t, K.adaptiveFaceCenter_mem_carrier U t⟩).1 ∈
        interior standardTrianglePlaneComplex.support := by
  let c := K.adaptiveFacePlaneHomeomorph U t
    ⟨K.adaptiveFaceCenter U t, K.adaptiveFaceCenter_mem_carrier U t⟩
  have hclosed : IsClosed standardTrianglePlaneComplex.support :=
    standardTrianglePlaneComplex_isTriangle.isCompact.isClosed
  by_contra hc
  have hcFrontier : c.1 ∈ frontier standardTrianglePlaneComplex.support := by
    rw [hclosed.frontier_eq]
    exact ⟨c.2, hc⟩
  have hcCircle : c.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier, ← standardTrianglePlaneComplex_support]
    exact hcFrontier
  obtain ⟨i, hci⟩ := Set.mem_iUnion.mp hcCircle
  change ZMod 3 at i
  have hcEdge : K.adaptiveFaceCenter U t ∈
      K.levelFaceEdgeCarrier t.2.1 i :=
    (K.adaptiveFacePlaneHomeomorph_mem_edge_iff U t i
      (K.adaptiveFaceCenter_mem_carrier U t)).mp hci
  have hzero := K.homeo_symm_apply_eq_zero_of_mem_levelFaceEdgeCarrier
    t.2.1 i hcEdge (K.faceVertex_add_two_not_mem_faceEdge t.2.1 i)
  have honeThird := K.adaptiveFaceCenter_source_apply U t (i + 2)
  rw [honeThird] at hzero
  norm_num at hzero

omit [AdaptiveSafety.IsAdmissible K U] in
/-- The inverse adaptive face chart is given by the explicit affine inverse in refined
barycentric coordinates. -/
theorem adaptiveFaceSourceHomeomorph_val_eq_planeInverseAffine
    (t : K.AdaptiveFace U) (p : K.AdaptiveClosedFace U t) :
    (K.adaptiveFaceSourceHomeomorph U t p).1.1 =
      (K.safeSubdivision t.1).refined.facePlaneInverseAffine t.2.1
        (K.adaptiveFacePlaneHomeomorph U t p).1 := by
  have h := (K.safeSubdivision t.1).refined.facePlaneHomeomorph_symm_val
    t.2.1 (K.adaptiveFacePlaneHomeomorph U t p)
  simpa only [adaptiveFacePlaneHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply] using h

omit [AdaptiveSafety.IsAdmissible K U] in
/-- A radial segment in the plane tile chart pulls back to the corresponding affine segment in
the refined barycentric face. -/
theorem adaptiveFaceSource_val_eq_lineMap_of_plane_eq
    (t : K.AdaptiveFace U) (p q : K.AdaptiveClosedFace U t)
    (r : ℝ)
    (hplane : (K.adaptiveFacePlaneHomeomorph U t p).1 =
      AffineMap.lineMap
        (K.adaptiveFacePlaneHomeomorph U t
          ⟨K.adaptiveFaceCenter U t, K.adaptiveFaceCenter_mem_carrier U t⟩).1
        (K.adaptiveFacePlaneHomeomorph U t q).1 r) :
    ((K.safeSubdivision t.1).homeo.symm p.1).1 =
      AffineMap.lineMap
        ((K.safeSubdivision t.1).homeo.symm (K.adaptiveFaceCenter U t)).1
        ((K.safeSubdivision t.1).homeo.symm q.1).1 r := by
  let c : K.AdaptiveClosedFace U t :=
    ⟨K.adaptiveFaceCenter U t, K.adaptiveFaceCenter_mem_carrier U t⟩
  calc
    ((K.safeSubdivision t.1).homeo.symm p.1).1 =
        (K.safeSubdivision t.1).refined.facePlaneInverseAffine t.2.1
          (K.adaptiveFacePlaneHomeomorph U t p).1 :=
      K.adaptiveFaceSourceHomeomorph_val_eq_planeInverseAffine U t p
    _ = (K.safeSubdivision t.1).refined.facePlaneInverseAffine t.2.1
          (AffineMap.lineMap (K.adaptiveFacePlaneHomeomorph U t c).1
            (K.adaptiveFacePlaneHomeomorph U t q).1 r) := by rw [hplane]
    _ = AffineMap.lineMap
          ((K.safeSubdivision t.1).refined.facePlaneInverseAffine t.2.1
            (K.adaptiveFacePlaneHomeomorph U t c).1)
          ((K.safeSubdivision t.1).refined.facePlaneInverseAffine t.2.1
            (K.adaptiveFacePlaneHomeomorph U t q).1) r := by
      rw [AffineMap.apply_lineMap]
    _ = AffineMap.lineMap
          ((K.safeSubdivision t.1).homeo.symm (K.adaptiveFaceCenter U t)).1
          ((K.safeSubdivision t.1).homeo.symm q.1).1 r := by
      rw [← K.adaptiveFaceSourceHomeomorph_val_eq_planeInverseAffine U t c,
        ← K.adaptiveFaceSourceHomeomorph_val_eq_planeInverseAffine U t q]
      rfl

omit [AdaptiveSafety.IsAdmissible K U] in
/-- The adaptive face chart carries the relative boundary of a tile into the standard
polygonal triangle boundary. -/
theorem adaptiveFacePlaneHomeomorph_mem_standardCircle_of_not_relInterior
    (t : K.AdaptiveFace U) {p : K.realization}
    (hp : p ∈ K.adaptiveFaceCarrier U t)
    (hpNot : p ∉ K.adaptiveFaceRelInterior U t) :
    (K.adaptiveFacePlaneHomeomorph U t ⟨p, hp⟩).1 ∈
      standardTriangleCircle.carrier := by
  obtain ⟨i, hpEdge⟩ := K.exists_levelFaceEdge_of_mem_not_relInterior t.2.1 hp hpNot
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  simpa only using K.adaptiveFacePlaneHomeomorph_mem_edge U t i hpEdge

/-- A point which an adaptive face chart sends to a standard triangle corner is one of that
tile's collected boundary marks. -/
theorem mem_boundaryVertices_of_adaptiveFacePlaneHomeomorph_eq_vertex
    (hU : IsOpen U) (t : K.AdaptiveFace U) {p : K.realization}
    (hp : p ∈ K.adaptiveFaceCarrier U t) (j : ZMod 3)
    (hpj : (K.adaptiveFacePlaneHomeomorph U t ⟨p, hp⟩).1 =
      standardTriangleCircle.vertex j) :
    p ∈ K.boundaryVertices U hU t := by
  let R := K.safeSubdivision t.1
  let q : Fin 3 := (ZMod.finEquiv 3).symm j
  let x : R.refined.ClosedFace t.2.1 :=
    ⟨R.homeo.symm p, K.levelFaceHomeoSymm_mem_carrier t.2.1 hp⟩
  have hchart : (R.refined.facePlaneHomeomorph t.2.1 x).1 =
      standardTriangleVertex q := by
    simpa [R, x, q, adaptiveFacePlaneHomeomorph, adaptiveFaceSourceHomeomorph,
      standardTriangleCircle] using hpj
  have hxval : x.1.1 =
      Pi.single (R.refined.faceVertexEmbedding t.2.1 q) 1 := by
    calc
      x.1.1 = ((R.refined.facePlaneHomeomorph t.2.1).symm
          (R.refined.facePlaneHomeomorph t.2.1 x)).1.1 := by
        rw [(R.refined.facePlaneHomeomorph t.2.1).symm_apply_apply]
      _ = R.refined.facePlaneInverseAffine t.2.1
          (R.refined.facePlaneHomeomorph t.2.1 x).1 :=
        R.refined.facePlaneHomeomorph_symm_val t.2.1 _
      _ = Pi.single (R.refined.faceVertexEmbedding t.2.1 q) 1 := by
        rw [hchart, R.refined.facePlaneInverseAffine_standardVertex]
  let v₀ : R.refined.Vertex := R.refined.faceVertexEmbedding t.2.1 q
  have hv₀ : v₀ ∈ t.2.1.1 := (R.refined.faceVertexEquiv t.2.1 q).2
  let v : K.AdaptiveVertexOccurrence U t := ⟨v₀, hv₀⟩
  have hxpoint : x.1 = R.refined.facePoint t.2.1 ⟨v₀, hv₀⟩ := by
    apply Subtype.ext
    rw [R.refined.facePoint_val]
    exact hxval
  have hpv : p = K.adaptiveVertexPoint U t v := by
    calc
      p = R.homeo (R.homeo.symm p) := (R.homeo.apply_symm_apply p).symm
      _ = R.homeo (R.refined.facePoint t.2.1 ⟨v₀, hv₀⟩) :=
        congrArg R.homeo hxpoint
      _ = K.adaptiveVertexPoint U t v := rfl
  rw [hpv]
  exact K.adaptiveVertexPoint_mem_boundaryVertices U hU t v

theorem continuous_levelFaceEdgeParameter {n : ℕ}
    (t : K.LevelFace n) (i : ZMod 3) :
    Continuous (K.levelFaceEdgeParameter t i) := by
  unfold levelFaceEdgeParameter
  exact ((continuous_apply
      ((K.safeSubdivision n).refined.faceVertex t (i + 1))).comp
        continuous_subtype_val).comp
    (K.safeSubdivision n).homeo.symm.continuous

/-- Along a fan base, the ambient edge parameter is the convex combination of the two endpoint
parameters with the two remaining simplex weights. -/
theorem levelFaceEdgeParameter_adaptiveFanFaceMap_of_center_eq_zero
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0) :
    K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanFaceMap U hU f x).1 =
      x (K.adaptiveFanFirstVertex U hU f) *
          K.levelFaceEdgeParameter f.1.2.1 f.2.1
            (K.adaptiveFanFirstVertex U hU f).1 +
        x (K.adaptiveFanSecondVertex U hU f) *
          K.levelFaceEdgeParameter f.1.2.1 f.2.1
            (K.adaptiveFanSecondVertex U hU f).1 := by
  classical
  let c := K.adaptiveFanCenterVertex U hU f
  let p := K.adaptiveFanFirstVertex U hU f
  let q := K.adaptiveFanSecondVertex U hU f
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, K.adaptiveFanCenterVertex_ne_first U hU f,
      K.adaptiveFanCenterVertex_ne_second U hU f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, K.adaptiveFanFirstVertex_ne_second U hU f]
  have hsymm : (K.safeSubdivision f.1.1).homeo.symm
      (K.adaptiveFanFaceMap U hU f x).1 =
        K.adaptiveFanSourcePoint U hU f x := by
    exact (K.safeSubdivision f.1.1).homeo.symm_apply_apply _
  unfold levelFaceEdgeParameter
  rw [hsymm]
  change (∑ r, x r * (K.adaptiveFanVertexSource U hU f r).1
      ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 (f.2.1 + 1))) = _
  rw [K.adaptiveFanVertex_univ U hU f,
    Finset.sum_insert hcNot, Finset.sum_insert hpNot, Finset.sum_singleton]
  change x c * _ + (x p * _ + x q * _) = _
  rw [show x c = 0 from hxCenter]
  simp only [zero_mul, zero_add]
  rfl

theorem levelFaceEdgeParameter_adaptiveFanFaceMap_mem_Icc_of_center_eq_zero
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0) :
    K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanFaceMap U hU f x).1 ∈ Set.Icc
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanFirstVertex U hU f).1)
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanSecondVertex U hU f).1) := by
  have hformula :=
    K.levelFaceEdgeParameter_adaptiveFanFaceMap_of_center_eq_zero U hU f x hxCenter
  have hsum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU f x hxCenter
  have hfirst := K.adaptiveEdgeInterval_parameter_lt U hU f.1 f.2.1 f.2.2
  have hxFirst := x.2.1 (K.adaptiveFanFirstVertex U hU f)
  have hxSecond := x.2.1 (K.adaptiveFanSecondVertex U hU f)
  change K.levelFaceEdgeParameter f.1.2.1 f.2.1
      (K.adaptiveFanFirstVertex U hU f).1 <
    K.levelFaceEdgeParameter f.1.2.1 f.2.1
      (K.adaptiveFanSecondVertex U hU f).1 at hfirst
  change 0 ≤ x (K.adaptiveFanFirstVertex U hU f) at hxFirst
  change 0 ≤ x (K.adaptiveFanSecondVertex U hU f) at hxSecond
  let z := K.levelFaceEdgeParameter f.1.2.1 f.2.1
    (K.adaptiveFanFaceMap U hU f x).1
  let a := K.levelFaceEdgeParameter f.1.2.1 f.2.1
    (K.adaptiveFanFirstVertex U hU f).1
  let b := K.levelFaceEdgeParameter f.1.2.1 f.2.1
    (K.adaptiveFanSecondVertex U hU f).1
  let α := x (K.adaptiveFanFirstVertex U hU f)
  let β := x (K.adaptiveFanSecondVertex U hU f)
  have hzLeft : z = a + β * (b - a) := by
    calc
      z = α * a + β * b := hformula
      _ = (α + β) * a + β * (b - a) := by ring
      _ = a + β * (b - a) := by rw [hsum, one_mul]
  have hzRight : z = b - α * (b - a) := by
    calc
      z = α * a + β * b := hformula
      _ = (α + β) * b - α * (b - a) := by ring
      _ = b - α * (b - a) := by rw [hsum, one_mul]
  constructor
  · change a ≤ z
    rw [hzLeft]
    exact le_add_of_nonneg_right (mul_nonneg hxSecond (sub_nonneg.mpr hfirst.le))
  · change z ≤ b
    rw [hzRight]
    exact sub_le_self _ (mul_nonneg hxFirst (sub_nonneg.mpr hfirst.le))

/-- Every point of a resolved adaptive edge is represented by one of its consecutive fan-base
paths. -/
theorem exists_adaptiveFanBasePath_eq_of_mem_levelFaceEdgeCarrier
    (hU : IsOpen U) (t : K.AdaptiveFace U) (i : ZMod 3)
    {p : K.realization} (hp : p ∈ K.levelFaceEdgeCarrier t.2.1 i) :
    ∃ j : K.AdaptiveEdgeInterval U hU t i, ∃ r : Set.Icc (0 : ℝ) 1,
      K.adaptiveFanBasePath U hU ⟨t, i, j⟩ r =
        ⟨p, K.adaptiveFaceCarrier_subset U t
          (K.levelFaceEdgeCarrier_subset t.2.1 i hp)⟩ := by
  let z := K.levelFaceEdgeParameter t.2.1 i p
  obtain ⟨j, hj⟩ := K.exists_adaptiveEdgeInterval_parameter_mem_Icc U hU t i
    (K.levelFaceEdgeParameter_mem_Icc t.2.1 i hp)
  let a := K.levelFaceEdgeParameter t.2.1 i
    (K.adaptiveEdgeIntervalFirst U hU t i j)
  let b := K.levelFaceEdgeParameter t.2.1 i
    (K.adaptiveEdgeIntervalSecond U hU t i j)
  have hab : 0 < b - a := sub_pos.mpr
    (K.adaptiveEdgeInterval_parameter_lt U hU t i j)
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨(z - a) / (b - a),
      div_nonneg (sub_nonneg.mpr hj.1) hab.le,
      (div_le_one hab).mpr (by linarith [hj.2])⟩
  refine ⟨j, r, ?_⟩
  apply Subtype.ext
  apply K.levelFaceEdgeParameter_injOn t.2.1 i
  · exact K.adaptiveFanBasePath_mem_baseEdge U hU ⟨t, i, j⟩ r
  · exact hp
  have hformula :=
    K.levelFaceEdgeParameter_adaptiveFanFaceMap_of_center_eq_zero U hU
      ⟨t, i, j⟩ (K.adaptiveFanBaseSimplexPath U hU ⟨t, i, j⟩ r)
      (K.adaptiveFanBaseSimplexPath_apply_center U hU ⟨t, i, j⟩ r)
  rw [K.adaptiveFanBaseSimplexPath_apply_first U hU ⟨t, i, j⟩ r,
    K.adaptiveFanBaseSimplexPath_apply_second U hU ⟨t, i, j⟩ r] at hformula
  change K.levelFaceEdgeParameter t.2.1 i
      (K.adaptiveFanBasePath U hU ⟨t, i, j⟩ r).1 = z
  rw [show K.levelFaceEdgeParameter t.2.1 i
      (K.adaptiveFanBasePath U hU ⟨t, i, j⟩ r).1 =
        (1 - r.1) * a + r.1 * b by
      simpa only [adaptiveFanBasePath, Function.comp_apply,
        adaptiveFanFirstVertex, adaptiveFanSecondVertex, a, b] using hformula]
  dsimp only [r]
  field_simp [hab.ne']
  ring

/-- The fan triangles over one adaptive tile cover the whole closed tile. -/
theorem exists_adaptiveFanFaceMap_eq_of_mem_adaptiveFaceCarrier
    (hU : IsOpen U) (t : K.AdaptiveFace U) {p : K.realization}
    (hp : p ∈ K.adaptiveFaceCarrier U t) :
    ∃ i : ZMod 3, ∃ j : K.AdaptiveEdgeInterval U hU t i,
      ∃ x : stdSimplex ℝ
        {q // q ∈ K.adaptiveFanFaceVertices U hU ⟨t, i, j⟩},
        K.adaptiveFanFaceMap U hU ⟨t, i, j⟩ x =
          ⟨p, K.adaptiveFaceCarrier_subset U t hp⟩ := by
  let pClosed : K.AdaptiveClosedFace U t := ⟨p, hp⟩
  let cClosed : K.AdaptiveClosedFace U t :=
    ⟨K.adaptiveFaceCenter U t, K.adaptiveFaceCenter_mem_carrier U t⟩
  let pPlane := K.adaptiveFacePlaneHomeomorph U t pClosed
  let cPlane := K.adaptiveFacePlaneHomeomorph U t cClosed
  obtain ⟨y, hyFrontier, hpSegment⟩ := exists_frontier_endpoint
    standardTrianglePlaneComplex_isTriangle.convex
    standardTrianglePlaneComplex_isTriangle.isCompact
    (K.adaptiveFacePlaneCenter_mem_interior U t) pPlane.2
    standardTrianglePlaneComplex_isTriangle.frontier_nonempty
  have hclosed : IsClosed standardTrianglePlaneComplex.support :=
    standardTrianglePlaneComplex_isTriangle.isCompact.isClosed
  have hySupport : y ∈ standardTrianglePlaneComplex.support :=
    hclosed.frontier_subset hyFrontier
  let ySupport : standardTrianglePlaneComplex.support := ⟨y, hySupport⟩
  let qClosed : K.AdaptiveClosedFace U t :=
    (K.adaptiveFacePlaneHomeomorph U t).symm ySupport
  have hqPlane : K.adaptiveFacePlaneHomeomorph U t qClosed = ySupport :=
    (K.adaptiveFacePlaneHomeomorph U t).apply_symm_apply ySupport
  have hyCircle : y ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier, ← standardTrianglePlaneComplex_support]
    exact hyFrontier
  obtain ⟨i, hyEdge⟩ := Set.mem_iUnion.mp hyCircle
  change ZMod 3 at i
  have hqEdge : qClosed.1 ∈ K.levelFaceEdgeCarrier t.2.1 i := by
    apply (K.adaptiveFacePlaneHomeomorph_mem_edge_iff U t i qClosed.2).mp
    rw [hqPlane]
    exact hyEdge
  obtain ⟨j, s, hbase⟩ :=
    K.exists_adaptiveFanBasePath_eq_of_mem_levelFaceEdgeCarrier U hU t i hqEdge
  rw [segment_eq_image_lineMap] at hpSegment
  obtain ⟨r, hr, hrPlane⟩ := hpSegment
  let rIcc : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
  let f : K.AdaptiveFanFace U hU := ⟨t, i, j⟩
  let center : stdSimplex ℝ
      {q // q ∈ K.adaptiveFanFaceVertices U hU f} :=
    stdSimplex.vertex (K.adaptiveFanCenterVertex U hU f)
  let base := K.adaptiveFanBaseSimplexPath U hU f s
  let x := K.adaptiveFanSimplexLineMap U hU f center base rIcc
  refine ⟨i, j, x, ?_⟩
  have hplane : (K.adaptiveFacePlaneHomeomorph U t pClosed).1 =
      AffineMap.lineMap
        (K.adaptiveFacePlaneHomeomorph U t cClosed).1
        (K.adaptiveFacePlaneHomeomorph U t qClosed).1 r := by
    calc
      (K.adaptiveFacePlaneHomeomorph U t pClosed).1 = pPlane.1 := rfl
      _ = AffineMap.lineMap cPlane.1 y r := hrPlane.symm
      _ = AffineMap.lineMap
          (K.adaptiveFacePlaneHomeomorph U t cClosed).1
          (K.adaptiveFacePlaneHomeomorph U t qClosed).1 r := by
        rw [hqPlane]
  have hpSource := K.adaptiveFaceSource_val_eq_lineMap_of_plane_eq U t
    pClosed qClosed r hplane
  have hbaseSource : K.adaptiveFanSourcePoint U hU f base =
      (K.safeSubdivision t.1).homeo.symm qClosed.1 := by
    apply (K.safeSubdivision t.1).homeo.injective
    have hbaseVal := congrArg Subtype.val hbase
    rw [(K.safeSubdivision t.1).homeo.apply_symm_apply]
    exact hbaseVal
  apply Subtype.ext
  change (K.safeSubdivision t.1).homeo
      (K.adaptiveFanSourcePoint U hU f x) = p
  rw [← (K.safeSubdivision t.1).homeo.apply_symm_apply p]
  apply congrArg (K.safeSubdivision t.1).homeo
  apply Subtype.ext
  calc
    (K.adaptiveFanSourcePoint U hU f x).1 =
        AffineMap.lineMap
          (K.adaptiveFanSourcePoint U hU f center).1
          (K.adaptiveFanSourcePoint U hU f base).1 r :=
      K.adaptiveFanSourcePoint_simplexLineMap U hU f center base rIcc
    _ = AffineMap.lineMap
          ((K.safeSubdivision t.1).homeo.symm (K.adaptiveFaceCenter U t)).1
          ((K.safeSubdivision t.1).homeo.symm qClosed.1).1 r := by
      rw [K.adaptiveFanSourcePoint_vertex U hU f
        (K.adaptiveFanCenterVertex U hU f), hbaseSource]
      rfl
    _ = ((K.safeSubdivision t.1).homeo.symm p).1 := hpSource.symm

theorem levelFaceEdgeParameter_adaptiveFanFaceMap_mem_Ioo_of_center_eq_zero
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0)
    (hxFirst : 0 < x (K.adaptiveFanFirstVertex U hU f))
    (hxSecond : 0 < x (K.adaptiveFanSecondVertex U hU f)) :
    K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanFaceMap U hU f x).1 ∈ Set.Ioo
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanFirstVertex U hU f).1)
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanSecondVertex U hU f).1) := by
  have hformula :=
    K.levelFaceEdgeParameter_adaptiveFanFaceMap_of_center_eq_zero U hU f x hxCenter
  have hsum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU f x hxCenter
  have hfirst := K.adaptiveEdgeInterval_parameter_lt U hU f.1 f.2.1 f.2.2
  change K.levelFaceEdgeParameter f.1.2.1 f.2.1
      (K.adaptiveFanFirstVertex U hU f).1 <
    K.levelFaceEdgeParameter f.1.2.1 f.2.1
      (K.adaptiveFanSecondVertex U hU f).1 at hfirst
  let z := K.levelFaceEdgeParameter f.1.2.1 f.2.1
    (K.adaptiveFanFaceMap U hU f x).1
  let a := K.levelFaceEdgeParameter f.1.2.1 f.2.1
    (K.adaptiveFanFirstVertex U hU f).1
  let b := K.levelFaceEdgeParameter f.1.2.1 f.2.1
    (K.adaptiveFanSecondVertex U hU f).1
  let α := x (K.adaptiveFanFirstVertex U hU f)
  let β := x (K.adaptiveFanSecondVertex U hU f)
  have hzLeft : z = a + β * (b - a) := by
    calc
      z = α * a + β * b := hformula
      _ = (α + β) * a + β * (b - a) := by ring
      _ = a + β * (b - a) := by rw [hsum, one_mul]
  have hzRight : z = b - α * (b - a) := by
    calc
      z = α * a + β * b := hformula
      _ = (α + β) * b - α * (b - a) := by ring
      _ = b - α * (b - a) := by rw [hsum, one_mul]
  constructor
  · change a < z
    rw [hzLeft]
    exact lt_add_of_pos_right _ (mul_pos hxSecond (sub_pos.mpr hfirst))
  · change z < b
    rw [hzRight]
    exact sub_lt_self _ (mul_pos hxFirst (sub_pos.mpr hfirst))

/-- A point in the relative interior of a resolved fan base is not one of the tile's collected
boundary marks. -/
theorem adaptiveFanFaceMap_not_mem_boundaryVertices_of_base_weights_pos
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0)
    (hxFirst : 0 < x (K.adaptiveFanFirstVertex U hU f))
    (hxSecond : 0 < x (K.adaptiveFanSecondVertex U hU f)) :
    (K.adaptiveFanFaceMap U hU f x).1 ∉ K.boundaryVertices U hU f.1 := by
  intro hp
  have hpEdge : (K.adaptiveFanFaceMap U hU f x).1 ∈
      K.levelFaceEdgeCarrier f.1.2.1 f.2.1 := by
    refine ⟨K.adaptiveFanSourcePoint U hU f x,
      K.adaptiveFanSourcePoint_mem_baseEdge_of_center_eq_zero U hU f x hxCenter, rfl⟩
  have hpResolved : (K.adaptiveFanFaceMap U hU f x).1 ∈
      K.boundaryEdgeVertices U hU f.1 f.2.1 :=
    (K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mpr ⟨hp, hpEdge⟩
  exact K.not_parameter_mem_Ioo_adaptiveEdgeInterval U hU f.1 f.2.1 f.2.2 hpResolved
    (K.levelFaceEdgeParameter_adaptiveFanFaceMap_mem_Ioo_of_center_eq_zero
      U hU f x hxCenter hxFirst hxSecond)

/-- Relative-interior points of resolved bases in one adaptive tile can agree only when the
bases lie on the same cyclic tile edge. -/
theorem adaptiveFanSide_eq_of_faceMap_eq_of_same_tile_of_base_weights_pos
    (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i j : ZMod 3) (a : K.AdaptiveEdgeInterval U hU t i)
    (b : K.AdaptiveEdgeInterval U hU t j)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩}}
    (hxy : K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x =
      K.adaptiveFanFaceMap U hU ⟨t, j, b⟩ y)
    (hxCenter : x (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) = 0)
    (hyCenter : y (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) = 0)
    (hxFirst : 0 < x (K.adaptiveFanFirstVertex U hU ⟨t, i, a⟩))
    (hxSecond : 0 < x (K.adaptiveFanSecondVertex U hU ⟨t, i, a⟩))
    (_ : 0 < y (K.adaptiveFanFirstVertex U hU ⟨t, j, b⟩))
    (_ : 0 < y (K.adaptiveFanSecondVertex U hU ⟨t, j, b⟩)) :
    i = j := by
  let R := K.safeSubdivision t.1
  have hsource : K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x =
      K.adaptiveFanSourcePoint U hU ⟨t, j, b⟩ y := by
    apply R.homeo.injective
    exact congrArg Subtype.val hxy
  have hxEdge : K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x ∈
      R.refined.faceCarrier (R.refined.faceEdge t.2.1 i).1 :=
    K.adaptiveFanSourcePoint_mem_baseEdge_of_center_eq_zero U hU
      ⟨t, i, a⟩ x hxCenter
  have hyEdge : K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x ∈
      R.refined.faceCarrier (R.refined.faceEdge t.2.1 j).1 := by
    rw [hsource]
    exact K.adaptiveFanSourcePoint_mem_baseEdge_of_center_eq_zero U hU
      ⟨t, j, b⟩ y hyCenter
  have hxNotBoundary :=
    K.adaptiveFanFaceMap_not_mem_boundaryVertices_of_base_weights_pos
      U hU ⟨t, i, a⟩ x hxCenter hxFirst hxSecond
  have hxNotVertex : ∀ v : {v // v ∈ t.2.1.1},
      K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x ≠
        R.refined.facePoint t.2.1 v := by
    intro v hv
    apply hxNotBoundary
    have hmap : (K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x).1 =
        K.adaptiveVertexPoint U t v := by
      change R.homeo (K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x) =
        R.homeo (R.refined.facePoint t.2.1 v)
      exact congrArg R.homeo hv
    rw [hmap]
    exact K.adaptiveVertexPoint_mem_boundaryVertices U hU t v
  have hedgeVal : (R.refined.faceEdge t.2.1 i).1 =
      (R.refined.faceEdge t.2.1 j).1 := by
    apply R.refined.eq_of_card_two_of_mem_faceCarriers_not_vertex t.2.1
      (R.refined.faceEdge_subset_face t.2.1 i)
      (R.refined.faceEdge_subset_face t.2.1 j)
      (R.refined.card_of_mem_edges (R.refined.faceEdge t.2.1 i).2)
      (R.refined.card_of_mem_edges (R.refined.faceEdge t.2.1 j).2)
      hxEdge hyEdge hxNotVertex
  exact K.levelFace_faceEdge_injective t.2.1 (Subtype.ext hedgeVal)

/-- Relative interiors of two consecutive-list intervals on the same tile edge are disjoint
unless the interval indices are equal. -/
theorem adaptiveFanInterval_eq_of_faceMap_eq_of_same_edge_of_base_weights_pos
    (hU : IsOpen U) (t : K.AdaptiveFace U) (i : ZMod 3)
    (a b : K.AdaptiveEdgeInterval U hU t i)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, i, b⟩}}
    (hxy : K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x =
      K.adaptiveFanFaceMap U hU ⟨t, i, b⟩ y)
    (hxCenter : x (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) = 0)
    (hyCenter : y (K.adaptiveFanCenterVertex U hU ⟨t, i, b⟩) = 0)
    (hxFirst : 0 < x (K.adaptiveFanFirstVertex U hU ⟨t, i, a⟩))
    (hxSecond : 0 < x (K.adaptiveFanSecondVertex U hU ⟨t, i, a⟩))
    (hyFirst : 0 < y (K.adaptiveFanFirstVertex U hU ⟨t, i, b⟩))
    (hySecond : 0 < y (K.adaptiveFanSecondVertex U hU ⟨t, i, b⟩)) :
    a = b := by
  have hxIoo :=
    K.levelFaceEdgeParameter_adaptiveFanFaceMap_mem_Ioo_of_center_eq_zero
      U hU ⟨t, i, a⟩ x hxCenter hxFirst hxSecond
  have hyIoo :=
    K.levelFaceEdgeParameter_adaptiveFanFaceMap_mem_Ioo_of_center_eq_zero
      U hU ⟨t, i, b⟩ y hyCenter hyFirst hySecond
  have hparam : K.levelFaceEdgeParameter t.2.1 i
      (K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x).1 =
    K.levelFaceEdgeParameter t.2.1 i
      (K.adaptiveFanFaceMap U hU ⟨t, i, b⟩ y).1 := by
    rw [hxy]
  apply Fin.ext
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · have hsep := K.adaptiveEdgeIntervalSecond_parameter_le_first_of_lt
      U hU t i a b hab
    have hxUpper : K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x).1 <
        K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalSecond U hU t i a) := hxIoo.2
    have hyLower : K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalFirst U hU t i b) <
        K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveFanFaceMap U hU ⟨t, i, b⟩ y).1 := hyIoo.1
    rw [← hparam] at hyLower
    exact (not_lt_of_ge hsep) (hyLower.trans hxUpper)
  · have hsep := K.adaptiveEdgeIntervalSecond_parameter_le_first_of_lt
      U hU t i b a hba
    have hxLower : K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalFirst U hU t i a) <
        K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x).1 := hxIoo.1
    have hyUpper : K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveFanFaceMap U hU ⟨t, i, b⟩ y).1 <
        K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalSecond U hU t i b) := hyIoo.2
    rw [hparam] at hxLower
    exact (not_lt_of_ge hsep) (hxLower.trans hyUpper)

theorem adaptiveFanBasePath_not_mem_boundaryVertices_of_mem_Ioo
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (r : Set.Icc (0 : ℝ) 1) (hr : r.1 ∈ Set.Ioo (0 : ℝ) 1) :
    (K.adaptiveFanBasePath U hU f r).1 ∉ K.boundaryVertices U hU f.1 := by
  apply K.adaptiveFanFaceMap_not_mem_boundaryVertices_of_base_weights_pos U hU
    (f := f) (x := K.adaptiveFanBaseSimplexPath U hU f r)
  · exact K.adaptiveFanBaseSimplexPath_apply_center U hU f r
  · rw [K.adaptiveFanBaseSimplexPath_apply_first U hU f r]
    exact sub_pos.mpr hr.2
  · rw [K.adaptiveFanBaseSimplexPath_apply_second U hU f r]
    exact hr.1

/-- Positive weight at the cone center places a fan point in the relative interior of its
adaptive tile. -/
theorem adaptiveFanFaceMap_mem_relInterior_of_center_pos (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : 0 < x (K.adaptiveFanCenterVertex U hU f)) :
    (K.adaptiveFanFaceMap U hU f x).1 ∈
      K.adaptiveFaceRelInterior U f.1 := by
  classical
  refine ⟨K.adaptiveFanSourcePoint U hU f x, ⟨
    K.adaptiveFanSourcePoint_mem_carrier U hU f x, ?_⟩, rfl⟩
  intro v hv
  obtain ⟨i, rfl⟩ := (K.safeSubdivision f.1.1).refined.exists_faceVertex_eq_of_mem
    f.1.2.1 hv
  let c := K.adaptiveFanCenterVertex U hU f
  have hterm : 0 < x c *
      (K.adaptiveFanVertexSource U hU f c).1
        ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 i) := by
    have hcCoord :
        (K.adaptiveFanVertexSource U hU f c).1
            ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 i) = 1 / 3 := by
      simpa only [c, adaptiveFanCenterVertex, adaptiveFanVertexSource] using
        K.adaptiveFaceCenter_source_apply U f.1 i
    rw [hcCoord]
    positivity
  have hnonneg : ∀ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
      0 ≤ x p * (K.adaptiveFanVertexSource U hU f p).1
        ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 i) := by
    intro p
    exact mul_nonneg (x.2.1 p)
      ((K.adaptiveFanVertexSource U hU f p).2.1.1 _)
  change 0 < ∑ p, x p * (K.adaptiveFanVertexSource U hU f p).1
    ((K.safeSubdivision f.1.1).refined.faceVertex f.1.2.1 i)
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (fun p _ ↦ hnonneg p) (Finset.mem_univ c))

/-- A point common to fan triangles from distinct adaptive tiles has zero cone-center weight in
the first triangle. -/
theorem adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne
    (hU : IsOpen U) {f g : K.AdaptiveFanFace U hU}
    (hfg : f.1 ≠ g.1)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU g}}
    (hxy : K.adaptiveFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU g y) :
    x (K.adaptiveFanCenterVertex U hU f) = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hx
    have hinter := K.adaptiveFanFaceMap_mem_relInterior_of_center_pos U hU f x hx
    have hcarrier : (K.adaptiveFanFaceMap U hU f x).1 ∈
        K.adaptiveFaceCarrier U g.1 := by
      rw [hxy]
      exact K.range_adaptiveFanFaceMap_subset_tile U hU g (Set.mem_range_self y)
    exact Set.disjoint_left.mp
      (K.disjoint_adaptiveFaceRelInterior_carrier U hfg) hinter hcarrier
  · exact x.2.1 _

/-- At a common nonvertex point, the base edge belonging to the later adaptive tile lies in the
earlier tile. -/
theorem adaptiveFanLaterBaseEdge_subset_earlierTile_of_faceMap_eq
    (hU : IsOpen U) {f g : K.AdaptiveFanFace U hU}
    (hfg : f.1 ≠ g.1) (hlevel : f.1.1 ≤ g.1.1)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU g}}
    (hxy : K.adaptiveFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU g y)
    (hyFirst : 0 < y (K.adaptiveFanFirstVertex U hU g))
    (hySecond : 0 < y (K.adaptiveFanSecondVertex U hU g)) :
    K.levelFaceEdgeCarrier g.1.2.1 g.2.1 ⊆
      K.adaptiveFaceCarrier U f.1 := by
  have hyCenter :=
    K.adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne U hU
      hfg.symm hxy.symm
  have hzInF : (K.adaptiveFanFaceMap U hU g y).1 ∈
      K.adaptiveFaceCarrier U f.1 := by
    rw [← hxy]
    exact K.range_adaptiveFanFaceMap_subset_tile U hU f (Set.mem_range_self x)
  have hzEdgeG : (K.adaptiveFanFaceMap U hU g y).1 ∈
      K.levelFaceEdgeCarrier g.1.2.1 g.2.1 := by
    refine ⟨K.adaptiveFanSourcePoint U hU g y,
      K.adaptiveFanSourcePoint_mem_baseEdge_of_center_eq_zero U hU g y hyCenter, rfl⟩
  have hzNotG :=
    K.adaptiveFanFaceMap_not_mem_boundaryVertices_of_base_weights_pos U hU g y
      hyCenter hyFirst hySecond
  exact K.adaptiveFace_edgeCarrier_subset_of_level_le_of_common_not_boundaryVertex
    U hU hfg hlevel g.2.1 hzInF hzEdgeG hzNotG

/-- If interiors of two resolved fan bases meet and the second tile is no earlier in the
adaptive hierarchy, then the entire second resolved interval lies in the first base edge. -/
theorem adaptiveFanLaterBasePath_subset_earlierBaseEdge_of_faceMap_eq
    (hU : IsOpen U) {f g : K.AdaptiveFanFace U hU}
    (hfg : f.1 ≠ g.1) (hlevel : f.1.1 ≤ g.1.1)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU g}}
    (hxy : K.adaptiveFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU g y)
    (_ : 0 < x (K.adaptiveFanFirstVertex U hU f))
    (_ : 0 < x (K.adaptiveFanSecondVertex U hU f))
    (hyFirst : 0 < y (K.adaptiveFanFirstVertex U hU g))
    (hySecond : 0 < y (K.adaptiveFanSecondVertex U hU g)) :
    ∀ r : Set.Icc (0 : ℝ) 1,
      (K.adaptiveFanBasePath U hU g r).1 ∈
        K.levelFaceEdgeCarrier f.1.2.1 f.2.1 := by
  have hxCenter :=
    K.adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne U hU hfg hxy
  have hyCenter :=
    K.adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne U hU hfg.symm hxy.symm
  have hLaterInEarlier :=
    K.adaptiveFanLaterBaseEdge_subset_earlierTile_of_faceMap_eq U hU
      hfg hlevel hxy hyFirst hySecond
  let inc : Set.Ioo (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
    fun r ↦ ⟨r.1, ⟨r.2.1.le, r.2.2.le⟩⟩
  let q : Set.Icc (0 : ℝ) 1 → K.AdaptiveClosedFace U f.1 :=
    fun r ↦ ⟨(K.adaptiveFanBasePath U hU g r).1,
      hLaterInEarlier (K.adaptiveFanBasePath_mem_baseEdge U hU g r)⟩
  let a : Set.Icc (0 : ℝ) 1 → Plane :=
    fun r ↦ (K.adaptiveFacePlaneHomeomorph U f.1 (q r)).1
  let aOpen : Set.Ioo (0 : ℝ) 1 → Plane := a ∘ inc
  let A : Set Plane := Set.range aOpen
  have hqcont : Continuous q := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (K.continuous_adaptiveFanBasePath U hU g)
  have hacont : Continuous a :=
    continuous_subtype_val.comp
      ((K.adaptiveFacePlaneHomeomorph U f.1).continuous.comp hqcont)
  have hinccont : Continuous inc := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have haOpenCont : Continuous aOpen := hacont.comp hinccont
  letI : PreconnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hApreconnected : IsPreconnected A := isPreconnected_range haOpenCont
  have hAcarrier : A ⊆ standardTriangleCircle.carrier := by
    rintro z ⟨r, rfl⟩
    let r' : Set.Icc (0 : ℝ) 1 := inc r
    have hzGEdge := K.adaptiveFanBasePath_mem_baseEdge U hU g r'
    have hzGCarrier : (K.adaptiveFanBasePath U hU g r').1 ∈
        K.adaptiveFaceCarrier U g.1 :=
      K.levelFaceEdgeCarrier_subset g.1.2.1 g.2.1 hzGEdge
    have hzFCarrier : (K.adaptiveFanBasePath U hU g r').1 ∈
        K.adaptiveFaceCarrier U f.1 := hLaterInEarlier hzGEdge
    have hzNotF : (K.adaptiveFanBasePath U hU g r').1 ∉
        K.adaptiveFaceRelInterior U f.1 := by
      intro hzInt
      exact Set.disjoint_left.mp
        (K.disjoint_adaptiveFaceRelInterior_carrier U hfg) hzInt hzGCarrier
    exact K.adaptiveFacePlaneHomeomorph_mem_standardCircle_of_not_relInterior
      U f.1 hzFCarrier hzNotF
  have hAvertices : ∀ j : ZMod 3, standardTriangleCircle.vertex j ∉ A := by
    intro j hj
    obtain ⟨r, hrj⟩ := hj
    let r' : Set.Icc (0 : ℝ) 1 := inc r
    have hzGEdge := K.adaptiveFanBasePath_mem_baseEdge U hU g r'
    have hzGCarrier : (K.adaptiveFanBasePath U hU g r').1 ∈
        K.adaptiveFaceCarrier U g.1 :=
      K.levelFaceEdgeCarrier_subset g.1.2.1 g.2.1 hzGEdge
    have hzFCarrier : (K.adaptiveFanBasePath U hU g r').1 ∈
        K.adaptiveFaceCarrier U f.1 := hLaterInEarlier hzGEdge
    have hzMarkF : (K.adaptiveFanBasePath U hU g r').1 ∈
        K.boundaryVertices U hU f.1 := by
      apply K.mem_boundaryVertices_of_adaptiveFacePlaneHomeomorph_eq_vertex
        U hU f.1 hzFCarrier j
      simpa [aOpen, a, q, r'] using hrj
    have hzMarkG : (K.adaptiveFanBasePath U hU g r').1 ∈
        K.boundaryVertices U hU g.1 :=
      (K.mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter U hU
        f.1 g.1 hzFCarrier hzGCarrier).mp hzMarkF
    exact K.adaptiveFanBasePath_not_mem_boundaryVertices_of_mem_Ioo U hU g r'
      r.2 hzMarkG
  have hAmeet : (A ∩ standardTriangleCircle.edgeSegment f.2.1).Nonempty := by
    have hySum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU g y hyCenter
    have hySecondLt : y (K.adaptiveFanSecondVertex U hU g) < 1 := by
      linarith
    let r₀ : Set.Ioo (0 : ℝ) 1 :=
      ⟨y (K.adaptiveFanSecondVertex U hU g), hySecond, hySecondLt⟩
    let r₁ : Set.Icc (0 : ℝ) 1 := inc r₀
    have hyPathSimplex : K.adaptiveFanBaseSimplexPath U hU g r₁ = y :=
      K.adaptiveFanBaseSimplexPath_eq_of_secondWeight U hU g y r₁ rfl hyCenter
    have hyPath : K.adaptiveFanBasePath U hU g r₁ =
        K.adaptiveFanFaceMap U hU g y := by
      change K.adaptiveFanFaceMap U hU g
        (K.adaptiveFanBaseSimplexPath U hU g r₁) = _
      rw [hyPathSimplex]
    have hxEdge : (K.adaptiveFanFaceMap U hU f x).1 ∈
        K.levelFaceEdgeCarrier f.1.2.1 f.2.1 := by
      refine ⟨K.adaptiveFanSourcePoint U hU f x,
        K.adaptiveFanSourcePoint_mem_baseEdge_of_center_eq_zero U hU f x hxCenter, rfl⟩
    have hr₁Edge : (K.adaptiveFanBasePath U hU g r₁).1 ∈
        K.levelFaceEdgeCarrier f.1.2.1 f.2.1 := by
      rw [hyPath, ← hxy]
      exact hxEdge
    refine ⟨aOpen r₀, Set.mem_range_self r₀, ?_⟩
    simpa [aOpen, a, q, r₁] using
      K.adaptiveFacePlaneHomeomorph_mem_edge U f.1 f.2.1 hr₁Edge
  have hAedge : A ⊆ standardTriangleCircle.edgeSegment f.2.1 :=
    standardTriangleCircle.isPreconnected_subset_edgeSegment_of_avoids_vertices
      A f.2.1 hApreconnected hAcarrier hAvertices hAmeet
  have hclosureAedge : closure A ⊆ standardTriangleCircle.edgeSegment f.2.1 :=
    closure_minimal hAedge (standardTriangleCircle.isClosed_edgeSegment f.2.1)
  have hincDense (r : Set.Icc (0 : ℝ) 1) : r ∈ closure (Set.range inc) := by
    rw [_root_.Topology.IsInducing.closure_eq_preimage_closure_image
      _root_.Topology.IsEmbedding.subtypeVal.isInducing]
    change r.1 ∈ closure (Subtype.val '' Set.range inc)
    have himage : Subtype.val '' Set.range inc = Set.Ioo (0 : ℝ) 1 := by
      ext z
      constructor
      · rintro ⟨-, ⟨s, rfl⟩, rfl⟩
        exact s.2
      · intro hz
        let s : Set.Ioo (0 : ℝ) 1 := ⟨z, hz⟩
        exact ⟨inc s, ⟨s, rfl⟩, rfl⟩
    rw [himage, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact r.2
  have hAimage : a '' Set.range inc = A := by
    ext z
    constructor
    · rintro ⟨-, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨inc s, ⟨s, rfl⟩, rfl⟩
  intro r
  have harClosure : a r ∈ closure A := by
    rw [← hAimage]
    exact image_closure_subset_closure_image hacont ⟨r, hincDense r, rfl⟩
  have harEdge := hclosureAedge harClosure
  exact (K.adaptiveFacePlaneHomeomorph_mem_edge_iff U f.1 f.2.1
    (hLaterInEarlier (K.adaptiveFanBasePath_mem_baseEdge U hU g r))).mp
      (by simpa [a, q] using harEdge)

/-- A continuous injective path through an open interval matches its two boundary values at the
domain endpoints, up to reversing their order, provided neither boundary value occurs inside. -/
private theorem endpoint_values_eq_or_swap_of_injective
    (psi : Set.Icc (0 : ℝ) 1 → ℝ) (hpsiCont : Continuous psi)
    (hpsiInj : Function.Injective psi) (r : Set.Icc (0 : ℝ) 1)
    (hrZero : (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) < r)
    (hrOne : r < (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1)) {a b : ℝ}
    (hrange : psi r ∈ Set.Ioo a b)
    (hzeroNot : psi ⟨0, by simp⟩ ∉ Set.Ioo a b)
    (honeNot : psi ⟨1, by simp⟩ ∉ Set.Ioo a b)
    (hnoA : ∀ s : Set.Icc (0 : ℝ) 1, s.1 ∈ Set.Ioo (0 : ℝ) 1 → psi s ≠ a)
    (hnoB : ∀ s : Set.Icc (0 : ℝ) 1, s.1 ∈ Set.Ioo (0 : ℝ) 1 → psi s ≠ b) :
    (psi ⟨0, by simp⟩ = a ∧ psi ⟨1, by simp⟩ = b) ∨
      (psi ⟨0, by simp⟩ = b ∧ psi ⟨1, by simp⟩ = a) := by
  let rzero : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
  let rone : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
  rcases hpsiCont.strictMono_of_inj_boundedOrder' hpsiInj with hmono | hanti
  · have hzeroZ : psi rzero < psi r := hmono hrZero
    have hzOne : psi r < psi rone := hmono hrOne
    have hzeroLeA : psi rzero ≤ a := by
      by_contra h
      exact hzeroNot ⟨lt_of_not_ge h, hzeroZ.trans hrange.2⟩
    have hbLeOne : b ≤ psi rone := by
      by_contra h
      exact honeNot ⟨hrange.1.trans hzOne, lt_of_not_ge h⟩
    have hzeroEqA : psi rzero = a := by
      apply le_antisymm hzeroLeA
      by_contra h
      have hlt : psi rzero < a := lt_of_not_ge h
      obtain ⟨s, hs, hps⟩ := intermediate_value_Icc
        (a := rzero) (b := r) (f := psi) hrZero.le hpsiCont.continuousOn
        (show a ∈ Set.Icc (psi rzero) (psi r) from ⟨hlt.le, hrange.1.le⟩)
      have hzeroS : rzero < s := lt_of_le_of_ne hs.1 fun heq ↦ by
        subst s
        exact hlt.ne hps
      have hsr : s < r := lt_of_le_of_ne hs.2 fun heq ↦ by
        subst s
        exact hrange.1.ne' hps
      exact hnoA s ⟨by simpa [rzero] using hzeroS, hsr.trans hrOne⟩ hps
    have hOneEqB : psi rone = b := by
      apply le_antisymm
      · by_contra h
        have hlt : b < psi rone := lt_of_not_ge h
        obtain ⟨s, hs, hps⟩ := intermediate_value_Icc
          (a := r) (b := rone) (f := psi) hrOne.le hpsiCont.continuousOn
          (show b ∈ Set.Icc (psi r) (psi rone) from ⟨hrange.2.le, hlt.le⟩)
        have hrs : r < s := lt_of_le_of_ne hs.1 fun heq ↦ by
          subst s
          exact hrange.2.ne hps
        have hsone : s < rone := lt_of_le_of_ne hs.2 fun heq ↦ by
          subst s
          exact hlt.ne' hps
        exact hnoB s ⟨hrZero.trans hrs, by simpa [rone] using hsone⟩ hps
      · exact hbLeOne
    exact Or.inl ⟨by simpa [rzero] using hzeroEqA, by simpa [rone] using hOneEqB⟩
  · have hzZero : psi r < psi rzero := hanti hrZero
    have hOneZ : psi rone < psi r := hanti hrOne
    have hOneLeA : psi rone ≤ a := by
      by_contra h
      exact honeNot ⟨lt_of_not_ge h, hOneZ.trans hrange.2⟩
    have hbLeZero : b ≤ psi rzero := by
      by_contra h
      exact hzeroNot ⟨hrange.1.trans hzZero, lt_of_not_ge h⟩
    have hOneEqA : psi rone = a := by
      apply le_antisymm hOneLeA
      by_contra h
      have hlt : psi rone < a := lt_of_not_ge h
      obtain ⟨s, hs, hps⟩ := intermediate_value_Icc'
        (a := r) (b := rone) (f := psi) hrOne.le hpsiCont.continuousOn
        (show a ∈ Set.Icc (psi rone) (psi r) from ⟨hlt.le, hrange.1.le⟩)
      have hrs : r < s := lt_of_le_of_ne hs.1 fun heq ↦ by
        subst s
        exact hrange.1.ne' hps
      have hsone : s < rone := lt_of_le_of_ne hs.2 fun heq ↦ by
        subst s
        exact hlt.ne hps
      exact hnoA s ⟨hrZero.trans hrs, by simpa [rone] using hsone⟩ hps
    have hzeroEqB : psi rzero = b := by
      apply le_antisymm
      · by_contra h
        have hlt : b < psi rzero := lt_of_not_ge h
        obtain ⟨s, hs, hps⟩ := intermediate_value_Icc'
          (a := rzero) (b := r) (f := psi) hrZero.le hpsiCont.continuousOn
          (show b ∈ Set.Icc (psi r) (psi rzero) from ⟨hrange.2.le, hlt.le⟩)
        have hzeroS : rzero < s := lt_of_le_of_ne hs.1 fun heq ↦ by
          subst s
          exact hlt.ne' hps
        have hsr : s < r := lt_of_le_of_ne hs.2 fun heq ↦ by
          subst s
          exact hrange.2.ne hps
        exact hnoB s ⟨by simpa [rzero] using hzeroS, hsr.trans hrOne⟩ hps
      · exact hbLeZero
    exact Or.inr ⟨by simpa [rzero] using hzeroEqB, by simpa [rone] using hOneEqA⟩

/-- Two resolved fan intervals whose relative interiors meet have the same geometric endpoints,
possibly with opposite order. -/
theorem adaptiveFanBaseEndpoints_eq_or_swap_of_faceMap_eq
    (hU : IsOpen U) {f g : K.AdaptiveFanFace U hU}
    (hfg : f.1 ≠ g.1) (hlevel : f.1.1 ≤ g.1.1)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU g}}
    (hxy : K.adaptiveFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU g y)
    (hxFirst : 0 < x (K.adaptiveFanFirstVertex U hU f))
    (hxSecond : 0 < x (K.adaptiveFanSecondVertex U hU f))
    (hyFirst : 0 < y (K.adaptiveFanFirstVertex U hU g))
    (hySecond : 0 < y (K.adaptiveFanSecondVertex U hU g)) :
    ((K.adaptiveFanFirstVertex U hU g).1 =
        (K.adaptiveFanFirstVertex U hU f).1 ∧
      (K.adaptiveFanSecondVertex U hU g).1 =
        (K.adaptiveFanSecondVertex U hU f).1) ∨
    ((K.adaptiveFanFirstVertex U hU g).1 =
        (K.adaptiveFanSecondVertex U hU f).1 ∧
      (K.adaptiveFanSecondVertex U hU g).1 =
        (K.adaptiveFanFirstVertex U hU f).1) := by
  let rzero : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
  let rone : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
  have hxCenter :=
    K.adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne U hU hfg hxy
  have hyCenter :=
    K.adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne U hU hfg.symm hxy.symm
  have hxSum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU f x hxCenter
  have hySum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU g y hyCenter
  have hxSecondLt : x (K.adaptiveFanSecondVertex U hU f) < 1 := by linarith
  have hySecondLt : y (K.adaptiveFanSecondVertex U hU g) < 1 := by linarith
  let rx : Set.Icc (0 : ℝ) 1 :=
    ⟨x (K.adaptiveFanSecondVertex U hU f), ⟨hxSecond.le, hxSecondLt.le⟩⟩
  let ry : Set.Icc (0 : ℝ) 1 :=
    ⟨y (K.adaptiveFanSecondVertex U hU g), ⟨hySecond.le, hySecondLt.le⟩⟩
  have hxPathSimplex : K.adaptiveFanBaseSimplexPath U hU f rx = x :=
    K.adaptiveFanBaseSimplexPath_eq_of_secondWeight U hU f x rx rfl hxCenter
  have hyPathSimplex : K.adaptiveFanBaseSimplexPath U hU g ry = y :=
    K.adaptiveFanBaseSimplexPath_eq_of_secondWeight U hU g y ry rfl hyCenter
  have hpathEq : K.adaptiveFanBasePath U hU f rx =
      K.adaptiveFanBasePath U hU g ry := by
    change K.adaptiveFanFaceMap U hU f
      (K.adaptiveFanBaseSimplexPath U hU f rx) =
        K.adaptiveFanFaceMap U hU g
          (K.adaptiveFanBaseSimplexPath U hU g ry)
    rw [hxPathSimplex, hyPathSimplex]
    exact hxy
  have hLaterInBase :=
    K.adaptiveFanLaterBasePath_subset_earlierBaseEdge_of_faceMap_eq U hU
      hfg hlevel hxy hxFirst hxSecond hyFirst hySecond
  have hpathZeroVal : (K.adaptiveFanBasePath U hU g rzero).1 =
      (K.adaptiveFanFirstVertex U hU g).1 := by
    have h := congrArg Subtype.val (K.adaptiveFanBasePath_zero U hU g)
    simpa only [rzero] using h
  have hpathOneVal : (K.adaptiveFanBasePath U hU g rone).1 =
      (K.adaptiveFanSecondVertex U hU g).1 := by
    have h := congrArg Subtype.val (K.adaptiveFanBasePath_one U hU g)
    simpa only [rone] using h
  let psi : Set.Icc (0 : ℝ) 1 → ℝ := fun r ↦
    K.levelFaceEdgeParameter f.1.2.1 f.2.1
      (K.adaptiveFanBasePath U hU g r).1
  have hpsiCont : Continuous psi :=
    (K.continuous_levelFaceEdgeParameter f.1.2.1 f.2.1).comp
      (continuous_subtype_val.comp (K.continuous_adaptiveFanBasePath U hU g))
  have hpsiInj : Function.Injective psi := by
    intro r s hrs
    apply K.adaptiveFanBasePath_injective U hU g
    apply Subtype.ext
    exact K.levelFaceEdgeParameter_injOn f.1.2.1 f.2.1
      (hLaterInBase r) (hLaterInBase s) hrs
  have hzIoo : psi ry ∈ Set.Ioo
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanFirstVertex U hU f).1)
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanSecondVertex U hU f).1) := by
    have hz := K.levelFaceEdgeParameter_adaptiveFanFaceMap_mem_Ioo_of_center_eq_zero
      U hU f x hxCenter hxFirst hxSecond
    change K.levelFaceEdgeParameter f.1.2.1 f.2.1
      (K.adaptiveFanBasePath U hU g ry).1 ∈ _
    rw [← hpathEq]
    change K.levelFaceEdgeParameter f.1.2.1 f.2.1
      (K.adaptiveFanFaceMap U hU f
        (K.adaptiveFanBaseSimplexPath U hU f rx)).1 ∈ _
    rwa [hxPathSimplex]
  have hgFirstEdgeG := (K.mem_boundaryEdgeVertices_iff U hU g.1 g.2.1 _).mp
    (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU
      g.1 g.2.1 g.2.2)
  have hgSecondEdgeG := (K.mem_boundaryEdgeVertices_iff U hU g.1 g.2.1 _).mp
    (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU
      g.1 g.2.1 g.2.2)
  have hgFirstEdgeF : (K.adaptiveFanFirstVertex U hU g).1 ∈
      K.levelFaceEdgeCarrier f.1.2.1 f.2.1 := by
    rw [← hpathZeroVal]
    exact hLaterInBase rzero
  have hgSecondEdgeF : (K.adaptiveFanSecondVertex U hU g).1 ∈
      K.levelFaceEdgeCarrier f.1.2.1 f.2.1 := by
    rw [← hpathOneVal]
    exact hLaterInBase rone
  have hgFirstCarrierF := K.levelFaceEdgeCarrier_subset f.1.2.1 f.2.1 hgFirstEdgeF
  have hgSecondCarrierF := K.levelFaceEdgeCarrier_subset f.1.2.1 f.2.1 hgSecondEdgeF
  have hgFirstCarrierG := K.levelFaceEdgeCarrier_subset g.1.2.1 g.2.1 hgFirstEdgeG.2
  have hgSecondCarrierG := K.levelFaceEdgeCarrier_subset g.1.2.1 g.2.1 hgSecondEdgeG.2
  have hgFirstMarkF : (K.adaptiveFanFirstVertex U hU g).1 ∈
      K.boundaryVertices U hU f.1 :=
    (K.mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter U hU
      g.1 f.1 hgFirstCarrierG hgFirstCarrierF).mp hgFirstEdgeG.1
  have hgSecondMarkF : (K.adaptiveFanSecondVertex U hU g).1 ∈
      K.boundaryVertices U hU f.1 :=
    (K.mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter U hU
      g.1 f.1 hgSecondCarrierG hgSecondCarrierF).mp hgSecondEdgeG.1
  have hgFirstBoundaryEdgeF : (K.adaptiveFanFirstVertex U hU g).1 ∈
      K.boundaryEdgeVertices U hU f.1 f.2.1 :=
    (K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mpr
      ⟨hgFirstMarkF, hgFirstEdgeF⟩
  have hgSecondBoundaryEdgeF : (K.adaptiveFanSecondVertex U hU g).1 ∈
      K.boundaryEdgeVertices U hU f.1 f.2.1 :=
    (K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mpr
      ⟨hgSecondMarkF, hgSecondEdgeF⟩
  have hpsiZeroNot : psi rzero ∉ Set.Ioo
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanFirstVertex U hU f).1)
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanSecondVertex U hU f).1) := by
    have h := K.not_parameter_mem_Ioo_adaptiveEdgeInterval
      U hU f.1 f.2.1 f.2.2 hgFirstBoundaryEdgeF
    change K.levelFaceEdgeParameter f.1.2.1 f.2.1
      (K.adaptiveFanBasePath U hU g rzero).1 ∉ _
    rw [hpathZeroVal]
    exact h
  have hpsiOneNot : psi rone ∉ Set.Ioo
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanFirstVertex U hU f).1)
      (K.levelFaceEdgeParameter f.1.2.1 f.2.1
        (K.adaptiveFanSecondVertex U hU f).1) := by
    have h := K.not_parameter_mem_Ioo_adaptiveEdgeInterval
      U hU f.1 f.2.1 f.2.2 hgSecondBoundaryEdgeF
    change K.levelFaceEdgeParameter f.1.2.1 f.2.1
      (K.adaptiveFanBasePath U hU g rone).1 ∉ _
    rw [hpathOneVal]
    exact h
  have hnoEndpointParameter (r : Set.Icc (0 : ℝ) 1)
      (hr : r.1 ∈ Set.Ioo (0 : ℝ) 1) (v : K.realization)
      (hvMarkF : v ∈ K.boundaryVertices U hU f.1)
      (hvEdgeF : v ∈ K.levelFaceEdgeCarrier f.1.2.1 f.2.1)
      (hparam : psi r = K.levelFaceEdgeParameter f.1.2.1 f.2.1 v) : False := by
    have hpEq : (K.adaptiveFanBasePath U hU g r).1 = v :=
      K.levelFaceEdgeParameter_injOn f.1.2.1 f.2.1
        (hLaterInBase r) hvEdgeF hparam
    have hpCarrierG : (K.adaptiveFanBasePath U hU g r).1 ∈
        K.adaptiveFaceCarrier U g.1 :=
      K.levelFaceEdgeCarrier_subset g.1.2.1 g.2.1
        (K.adaptiveFanBasePath_mem_baseEdge U hU g r)
    have hpMarkF : (K.adaptiveFanBasePath U hU g r).1 ∈
        K.boundaryVertices U hU f.1 := hpEq ▸ hvMarkF
    have hpMarkG : (K.adaptiveFanBasePath U hU g r).1 ∈
        K.boundaryVertices U hU g.1 :=
      (K.mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter U hU
        f.1 g.1 (K.levelFaceEdgeCarrier_subset f.1.2.1 f.2.1
          (hLaterInBase r)) hpCarrierG).mp hpMarkF
    exact K.adaptiveFanBasePath_not_mem_boundaryVertices_of_mem_Ioo
      U hU g r hr hpMarkG
  let af := K.levelFaceEdgeParameter f.1.2.1 f.2.1
    (K.adaptiveFanFirstVertex U hU f).1
  let bf := K.levelFaceEdgeParameter f.1.2.1 f.2.1
    (K.adaptiveFanSecondVertex U hU f).1
  have hfFirstBoundary := (K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp
    (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU
      f.1 f.2.1 f.2.2)
  have hfSecondBoundary := (K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp
    (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU
      f.1 f.2.1 f.2.2)
  have hzeroRy : rzero < ry := by
    change (0 : ℝ) < y (K.adaptiveFanSecondVertex U hU g)
    exact hySecond
  have hryOne : ry < rone := by
    change y (K.adaptiveFanSecondVertex U hU g) < (1 : ℝ)
    exact hySecondLt
  have hendpointValues := endpoint_values_eq_or_swap_of_injective psi hpsiCont hpsiInj ry
    hzeroRy hryOne hzIoo hpsiZeroNot hpsiOneNot
    (fun r hr hpr ↦ hnoEndpointParameter r hr
      (K.adaptiveFanFirstVertex U hU f).1 hfFirstBoundary.1 hfFirstBoundary.2
      (by simpa [psi, af] using hpr))
    (fun r hr hpr ↦ hnoEndpointParameter r hr
      (K.adaptiveFanSecondVertex U hU f).1 hfSecondBoundary.1 hfSecondBoundary.2
      (by simpa [psi, bf] using hpr))
  rcases hendpointValues with ⟨hzero, hone⟩ | ⟨hzero, hone⟩
  · left
    constructor
    · apply K.levelFaceEdgeParameter_injOn f.1.2.1 f.2.1
        hgFirstEdgeF hfFirstBoundary.2
      rw [← hpathZeroVal]
      change psi rzero = af
      simpa [rzero] using hzero
    · apply K.levelFaceEdgeParameter_injOn f.1.2.1 f.2.1
        hgSecondEdgeF hfSecondBoundary.2
      rw [← hpathOneVal]
      change psi rone = bf
      simpa [rone] using hone
  · right
    constructor
    · apply K.levelFaceEdgeParameter_injOn f.1.2.1 f.2.1
        hgFirstEdgeF hfSecondBoundary.2
      rw [← hpathZeroVal]
      change psi rzero = bf
      simpa [rzero] using hzero
    · apply K.levelFaceEdgeParameter_injOn f.1.2.1 f.2.1
        hgSecondEdgeF hfFirstBoundary.2
      rw [← hpathOneVal]
      change psi rone = af
      simpa [rone] using hone

/-- Extended coordinates of a fan triangle are the sum of its three vertex-weight spikes. -/
theorem extendFaceCoordinates_adaptiveFanFace (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}) :
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x =
      Pi.single (K.adaptiveFanCenterVertex U hU f).1
          (x (K.adaptiveFanCenterVertex U hU f)) +
        Pi.single (K.adaptiveFanFirstVertex U hU f).1
          (x (K.adaptiveFanFirstVertex U hU f)) +
        Pi.single (K.adaptiveFanSecondVertex U hU f).1
          (x (K.adaptiveFanSecondVertex U hU f)) := by
  classical
  let c := K.adaptiveFanCenterVertex U hU f
  let p := K.adaptiveFanFirstVertex U hU f
  let q := K.adaptiveFanSecondVertex U hU f
  have hcp : c.1 ≠ p.1 := fun h ↦
    K.adaptiveFanCenterVertex_ne_first U hU f (Subtype.ext h)
  have hcq : c.1 ≠ q.1 := fun h ↦
    K.adaptiveFanCenterVertex_ne_second U hU f (Subtype.ext h)
  have hpq : p.1 ≠ q.1 := fun h ↦
    K.adaptiveFanFirstVertex_ne_second U hU f (Subtype.ext h)
  funext v
  by_cases hvc : v = c.1
  · subst v
    have hcMem : c.1 ∈ K.adaptiveFanFaceVertices U hU f := c.2
    rw [extendFaceCoordinates_of_mem _ _ hcMem]
    have hcEq : (⟨c.1, hcMem⟩ :
        {z // z ∈ K.adaptiveFanFaceVertices U hU f}) = c := Subtype.ext rfl
    rw [hcEq]
    simp [c, p, q, hcp, hcq]
  by_cases hvp : v = p.1
  · subst v
    have hpMem : p.1 ∈ K.adaptiveFanFaceVertices U hU f := p.2
    rw [extendFaceCoordinates_of_mem _ _ hpMem]
    have hpEq : (⟨p.1, hpMem⟩ :
        {z // z ∈ K.adaptiveFanFaceVertices U hU f}) = p := Subtype.ext rfl
    rw [hpEq]
    simp [c, p, q, hcp, hpq]
  by_cases hvq : v = q.1
  · subst v
    have hqMem : q.1 ∈ K.adaptiveFanFaceVertices U hU f := q.2
    rw [extendFaceCoordinates_of_mem _ _ hqMem]
    have hqEq : (⟨q.1, hqMem⟩ :
        {z // z ∈ K.adaptiveFanFaceVertices U hU f}) = q := Subtype.ext rfl
    rw [hqEq]
    simp [c, p, q, hcq, hpq]
  · have hvNot : v ∉ K.adaptiveFanFaceVertices U hU f := by
      intro hv
      simp only [adaptiveFanFaceVertices, Finset.mem_insert,
        Finset.mem_singleton] at hv
      exact hv.elim hvc (fun h ↦ h.elim hvp hvq)
    rw [extendFaceCoordinates_of_notMem _ _ hvNot]
    simp [c, p, q, hvc, hvp, hvq]

/-- Radial projection to the fan base recovers the original global coordinates after restoring
the cone-center weight. -/
theorem extendFaceCoordinates_eq_center_add_smul_normalizedBase (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) < 1) :
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x =
      Pi.single (K.adaptiveFanCenterVertex U hU f).1
          (x (K.adaptiveFanCenterVertex U hU f)) +
        (1 - x (K.adaptiveFanCenterVertex U hU f)) •
          extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f)
            (K.adaptiveFanNormalizedBasePoint U hU f x hxCenter) := by
  classical
  let d := 1 - x (K.adaptiveFanCenterVertex U hU f)
  have hd : d ≠ 0 := (sub_pos.mpr hxCenter).ne'
  have hfirst : d • Pi.single (K.adaptiveFanFirstVertex U hU f).1
        (x (K.adaptiveFanFirstVertex U hU f) / d) =
      Pi.single (K.adaptiveFanFirstVertex U hU f).1
        (x (K.adaptiveFanFirstVertex U hU f)) := by
    funext v
    by_cases hv : (K.adaptiveFanFirstVertex U hU f).1 = v
    · simp only [hv, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      exact mul_div_cancel₀ _ hd
    · simp only [Pi.smul_apply, ne_eq, hv, not_false_eq_true, Pi.single_eq_of_ne', smul_eq_mul,
        mul_zero]
  have hsecond : d • Pi.single (K.adaptiveFanSecondVertex U hU f).1
        (x (K.adaptiveFanSecondVertex U hU f) / d) =
      Pi.single (K.adaptiveFanSecondVertex U hU f).1
        (x (K.adaptiveFanSecondVertex U hU f)) := by
    funext v
    by_cases hv : (K.adaptiveFanSecondVertex U hU f).1 = v
    · simp only [hv, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      exact mul_div_cancel₀ _ hd
    · simp [hv]
  rw [K.extendFaceCoordinates_adaptiveFanFace U hU f x,
    K.extendFaceCoordinates_adaptiveFanFace U hU f
      (K.adaptiveFanNormalizedBasePoint U hU f x hxCenter),
    K.adaptiveFanNormalizedBasePoint_apply_center U hU f x hxCenter,
    K.adaptiveFanNormalizedBasePoint_apply_first U hU f x hxCenter,
    K.adaptiveFanNormalizedBasePoint_apply_second U hU f x hxCenter]
  dsimp only [d] at hfirst hsecond
  rw [smul_add, smul_add, Pi.single_zero, smul_zero, zero_add]
  change
    Pi.single (K.adaptiveFanCenterVertex U hU f).1
          (x (K.adaptiveFanCenterVertex U hU f)) +
        Pi.single (K.adaptiveFanFirstVertex U hU f).1
          (x (K.adaptiveFanFirstVertex U hU f)) +
      Pi.single (K.adaptiveFanSecondVertex U hU f).1
          (x (K.adaptiveFanSecondVertex U hU f)) =
      Pi.single (K.adaptiveFanCenterVertex U hU f).1
          (x (K.adaptiveFanCenterVertex U hU f)) +
        ((1 - x (K.adaptiveFanCenterVertex U hU f)) •
            Pi.single (K.adaptiveFanFirstVertex U hU f).1
              (x (K.adaptiveFanFirstVertex U hU f) /
                (1 - x (K.adaptiveFanCenterVertex U hU f))) +
          (1 - x (K.adaptiveFanCenterVertex U hU f)) •
            Pi.single (K.adaptiveFanSecondVertex U hU f).1
              (x (K.adaptiveFanSecondVertex U hU f) /
                (1 - x (K.adaptiveFanCenterVertex U hU f))))
  rw [hfirst, hsecond, add_assoc]

/-- Cross-tile interior overlap is face-to-face not only as a set: the two affine
parametrizations assign the same global barycentric coordinates. -/
theorem adaptiveFanExtendedCoordinates_eq_of_faceMap_eq_of_tile_ne_of_base_weights_pos
    (hU : IsOpen U) {f g : K.AdaptiveFanFace U hU}
    (hfg : f.1 ≠ g.1) (hlevel : f.1.1 ≤ g.1.1)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU g}}
    (hxy : K.adaptiveFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU g y)
    (hxFirst : 0 < x (K.adaptiveFanFirstVertex U hU f))
    (hxSecond : 0 < x (K.adaptiveFanSecondVertex U hU f))
    (hyFirst : 0 < y (K.adaptiveFanFirstVertex U hU g))
    (hySecond : 0 < y (K.adaptiveFanSecondVertex U hU g)) :
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x =
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU g) y := by
  have hxCenter :=
    K.adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne U hU hfg hxy
  have hyCenter :=
    K.adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne U hU hfg.symm hxy.symm
  have hxSum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU f x hxCenter
  have hySum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU g y hyCenter
  have hxSecondLt : x (K.adaptiveFanSecondVertex U hU f) ≤ 1 := by linarith
  have hySecondLt : y (K.adaptiveFanSecondVertex U hU g) ≤ 1 := by linarith
  let rx : Set.Icc (0 : ℝ) 1 :=
    ⟨x (K.adaptiveFanSecondVertex U hU f), ⟨hxSecond.le, hxSecondLt⟩⟩
  let ry : Set.Icc (0 : ℝ) 1 :=
    ⟨y (K.adaptiveFanSecondVertex U hU g), ⟨hySecond.le, hySecondLt⟩⟩
  have hxPathSimplex : K.adaptiveFanBaseSimplexPath U hU f rx = x :=
    K.adaptiveFanBaseSimplexPath_eq_of_secondWeight U hU f x rx rfl hxCenter
  have hyPathSimplex : K.adaptiveFanBaseSimplexPath U hU g ry = y :=
    K.adaptiveFanBaseSimplexPath_eq_of_secondWeight U hU g y ry rfl hyCenter
  have hpathEq : K.adaptiveFanBasePath U hU f rx =
      K.adaptiveFanBasePath U hU g ry := by
    change K.adaptiveFanFaceMap U hU f
      (K.adaptiveFanBaseSimplexPath U hU f rx) =
        K.adaptiveFanFaceMap U hU g
          (K.adaptiveFanBaseSimplexPath U hU g ry)
    rw [hxPathSimplex, hyPathSimplex]
    exact hxy
  have hcoordEq := congrArg (fun z : U ↦ z.1.1) hpathEq
  rw [K.adaptiveFanBasePath_val_eq_lineMap U hU f rx,
    K.adaptiveFanBasePath_val_eq_lineMap U hU g ry] at hcoordEq
  have hPQ : (K.adaptiveFanFirstVertex U hU f).1.1 ≠
      (K.adaptiveFanSecondVertex U hU f).1.1 := by
    intro h
    exact K.adaptiveFanFirstVertex_ne_second U hU f
      (Subtype.ext (Subtype.ext h))
  have hzeroF : Pi.single (K.adaptiveFanCenterVertex U hU f).1 (0 : ℝ) =
      (0 : K.realization → ℝ) := Pi.single_zero _
  have hzeroG : Pi.single (K.adaptiveFanCenterVertex U hU g).1 (0 : ℝ) =
      (0 : K.realization → ℝ) := Pi.single_zero _
  rcases K.adaptiveFanBaseEndpoints_eq_or_swap_of_faceMap_eq U hU
      hfg hlevel hxy hxFirst hxSecond hyFirst hySecond with hsame | hswap
  · have hfirstCoord := congrArg Subtype.val hsame.1
    have hsecondCoord := congrArg Subtype.val hsame.2
    rw [hfirstCoord, hsecondCoord] at hcoordEq
    have hr : rx.1 = ry.1 := (AffineMap.lineMap_injective ℝ hPQ) hcoordEq
    have hsecond : x (K.adaptiveFanSecondVertex U hU f) =
        y (K.adaptiveFanSecondVertex U hU g) := hr
    have hfirst : x (K.adaptiveFanFirstVertex U hU f) =
        y (K.adaptiveFanFirstVertex U hU g) := by linarith
    rw [K.extendFaceCoordinates_adaptiveFanFace U hU f x,
      K.extendFaceCoordinates_adaptiveFanFace U hU g y,
      hxCenter, hyCenter, hzeroF, hzeroG, zero_add, zero_add,
      hsame.1, hsame.2, hfirst, hsecond]
  · have hfirstCoord := congrArg Subtype.val hswap.1
    have hsecondCoord := congrArg Subtype.val hswap.2
    rw [hfirstCoord, hsecondCoord] at hcoordEq
    have hcoordEq' :
        AffineMap.lineMap (K.adaptiveFanFirstVertex U hU f).1.1
            (K.adaptiveFanSecondVertex U hU f).1.1 rx.1 =
          AffineMap.lineMap (K.adaptiveFanFirstVertex U hU f).1.1
            (K.adaptiveFanSecondVertex U hU f).1.1 (1 - ry.1) :=
      hcoordEq.trans (AffineMap.lineMap_apply_one_sub
        (K.adaptiveFanFirstVertex U hU f).1.1
        (K.adaptiveFanSecondVertex U hU f).1.1 ry.1).symm
    have hr : rx.1 = 1 - ry.1 := (AffineMap.lineMap_injective ℝ hPQ) hcoordEq'
    have hsecondFirst : x (K.adaptiveFanSecondVertex U hU f) =
        y (K.adaptiveFanFirstVertex U hU g) := by linarith
    have hfirstSecond : x (K.adaptiveFanFirstVertex U hU f) =
        y (K.adaptiveFanSecondVertex U hU g) := by linarith
    rw [K.extendFaceCoordinates_adaptiveFanFace U hU f x,
      K.extendFaceCoordinates_adaptiveFanFace U hU g y,
      hxCenter, hyCenter, hzeroF, hzeroG, zero_add, zero_add,
      hswap.1, hswap.2, hsecondFirst, hfirstSecond, add_comm]

/-- A zero-center fan point which is not in the relative interior of its base is one of the two
declared base vertices, both geometrically and in extended barycentric coordinates. -/
theorem adaptiveFanEndpointData_of_center_eq_zero_of_not_base_weights_pos
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0)
    (hxNot : ¬(0 < x (K.adaptiveFanFirstVertex U hU f) ∧
      0 < x (K.adaptiveFanSecondVertex U hU f))) :
    ((K.adaptiveFanFaceMap U hU f x).1 =
        (K.adaptiveFanFirstVertex U hU f).1 ∧
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x =
        Pi.single (K.adaptiveFanFirstVertex U hU f).1 1) ∨
    ((K.adaptiveFanFaceMap U hU f x).1 =
        (K.adaptiveFanSecondVertex U hU f).1 ∧
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x =
        Pi.single (K.adaptiveFanSecondVertex U hU f).1 1) := by
  have hsum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU f x hxCenter
  have hxFirstNonneg := x.2.1 (K.adaptiveFanFirstVertex U hU f)
  have hxSecondNonneg := x.2.1 (K.adaptiveFanSecondVertex U hU f)
  by_cases hxFirst : x (K.adaptiveFanFirstVertex U hU f) = 0
  · right
    have hxSecond : x (K.adaptiveFanSecondVertex U hU f) = 1 := by linarith
    let rone : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
    have hxPath : K.adaptiveFanBaseSimplexPath U hU f rone = x :=
      K.adaptiveFanBaseSimplexPath_eq_of_secondWeight U hU f x rone
        hxSecond.symm hxCenter
    have hxVertex : x =
        stdSimplex.vertex (K.adaptiveFanSecondVertex U hU f) := by
      simpa only [rone, K.adaptiveFanBaseSimplexPath_one U hU f] using hxPath.symm
    constructor
    · rw [hxVertex, K.adaptiveFanFaceMap_vertex U hU f]
    · rw [hxVertex]
      funext v
      by_cases hv : v = (K.adaptiveFanSecondVertex U hU f).1
      · subst v
        simp [extendFaceCoordinates,
          (K.adaptiveFanSecondVertex U hU f).2]
      · by_cases hmem : v ∈ K.adaptiveFanFaceVertices U hU f
        · have hne :
            (⟨v, hmem⟩ : {p // p ∈ K.adaptiveFanFaceVertices U hU f}) ≠
              K.adaptiveFanSecondVertex U hU f := by
            exact fun h ↦ hv (congrArg Subtype.val h)
          simp [extendFaceCoordinates, hmem, hv, hne]
        · simp [extendFaceCoordinates, hmem, hv]
  · left
    have hxFirstPos : 0 < x (K.adaptiveFanFirstVertex U hU f) :=
      lt_of_le_of_ne hxFirstNonneg (Ne.symm hxFirst)
    have hxSecond : x (K.adaptiveFanSecondVertex U hU f) = 0 := by
      apply le_antisymm
      · apply le_of_not_gt
        intro hxSecondPos
        exact hxNot ⟨hxFirstPos, hxSecondPos⟩
      · exact hxSecondNonneg
    have hxFirstOne : x (K.adaptiveFanFirstVertex U hU f) = 1 := by linarith
    let rzero : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
    have hxPath : K.adaptiveFanBaseSimplexPath U hU f rzero = x :=
      K.adaptiveFanBaseSimplexPath_eq_of_secondWeight U hU f x rzero
        hxSecond.symm hxCenter
    have hxVertex : x =
        stdSimplex.vertex (K.adaptiveFanFirstVertex U hU f) := by
      simpa only [rzero, K.adaptiveFanBaseSimplexPath_zero U hU f] using hxPath.symm
    constructor
    · rw [hxVertex, K.adaptiveFanFaceMap_vertex U hU f]
    · rw [hxVertex]
      funext v
      by_cases hv : v = (K.adaptiveFanFirstVertex U hU f).1
      · subst v
        simp [extendFaceCoordinates,
          (K.adaptiveFanFirstVertex U hU f).2]
      · by_cases hmem : v ∈ K.adaptiveFanFaceVertices U hU f
        · have hne :
            (⟨v, hmem⟩ : {p // p ∈ K.adaptiveFanFaceVertices U hU f}) ≠
              K.adaptiveFanFirstVertex U hU f := by
            exact fun h ↦ hv (congrArg Subtype.val h)
          simp [extendFaceCoordinates, hmem, hv, hne]
        · simp [extendFaceCoordinates, hmem, hv]

theorem adaptiveFanFaceMap_mem_boundaryVertices_of_center_zero_of_not_base_weights_pos
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0)
    (hxPos : ¬(0 < x (K.adaptiveFanFirstVertex U hU f) ∧
      0 < x (K.adaptiveFanSecondVertex U hU f))) :
    (K.adaptiveFanFaceMap U hU f x).1 ∈ K.boundaryVertices U hU f.1 := by
  rcases K.adaptiveFanEndpointData_of_center_eq_zero_of_not_base_weights_pos
      U hU f x hxCenter hxPos with hxEnd | hxEnd
  · rw [hxEnd.1]
    exact ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp
      (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU
        f.1 f.2.1 f.2.2)).1
  · rw [hxEnd.1]
    exact ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp
      (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU
        f.1 f.2.1 f.2.2)).1

-- A shorthand for the simplex of a resolved fan face.
/-- The resolved fan face assembled from a tile, edge, and interval. -/
def adaptiveFanFace (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) (a : K.AdaptiveEdgeInterval U hU t i) : K.AdaptiveFanFace U hU :=
  ⟨t, i, a⟩

/-- The simplex parametrizing a resolved fan face. -/
abbrev adaptiveFanFaceSimplex (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) (a : K.AdaptiveEdgeInterval U hU t i) :=
  stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU
    (K.adaptiveFanFace U hU t i a)}

-- Comparing boundary membership reduces to two fan faces with the same underlying tile.
theorem adaptiveFanBaseWeights_pos_of_faceMap_eq_of_same_tile
    (hU : IsOpen U) (f g : K.AdaptiveFanFace U hU) (hfg : f.1 = g.1)
    {x : K.adaptiveFanSimplex U hU f}
    {y : K.adaptiveFanSimplex U hU g}
    (hxy : K.adaptiveFanFaceMap U hU f x = K.adaptiveFanFaceMap U hU g y)
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0)
    (hyCenter : y (K.adaptiveFanCenterVertex U hU g) = 0)
    (hxPos : 0 < x (K.adaptiveFanFirstVertex U hU f) ∧
      0 < x (K.adaptiveFanSecondVertex U hU f)) :
    0 < y (K.adaptiveFanFirstVertex U hU g) ∧
      0 < y (K.adaptiveFanSecondVertex U hU g) := by
  have hactual : (K.adaptiveFanFaceMap U hU f x).1 =
      (K.adaptiveFanFaceMap U hU g y).1 :=
    congrArg Subtype.val hxy
  by_contra hyPos
  have hyMark :=
    K.adaptiveFanFaceMap_mem_boundaryVertices_of_center_zero_of_not_base_weights_pos
      U hU g y hyCenter hyPos
  have hyMark' : (K.adaptiveFanFaceMap U hU g y).1 ∈
      K.boundaryVertices U hU f.1 := by
    rw [hfg]
    exact hyMark
  exact K.adaptiveFanFaceMap_not_mem_boundaryVertices_of_base_weights_pos
    U hU f x hxCenter hxPos.1 hxPos.2 (hactual ▸ hyMark')

/- Resolved fan bases in one adaptive tile use compatible global barycentric coordinates at
every common point. -/
theorem adaptiveFanExtendedCoordinates_eq_of_faceMap_eq_of_same_tile_of_center_eq_zero
    (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i j : ZMod 3) (a : K.AdaptiveEdgeInterval U hU t i)
    (b : K.AdaptiveEdgeInterval U hU t j)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩}}
    (hxy : K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x =
      K.adaptiveFanFaceMap U hU ⟨t, j, b⟩ y)
    (hxCenter : x (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) = 0)
    (hyCenter : y (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) = 0) :
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩) x =
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩) y := by
  have hactual : (K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x).1 =
      (K.adaptiveFanFaceMap U hU ⟨t, j, b⟩ y).1 :=
    congrArg Subtype.val hxy
  by_cases hxPos :
      0 < x (K.adaptiveFanFirstVertex U hU ⟨t, i, a⟩) ∧
        0 < x (K.adaptiveFanSecondVertex U hU ⟨t, i, a⟩)
  · have hyPos := K.adaptiveFanBaseWeights_pos_of_faceMap_eq_of_same_tile
        U hU ⟨t, i, a⟩ ⟨t, j, b⟩ rfl hxy hxCenter hyCenter hxPos
    have hij :=
      K.adaptiveFanSide_eq_of_faceMap_eq_of_same_tile_of_base_weights_pos
        U hU t i j a b hxy hxCenter hyCenter
          hxPos.1 hxPos.2 hyPos.1 hyPos.2
    subst j
    have hab :=
      K.adaptiveFanInterval_eq_of_faceMap_eq_of_same_edge_of_base_weights_pos
        U hU t i a b hxy hxCenter hyCenter
          hxPos.1 hxPos.2 hyPos.1 hyPos.2
    subst b
    have hpoint := K.adaptiveFanFaceMap_injective U hU ⟨t, i, a⟩ hxy
    subst y
    rfl
  · rcases K.adaptiveFanEndpointData_of_center_eq_zero_of_not_base_weights_pos
        U hU ⟨t, i, a⟩ x hxCenter hxPos with hxEnd | hxEnd
    · have hxMark : (K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x).1 ∈
          K.boundaryVertices U hU t := by
        rw [hxEnd.1]
        exact ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
          (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU t i a)).1
      have hyNot : ¬(0 < y (K.adaptiveFanFirstVertex U hU ⟨t, j, b⟩) ∧
          0 < y (K.adaptiveFanSecondVertex U hU ⟨t, j, b⟩)) := by
        intro hyPos
        exact hxPos (K.adaptiveFanBaseWeights_pos_of_faceMap_eq_of_same_tile
          U hU ⟨t, j, b⟩ ⟨t, i, a⟩ rfl hxy.symm hyCenter hxCenter hyPos)
      rcases K.adaptiveFanEndpointData_of_center_eq_zero_of_not_base_weights_pos
          U hU ⟨t, j, b⟩ y hyCenter hyNot with hyEnd | hyEnd
      · have hv : (K.adaptiveFanFirstVertex U hU ⟨t, i, a⟩).1 =
            (K.adaptiveFanFirstVertex U hU ⟨t, j, b⟩).1 :=
          hxEnd.1.symm.trans (hactual.trans hyEnd.1)
        rw [hxEnd.2, hyEnd.2, hv]
      · have hv : (K.adaptiveFanFirstVertex U hU ⟨t, i, a⟩).1 =
            (K.adaptiveFanSecondVertex U hU ⟨t, j, b⟩).1 :=
          hxEnd.1.symm.trans (hactual.trans hyEnd.1)
        rw [hxEnd.2, hyEnd.2, hv]
    · have hxMark : (K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x).1 ∈
          K.boundaryVertices U hU t := by
        rw [hxEnd.1]
        exact ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
          (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU t i a)).1
      have hyNot : ¬(0 < y (K.adaptiveFanFirstVertex U hU ⟨t, j, b⟩) ∧
          0 < y (K.adaptiveFanSecondVertex U hU ⟨t, j, b⟩)) := by
        intro hyPos
        exact hxPos (K.adaptiveFanBaseWeights_pos_of_faceMap_eq_of_same_tile
          U hU ⟨t, j, b⟩ ⟨t, i, a⟩ rfl hxy.symm hyCenter hxCenter hyPos)
      rcases K.adaptiveFanEndpointData_of_center_eq_zero_of_not_base_weights_pos
          U hU ⟨t, j, b⟩ y hyCenter hyNot with hyEnd | hyEnd
      · have hv : (K.adaptiveFanSecondVertex U hU ⟨t, i, a⟩).1 =
            (K.adaptiveFanFirstVertex U hU ⟨t, j, b⟩).1 :=
          hxEnd.1.symm.trans (hactual.trans hyEnd.1)
        rw [hxEnd.2, hyEnd.2, hv]
      · have hv : (K.adaptiveFanSecondVertex U hU ⟨t, i, a⟩).1 =
            (K.adaptiveFanSecondVertex U hU ⟨t, j, b⟩).1 :=
          hxEnd.1.symm.trans (hactual.trans hyEnd.1)
        rw [hxEnd.2, hyEnd.2, hv]

/- Fan triangles in one adaptive tile assign the same global barycentric coordinates to every
common point, including the cone center. -/
theorem adaptiveFanExtendedCoordinates_eq_of_faceMap_eq_of_same_tile
    (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i j : ZMod 3) (a : K.AdaptiveEdgeInterval U hU t i)
    (b : K.AdaptiveEdgeInterval U hU t j)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩}}
    (hxy : K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x =
      K.adaptiveFanFaceMap U hU ⟨t, j, b⟩ y) :
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩) x =
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩) y := by
  have hc := K.adaptiveFanCenterWeight_eq_of_faceMap_eq_of_tile_eq
    U hU t i j a b hxy
  have hxSum := K.adaptiveFanWeights_sum U hU ⟨t, i, a⟩ x
  have hySum := K.adaptiveFanWeights_sum U hU ⟨t, j, b⟩ y
  have hxFirstNonneg := x.2.1 (K.adaptiveFanFirstVertex U hU ⟨t, i, a⟩)
  have hxSecondNonneg := x.2.1 (K.adaptiveFanSecondVertex U hU ⟨t, i, a⟩)
  have hyFirstNonneg := y.2.1 (K.adaptiveFanFirstVertex U hU ⟨t, j, b⟩)
  have hySecondNonneg := y.2.1 (K.adaptiveFanSecondVertex U hU ⟨t, j, b⟩)
  have hxCenterLe : x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) ≤ 1 := by
    linarith
  have hyCenterLe : y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) ≤ 1 := by
    linarith
  by_cases hxOne : x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) = 1
  · have hyOne : y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) = 1 :=
      hc.symm.trans hxOne
    have hxFirstZero : x.1 (K.adaptiveFanFirstVertex U hU ⟨t, i, a⟩) = 0 := by
      linarith
    have hxSecondZero : x.1 (K.adaptiveFanSecondVertex U hU ⟨t, i, a⟩) = 0 := by
      linarith
    have hyFirstZero : y.1 (K.adaptiveFanFirstVertex U hU ⟨t, j, b⟩) = 0 := by
      linarith
    have hySecondZero : y.1 (K.adaptiveFanSecondVertex U hU ⟨t, j, b⟩) = 0 := by
      linarith
    rw [K.extendFaceCoordinates_adaptiveFanFace U hU ⟨t, i, a⟩ x,
      K.extendFaceCoordinates_adaptiveFanFace U hU ⟨t, j, b⟩ y]
    change
      (Pi.single (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩).1
          (x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩)) : K.realization → ℝ) +
        (Pi.single (K.adaptiveFanFirstVertex U hU ⟨t, i, a⟩).1
          (x.1 (K.adaptiveFanFirstVertex U hU ⟨t, i, a⟩)) : K.realization → ℝ) +
        (Pi.single (K.adaptiveFanSecondVertex U hU ⟨t, i, a⟩).1
          (x.1 (K.adaptiveFanSecondVertex U hU ⟨t, i, a⟩)) : K.realization → ℝ) =
      (Pi.single (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩).1
          (y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩)) : K.realization → ℝ) +
        (Pi.single (K.adaptiveFanFirstVertex U hU ⟨t, j, b⟩).1
          (y.1 (K.adaptiveFanFirstVertex U hU ⟨t, j, b⟩)) : K.realization → ℝ) +
        (Pi.single (K.adaptiveFanSecondVertex U hU ⟨t, j, b⟩).1
          (y.1 (K.adaptiveFanSecondVertex U hU ⟨t, j, b⟩)) : K.realization → ℝ)
    rw [hxOne, hyOne, hxFirstZero, hxSecondZero, hyFirstZero, hySecondZero]
    simp only [Pi.single_zero, add_zero]
    rfl
  · have hxCenter : x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩) < 1 :=
      lt_of_le_of_ne hxCenterLe hxOne
    have hyOne : y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) ≠ 1 := by
      intro h
      exact hxOne (hc.trans h)
    have hyCenter : y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩) < 1 :=
      lt_of_le_of_ne hyCenterLe hyOne
    have hbaseMap := K.adaptiveFanNormalizedBaseFaceMap_eq_of_same_tile
      U hU t i j a b hxy hxCenter hyCenter
    have hbaseCoords :=
      K.adaptiveFanExtendedCoordinates_eq_of_faceMap_eq_of_same_tile_of_center_eq_zero
        U hU t i j a b hbaseMap
          (K.adaptiveFanNormalizedBasePoint_apply_center U hU ⟨t, i, a⟩ x hxCenter)
          (K.adaptiveFanNormalizedBasePoint_apply_center U hU ⟨t, j, b⟩ y hyCenter)
    calc
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩) x =
          Pi.single (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩).1
              (x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩)) +
            (1 - x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩)) •
              extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩)
                (K.adaptiveFanNormalizedBasePoint U hU ⟨t, i, a⟩ x hxCenter) :=
        K.extendFaceCoordinates_eq_center_add_smul_normalizedBase
          U hU ⟨t, i, a⟩ x hxCenter
      _ = Pi.single (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩).1
              (y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩)) +
            (1 - y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩)) •
              extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩)
                (K.adaptiveFanNormalizedBasePoint U hU ⟨t, j, b⟩ y hyCenter) := by
        change Pi.single (K.adaptiveFaceCenter U t)
              (x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩)) +
            (1 - x.1 (K.adaptiveFanCenterVertex U hU ⟨t, i, a⟩)) •
              extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩)
                (K.adaptiveFanNormalizedBasePoint U hU ⟨t, i, a⟩ x hxCenter) =
          Pi.single (K.adaptiveFaceCenter U t)
              (y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩)) +
            (1 - y.1 (K.adaptiveFanCenterVertex U hU ⟨t, j, b⟩)) •
              extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩)
                (K.adaptiveFanNormalizedBasePoint U hU ⟨t, j, b⟩ y hyCenter)
        rw [hc, hbaseCoords]
      _ = extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩) y :=
        (K.extendFaceCoordinates_eq_center_add_smul_normalizedBase
          U hU ⟨t, j, b⟩ y hyCenter).symm

/-- Fan triangles belonging to distinct adaptive tiles assign the same global barycentric
coordinates to every common geometric point.  Interior points use the resolved-interval
compatibility theorem; endpoint points are the common boundary marks collected by both tiles. -/
theorem adaptiveFanExtendedCoordinates_eq_of_faceMap_eq_of_tile_ne
    (hU : IsOpen U) {f g : K.AdaptiveFanFace U hU}
    (hfg : f.1 ≠ g.1)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU g}}
    (hxy : K.adaptiveFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU g y) :
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x =
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU g) y := by
  have hxCenter :=
    K.adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne U hU hfg hxy
  have hyCenter :=
    K.adaptiveFanCenterWeight_eq_zero_of_faceMap_eq_of_tile_ne U hU hfg.symm hxy.symm
  have hactual : (K.adaptiveFanFaceMap U hU f x).1 =
      (K.adaptiveFanFaceMap U hU g y).1 := congrArg Subtype.val hxy
  let xPos := 0 < x (K.adaptiveFanFirstVertex U hU f) ∧
    0 < x (K.adaptiveFanSecondVertex U hU f)
  let yPos := 0 < y (K.adaptiveFanFirstVertex U hU g) ∧
    0 < y (K.adaptiveFanSecondVertex U hU g)
  by_cases hxPos : xPos
  · by_cases hyPos : yPos
    · rcases Nat.le_total f.1.1 g.1.1 with hlevel | hlevel
      · exact K.adaptiveFanExtendedCoordinates_eq_of_faceMap_eq_of_tile_ne_of_base_weights_pos
          U hU hfg hlevel hxy hxPos.1 hxPos.2 hyPos.1 hyPos.2
      · exact (K.adaptiveFanExtendedCoordinates_eq_of_faceMap_eq_of_tile_ne_of_base_weights_pos
          U hU hfg.symm hlevel hxy.symm hyPos.1 hyPos.2 hxPos.1 hxPos.2).symm
    · rcases K.adaptiveFanEndpointData_of_center_eq_zero_of_not_base_weights_pos
          U hU g y hyCenter hyPos with hyEnd | hyEnd
      all_goals
        have hyCarrierG : (K.adaptiveFanFaceMap U hU g y).1 ∈
            K.adaptiveFaceCarrier U g.1 :=
          K.range_adaptiveFanFaceMap_subset_tile U hU g (Set.mem_range_self y)
        have hyCarrierF : (K.adaptiveFanFaceMap U hU g y).1 ∈
            K.adaptiveFaceCarrier U f.1 := by
          rw [← hactual]
          exact K.range_adaptiveFanFaceMap_subset_tile U hU f (Set.mem_range_self x)
      · have hyMarkG : (K.adaptiveFanFaceMap U hU g y).1 ∈
            K.boundaryVertices U hU g.1 := by
          rw [hyEnd.1]
          exact ((K.mem_boundaryEdgeVertices_iff U hU g.1 g.2.1 _).mp
            (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU
              g.1 g.2.1 g.2.2)).1
        have hyMarkF : (K.adaptiveFanFaceMap U hU g y).1 ∈
            K.boundaryVertices U hU f.1 :=
          (K.mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter U hU
            g.1 f.1 hyCarrierG hyCarrierF).mp hyMarkG
        exact False.elim
          (K.adaptiveFanFaceMap_not_mem_boundaryVertices_of_base_weights_pos
            U hU f x hxCenter hxPos.1 hxPos.2 (hactual ▸ hyMarkF))
      · have hyMarkG : (K.adaptiveFanFaceMap U hU g y).1 ∈
            K.boundaryVertices U hU g.1 := by
          rw [hyEnd.1]
          exact ((K.mem_boundaryEdgeVertices_iff U hU g.1 g.2.1 _).mp
            (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU
              g.1 g.2.1 g.2.2)).1
        have hyMarkF : (K.adaptiveFanFaceMap U hU g y).1 ∈
            K.boundaryVertices U hU f.1 :=
          (K.mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter U hU
            g.1 f.1 hyCarrierG hyCarrierF).mp hyMarkG
        exact False.elim
          (K.adaptiveFanFaceMap_not_mem_boundaryVertices_of_base_weights_pos
            U hU f x hxCenter hxPos.1 hxPos.2 (hactual ▸ hyMarkF))
  · rcases K.adaptiveFanEndpointData_of_center_eq_zero_of_not_base_weights_pos
        U hU f x hxCenter hxPos with hxEnd | hxEnd
    · have hxMarkF : (K.adaptiveFanFaceMap U hU f x).1 ∈
          K.boundaryVertices U hU f.1 := by
        rw [hxEnd.1]
        exact ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp
          (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU
            f.1 f.2.1 f.2.2)).1
      have hxCarrierF : (K.adaptiveFanFaceMap U hU f x).1 ∈
          K.adaptiveFaceCarrier U f.1 :=
        K.range_adaptiveFanFaceMap_subset_tile U hU f (Set.mem_range_self x)
      have hxCarrierG : (K.adaptiveFanFaceMap U hU f x).1 ∈
          K.adaptiveFaceCarrier U g.1 := by
        rw [hactual]
        exact K.range_adaptiveFanFaceMap_subset_tile U hU g (Set.mem_range_self y)
      have hxMarkG : (K.adaptiveFanFaceMap U hU f x).1 ∈
          K.boundaryVertices U hU g.1 :=
        (K.mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter U hU
          f.1 g.1 hxCarrierF hxCarrierG).mp hxMarkF
      have hyNot : ¬yPos := by
        intro hyPos
        exact K.adaptiveFanFaceMap_not_mem_boundaryVertices_of_base_weights_pos
          U hU g y hyCenter hyPos.1 hyPos.2 (hactual ▸ hxMarkG)
      rcases K.adaptiveFanEndpointData_of_center_eq_zero_of_not_base_weights_pos
          U hU g y hyCenter hyNot with hyEnd | hyEnd
      · have hv : (K.adaptiveFanFirstVertex U hU f).1 =
            (K.adaptiveFanFirstVertex U hU g).1 :=
          hxEnd.1.symm.trans (hactual.trans hyEnd.1)
        rw [hxEnd.2, hyEnd.2, hv]
      · have hv : (K.adaptiveFanFirstVertex U hU f).1 =
            (K.adaptiveFanSecondVertex U hU g).1 :=
          hxEnd.1.symm.trans (hactual.trans hyEnd.1)
        rw [hxEnd.2, hyEnd.2, hv]
    · have hxMarkF : (K.adaptiveFanFaceMap U hU f x).1 ∈
          K.boundaryVertices U hU f.1 := by
        rw [hxEnd.1]
        exact ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp
          (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU
            f.1 f.2.1 f.2.2)).1
      have hxCarrierF : (K.adaptiveFanFaceMap U hU f x).1 ∈
          K.adaptiveFaceCarrier U f.1 :=
        K.range_adaptiveFanFaceMap_subset_tile U hU f (Set.mem_range_self x)
      have hxCarrierG : (K.adaptiveFanFaceMap U hU f x).1 ∈
          K.adaptiveFaceCarrier U g.1 := by
        rw [hactual]
        exact K.range_adaptiveFanFaceMap_subset_tile U hU g (Set.mem_range_self y)
      have hxMarkG : (K.adaptiveFanFaceMap U hU f x).1 ∈
          K.boundaryVertices U hU g.1 :=
        (K.mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter U hU
          f.1 g.1 hxCarrierF hxCarrierG).mp hxMarkF
      have hyNot : ¬yPos := by
        intro hyPos
        exact K.adaptiveFanFaceMap_not_mem_boundaryVertices_of_base_weights_pos
          U hU g y hyCenter hyPos.1 hyPos.2 (hactual ▸ hxMarkG)
      rcases K.adaptiveFanEndpointData_of_center_eq_zero_of_not_base_weights_pos
          U hU g y hyCenter hyNot with hyEnd | hyEnd
      · have hv : (K.adaptiveFanSecondVertex U hU f).1 =
            (K.adaptiveFanFirstVertex U hU g).1 :=
          hxEnd.1.symm.trans (hactual.trans hyEnd.1)
        rw [hxEnd.2, hyEnd.2, hv]
      · have hv : (K.adaptiveFanSecondVertex U hU f).1 =
            (K.adaptiveFanSecondVertex U hU g).1 :=
          hxEnd.1.symm.trans (hactual.trans hyEnd.1)
        rw [hxEnd.2, hyEnd.2, hv]

/-- All adaptive fan faces use one global barycentric coordinate system on their overlaps. -/
theorem adaptiveFanExtendedCoordinates_eq_of_faceMap_eq (hU : IsOpen U)
    {f g : K.AdaptiveFanFace U hU}
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU g}}
    (hxy : K.adaptiveFanFaceMap U hU f x = K.adaptiveFanFaceMap U hU g y) :
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x =
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU g) y := by
  by_cases hfg : f.1 = g.1
  · rcases f with ⟨t, i, a⟩
    rcases g with ⟨s, j, b⟩
    dsimp only at hfg
    subst s
    exact K.adaptiveFanExtendedCoordinates_eq_of_faceMap_eq_of_same_tile
      U hU t i j a b hxy
  · exact K.adaptiveFanExtendedCoordinates_eq_of_faceMap_eq_of_tile_ne U hU hfg hxy

/-- In one adaptive tile, equal global coordinates have equal pulled-back barycentric sums and
hence equal images. -/
theorem adaptiveFanFaceMap_eq_of_extendedCoordinates_eq_of_same_tile
    (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i j : ZMod 3) (a : K.AdaptiveEdgeInterval U hU t i)
    (b : K.AdaptiveEdgeInterval U hU t j)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩}}
    (hxy : extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, i, a⟩) x =
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU ⟨t, j, b⟩) y) :
    K.adaptiveFanFaceMap U hU ⟨t, i, a⟩ x =
      K.adaptiveFanFaceMap U hU ⟨t, j, b⟩ y := by
  apply Subtype.ext
  change (K.safeSubdivision t.1).homeo
      (K.adaptiveFanSourcePoint U hU ⟨t, i, a⟩ x) =
    (K.safeSubdivision t.1).homeo
      (K.adaptiveFanSourcePoint U hU ⟨t, j, b⟩ y)
  apply congrArg (K.safeSubdivision t.1).homeo
  apply Subtype.ext
  funext v
  change (∑ p, x p * (K.adaptiveFanVertexSource U hU ⟨t, i, a⟩ p).1 v) =
    ∑ p, y p * (K.adaptiveFanVertexSource U hU ⟨t, j, b⟩ p).1 v
  simpa only [adaptiveFanVertexSource] using
    (sum_extendFaceCoordinates_eq_of_eq x y hxy
      (fun p ↦ ((K.safeSubdivision t.1).homeo.symm p).1 v))

/-- The center of one adaptive tile is not a fan vertex of a distinct tile. -/
theorem adaptiveFaceCenter_not_mem_adaptiveFanFaceVertices_of_ne
    (hU : IsOpen U) {f g : K.AdaptiveFanFace U hU} (hfg : f.1 ≠ g.1) :
    K.adaptiveFaceCenter U f.1 ∉ K.adaptiveFanFaceVertices U hU g := by
  intro hmem
  have hgCarrier := K.adaptiveFanVertex_mem_carrier U hU g hmem
  have hinter := K.adaptiveFaceCenter_mem_relInterior U f.1
  have hover := K.adaptiveFaceCarrier_inter_subset_relativeBoundaries U hfg
    ⟨K.adaptiveFaceCenter_mem_carrier U f.1, hgCarrier⟩
  exact hover.1.2 hinter

/-- On a fan base, the parametrization is the literal weighted sum of its declared geometric
vertices. -/
theorem adaptiveFanFaceMap_val_eq_weightedVertices_of_center_eq_zero
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f})
    (hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0) :
    (K.adaptiveFanFaceMap U hU f x).1.1 =
      fun v ↦ ∑ p, x p * p.1.1 v := by
  classical
  have hsum := K.adaptiveFanBaseWeights_sum_of_center_eq_zero U hU f x hxCenter
  have hsum' : x.1 (K.adaptiveFanFirstVertex U hU f) +
      x.1 (K.adaptiveFanSecondVertex U hU f) = 1 := hsum
  have hxSecondNonneg := x.2.1 (K.adaptiveFanSecondVertex U hU f)
  have hxSecondLe : x.1 (K.adaptiveFanSecondVertex U hU f) ≤ 1 := by
    have hxFirstNonneg := x.2.1 (K.adaptiveFanFirstVertex U hU f)
    linarith
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨x.1 (K.adaptiveFanSecondVertex U hU f), hxSecondNonneg, hxSecondLe⟩
  have hpath : K.adaptiveFanBaseSimplexPath U hU f r = x :=
    K.adaptiveFanBaseSimplexPath_eq_of_secondWeight U hU f x r rfl hxCenter
  have hmap : K.adaptiveFanFaceMap U hU f x = K.adaptiveFanBasePath U hU f r := by
    change K.adaptiveFanFaceMap U hU f x =
      K.adaptiveFanFaceMap U hU f (K.adaptiveFanBaseSimplexPath U hU f r)
    rw [hpath]
  rw [hmap, K.adaptiveFanBasePath_val_eq_lineMap U hU f r]
  let c := K.adaptiveFanCenterVertex U hU f
  let p := K.adaptiveFanFirstVertex U hU f
  let q := K.adaptiveFanSecondVertex U hU f
  have hcNot : c ∉ ({p, q} : Finset _) := by
    simp [c, p, q, K.adaptiveFanCenterVertex_ne_first U hU f,
      K.adaptiveFanCenterVertex_ne_second U hU f]
  have hpNot : p ∉ ({q} : Finset _) := by
    simp [p, q, K.adaptiveFanFirstVertex_ne_second U hU f]
  funext v
  rw [K.adaptiveFanVertex_univ U hU f,
    Finset.sum_insert hcNot, Finset.sum_insert hpNot, Finset.sum_singleton]
  simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    r, c, p, q]
  have hxCenter' : x.1 (K.adaptiveFanCenterVertex U hU f) = 0 := hxCenter
  change
    (1 - x.1 (K.adaptiveFanSecondVertex U hU f)) *
          (K.adaptiveFanFirstVertex U hU f).1.1 v +
        x.1 (K.adaptiveFanSecondVertex U hU f) *
          (K.adaptiveFanSecondVertex U hU f).1.1 v =
      x.1 (K.adaptiveFanCenterVertex U hU f) *
          (K.adaptiveFanCenterVertex U hU f).1.1 v +
        (x.1 (K.adaptiveFanFirstVertex U hU f) *
            (K.adaptiveFanFirstVertex U hU f).1.1 v +
          x.1 (K.adaptiveFanSecondVertex U hU f) *
            (K.adaptiveFanSecondVertex U hU f).1.1 v)
  rw [hxCenter', zero_mul, zero_add]
  have hxFirst : x.1 (K.adaptiveFanFirstVertex U hU f) =
      1 - x.1 (K.adaptiveFanSecondVertex U hU f) := by
    linarith [hsum']
  rw [hxFirst]

/-- Across distinct adaptive tiles, equal global coordinates describe the same point on their
common resolved boundary. -/
theorem adaptiveFanFaceMap_eq_of_extendedCoordinates_eq_of_tile_ne
    (hU : IsOpen U) {f g : K.AdaptiveFanFace U hU} (hfg : f.1 ≠ g.1)
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU g}}
    (hxy : extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x =
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU g) y) :
    K.adaptiveFanFaceMap U hU f x = K.adaptiveFanFaceMap U hU g y := by
  have hxCenter : x (K.adaptiveFanCenterVertex U hU f) = 0 := by
    calc
      x (K.adaptiveFanCenterVertex U hU f) =
          extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x
            (K.adaptiveFanCenterVertex U hU f).1 := by
        symm
        exact extendFaceCoordinates_of_mem _ _
          (K.adaptiveFanCenterVertex U hU f).2
      _ = extendFaceCoordinates (K.adaptiveFanFaceVertices U hU g) y
            (K.adaptiveFanCenterVertex U hU f).1 := congrFun hxy _
      _ = 0 := extendFaceCoordinates_of_notMem _ _
        (K.adaptiveFaceCenter_not_mem_adaptiveFanFaceVertices_of_ne U hU hfg)
  have hyCenter : y (K.adaptiveFanCenterVertex U hU g) = 0 := by
    calc
      y (K.adaptiveFanCenterVertex U hU g) =
          extendFaceCoordinates (K.adaptiveFanFaceVertices U hU g) y
            (K.adaptiveFanCenterVertex U hU g).1 := by
        symm
        exact extendFaceCoordinates_of_mem _ _
          (K.adaptiveFanCenterVertex U hU g).2
      _ = extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x
            (K.adaptiveFanCenterVertex U hU g).1 := congrFun hxy.symm _
      _ = 0 := extendFaceCoordinates_of_notMem _ _
        (K.adaptiveFaceCenter_not_mem_adaptiveFanFaceVertices_of_ne U hU hfg.symm)
  apply Subtype.ext
  apply Subtype.ext
  rw [K.adaptiveFanFaceMap_val_eq_weightedVertices_of_center_eq_zero U hU f x hxCenter,
    K.adaptiveFanFaceMap_val_eq_weightedVertices_of_center_eq_zero U hU g y hyCenter]
  funext v
  exact sum_extendFaceCoordinates_eq_of_eq x y hxy (fun p ↦ p.1 v)

/-- Equal global barycentric coordinates are sufficient for equality of adaptive fan images. -/
theorem adaptiveFanFaceMap_eq_of_extendedCoordinates_eq (hU : IsOpen U)
    {f g : K.AdaptiveFanFace U hU}
    {x : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU f}}
    {y : stdSimplex ℝ {p // p ∈ K.adaptiveFanFaceVertices U hU g}}
    (hxy : extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f) x =
      extendFaceCoordinates (K.adaptiveFanFaceVertices U hU g) y) :
    K.adaptiveFanFaceMap U hU f x = K.adaptiveFanFaceMap U hU g y := by
  by_cases hfg : f.1 = g.1
  · rcases f with ⟨t, i, a⟩
    rcases g with ⟨s, j, b⟩
    dsimp only at hfg
    subst s
    exact K.adaptiveFanFaceMap_eq_of_extendedCoordinates_eq_of_same_tile
      U hU t i j a b hxy
  · exact K.adaptiveFanFaceMap_eq_of_extendedCoordinates_eq_of_tile_ne U hU hfg hxy

/-- The fan-triangle family is locally finite because it has finitely many faces over each
adaptive tile and the adaptive tile family is locally finite. -/
theorem locallyFinite_adaptiveFanFaceMap (hU : IsOpen U) :
    LocallyFinite fun f : K.AdaptiveFanFace U hU ↦
      Set.range (K.adaptiveFanFaceMap U hU f) := by
  classical
  intro p
  obtain ⟨V, hpV, hfinite⟩ := K.locallyFinite_adaptiveFaceCarrierInOpen U hU p
  refine ⟨V, hpV, ?_⟩
  let tiles : Set (K.AdaptiveFace U) :=
    {t | (K.adaptiveFaceCarrierInOpen U t ∩ V).Nonempty}
  have htiles : tiles.Finite := hfinite
  let faces : Finset (K.AdaptiveFanFace U hU) :=
    htiles.toFinset.sigma fun t ↦
      Finset.univ.sigma fun i : ZMod 3 ↦ Finset.univ
  apply faces.finite_toSet.subset
  intro f hf
  apply Finset.mem_coe.mpr
  rw [Finset.mem_sigma]
  constructor
  · rw [Set.Finite.mem_toFinset]
    obtain ⟨q, hqFace, hqV⟩ := hf
    exact ⟨q,
      K.range_adaptiveFanFaceMap_subset_tile U hU f hqFace,
      hqV⟩
  · rw [Finset.mem_sigma]
    exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
