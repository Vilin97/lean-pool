/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.LineSubdivision
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalJordan

/-!
# Polygonal Jordan regions as finite plane complexes

This file formalizes Moise Chapter 2, Theorem 2.  The finitely many affine lines containing the
edges of a polygon cut an enclosing triangle into a finite triangle mesh.  The triangles on the
bounded side of polygonal Jordan form the required finite complex.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PolygonalCircle

variable (J : PolygonalCircle)

/-- The linear functional whose zero set is parallel to the vector from `p` to `q`. -/
noncomputable def edgeNormalLinear (p q : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun x := (q - p) 0 * x 1 - (q - p) 1 * x 0
  map_add' := by
    intro x y
    simp only [PiLp.add_apply]
    ring
  map_smul' := by
    intro c x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- An affine equation for the line containing polygon edge `i`. -/
noncomputable def edgeLine (i : ZMod J.n) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.mk' (fun x => edgeNormalLinear (J.vertex i) (J.vertex (i + 1))
      (x - J.vertex i))
    (edgeNormalLinear (J.vertex i) (J.vertex (i + 1))) (J.vertex i) (by
      intro x
      simp)

@[simp] theorem edgeLine_initial (i : ZMod J.n) :
    J.edgeLine i (J.vertex i) = 0 := by
  simp [edgeLine]

@[simp] theorem edgeLine_terminal (i : ZMod J.n) :
    J.edgeLine i (J.vertex (i + 1)) = 0 := by
  simp [edgeLine, edgeNormalLinear]
  ring

theorem edgeLine_eq_zero_of_mem_edgeSegment (i : ZMod J.n) {x : Plane}
    (hx : x ∈ J.edgeSegment i) : J.edgeLine i x = 0 := by
  rw [edgeSegment, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simp [edgeLine, edgeNormalLinear]
  ring

theorem edgeLine_surjective (i : ZMod J.n) : Function.Surjective (J.edgeLine i) := by
  let dx : ℝ := (J.vertex (i + 1) - J.vertex i) 0
  let dy : ℝ := (J.vertex (i + 1) - J.vertex i) 1
  have hxy : dx ≠ 0 ∨ dy ≠ 0 := by
    by_contra h
    push Not at h
    apply J.adjacent_ne i
    ext j
    fin_cases j
    · exact (sub_eq_zero.mp (by simpa [dx, PiLp.sub_apply] using h.1)).symm
    · exact (sub_eq_zero.mp (by simpa [dy, PiLp.sub_apply] using h.2)).symm
  have hden : dx ^ 2 + dy ^ 2 ≠ 0 := by
    rcases hxy with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx]
    · nlinarith [sq_pos_of_ne_zero hy]
  intro y
  refine ⟨J.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx, ?_⟩
  change (J.vertex (i + 1) - J.vertex i) 0 *
      (J.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx - J.vertex i) 1 -
      (J.vertex (i + 1) - J.vertex i) 1 *
      (J.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx - J.vertex i) 0 = y
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, planePoint_apply_zero,
    planePoint_apply_one, smul_eq_mul]
  ring_nf
  field_simp [hden]
  dsimp [dx, dy]
  ring_nf

theorem interior_edgeLine_nonneg (i : ZMod J.n) :
    interior {x | 0 ≤ J.edgeLine i x} = {x | 0 < J.edgeLine i x} := by
  let f := J.edgeLine i
  change interior (f ⁻¹' Set.Ici 0) = f ⁻¹' Set.Ioi 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional
    (J.edgeLine_surjective i)).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Ici]

theorem interior_edgeLine_nonpos (i : ZMod J.n) :
    interior {x | J.edgeLine i x ≤ 0} = {x | J.edgeLine i x < 0} := by
  let f := J.edgeLine i
  change interior (f ⁻¹' Set.Iic 0) = f ⁻¹' Set.Iio 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional
    (J.edgeLine_surjective i)).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Iic]

/-- The finite list of supporting lines used in Moise's arrangement proof. -/
noncomputable def edgeLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (ZMod J.n)).toList.map J.edgeLine

theorem edgeLine_mem_edgeLines (i : ZMod J.n) : J.edgeLine i ∈ J.edgeLines := by
  simp [edgeLines]

/-- A positive radius of a closed ball containing the closed polygonal region. -/
noncomputable def enclosingRadius : ℝ :=
  max (J.isCompact_closedRegion.isBounded.subset_closedBall (0 : Plane)).choose 1

theorem enclosingRadius_pos : 0 < J.enclosingRadius := by
  unfold enclosingRadius
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem closedRegion_subset_enclosingBall :
    J.closedRegion ⊆ Metric.closedBall (0 : Plane) J.enclosingRadius := by
  intro x hx
  have h := (J.isCompact_closedRegion.isBounded.subset_closedBall (0 : Plane)).choose_spec hx
  rw [Metric.mem_closedBall] at h ⊢
  exact h.trans (le_max_left _ _)

/-- Vertices of a large triangle containing the ball of radius `R`. -/
def enclosingTriangleVertices (R : ℝ) : Fin 3 → Plane :=
  ![planePoint (-3 * R) (-2 * R), planePoint (3 * R) (-2 * R), planePoint 0 (4 * R)]

theorem enclosingTriangleVertices_affineIndependent {R : ℝ} (hR : 0 < R) :
    AffineIndependent ℝ (enclosingTriangleVertices R) := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

theorem closedBall_subset_enclosingTriangle {R : ℝ} (hR : 0 < R) :
    Metric.closedBall (0 : Plane) R ⊆
      convexHull ℝ (Set.range (enclosingTriangleVertices R)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hx0 := PiLp.norm_apply_le (p := 2) x (0 : Fin 2)
  have hx1 := PiLp.norm_apply_le (p := 2) x (1 : Fin 2)
  simp only [Real.norm_eq_abs] at hx0 hx1
  have hx0lo : -R ≤ x 0 := by linarith [neg_abs_le (x 0)]
  have hx0hi : x 0 ≤ R := by linarith [le_abs_self (x 0)]
  have hx1lo : -R ≤ x 1 := by linarith [neg_abs_le (x 1)]
  have hx1hi : x 1 ≤ R := by linarith [le_abs_self (x 1)]
  let w : Fin 3 → ℝ :=
    ![(4 * R - x 1 - 2 * x 0) / (12 * R),
      (4 * R - x 1 + 2 * x 0) / (12 * R),
      (x 1 + 2 * R) / (6 * R)]
  apply mem_convexHull_range_fin3_of_weights _ x w
  · intro i
    fin_cases i
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
  · change (4 * R - x 1 - 2 * x 0) / (12 * R) +
        (4 * R - x 1 + 2 * x 0) / (12 * R) +
        (x 1 + 2 * R) / (6 * R) = 1
    field_simp [hR.ne']
    ring
  · ext i
    fin_cases i <;> simp [w, enclosingTriangleVertices, planePoint]
    all_goals field_simp [hR.ne']; ring

/-- The one-triangle seed mesh in which the supporting-line arrangement is constructed. -/
noncomputable def enclosingMesh : TriangleMesh :=
  TriangleMesh.single (enclosingTriangleVertices J.enclosingRadius)
    (enclosingTriangleVertices_affineIndependent J.enclosingRadius_pos)

theorem closedRegion_subset_enclosingMesh_support :
    J.closedRegion ⊆ J.enclosingMesh.toPlaneComplex.support := by
  rw [enclosingMesh, TriangleMesh.single_support]
  exact J.closedRegion_subset_enclosingBall.trans
    (closedBall_subset_enclosingTriangle J.enclosingRadius_pos)

/-- The finite mesh obtained by cutting the enclosing triangle along every polygon edge line. -/
noncomputable def arrangementMesh : TriangleMesh :=
  J.enclosingMesh.refineByLines J.edgeLines

theorem arrangementMesh_support :
    J.arrangementMesh.toPlaneComplex.support = J.enclosingMesh.toPlaneComplex.support :=
  J.enclosingMesh.refineByLines_support J.edgeLines

theorem arrangementMesh_isMonochromatic (i : ZMod J.n) :
    J.arrangementMesh.IsMonochromatic (J.edgeLine i) :=
  J.enclosingMesh.refineByLines_isMonochromatic_of_mem J.edgeLines (J.edgeLine_mem_edgeLines i)

theorem closedRegion_subset_arrangementMesh_support :
    J.closedRegion ⊆ J.arrangementMesh.toPlaneComplex.support := by
  rw [J.arrangementMesh_support]
  exact J.closedRegion_subset_enclosingMesh_support

/-- Carrier of one maximal triangle in the supporting-line arrangement. -/
def arrangementTriangleCarrier (t : Finset J.arrangementMesh.Vertex) : Set Plane :=
  convexHull ℝ (J.arrangementMesh.position '' (t : Set _))

theorem convex_arrangementTriangleCarrier (t : Finset J.arrangementMesh.Vertex) :
    Convex ℝ (J.arrangementTriangleCarrier t) :=
  convex_convexHull ℝ _

theorem isClosed_arrangementTriangleCarrier (t : Finset J.arrangementMesh.Vertex) :
    IsClosed (J.arrangementTriangleCarrier t) :=
  (t.finite_toSet.image J.arrangementMesh.position).isClosed_convexHull ℝ

theorem arrangementTriangleCarrier_interior_nonempty
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles) :
    (interior (J.arrangementTriangleCarrier t)).Nonempty := by
  apply (J.convex_arrangementTriangleCarrier t).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [arrangementTriangleCarrier, affineSpan_convexHull]
  have hrange : Set.range (fun v : t => J.arrangementMesh.position v) =
      J.arrangementMesh.position '' (t : Set _) := by
    ext x
    simp
  rw [← hrange]
  have hAI := J.arrangementMesh.affineIndependent_triangle t ht
  apply hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Fintype.card_coe, J.arrangementMesh.card_triangle t ht]
  simp [Plane]

theorem closure_interior_arrangementTriangleCarrier
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles) :
    closure (interior (J.arrangementTriangleCarrier t)) = J.arrangementTriangleCarrier t := by
  calc
    closure (interior (J.arrangementTriangleCarrier t)) =
        closure (J.arrangementTriangleCarrier t) :=
      (J.convex_arrangementTriangleCarrier t).closure_interior_eq_closure_of_nonempty_interior
        (J.arrangementTriangleCarrier_interior_nonempty ht)
    _ = J.arrangementTriangleCarrier t := (J.isClosed_arrangementTriangleCarrier t).closure_eq

/-- Every open triangle chamber of the supporting-line arrangement misses the polygon. -/
theorem arrangementTriangle_interior_disjoint_carrier
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles) :
    Disjoint
      (interior (J.arrangementTriangleCarrier t))
      J.carrier := by
  rw [Set.disjoint_left]
  intro x hxint hxcarrier
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcarrier
  have hxzero : J.edgeLine i x = 0 := J.edgeLine_eq_zero_of_mem_edgeSegment i hxi
  rcases J.arrangementMesh_isMonochromatic i t ht with hpos | hneg
  · have hsubset : J.arrangementTriangleCarrier t ⊆
        {y | 0 ≤ J.edgeLine i y} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hpos v hv
      · exact (convex_Ici (0 : ℝ)).affine_preimage (J.edgeLine i)
    have hxstrict := interior_mono hsubset hxint
    rw [J.interior_edgeLine_nonneg i] at hxstrict
    change 0 < J.edgeLine i x at hxstrict
    linarith
  · have hsubset : J.arrangementTriangleCarrier t ⊆
        {y | J.edgeLine i y ≤ 0} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact (convex_Iic (0 : ℝ)).affine_preimage (J.edgeLine i)
    have hxstrict := interior_mono hsubset hxint
    rw [J.interior_edgeLine_nonpos i] at hxstrict
    change J.edgeLine i x < 0 at hxstrict
    linarith

theorem arrangementTriangle_interior_side
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles) :
    interior (J.arrangementTriangleCarrier t) ⊆ J.interiorRegion ∨
      interior (J.arrangementTriangleCarrier t) ⊆ J.exteriorRegion := by
  let s := interior (J.arrangementTriangleCarrier t)
  have hsconn : IsPreconnected s :=
    (J.convex_arrangementTriangleCarrier t).interior.isPreconnected
  have hscarrier : s ⊆ J.carrierᶜ := by
    intro x hx
    exact Set.disjoint_left.mp (J.arrangementTriangle_interior_disjoint_carrier ht) hx
  have hsunion : s ⊆ J.interiorRegion ∪ J.exteriorRegion := by
    rw [J.interior_union_exterior]
    exact hscarrier
  obtain ⟨x, hx⟩ := J.arrangementTriangleCarrier_interior_nonempty ht
  have hxside := hsunion hx
  rcases hxside with hxin | hxout
  · exact Or.inl <| hsconn.subset_left_of_subset_union J.isOpen_interiorRegion
      J.isOpen_exteriorRegion J.disjoint_interior_exterior hsunion ⟨x, hx, hxin⟩
  · exact Or.inr <| hsconn.subset_right_of_subset_union J.isOpen_interiorRegion
      J.isOpen_exteriorRegion J.disjoint_interior_exterior hsunion ⟨x, hx, hxout⟩

/-- The arrangement chambers lying on the bounded side of the polygon. -/
def IsInteriorArrangementTriangle (t : Finset J.arrangementMesh.Vertex) : Prop :=
  interior (J.arrangementTriangleCarrier t) ⊆ J.interiorRegion

/-- The finite mesh formed by all bounded-side arrangement chambers. -/
noncomputable def closedRegionMesh : TriangleMesh :=
  by
    classical
    exact J.arrangementMesh.restrictTriangles J.IsInteriorArrangementTriangle

theorem closedRegionMesh_triangle_mem {t : Finset J.closedRegionMesh.Vertex} :
    t ∈ J.closedRegionMesh.triangles ↔
      t ∈ J.arrangementMesh.triangles ∧ J.IsInteriorArrangementTriangle t := by
  classical
  exact J.arrangementMesh.mem_restrictTriangles_triangles J.IsInteriorArrangementTriangle

theorem arrangementTriangleCarrier_subset_closedRegion
    {t : Finset J.arrangementMesh.Vertex} (ht : t ∈ J.arrangementMesh.triangles)
    (hinside : J.IsInteriorArrangementTriangle t) :
    J.arrangementTriangleCarrier t ⊆ J.closedRegion := by
  rw [← J.closure_interior_arrangementTriangleCarrier ht, closedRegion]
  exact closure_mono hinside

theorem closedRegionMesh_support_subset :
    J.closedRegionMesh.toPlaneComplex.support ⊆ J.closedRegion := by
  rw [TriangleMesh.toPlaneComplex_support]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨htarr, htinside⟩ := J.closedRegionMesh_triangle_mem.mp ht
  exact J.arrangementTriangleCarrier_subset_closedRegion htarr htinside hxt

theorem interiorRegion_subset_closedRegionMesh_support :
    J.interiorRegion ⊆ J.closedRegionMesh.toPlaneComplex.support := by
  intro x hxinside
  have hxclosed : x ∈ J.closedRegion := by
    rw [J.closedRegion_eq_union]
    exact Or.inl hxinside
  have hxsupport := J.closedRegion_subset_arrangementMesh_support hxclosed
  rw [TriangleMesh.toPlaneComplex_support] at hxsupport
  simp only [Set.mem_iUnion] at hxsupport
  obtain ⟨t, ht, hxt⟩ := hxsupport
  have hxclosure : x ∈ closure (interior (J.arrangementTriangleCarrier t)) := by
    rw [J.closure_interior_arrangementTriangleCarrier ht]
    exact hxt
  have hxclosureInter :
      x ∈ closure (J.interiorRegion ∩ interior (J.arrangementTriangleCarrier t)) :=
    J.isOpen_interiorRegion.inter_closure ⟨hxinside, hxclosure⟩
  have hmeet' :
      (J.interiorRegion ∩ interior (J.arrangementTriangleCarrier t)).Nonempty :=
    Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
  have hmeet :
      (interior (J.arrangementTriangleCarrier t) ∩ J.interiorRegion).Nonempty := by
    obtain ⟨y, hyinside, hyt⟩ := hmeet'
    exact ⟨y, hyt, hyinside⟩
  have htinside : J.IsInteriorArrangementTriangle t := by
    rcases J.arrangementTriangle_interior_side ht with hin | hout
    · exact hin
    · obtain ⟨y, hyt, hyinside⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp J.disjoint_interior_exterior hyinside (hout hyt)
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [Set.mem_iUnion]
  exact ⟨t, J.closedRegionMesh_triangle_mem.mpr ⟨ht, htinside⟩, hxt⟩

theorem closedRegionMesh_support :
    J.closedRegionMesh.toPlaneComplex.support = J.closedRegion := by
  apply Set.Subset.antisymm J.closedRegionMesh_support_subset
  rw [closedRegion]
  exact closure_minimal
    J.interiorRegion_subset_closedRegionMesh_support
    J.closedRegionMesh.toPlaneComplex.isCompact_support.isClosed

theorem disjoint_carrier_exteriorRegion : Disjoint J.carrier J.exteriorRegion := by
  rw [Set.disjoint_left]
  intro x hxcarrier hxexterior
  have hxcompl : x ∈ J.carrierᶜ := by
    rw [← J.interior_union_exterior]
    exact Or.inr hxexterior
  exact hxcompl hxcarrier

theorem disjoint_closedRegion_exteriorRegion : Disjoint J.closedRegion J.exteriorRegion := by
  rw [J.closedRegion_eq_union]
  exact J.disjoint_interior_exterior.sup_left J.disjoint_carrier_exteriorRegion

/-- The topological boundary of the closed polygonal disk is the original polygon. -/
theorem frontier_closedRegion : frontier J.closedRegion = J.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxclosed : x ∈ J.closedRegion := by
      have hx' := frontier_subset_closure hx
      simpa [J.isCompact_closedRegion.isClosed.closure_eq] using hx'
    rw [J.closedRegion_eq_union] at hxclosed
    rcases hxclosed with hxinside | hxcarrier
    · have hxint : x ∈ interior J.closedRegion :=
        interior_maximal (by rw [J.closedRegion_eq_union]; exact Set.subset_union_left)
          J.isOpen_interiorRegion hxinside
      exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier hxint hx
    · exact hxcarrier
  · intro x hxcarrier
    have hxclosed : x ∈ J.closedRegion := by
      rw [J.closedRegion_eq_union]
      exact Or.inr hxcarrier
    rw [J.isCompact_closedRegion.isClosed.frontier_eq]
    refine ⟨hxclosed, ?_⟩
    intro hxint
    have hxclosureExterior : x ∈ closure J.exteriorRegion :=
      frontier_subset_closure (J.frontier_exteriorRegion.symm ▸ hxcarrier)
    have hxclosureInter :
        x ∈ closure (interior J.closedRegion ∩ J.exteriorRegion) :=
      isOpen_interior.inter_closure ⟨hxint, hxclosureExterior⟩
    obtain ⟨y, hyint, hyexterior⟩ := Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
    exact Set.disjoint_left.mp J.disjoint_closedRegion_exteriorRegion
      (interior_subset hyint) hyexterior

theorem interior_closedRegion : interior J.closedRegion = J.interiorRegion := by
  apply Set.Subset.antisymm
  · intro p hp
    have hpClosed : p ∈ J.closedRegion := interior_subset hp
    rw [J.closedRegion_eq_union] at hpClosed
    rcases hpClosed with hpInside | hpCarrier
    · exact hpInside
    · have hpFrontier : p ∈ frontier J.closedRegion := by
        rw [J.frontier_closedRegion]
        exact hpCarrier
      exact (Set.disjoint_left.mp disjoint_interior_frontier hp hpFrontier).elim
  · exact interior_maximal (by rw [J.closedRegion_eq_union]; exact Set.subset_union_left)
      J.isOpen_interiorRegion

theorem isConnected_closedRegion : IsConnected J.closedRegion := by
  rw [closedRegion]
  exact J.isConnected_interiorRegion.closure

end PolygonalCircle

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
