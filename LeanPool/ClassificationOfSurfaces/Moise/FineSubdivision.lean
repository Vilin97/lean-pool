/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ConeExtension
import LeanPool.ClassificationOfSurfaces.Moise.CommonSubdivision

/-!
# Fine subdivisions of finite plane complexes

Moise Chapter 6 repeatedly chooses a subdivision sufficiently fine for a continuous map.  For a
finite plane complex this follows from a concrete finite line arrangement: cover the compact
support by small balls and, around every center, cut by two vertical and two horizontal lines.
Every chamber meeting the corresponding smaller ball is trapped in the resulting rectangle.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex)

theorem affine_nonneg_on_cellCarrier {a : Plane →ᵃ[ℝ] ℝ}
    {s : Finset K.Vertex} (hs : ∀ v ∈ s, 0 ≤ a (K.position v)) :
    ∀ x ∈ K.cellCarrier s, 0 ≤ a x := by
  intro x hx
  have hsubset : K.position '' (s : Set K.Vertex) ⊆ {x | 0 ≤ a x} := by
    rintro y ⟨v, hv, rfl⟩
    exact hs v hv
  exact convexHull_min hsubset ((convex_Ici 0).affine_preimage a) hx

theorem affine_nonpos_on_cellCarrier {a : Plane →ᵃ[ℝ] ℝ}
    {s : Finset K.Vertex} (hs : ∀ v ∈ s, a (K.position v) ≤ 0) :
    ∀ x ∈ K.cellCarrier s, a x ≤ 0 := by
  intro x hx
  have hsubset : K.position '' (s : Set K.Vertex) ⊆ {x | a x ≤ 0} := by
    rintro y ⟨v, hv, rfl⟩
    exact hs v hv
  exact convexHull_min hsubset ((convex_Iic 0).affine_preimage a) hx

end PlaneComplex

/-- The vertical line whose zero set is `x = c`. -/
noncomputable def verticalCut (c : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX - AffineMap.const ℝ Plane c

/-- The horizontal line whose zero set is `y = c`. -/
noncomputable def horizontalCut (c : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianY - AffineMap.const ℝ Plane c

@[simp] theorem verticalCut_apply (c : ℝ) (p : Plane) : verticalCut c p = p 0 - c := by
  rfl

@[simp] theorem horizontalCut_apply (c : ℝ) (p : Plane) : horizontalCut c p = p 1 - c := by
  rfl

/-- Four coordinate cuts bounding a square of radius `r` around `p`. -/
noncomputable def boxCuts (p : Plane) (r : ℝ) : List (Plane →ᵃ[ℝ] ℝ) :=
  [verticalCut (p 0 - r), verticalCut (p 0 + r),
    horizontalCut (p 1 - r), horizontalCut (p 1 + r)]

@[simp] theorem mem_boxCuts {p : Plane} {r : ℝ} {a : Plane →ᵃ[ℝ] ℝ} :
    a ∈ boxCuts p r ↔
      a = verticalCut (p 0 - r) ∨ a = verticalCut (p 0 + r) ∨
      a = horizontalCut (p 1 - r) ∨ a = horizontalCut (p 1 + r) := by
  simp [boxCuts]

/-- All box cuts associated to a finite set of centers. -/
noncomputable def coverCuts (centers : Finset Plane) (r : ℝ) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  centers.toList.flatMap fun p => boxCuts p r

theorem boxCut_mem_coverCuts {centers : Finset Plane} {p : Plane} (hp : p ∈ centers)
    (r : ℝ) {a : Plane →ᵃ[ℝ] ℝ} (ha : a ∈ boxCuts p r) :
    a ∈ coverCuts centers r := by
  simp only [coverCuts, List.mem_flatMap]
  exact ⟨p, by simpa using hp, ha⟩

private theorem coordinate_dist_le (x y : Plane) (k : Fin 2) :
    |x k - y k| ≤ dist x y := by
  have h := PiLp.norm_apply_le (x - y) k
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, dist_eq_norm] using h

/-- A chamber cut by the four box lines around `p` is trapped in that box as soon as it meets
the concentric half-radius ball. -/
theorem TriangleMesh.cellCarrier_subset_box_of_monochromatic
    (N : TriangleMesh) {p : Plane} {r : ℝ} (hr : 0 < r)
    (hmono : ∀ a ∈ boxCuts p r, N.IsMonochromatic a)
    {t : Finset N.Vertex} (ht : t ∈ N.triangles) {x : Plane}
    (hx : x ∈ N.toPlaneComplex.cellCarrier t) (hxp : dist x p < r / 2) :
    ∀ y ∈ N.toPlaneComplex.cellCarrier t,
      p 0 - r ≤ y 0 ∧ y 0 ≤ p 0 + r ∧
      p 1 - r ≤ y 1 ∧ y 1 ≤ p 1 + r := by
  have hxcoord (k : Fin 2) : |x k - p k| < r / 2 :=
    (coordinate_dist_le x p k).trans_lt hxp
  have trapLower (a : Plane →ᵃ[ℝ] ℝ) (ha : a ∈ boxCuts p r)
      (hax : 0 < a x) : ∀ y ∈ N.toPlaneComplex.cellCarrier t, 0 ≤ a y := by
    rcases hmono a ha t ht with hnonneg | hnonpos
    · exact N.toPlaneComplex.affine_nonneg_on_cellCarrier hnonneg
    · have := N.toPlaneComplex.affine_nonpos_on_cellCarrier hnonpos x hx
      exact (not_le_of_gt hax this).elim
  have trapUpper (a : Plane →ᵃ[ℝ] ℝ) (ha : a ∈ boxCuts p r)
      (hax : a x < 0) : ∀ y ∈ N.toPlaneComplex.cellCarrier t, a y ≤ 0 := by
    rcases hmono a ha t ht with hnonneg | hnonpos
    · have := N.toPlaneComplex.affine_nonneg_on_cellCarrier hnonneg x hx
      exact (not_le_of_gt hax this).elim
    · exact N.toPlaneComplex.affine_nonpos_on_cellCarrier hnonpos
  have hx0lower : 0 < verticalCut (p 0 - r) x := by
    rw [verticalCut_apply]
    have := hxcoord 0
    rw [abs_lt] at this
    linarith
  have hx0upper : verticalCut (p 0 + r) x < 0 := by
    rw [verticalCut_apply]
    have := hxcoord 0
    rw [abs_lt] at this
    linarith
  have hx1lower : 0 < horizontalCut (p 1 - r) x := by
    rw [horizontalCut_apply]
    have := hxcoord 1
    rw [abs_lt] at this
    linarith
  have hx1upper : horizontalCut (p 1 + r) x < 0 := by
    rw [horizontalCut_apply]
    have := hxcoord 1
    rw [abs_lt] at this
    linarith
  intro y hy
  have h0lower := trapLower (verticalCut (p 0 - r)) (by simp) hx0lower y hy
  have h0upper := trapUpper (verticalCut (p 0 + r)) (by simp) hx0upper y hy
  have h1lower := trapLower (horizontalCut (p 1 - r)) (by simp) hx1lower y hy
  have h1upper := trapUpper (horizontalCut (p 1 + r)) (by simp) hx1upper y hy
  simp only [verticalCut_apply] at h0lower h0upper
  simp only [horizontalCut_apply] at h1lower h1upper
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem dist_lt_four_mul_of_mem_box {p x y : Plane} {r : ℝ} (hr : 0 < r)
    (hx : p 0 - r ≤ x 0 ∧ x 0 ≤ p 0 + r ∧
      p 1 - r ≤ x 1 ∧ x 1 ≤ p 1 + r)
    (hy : p 0 - r ≤ y 0 ∧ y 0 ≤ p 0 + r ∧
      p 1 - r ≤ y 1 ∧ y 1 ≤ p 1 + r) :
    dist x y < 4 * r := by
  have h0 : |x 0 - y 0| ≤ 2 * r := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2.1, hy.1, hy.2.1]
  have h1 : |x 1 - y 1| ≤ 2 * r := by
    rw [abs_le]
    constructor <;> linarith [hx.2.2.1, hx.2.2.2, hy.2.2.1, hy.2.2.2]
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq]
  apply (Real.sqrt_lt' (by positivity : 0 < 4 * r)).2
  have h0sq : |x 0 - y 0| ^ 2 ≤ (2 * r) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h0
  have h1sq : |x 1 - y 1| ^ 2 ≤ (2 * r) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h1
  simp only [sq_abs] at h0sq h1sq
  simp only [sq_abs]
  nlinarith [sq_nonneg r]

/-- A finite pure plane complex has a subdivision on whose two-cells a prescribed continuous map
has arbitrarily small oscillation. -/
theorem PlaneComplex.exists_subdivision_image_dist_lt (K : PlaneComplex)
    (hpure : K.IsPure2) {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ L : PlaneComplex, L.IsPure2 ∧ L.Subdivides K ∧
      ∀ t ∈ L.cells, ∀ x ∈ L.cellCarrier t, ∀ y ∈ L.cellCarrier t,
        dist (h x) (h y) < eps := by
  classical
  have huniform : UniformContinuousOn h K.support :=
    K.isCompact_support.uniformContinuousOn_of_continuous hcont
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huniform) eps heps
  let r : ℝ := delta / 8
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨centers, hcentersSub, hcentersFinite, hcover⟩ :=
    K.isCompact_support.finite_cover_balls (show 0 < r / 2 by positivity)
  let centerFinset : Finset Plane := hcentersFinite.toFinset
  let M : TriangleMesh := K.toTriangleMesh
  let lines := coverCuts centerFinset r
  let N : TriangleMesh := M.refineByLines lines
  let L : PlaneComplex := N.toPlaneComplex
  have hMK : M.toPlaneComplex.Subdivides K := by
    constructor
    · exact K.toTriangleMesh_support hpure
    · intro s hs
      obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
      exact ⟨t, K.mem_simplexes_of_mem_cells ht, convexHull_mono (Set.image_mono hst)⟩
  have hLK : L.Subdivides K :=
    (M.refineByLines_subdivides lines).trans hMK
  refine ⟨L, N.toPlaneComplex_isPure2, hLK, ?_⟩
  intro t ht x hx y hy
  have htSimplex : t ∈ L.simplexes := (Finset.mem_filter.mp ht).1
  have htcard : t.card = 3 := (Finset.mem_filter.mp ht).2
  obtain ⟨-, T, hT, htT⟩ := N.mem_faces_iff.mp htSimplex
  have hteq : t = T := by
    apply Finset.eq_of_subset_of_card_le htT
    have hcardT := N.card_triangle T hT
    exact (hcardT.trans htcard.symm).le
  subst T
  have hxK : x ∈ K.support := hLK.1 ▸ L.cellCarrier_subset_support htSimplex hx
  have hyK : y ∈ K.support := hLK.1 ▸ L.cellCarrier_subset_support htSimplex hy
  have hxCover := hcover hxK
  simp only [Set.mem_iUnion, Metric.mem_ball] at hxCover
  obtain ⟨p, hpCenters, hxp⟩ := hxCover
  have hpFinset : p ∈ centerFinset := by
    simpa only [centerFinset, Set.Finite.mem_toFinset] using hpCenters
  have hmono : ∀ a ∈ boxCuts p r, N.IsMonochromatic a := by
    intro a ha
    exact M.refineByLines_isMonochromatic_of_mem lines
      (boxCut_mem_coverCuts hpFinset r ha)
  have htrap := N.cellCarrier_subset_box_of_monochromatic hr hmono hT hx hxp
  have hxbox := htrap x hx
  have hybox := htrap y hy
  have hxy : dist x y < delta := by
    have hsmall := dist_lt_four_mul_of_mem_box hr hxbox hybox
    dsimp [r] at hsmall
    linarith
  exact hcontrol x hxK y hyK hxy

/-- A sufficiently fine subdivision of a pure finite plane complex is subordinate to any open
cover of its support. -/
theorem PlaneComplex.exists_subdivision_subordinate_openCover
    (K : PlaneComplex) (hpure : K.IsPure2)
    {I : Type*} (U : I → Set Plane) (hU : ∀ i, IsOpen (U i))
    (hcover : K.support ⊆ ⋃ i, U i) :
    ∃ L : PlaneComplex, L.IsPure2 ∧ L.Subdivides K ∧
      ∀ t ∈ L.cells, ∃ i, L.cellCarrier t ⊆ U i := by
  obtain ⟨delta, hdelta, hLebesgue⟩ :=
    lebesgue_number_lemma_of_metric K.isCompact_support hU hcover
  obtain ⟨L, hLpure, hLK, hsmall⟩ :=
    K.exists_subdivision_image_dist_lt hpure continuousOn_id hdelta
  refine ⟨L, hLpure, hLK, ?_⟩
  intro t ht
  have htpos : 0 < t.card := by
    rw [L.card_of_mem_cells ht]
    decide
  obtain ⟨v, hv⟩ := Finset.card_pos.mp htpos
  have hpCarrier : L.position v ∈ L.cellCarrier t := by
    exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  have hpSupport : L.position v ∈ K.support := by
    rw [← hLK.1]
    exact L.cellCarrier_subset_support (L.mem_simplexes_of_mem_cells ht) hpCarrier
  obtain ⟨i, hi⟩ := hLebesgue (L.position v) hpSupport
  refine ⟨i, fun x hx => hi ?_⟩
  rw [Metric.mem_ball]
  exact hsmall t ht x hx (L.position v) hpCarrier

/-- A finite triangle submesh selected between a compact set and an ambient open set.  Unlike a
full subdivision, its support is only the retained compact polyhedron; every retained triangle
is nevertheless subordinate to the original plane complex. -/
structure PlaneComplex.OpenSubmesh
    (K : PlaneComplex) (C U : Set Plane) where
  /-- The `mesh` declaration. -/
  mesh : TriangleMesh
  face_subordinate : ∀ t ∈ mesh.triangles,
    ∃ s ∈ K.simplexes, mesh.toPlaneComplex.cellCarrier t ⊆ K.cellCarrier s
  covers : C ⊆ mesh.toPlaneComplex.support
  contained : mesh.toPlaneComplex.support ⊆ U

namespace PlaneComplex.OpenSubmesh

variable {K : PlaneComplex} {C U : Set Plane}

/-- Every retained triangle of an open submesh still lies in the original complex support. -/
theorem support_subset_original (L : K.OpenSubmesh C U) :
    L.mesh.toPlaneComplex.support ⊆ K.support := by
  intro x hx
  rw [L.mesh.toPlaneComplex_support] at hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨s, hs, hts⟩ := L.face_subordinate t ht
  exact K.cellCarrier_subset_support hs (hts hxt)

end PlaneComplex.OpenSubmesh

/-- Every compact subset of an open subset of a pure finite plane complex is covered by a finite
triangle submesh lying in that open set. -/
theorem PlaneComplex.exists_openSubmesh
    (K : PlaneComplex) (hpure : K.IsPure2) {C U : Set Plane}
    (hC : IsCompact C) (hCK : C ⊆ K.support)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    Nonempty (K.OpenSubmesh C U) := by
  classical
  let W : Bool → Set Plane := fun b => if b then Cᶜ else U
  have hWopen : ∀ b, IsOpen (W b) := by
    intro b
    cases b <;> simp [W, hU, hC.isClosed]
  have hWcover : K.support ⊆ ⋃ b, W b := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact Set.mem_iUnion.mpr ⟨false, by simpa [W] using hCU hxC⟩
    · exact Set.mem_iUnion.mpr ⟨true, by simpa [W] using hxC⟩
  obtain ⟨L, hLpure, hLK, hsubordinate⟩ :=
    K.exists_subdivision_subordinate_openCover hpure W hWopen hWcover
  let M := L.toTriangleMesh
  let N : TriangleMesh := M.restrictTriangles fun t =>
    L.cellCarrier t ⊆ U
  refine ⟨{
    mesh := N
    face_subordinate := ?_
    covers := ?_
    contained := ?_ }⟩
  · intro t ht
    have htM : t ∈ M.triangles :=
      (M.mem_restrictTriangles_triangles (fun s => L.cellCarrier s ⊆ U)).mp ht |>.1
    have htL : t ∈ L.simplexes := by
      exact L.mem_simplexes_of_mem_cells htM
    obtain ⟨s, hs, hts⟩ := hLK.2 t htL
    exact ⟨s, hs, hts⟩
  · intro z hzC
    have hzK : z ∈ K.support := hCK hzC
    have hzL : z ∈ L.support := by
      rw [hLK.1]
      exact hzK
    rw [PlaneComplex.support] at hzL
    obtain ⟨s, hs, hzs⟩ := Set.mem_iUnion₂.mp hzL
    obtain ⟨t, ht, hst, htcard⟩ := hLpure s hs
    have hzt : z ∈ L.cellCarrier t := by
      exact convexHull_mono (Set.image_mono hst) hzs
    have htCell : t ∈ L.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    obtain ⟨b, hb⟩ := hsubordinate t htCell
    have htU : L.cellCarrier t ⊆ U := by
      cases b with
      | false => simpa [W] using hb
      | true =>
          exfalso
          have hzNotC : z ∈ Cᶜ := by simpa [W] using hb hzt
          exact hzNotC hzC
    have htN : t ∈ N.triangles := by
      exact (M.mem_restrictTriangles_triangles
        (fun s => L.cellCarrier s ⊆ U)).mpr ⟨htCell, htU⟩
    rw [N.toPlaneComplex_support]
    exact Set.mem_iUnion₂.mpr ⟨t, htN, hzt⟩
  · intro z hz
    rw [N.toPlaneComplex_support] at hz
    obtain ⟨t, htN, hzt⟩ := Set.mem_iUnion₂.mp hz
    have htU :=
      (M.mem_restrictTriangles_triangles
        (fun s => L.cellCarrier s ⊆ U)).mp htN |>.2
    exact htU hzt

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
