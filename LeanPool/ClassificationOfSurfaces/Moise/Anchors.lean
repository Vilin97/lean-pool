/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalJordan
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Positive anchors for the Moise plane structures

Concrete instances required by the definition-faithfulness rules
(`docs/AUTOFORMALIZATION_GUIDE.md`): the standard triangle with vertices `(0,0)`, `(1,0)`,
`(0,1)` realizes

* a `PolygonalCircle` (`standardTriangleCircle`): its boundary as a polygonal simple closed
  curve with three vertices and three edges; and
* a `PlaneComplex` (`standardTrianglePlaneComplex`): the full simplicial complex of the closed
  triangle, with three vertices, three edges and one 2-face (all seven nonempty vertex subsets).

Both geometric side conditions (`consecutive_inter`, `face_inter`) reduce to
`AffineIndependent.convexHull_inter`: convex hulls of subfamilies of an affinely independent
family intersect in the hull of the shared vertices.  The only genuinely geometric input is the
affine independence of the three vertices, proved from non-collinearity by coordinate
computation.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- The vertices of the standard triangle: `(0,0)`, `(1,0)`, `(0,1)`. -/
def standardTriangleVertex : Fin 3 → Plane :=
  ![!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(0 : ℝ), 1]]

/-- The vertices of the standard triangle are not collinear. -/
theorem standardTriangle_not_collinear :
    ¬ Collinear ℝ ({!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(0 : ℝ), 1]} : Set Plane) := by
  intro hcol
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_insert _ _)).mp hcol
  obtain ⟨rB, hB⟩ := hv !₂[(1 : ℝ), 0] (by simp)
  obtain ⟨rC, hC⟩ := hv !₂[(0 : ℝ), 1] (by simp)
  have hB0 := congrArg (fun p : Plane => p 0) hB
  have hC0 := congrArg (fun p : Plane => p 0) hC
  have hC1 := congrArg (fun p : Plane => p 1) hC
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_zero] at hB0 hC0 hC1
  rcases mul_eq_zero.mp hC0.symm with h | h
  · rw [h, zero_mul] at hC1
    exact one_ne_zero hC1
  · rw [h, mul_zero] at hB0
    exact one_ne_zero hB0

/-- The vertices of the standard triangle are affinely independent. -/
theorem standardTriangleVertex_affineIndependent :
    AffineIndependent ℝ standardTriangleVertex :=
  affineIndependent_iff_not_collinear_set.mpr standardTriangle_not_collinear

theorem standardTriangleVertex_injective :
    Function.Injective standardTriangleVertex :=
  standardTriangleVertex_affineIndependent.injective

/-- Any relabelling of the standard triangle vertices by an injective index vector is affinely
independent. -/
theorem standardTriangleVertex_triple_affineIndependent (a b c : Fin 3)
    (h : Function.Injective ![a, b, c]) :
    AffineIndependent ℝ
      ![standardTriangleVertex a, standardTriangleVertex b, standardTriangleVertex c] := by
  have he : ![standardTriangleVertex a, standardTriangleVertex b, standardTriangleVertex c]
      = standardTriangleVertex ∘ ![a, b, c] := by
    funext j
    fin_cases j <;> rfl
  rw [he]
  exact standardTriangleVertex_affineIndependent.comp_embedding ⟨![a, b, c], h⟩

/-- **Positive anchor** for `PolygonalCircle`: the boundary of the standard triangle with
vertices `(0,0)`, `(1,0)`, `(0,1)` is a polygonal simple closed curve. -/
def standardTriangleCircle : PolygonalCircle where
  n := 3
  three_le := le_rfl
  vertex := standardTriangleVertex
  adjacent_ne := fun i =>
    standardTriangleVertex_injective.ne ((by decide : ∀ j : ZMod 3, j ≠ j + 1) i)
  consecutive_inter := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases hcase with rfl | rfl | rfl
    · rw [show (0 : ZMod 3) + 1 = 1 by decide, show (0 : ZMod 3) + 2 = 2 by decide]
      exact segment_inter_segment_of_affineIndependent
        (standardTriangleVertex_triple_affineIndependent 0 1 2 (by decide))
    · rw [show (1 : ZMod 3) + 1 = 2 by decide, show (1 : ZMod 3) + 2 = 0 by decide]
      exact segment_inter_segment_of_affineIndependent
        (standardTriangleVertex_triple_affineIndependent 1 2 0 (by decide))
    · rw [show (2 : ZMod 3) + 1 = 0 by decide, show (2 : ZMod 3) + 2 = 1 by decide]
      exact segment_inter_segment_of_affineIndependent
        (standardTriangleVertex_triple_affineIndependent 2 0 1 (by decide))
  nonadjacent_disjoint := fun i j h₁ h₂ h₃ =>
    absurd ((by decide : ∀ i j : ZMod 3, i ≠ j → i ≠ j + 1 → j = i + 1) i j h₁ h₂) h₃

/-- Three affinely independent points in the plane form an affine basis. -/
noncomputable def planeAffineBasisOfTriple (p : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) : AffineBasis (Fin 3) ℝ Plane where
  toFun := p
  ind' := hp
  tot' := hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Plane])

/-- The interior of a full-dimensional plane triangle consists exactly of points with all
three barycentric coordinates positive. -/
theorem interior_convexHull_affineBasis (b : AffineBasis (Fin 3) ℝ Plane) :
    interior (convexHull ℝ (Set.range b)) = {x | ∀ i, 0 < b.coord i x} := by
  have hC : convexHull ℝ (Set.range b) = {x | ∀ i, 0 ≤ b.coord i x} :=
    b.convexHull_eq_nonneg_coord
  apply Set.Subset.antisymm
  · intro x hx
    have hxC : x ∈ convexHull ℝ (Set.range b) := interior_subset hx
    have hxnonneg : ∀ i, 0 ≤ b.coord i x := by rwa [hC] at hxC
    intro i
    apply lt_of_le_of_ne (hxnonneg i)
    intro hzero
    have hzero' : b.coord i x = 0 := hzero.symm
    have hxi : x ≠ b i := by
      intro hxi
      rw [hxi, b.coord_apply_eq] at hzero'
      norm_num at hzero'
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp hx)
    let d := dist (b i) x
    have hd : 0 < d := by
      dsimp [d]
      exact dist_pos.mpr hxi.symm
    let δ := ε / (2 * d)
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hd)
    let y := AffineMap.lineMap (b i) x (1 + δ)
    have hyball : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball]
      dsimp [y]
      rw [dist_lineMap_right, show (1 : ℝ) - (1 + δ) = -δ by ring,
        norm_neg, Real.norm_eq_abs, abs_of_pos hδ]
      change δ * d < ε
      dsimp [δ]
      have hdne : d ≠ 0 := hd.ne'
      have heq : ε / (2 * d) * d = ε / 2 := by
        field_simp [hdne]
      rw [heq]
      linarith
    have hyC := hball hyball
    have hycoord : 0 ≤ b.coord i y := by
      rw [hC] at hyC
      exact hyC i
    have hcoord : b.coord i y = -δ := by
      dsimp [y]
      rw [AffineMap.apply_lineMap, b.coord_apply_eq, hzero']
      simp [AffineMap.lineMap_apply_module]
    rw [hcoord] at hycoord
    linarith
  · intro x hx
    let P : Set Plane := ⋂ i : Fin 3, (b.coord i) ⁻¹' Set.Ioi 0
    have hPopen : IsOpen P := by
      dsimp [P]
      exact isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage
        (b.coord i).continuous_of_finiteDimensional
    have hxP : x ∈ P := by
      simp only [P, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]
      exact hx
    apply interior_maximal _ hPopen hxP
    intro y hy
    rw [hC]
    intro i
    have : 0 < b.coord i y := by
      have hi := Set.mem_iInter.mp hy i
      simpa only [Set.mem_preimage, Set.mem_Ioi] using hi
    exact this.le

/-- The standard triangle vertices, regarded as an affine basis of the plane. -/
noncomputable def standardTriangleAffineBasis : AffineBasis (Fin 3) ℝ Plane :=
  planeAffineBasisOfTriple standardTriangleVertex standardTriangleVertex_affineIndependent

/-- The standard triangle as an affine simplex. -/
noncomputable def standardTriangleSimplex : Affine.Simplex ℝ Plane 2 where
  points := standardTriangleVertex
  independent := standardTriangleVertex_affineIndependent

/-- The carrier of `standardTriangleCircle` is the frontier of the closed standard triangle. -/
theorem standardTriangleCircle_carrier :
    standardTriangleCircle.carrier =
      frontier (convexHull ℝ (Set.range standardTriangleVertex)) := by
  let S := standardTriangleSimplex
  have hclosed : IsClosed (convexHull ℝ (Set.range standardTriangleVertex)) :=
    ((Set.finite_range standardTriangleVertex).isCompact_convexHull ℝ).isClosed
  rw [hclosed.frontier_eq]
  have hinter : interior (convexHull ℝ (Set.range standardTriangleVertex)) =
      S.interior := by
    have hrange : Set.range (standardTriangleAffineBasis : Fin 3 → Plane) =
        Set.range standardTriangleVertex := rfl
    rw [← hrange, interior_convexHull_affineBasis standardTriangleAffineBasis]
    ext x
    simp only [Affine.Simplex.interior, Affine.Simplex.setInterior, Set.mem_ofPred_eq]
    constructor
    · intro hx
      let w : Fin 3 → ℝ := fun i => standardTriangleAffineBasis.coord i x
      refine ⟨w, standardTriangleAffineBasis.sum_coord_apply_eq_one x, ?_, ?_⟩
      · intro i
        have hi := hx i
        constructor
        · exact hi
        · have hsum := standardTriangleAffineBasis.sum_coord_apply_eq_one x
          rw [Fin.sum_univ_three] at hsum
          have h0 := hx (0 : Fin 3)
          have h1 := hx (1 : Fin 3)
          have h2 := hx (2 : Fin 3)
          fin_cases i <;> dsimp [w] <;> nlinarith
      · exact standardTriangleAffineBasis.affineCombination_coord_eq_self x
    · rintro ⟨w, hw, hwI, hwx⟩ i
      have hwx' : (Finset.univ.affineCombination ℝ
          (standardTriangleAffineBasis : Fin 3 → Plane)) w = x := by
        have hb : (standardTriangleAffineBasis : Fin 3 → Plane) =
            standardTriangleVertex := rfl
        rw [hb]
        simpa [S, standardTriangleSimplex] using hwx
      have hcoord := congrArg (standardTriangleAffineBasis.coord i) hwx'.symm
      rw [standardTriangleAffineBasis.coord_apply_combination_of_mem
        (Finset.mem_univ i) hw] at hcoord
      exact hcoord ▸ (hwI i).1
  have hclosedInterior : S.closedInterior =
      convexHull ℝ (Set.range standardTriangleVertex) := by
    exact (Affine.Simplex.convexHull_eq_closedInterior S).symm
  rw [← hclosedInterior]
  change standardTriangleCircle.carrier = S.closedInterior \ interior S.closedInterior
  rw [show interior S.closedInterior = S.interior by
    rw [hclosedInterior, hinter], S.closedInterior_sdiff_interior]
  have hface0 : (S.faceOpposite 0).closedInterior =
      segment ℝ (standardTriangleVertex 1) (standardTriangleVertex 2) := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior (S.faceOpposite 0),
      S.range_faceOpposite_points]
    have himage : standardTriangleVertex '' ({0}ᶜ : Set (Fin 3)) =
        {standardTriangleVertex 1, standardTriangleVertex 2} := by
      ext z
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j <;> simp at hj ⊢
      · rintro (rfl | rfl)
        · exact ⟨1, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
    rw [show S.points = standardTriangleVertex by rfl, himage, convexHull_pair]
  have hface1 : (S.faceOpposite 1).closedInterior =
      segment ℝ (standardTriangleVertex 0) (standardTriangleVertex 2) := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior (S.faceOpposite 1),
      S.range_faceOpposite_points]
    have himage : standardTriangleVertex '' ({1}ᶜ : Set (Fin 3)) =
        {standardTriangleVertex 0, standardTriangleVertex 2} := by
      ext z
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j <;> simp at hj ⊢
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
    rw [show S.points = standardTriangleVertex by rfl, himage, convexHull_pair]
  have hface2 : (S.faceOpposite 2).closedInterior =
      segment ℝ (standardTriangleVertex 0) (standardTriangleVertex 1) := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior (S.faceOpposite 2),
      S.range_faceOpposite_points]
    have himage : standardTriangleVertex '' ({2}ᶜ : Set (Fin 3)) =
        {standardTriangleVertex 0, standardTriangleVertex 1} := by
      ext z
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j <;> simp at hj ⊢
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
    rw [show S.points = standardTriangleVertex by rfl, himage, convexHull_pair]
  ext x
  simp only [PolygonalCircle.carrier, PolygonalCircle.edgeSegment, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    have hcases : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := hcases i
    rcases hcase with rfl | rfl | rfl
    · refine ⟨2, ?_⟩
      rw [hface2]
      change x ∈ segment ℝ (standardTriangleVertex 0)
        (standardTriangleVertex ((0 : ZMod 3) + (1 : ZMod 3))) at hi
      rw [show (0 : ZMod 3) + (1 : ZMod 3) = 1 by decide] at hi
      convert hi using 1; rfl
    · refine ⟨0, ?_⟩
      rw [hface0]
      change x ∈ segment ℝ (standardTriangleVertex 1)
        (standardTriangleVertex ((1 : ZMod 3) + (1 : ZMod 3))) at hi
      rw [show (1 : ZMod 3) + (1 : ZMod 3) = 2 by decide] at hi
      convert hi using 1; rfl
    · refine ⟨1, ?_⟩
      rw [hface1, segment_symm]
      change x ∈ segment ℝ (standardTriangleVertex 2)
        (standardTriangleVertex ((2 : ZMod 3) + (1 : ZMod 3))) at hi
      rw [show (2 : ZMod 3) + (1 : ZMod 3) = 0 by decide] at hi
      convert hi using 1; rfl
  · rintro ⟨i, hi⟩
    have hcases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases hcases i with rfl | rfl | rfl
    · rw [hface0] at hi
      refine ⟨1, ?_⟩
      change x ∈ segment ℝ (standardTriangleVertex 1)
        (standardTriangleVertex ((1 : ZMod 3) + (1 : ZMod 3)))
      rw [show (1 : ZMod 3) + (1 : ZMod 3) = 2 by decide]
      convert hi using 1; rfl
    · rw [hface1] at hi
      refine ⟨2, ?_⟩
      change x ∈ segment ℝ (standardTriangleVertex 2)
        (standardTriangleVertex ((2 : ZMod 3) + (1 : ZMod 3)))
      rw [show (2 : ZMod 3) + (1 : ZMod 3) = 0 by decide, segment_symm]
      exact hi
    · rw [hface2] at hi
      refine ⟨0, ?_⟩
      change x ∈ segment ℝ (standardTriangleVertex 0)
        (standardTriangleVertex ((0 : ZMod 3) + (1 : ZMod 3)))
      rw [show (0 : ZMod 3) + (1 : ZMod 3) = 1 by decide]
      convert hi using 1; rfl

/-- **Positive anchor** for `PlaneComplex`: the closed standard triangle as a simplicial
complex, with the seven nonempty subsets of its three vertices as faces. -/
noncomputable abbrev standardTrianglePlaneComplex : PlaneComplex where
  Vertex := Fin 3
  position := standardTriangleVertex
  position_injective := standardTriangleVertex_injective
  simplexes := Finset.univ.powerset.filter (·.Nonempty)
  nonempty_of_mem := fun _ hs => (Finset.mem_filter.mp hs).2
  card_le_three := by decide
  down_closed := by decide
  affineIndependent := fun s _ =>
    standardTriangleVertex_affineIndependent.comp_embedding (Function.Embedding.subtype _)
  face_inter := by
    intro s _ t _
    classical
    have hS : AffineIndependent ℝ
        ((↑) : (Finset.univ.image standardTriangleVertex) → Plane) :=
      affineIndependent_finset_coe standardTriangleVertex_affineIndependent fun a ha => by
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
        exact ⟨i, hi⟩
    have hmain := hS.convexHull_inter
      (t₁ := s.image standardTriangleVertex) (t₂ := t.image standardTriangleVertex)
      (Finset.image_subset_image (Finset.subset_univ s))
      (Finset.image_subset_image (Finset.subset_univ t))
    rw [← Finset.coe_inter, ← Finset.image_inter s t standardTriangleVertex_injective] at hmain
    simpa [Finset.coe_image] using hmain.symm

@[simp] theorem standardTrianglePlaneComplex_position :
    standardTrianglePlaneComplex.position = standardTriangleVertex := rfl

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
