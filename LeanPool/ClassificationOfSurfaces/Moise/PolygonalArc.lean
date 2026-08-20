/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.BrokenLine
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalPolyhedron
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Polygonal arcs from broken lines

This is the finite-arrangement layer needed between Moise Chapter 6, Theorems 1 and 2.  The
connectivity theorem produces an arbitrary finite chain of segments.  Subdividing a large
triangle by the supporting lines of those segments, and by two coordinate lines through every
chain vertex, turns all crossings and all chain vertices into vertices of one finite triangle
mesh.  A simple graph path in the resulting one-skeleton is then a loop-free polygonal arc.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Concrete data carried by a broken-line witness. -/
structure BrokenLineData (U : Set Plane) where
  /-- The `n` declaration. -/
  n : ℕ
  /-- The `vertex` declaration. -/
  vertex : Fin (n + 1) → Plane
  segment_subset : ∀ i : Fin n,
    segment ℝ (vertex i.castSucc) (vertex i.succ) ⊆ U

namespace BrokenLineData

variable {U : Set Plane} (B : BrokenLineData U)

/-- The `start` declaration. -/
def start : Plane := B.vertex 0

/-- The `finish` declaration. -/
def finish : Plane := B.vertex (Fin.last B.n)

/-- An auxiliary broken line listing an arbitrary finite family of segments.  The prescribed
segments occur at the even indices; the odd indices are disposable connectors.  This is the
common-arrangement input used when several independently constructed polygonal arcs must be
viewed in one finite plane complex. -/
noncomputable def segmentFamilyChain {I : Type*} [Fintype I]
    (left right : I → Plane) : BrokenLineData (Set.univ : Set Plane) := by
  classical
  let m := Fintype.card I
  let e := Fintype.equivFin I
  let vertex : Fin (2 * m + 1) → Plane := fun k =>
    if hk : k.val < 2 * m then
      let i : Fin m := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then left (e.symm i) else right (e.symm i)
    else 0
  exact {
    n := 2 * m
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

/-- The even index carrying the segment labelled by `i`. -/
noncomputable def segmentFamilyIndex {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    Fin (segmentFamilyChain left right).n :=
  ⟨2 * (Fintype.equivFin I i).val, by
    change 2 * (Fintype.equivFin I i).val < 2 * Fintype.card I
    omega⟩

theorem segmentFamilyChain_vertex_even {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).vertex
        ⟨2 * (Fintype.equivFin I i).val, by
          change 2 * (Fintype.equivFin I i).val < 2 * Fintype.card I + 1
          omega⟩ = left i := by
  classical
  simp only [segmentFamilyChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * (Fintype.equivFin I i).val) % 2 = 0 := by omega
  rw [if_pos hmod]
  have hdiv : 2 * (Fintype.equivFin I i).val / 2 =
      (Fintype.equivFin I i).val := by omega
  have hi : (⟨2 * (Fintype.equivFin I i).val / 2, by omega⟩ :
      Fin (Fintype.card I)) = Fintype.equivFin I i := Fin.ext hdiv
  rw [hi, (Fintype.equivFin I).symm_apply_apply]

theorem segmentFamilyChain_vertex_odd {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).vertex
        ⟨2 * (Fintype.equivFin I i).val + 1, by
          change 2 * (Fintype.equivFin I i).val + 1 < 2 * Fintype.card I + 1
          omega⟩ = right i := by
  classical
  simp only [segmentFamilyChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * (Fintype.equivFin I i).val + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  have hdiv : (2 * (Fintype.equivFin I i).val + 1) / 2 =
      (Fintype.equivFin I i).val := by omega
  have hi : (⟨(2 * (Fintype.equivFin I i).val + 1) / 2, by omega⟩ :
      Fin (Fintype.card I)) = Fintype.equivFin I i := Fin.ext hdiv
  rw [hi, (Fintype.equivFin I).symm_apply_apply]

@[simp] theorem segmentFamilyIndex_castSucc {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyIndex left right i).castSucc =
      ⟨2 * (Fintype.equivFin I i).val, by
        change 2 * (Fintype.equivFin I i).val < 2 * Fintype.card I + 1
        omega⟩ := rfl

@[simp] theorem segmentFamilyIndex_succ {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyIndex left right i).succ =
      ⟨2 * (Fintype.equivFin I i).val + 1, by
        change 2 * (Fintype.equivFin I i).val + 1 < 2 * Fintype.card I + 1
        omega⟩ := rfl

/-- The segment at the distinguished even index is exactly the requested family member. -/
theorem segmentFamilyChain_segment {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    segment ℝ
        ((segmentFamilyChain left right).vertex
          (segmentFamilyIndex left right i).castSucc)
        ((segmentFamilyChain left right).vertex
          (segmentFamilyIndex left right i).succ) =
      segment ℝ (left i) (right i) := by
  rw [segmentFamilyIndex_castSucc, segmentFamilyIndex_succ,
    segmentFamilyChain_vertex_even, segmentFamilyChain_vertex_odd]

theorem exists_data_of_joined {a b : Plane} (h : JoinedByBrokenLine U a b) :
    ∃ B : BrokenLineData U, B.start = a ∧ B.finish = b := by
  obtain ⟨n, v, hv0, hvlast, hvseg⟩ := h
  exact ⟨⟨n, v, hvseg⟩, hv0, hvlast⟩

/-- The affine functional whose zero set contains the line through `a` and `b`. -/
noncomputable def segmentLine (a b : Plane) : Plane →ᵃ[ℝ] ℝ :=
  (b 1 - a 1) • cartesianX - (b 0 - a 0) • cartesianY -
    AffineMap.const ℝ Plane ((b 1 - a 1) * a 0 - (b 0 - a 0) * a 1)

@[simp] theorem segmentLine_apply_left (a b : Plane) : segmentLine a b a = 0 := by
  simp [segmentLine]

@[simp] theorem segmentLine_apply_right (a b : Plane) : segmentLine a b b = 0 := by
  simp [segmentLine]
  ring

theorem segmentLine_eq_zero_of_mem_segment (a b : Plane) {x : Plane}
    (hx : x ∈ segment ℝ a b) : segmentLine a b x = 0 := by
  rw [segment_eq_image] at hx
  obtain ⟨t, -, rfl⟩ := hx
  simp [segmentLine]
  ring

/-- A point on the supporting line of a nondegenerate segment belongs to the segment exactly when
its coordinates lie between the endpoint coordinates.  Both coordinate hypotheses make the
statement symmetric and avoid selecting a preferred nonconstant coordinate in its interface. -/
theorem mem_segment_of_segmentLine_eq_zero {a b x : Plane} (hab : a ≠ b)
    (hline : segmentLine a b x = 0)
    (hx0 : x 0 ∈ Set.uIcc (a 0) (b 0))
    (hx1 : x 1 ∈ Set.uIcc (a 1) (b 1)) : x ∈ segment ℝ a b := by
  have hcoord : a 0 ≠ b 0 ∨ a 1 ≠ b 1 := by
    by_contra h
    push Not at h
    apply hab
    ext i
    fin_cases i
    · exact h.1
    · exact h.2
  rw [segment_eq_image']
  rcases hcoord with h0 | h1
  · let t : ℝ := (x 0 - a 0) / (b 0 - a 0)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_uIcc] at hx0
      rcases hx0 with hx0 | hx0
      · have hab0 : a 0 < b 0 := lt_of_le_of_ne (hx0.1.trans hx0.2) h0
        have hden : 0 < b 0 - a 0 := by linarith
        constructor
        · exact div_nonneg (by linarith) hden.le
        · exact (div_le_one hden).mpr (by linarith)
      · have hden : b 0 - a 0 < 0 := by
          have hba0 : b 0 < a 0 := lt_of_le_of_ne (hx0.1.trans hx0.2) h0.symm
          linarith
        constructor
        · exact div_nonneg_of_nonpos (by linarith) hden.le
        · exact (div_le_one_of_neg hden).mpr (by linarith)
    refine ⟨t, ht, ?_⟩
    ext i
    fin_cases i
    · dsimp [t]
      field_simp [sub_ne_zero.mpr h0.symm]
      ring
    · dsimp [t]
      simp [segmentLine] at hline
      field_simp [sub_ne_zero.mpr h0.symm]
      nlinarith
  · let t : ℝ := (x 1 - a 1) / (b 1 - a 1)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_uIcc] at hx1
      rcases hx1 with hx1 | hx1
      · have hab1 : a 1 < b 1 := lt_of_le_of_ne (hx1.1.trans hx1.2) h1
        have hden : 0 < b 1 - a 1 := by linarith
        constructor
        · exact div_nonneg (by linarith) hden.le
        · exact (div_le_one hden).mpr (by linarith)
      · have hden : b 1 - a 1 < 0 := by
          have hba1 : b 1 < a 1 := lt_of_le_of_ne (hx1.1.trans hx1.2) h1.symm
          linarith
        constructor
        · exact div_nonneg_of_nonpos (by linarith) hden.le
        · exact (div_le_one_of_neg hden).mpr (by linarith)
    refine ⟨t, ht, ?_⟩
    ext i
    fin_cases i
    · dsimp [t]
      simp [segmentLine] at hline
      field_simp [sub_ne_zero.mpr h1.symm]
      nlinarith
    · dsimp [t]
      field_simp [sub_ne_zero.mpr h1.symm]
      ring

/-- The `verticalLine` declaration. -/
noncomputable def verticalLine (p : Plane) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX - AffineMap.const ℝ Plane (p 0)

/-- The `horizontalLine` declaration. -/
noncomputable def horizontalLine (p : Plane) : Plane →ᵃ[ℝ] ℝ :=
  cartesianY - AffineMap.const ℝ Plane (p 1)

@[simp] theorem verticalLine_apply_self (p : Plane) : verticalLine p p = 0 := by
  simp [verticalLine]

@[simp] theorem horizontalLine_apply_self (p : Plane) : horizontalLine p p = 0 := by
  simp [horizontalLine]

/-- Supporting lines of the chain segments. -/
noncomputable def segmentLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (Fin B.n)).toList.map fun i =>
    segmentLine (B.vertex i.castSucc) (B.vertex i.succ)

/-- Coordinate lines force every chain vertex to become an arrangement vertex, including at a
collinear turn or a degenerate segment. -/
noncomputable def vertexLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (Fin (B.n + 1))).toList.flatMap fun i =>
    [verticalLine (B.vertex i), horizontalLine (B.vertex i)]

/-- The `arrangementLines` declaration. -/
noncomputable def arrangementLines : List (Plane →ᵃ[ℝ] ℝ) :=
  B.segmentLines ++ B.vertexLines

/-- A positive radius containing every chain vertex. -/
noncomputable def enclosingRadius : ℝ :=
  1 + ∑ i, ‖B.vertex i‖

theorem enclosingRadius_pos : 0 < B.enclosingRadius := by
  unfold enclosingRadius
  have hsum : 0 ≤ ∑ i, ‖B.vertex i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

theorem vertex_mem_enclosingBall (i : Fin (B.n + 1)) :
    B.vertex i ∈ Metric.closedBall (0 : Plane) B.enclosingRadius := by
  rw [Metric.mem_closedBall, dist_zero_right]
  unfold enclosingRadius
  have hi : ‖B.vertex i‖ ≤ ∑ j, ‖B.vertex j‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  linarith

theorem segment_subset_enclosingBall (i : Fin B.n) :
    segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) ⊆
      Metric.closedBall (0 : Plane) B.enclosingRadius :=
  (convex_closedBall (0 : Plane) B.enclosingRadius).segment_subset
    (B.vertex_mem_enclosingBall i.castSucc) (B.vertex_mem_enclosingBall i.succ)

/-- The `enclosingMesh` declaration. -/
noncomputable def enclosingMesh : TriangleMesh :=
  TriangleMesh.single (PolygonalCircle.enclosingTriangleVertices B.enclosingRadius)
    (PolygonalCircle.enclosingTriangleVertices_affineIndependent B.enclosingRadius_pos)

/-- The finite line arrangement resolving every segment crossing and chain vertex. -/
noncomputable def arrangementMesh : TriangleMesh :=
  B.enclosingMesh.refineByLines B.arrangementLines

theorem arrangementMesh_support :
    B.arrangementMesh.toPlaneComplex.support =
      convexHull ℝ (Set.range
        (PolygonalCircle.enclosingTriangleVertices B.enclosingRadius)) := by
  rw [arrangementMesh, TriangleMesh.refineByLines_support, enclosingMesh,
    TriangleMesh.single_support]

theorem segment_subset_arrangementMesh_support (i : Fin B.n) :
    segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) ⊆
      B.arrangementMesh.toPlaneComplex.support := by
  rw [B.arrangementMesh_support]
  exact (B.segment_subset_enclosingBall i).trans
    (PolygonalCircle.closedBall_subset_enclosingTriangle B.enclosingRadius_pos)

theorem segmentLine_mem_arrangementLines (i : Fin B.n) :
    segmentLine (B.vertex i.castSucc) (B.vertex i.succ) ∈ B.arrangementLines := by
  simp [arrangementLines, segmentLines]

theorem verticalLine_mem_arrangementLines (i : Fin (B.n + 1)) :
    verticalLine (B.vertex i) ∈ B.arrangementLines := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  exact ⟨i, by simp, by simp⟩

theorem horizontalLine_mem_arrangementLines (i : Fin (B.n + 1)) :
    horizontalLine (B.vertex i) ∈ B.arrangementLines := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  exact ⟨i, by simp, by simp⟩

theorem arrangementMesh_monochromatic_segmentLine (i : Fin B.n) :
    B.arrangementMesh.IsMonochromatic
      (segmentLine (B.vertex i.castSucc) (B.vertex i.succ)) := by
  exact B.enclosingMesh.refineByLines_isMonochromatic_of_mem B.arrangementLines
    (B.segmentLine_mem_arrangementLines i)

theorem arrangementMesh_monochromatic_verticalLine (i : Fin (B.n + 1)) :
    B.arrangementMesh.IsMonochromatic (verticalLine (B.vertex i)) := by
  exact B.enclosingMesh.refineByLines_isMonochromatic_of_mem B.arrangementLines
    (B.verticalLine_mem_arrangementLines i)

theorem arrangementMesh_monochromatic_horizontalLine (i : Fin (B.n + 1)) :
    B.arrangementMesh.IsMonochromatic (horizontalLine (B.vertex i)) := by
  exact B.enclosingMesh.refineByLines_isMonochromatic_of_mem B.arrangementLines
    (B.horizontalLine_mem_arrangementLines i)

end BrokenLineData

namespace TriangleMesh

variable (M : TriangleMesh)

/-- In a triangulation monochromatic for an affine functional, every point of its zero set lies
in a face all of whose vertices are zero. -/
theorem exists_zero_face_of_mem_support {f : Plane →ᵃ[ℝ] ℝ}
    (hmono : M.IsMonochromatic f) {x : Plane} (hx : x ∈ M.toPlaneComplex.support)
    (hfx : f x = 0) :
    ∃ s ∈ M.toPlaneComplex.simplexes,
      x ∈ M.toPlaneComplex.cellCarrier s ∧ ∀ v ∈ s, f (M.position v) = 0 := by
  rw [M.toPlaneComplex_support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨w, hwsupp, hw0, hw1, hweval⟩ :=
    M.toPlaneComplex.exists_weights_of_mem_cellCarrier hxt
  change M.Vertex → ℝ at w
  change ∀ v : M.Vertex, 0 ≤ w v at hw0
  change (∑ v : M.Vertex, w v) = 1 at hw1
  change (∑ v : M.Vertex, w v • M.position v) = x at hweval
  have hsum : ∑ v ∈ t, w v = 1 := by
    exact (Finset.sum_subset (Finset.subset_univ t)
      (fun v _ hv => hwsupp v hv)).trans hw1
  have hfeval : ∑ v ∈ t, w v * f (M.position v) = 0 := by
    have hcomb : t.affineCombination ℝ M.position w = x := by
      rw [t.affineCombination_eq_linear_combination M.position w hsum]
      exact (Finset.sum_subset (Finset.subset_univ t)
        (fun v _ hv => by rw [hwsupp v hv, zero_smul])).trans hweval
    have hmap := t.map_affineCombination M.position w hsum f
    rw [hcomb, hfx] at hmap
    simpa [Finset.affineCombination_eq_linear_combination, hsum] using hmap.symm
  let s : Finset M.Vertex := t.filter fun v => f (M.position v) = 0
  have hzero : ∀ v ∈ t, v ∉ s → w v = 0 := by
    intro v hvt hvs
    have hfv : f (M.position v) ≠ 0 := by simpa [s, hvt] using hvs
    rcases hmono t ht with hpos | hneg
    · have hterm : w v * f (M.position v) = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (s := t) (f := fun u =>
          w u * f (M.position u)) (fun u hu => mul_nonneg (hw0 u) (hpos u hu))).mp hfeval v hvt
      exact (mul_eq_zero.mp hterm).resolve_right hfv
    · have hterm : w v * (-f (M.position v)) = 0 := by
        have hsumNeg : ∑ u ∈ t, w u * (-f (M.position u)) = 0 := by
          calc
            ∑ u ∈ t, w u * (-f (M.position u)) =
                -(∑ u ∈ t, w u * f (M.position u)) := by
              simp only [mul_neg, Finset.sum_neg_distrib]
            _ = 0 := by rw [hfeval]; simp
        apply (Finset.sum_eq_zero_iff_of_nonneg (s := t) (f := fun u =>
          w u * (-f (M.position u))) (fun u hu =>
            mul_nonneg (hw0 u) (neg_nonneg.mpr (hneg u hu)))).mp hsumNeg v hvt
      exact (mul_eq_zero.mp hterm).resolve_right (neg_ne_zero.mpr hfv)
  have hsne : s.Nonempty := by
    by_contra hs
    have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hwAll : ∀ v, w v = 0 := by
      intro v
      by_cases hvt : v ∈ t
      · exact hzero v hvt (by simp [hsEmpty])
      · exact hwsupp v hvt
    have : (∑ v, w v) = 0 := by simp [hwAll]
    exact one_ne_zero (hw1.symm.trans this)
  have hst : s ⊆ t := Finset.filter_subset _ _
  have hsface : s ∈ M.toPlaneComplex.simplexes :=
    M.toPlaneComplex.down_closed t
      (M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t ht]; omega),
        t, ht, subset_rfl⟩) s hst hsne
  refine ⟨s, hsface, ?_, ?_⟩
  · rw [← hweval]
    apply M.toPlaneComplex.baryEval_mem_cellCarrier
    · intro v hvs
      by_cases hvt : v ∈ t
      · exact hzero v hvt hvs
      · exact hwsupp v hvt
    · exact hw0
    · exact hw1
  · intro v hv
    exact (Finset.mem_filter.mp hv).2

/-- Two monochromatic coordinate lines through a supported point force that point to occur as an
actual mesh vertex. -/
theorem exists_vertex_position_eq_of_monochromatic_coordinates (p : Plane)
    (hp : p ∈ M.toPlaneComplex.support)
    (hx : M.IsMonochromatic (BrokenLineData.verticalLine p))
    (hy : M.IsMonochromatic (BrokenLineData.horizontalLine p)) :
    ∃ v : M.Vertex, M.toPlaneComplex.position v = p ∧
      ({v} : Finset M.Vertex) ∈ M.toPlaneComplex.simplexes := by
  obtain ⟨s, hs, hps, hs0⟩ := M.exists_zero_face_of_mem_support hx hp
    (BrokenLineData.verticalLine_apply_self p)
  obtain ⟨t, ht, hpt, ht0⟩ := M.exists_zero_face_of_mem_support hy hp
    (BrokenLineData.horizontalLine_apply_self p)
  have hpInter : p ∈ M.toPlaneComplex.cellCarrier (s ∩ t) := by
    have hface := M.toPlaneComplex.face_inter s hs t ht
    have hmem : p ∈ M.toPlaneComplex.cellCarrier s ∩
        M.toPlaneComplex.cellCarrier t := ⟨hps, hpt⟩
    change p ∈ convexHull ℝ
        (M.toPlaneComplex.position '' (s : Set M.toPlaneComplex.Vertex)) ∩
      convexHull ℝ (M.toPlaneComplex.position '' (t : Set M.toPlaneComplex.Vertex)) at hmem
    rw [hface] at hmem
    exact hmem
  have hne : (s ∩ t).Nonempty := by
    by_contra h
    have hempty : s ∩ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty, PlaneComplex.cellCarrier] at hpInter
    simp at hpInter
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, plane_ext ?_ ?_, ?_⟩
  · have hv0 := hs0 v (Finset.mem_of_mem_inter_left hv)
    change M.toPlaneComplex.position v 0 - p 0 = 0 at hv0
    exact sub_eq_zero.mp hv0
  · have hv1 := ht0 v (Finset.mem_of_mem_inter_right hv)
    change M.toPlaneComplex.position v 1 - p 1 = 0 at hv1
    exact sub_eq_zero.mp hv1
  · exact M.toPlaneComplex.down_closed s hs {v}
      (by
        intro w hw
        simp only [Finset.mem_singleton] at hw
        subst w
        exact Finset.mem_of_mem_inter_left hv)
      (Finset.singleton_nonempty _)

theorem nonneg_on_face_of_monochromatic_of_pos {f : Plane →ᵃ[ℝ] ℝ}
    (hmono : M.IsMonochromatic f) {s : Finset M.Vertex}
    (hs : s ∈ M.toPlaneComplex.simplexes) {x : Plane}
    (hxs : x ∈ M.toPlaneComplex.cellCarrier s) (hfx : 0 < f x) :
    ∀ v ∈ s, 0 ≤ f (M.position v) := by
  obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
  rcases hmono t ht with hnonneg | hnonpos
  · exact fun v hv => hnonneg v (hst hv)
  · exfalso
    have hxnonpos : f x ≤ 0 := by
      apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage f) hxs
      rintro y ⟨v, hv, rfl⟩
      exact hnonpos v (hst hv)
    linarith

theorem nonpos_on_face_of_monochromatic_of_neg {f : Plane →ᵃ[ℝ] ℝ}
    (hmono : M.IsMonochromatic f) {s : Finset M.Vertex}
    (hs : s ∈ M.toPlaneComplex.simplexes) {x : Plane}
    (hxs : x ∈ M.toPlaneComplex.cellCarrier s) (hfx : f x < 0) :
    ∀ v ∈ s, f (M.position v) ≤ 0 := by
  obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
  rcases hmono t ht with hnonneg | hnonpos
  · exfalso
    have hxnonneg : 0 ≤ f x := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage f) hxs
      rintro y ⟨v, hv, rfl⟩
      exact hnonneg v (hst hv)
    linarith
  · exact fun v hv => hnonpos v (hst hv)

end TriangleMesh

namespace PlaneComplex

variable (K : PlaneComplex)

/-- An affine-independent face whose vertices lie on one segment has at most two vertices. -/
theorem card_le_two_of_vertices_mem_segment {s : Finset K.Vertex}
    (hs : s ∈ K.simplexes) {a b : Plane}
    (hseg : ∀ v ∈ s, K.position v ∈ segment ℝ a b) : s.card ≤ 2 := by
  classical
  let A : Finset Plane := s.image K.position
  have hAI : AffineIndependent ℝ ((↑) : A → Plane) := by
    apply affineIndependent_finset_coe (K.affineIndependent s hs)
    intro x hx
    obtain ⟨v, hvs, hvx⟩ := Finset.mem_image.mp hx
    exact ⟨⟨v, hvs⟩, hvx⟩
  have hspan : (A : Set Plane) ⊆
      affineSpan ℝ (({a, b} : Finset Plane) : Set Plane) := by
    intro x hx
    obtain ⟨v, hvs, hvx⟩ := Finset.mem_image.mp hx
    rw [← hvx]
    apply convexHull_subset_affineSpan
      (({a, b} : Finset Plane) : Set Plane)
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using
      hseg v hvs
  have hcard := hAI.card_le_card_of_subset_affineSpan (t := {a, b}) hspan
  calc
    s.card = A.card := by
      symm
      exact Finset.card_image_iff.mpr K.position_injective.injOn
    _ ≤ ({a, b} : Finset Plane).card := hcard
    _ ≤ 2 := Finset.card_le_two

/-- A point in a nonempty face of cardinality at most two lies on a segment joining two of that
face's vertices (the two vertices may coincide for a zero-face). -/
theorem exists_vertex_pair_segment_of_mem_cellCarrier {s : Finset K.Vertex}
    (hs : s ∈ K.simplexes) (hcard : s.card ≤ 2) {x : Plane}
    (hx : x ∈ K.cellCarrier s) :
    ∃ v w : K.Vertex, v ∈ s ∧ w ∈ s ∧
      x ∈ segment ℝ (K.position v) (K.position w) := by
  have hpos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
  have hcases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with hone | htwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
    refine ⟨v, v, by simp, by simp, ?_⟩
    simpa [PlaneComplex.cellCarrier, segment_same] using hx
  · obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp htwo
    refine ⟨v, w, by simp, by simp, ?_⟩
    rw [PlaneComplex.cellCarrier] at hx
    have himage : K.position ''
        (({v, w} : Finset K.Vertex) : Set K.Vertex) =
        {K.position v, K.position w} := by
      ext y
      simp [eq_comm]
    rwa [himage, convexHull_pair] at hx

/-- The graph formed by the one-dimensional faces of a plane complex. -/
def vertexGraph : SimpleGraph K.Vertex where
  Adj v w := v ≠ w ∧ ({v, w} : Finset K.Vertex) ∈ K.simplexes
  symm := ⟨by
    rintro v w ⟨hvw, hedge⟩
    exact ⟨hvw.symm, by simpa [Finset.pair_comm] using hedge⟩⟩
  loopless := ⟨by
    rintro v ⟨hvv, -⟩
    exact hvv rfl⟩

theorem vertexGraph_adj_iff {v w : K.Vertex} :
    K.vertexGraph.Adj v w ↔
      v ≠ w ∧ ({v, w} : Finset K.Vertex) ∈ K.simplexes := Iff.rfl

/-- Every vertex visited by a one-skeleton walk is geometrically supported, provided the final
vertex is an actual zero-face.  All earlier vertices occur in an edge of the walk. -/
theorem position_mem_support_of_mem_walk {u v w : K.Vertex}
    (p : K.vertexGraph.Walk u v)
    (hv : ({v} : Finset K.Vertex) ∈ K.simplexes)
    (hw : w ∈ p.support) : K.position w ∈ K.support := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mp hw with hwv | ⟨e, he, hwe⟩
  · rw [hwv]
    exact K.cellCarrier_subset_support hv
      (subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩)
  · induction e using Sym2.inductionOn with
    | hf a b =>
        rcases Sym2.mem_iff.mp hwe with hwa | hwb
        · rw [hwa]
          have hab := p.adj_of_mem_edges he
          exact K.cellCarrier_subset_support hab.2
            (subset_convexHull ℝ _ ⟨a, by simp, rfl⟩)
        · rw [hwb]
          have hab := p.adj_of_mem_edges he
          exact K.cellCarrier_subset_support hab.2
            (subset_convexHull ℝ _ ⟨b, by simp, rfl⟩)

/-- The induced subcomplex on the vertices satisfying `p`.  Vertices outside `p` remain in the
ambient finite type but occur in no face; `PlaneComplex.active` can remove them when desired. -/
noncomputable def inducedBy (p : K.Vertex → Prop) : PlaneComplex := by
  classical
  exact {
    Vertex := K.Vertex
    position := K.position
    position_injective := K.position_injective
    simplexes := K.simplexes.filter fun s => ∀ v ∈ s, p v
    nonempty_of_mem := by
      intro s hs
      exact K.nonempty_of_mem s (Finset.mem_filter.mp hs).1
    card_le_three := by
      intro s hs
      exact K.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs t hts ht
      obtain ⟨hsK, hsp⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      exact ⟨K.down_closed s hsK t hts ht, fun v hv => hsp v (hts hv)⟩
    affineIndependent := by
      intro s hs
      exact K.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := by
      intro s hs t ht
      exact K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

@[simp] theorem inducedBy_position (p : K.Vertex → Prop) :
    (K.inducedBy p).position = K.position := rfl

@[simp] theorem inducedBy_cellCarrier (p : K.Vertex → Prop) (s : Finset K.Vertex) :
    (K.inducedBy p).cellCarrier s = K.cellCarrier s := rfl

theorem mem_inducedBy_simplexes_iff (p : K.Vertex → Prop) {s : Finset K.Vertex} :
    s ∈ (K.inducedBy p).simplexes ↔ s ∈ K.simplexes ∧ ∀ v ∈ s, p v := by
  classical
  change s ∈ K.simplexes.filter (fun t => ∀ v ∈ t, p v) ↔ _
  exact Finset.mem_filter

theorem inducedBy_support_subset {C : Set Plane} (hC : Convex ℝ C)
    (p : K.Vertex → Prop) (hp : ∀ v, p v → K.position v ∈ C) :
    (K.inducedBy p).support ⊆ C := by
  intro x hx
  rw [PlaneComplex.support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  apply convexHull_min _ hC hxs
  rintro y ⟨v, hv, rfl⟩
  exact hp v (((K.mem_inducedBy_simplexes_iff p).mp hs).2 v hv)

theorem inducedBy_support_eq {C : Set Plane} (hC : Convex ℝ C)
    (p : K.Vertex → Prop) (hp : ∀ v, p v → K.position v ∈ C)
    (hcover : ∀ x ∈ C, ∃ s ∈ K.simplexes,
      x ∈ K.cellCarrier s ∧ ∀ v ∈ s, p v) :
    (K.inducedBy p).support = C := by
  apply Set.Subset.antisymm (K.inducedBy_support_subset hC p hp)
  intro x hx
  obtain ⟨s, hs, hxs, hsp⟩ := hcover x hx
  rw [PlaneComplex.support]
  exact Set.mem_iUnion₂.mpr
    ⟨s, (K.mem_inducedBy_simplexes_iff p).mpr ⟨hs, hsp⟩, hxs⟩

/-- The subcomplex consisting of exactly those faces whose whole geometric carrier lies in `C`.
Unlike `inducedBy`, this is appropriate when `C` is a nonconvex polygonal set. -/
noncomputable abbrev restrictedTo (C : Set Plane) : PlaneComplex := by
  classical
  exact {
    Vertex := K.Vertex
    position := K.position
    position_injective := K.position_injective
    simplexes := K.simplexes.filter fun s => K.cellCarrier s ⊆ C
    nonempty_of_mem := by
      intro s hs
      exact K.nonempty_of_mem s (Finset.mem_filter.mp hs).1
    card_le_three := by
      intro s hs
      exact K.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs t hts ht
      obtain ⟨hsK, hsC⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      refine ⟨K.down_closed s hsK t hts ht, ?_⟩
      exact (convexHull_mono (Set.image_mono hts)).trans hsC
    affineIndependent := by
      intro s hs
      exact K.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := by
      intro s hs t ht
      exact K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

@[simp] theorem restrictedTo_position (C : Set Plane) :
    (K.restrictedTo C).position = K.position := rfl

@[simp] theorem restrictedTo_cellCarrier (C : Set Plane) (s : Finset K.Vertex) :
    (K.restrictedTo C).cellCarrier s = K.cellCarrier s := rfl

theorem mem_restrictedTo_simplexes_iff (C : Set Plane) {s : Finset K.Vertex} :
    s ∈ (K.restrictedTo C).simplexes ↔ s ∈ K.simplexes ∧ K.cellCarrier s ⊆ C := by
  classical
  change s ∈ K.simplexes.filter (fun t => K.cellCarrier t ⊆ C) ↔ _
  exact Finset.mem_filter

theorem restrictedTo_support_subset (C : Set Plane) :
    (K.restrictedTo C).support ⊆ C := by
  intro x hx
  rw [PlaneComplex.support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  exact ((K.mem_restrictedTo_simplexes_iff C).mp hs).2 hxs

theorem restrictedTo_support_eq (C : Set Plane)
    (hcover : ∀ x ∈ C, ∃ s ∈ K.simplexes,
      x ∈ K.cellCarrier s ∧ K.cellCarrier s ⊆ C) :
    (K.restrictedTo C).support = C := by
  apply Set.Subset.antisymm (K.restrictedTo_support_subset C)
  intro x hx
  obtain ⟨s, hs, hxs, hsC⟩ := hcover x hx
  rw [PlaneComplex.support]
  exact Set.mem_iUnion₂.mpr
    ⟨s, (K.mem_restrictedTo_simplexes_iff C).mpr ⟨hs, hsC⟩, hxs⟩

/-- All vertices of one simplex lie in one reachability class of the vertex graph. -/
theorem vertexGraph_reachable_of_mem_simplex {s : Finset K.Vertex} (hs : s ∈ K.simplexes)
    {v w : K.Vertex} (hv : v ∈ s) (hw : w ∈ s) : K.vertexGraph.Reachable v w := by
  by_cases hvw : v = w
  · simp [hvw]
  · apply SimpleGraph.Adj.reachable
    rw [K.vertexGraph_adj_iff]
    refine ⟨hvw, K.down_closed s hs {v, w} ?_ (by simp)⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact hw

/-- If the support of a finite plane complex is connected, then any two vertices which actually
occur as zero-faces are joined by a path in its one-skeleton. -/
theorem vertexGraph_reachable_of_isPreconnected
    (hconn : IsPreconnected K.support) {u v : K.Vertex}
    (hu : ({u} : Finset K.Vertex) ∈ K.simplexes)
    (hv : ({v} : Finset K.Vertex) ∈ K.simplexes) :
    K.vertexGraph.Reachable u v := by
  classical
  by_contra huv
  let R : K.Vertex → Prop := fun w => K.vertexGraph.Reachable u w
  let leftFaces := K.simplexes.filter fun s => ∃ w ∈ s, R w
  let rightFaces := K.simplexes.filter fun s => ∃ w ∈ s, ¬R w
  let A : Set Plane := ⋃ s ∈ leftFaces, K.cellCarrier s
  let B : Set Plane := ⋃ s ∈ rightFaces, K.cellCarrier s
  have hface_uniform (s : Finset K.Vertex) (hs : s ∈ K.simplexes) :
      (∀ w ∈ s, R w) ∨ (∀ w ∈ s, ¬R w) := by
    obtain ⟨w, hw⟩ := K.nonempty_of_mem s hs
    by_cases hRw : R w
    · left
      intro z hz
      exact hRw.trans (K.vertexGraph_reachable_of_mem_simplex hs hw hz)
    · right
      intro z hz hRz
      exact hRw (hRz.trans (K.vertexGraph_reachable_of_mem_simplex hs hz hw))
  have hclosedA : IsClosed A := by
    apply isClosed_biUnion_finset
    intro s hs
    exact K.isCompact_cellCarrier s |>.isClosed
  have hclosedB : IsClosed B := by
    apply isClosed_biUnion_finset
    intro s hs
    exact K.isCompact_cellCarrier s |>.isClosed
  have hcover : K.support ⊆ A ∪ B := by
    intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    rcases hface_uniform s hs with hleft | hright
    · left
      obtain ⟨w, hw⟩ := K.nonempty_of_mem s hs
      exact Set.mem_iUnion₂.mpr
        ⟨s, Finset.mem_filter.mpr ⟨hs, w, hw, hleft w hw⟩, hxs⟩
    · right
      obtain ⟨w, hw⟩ := K.nonempty_of_mem s hs
      exact Set.mem_iUnion₂.mpr
        ⟨s, Finset.mem_filter.mpr ⟨hs, w, hw, hright w hw⟩, hxs⟩
  have hdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    obtain ⟨s, hsleft, hxs⟩ := Set.mem_iUnion₂.mp hxA
    obtain ⟨t, htright, hxt⟩ := Set.mem_iUnion₂.mp hxB
    obtain ⟨hs, w, hws, hRw⟩ := Finset.mem_filter.mp hsleft
    obtain ⟨ht, z, hzt, hRz⟩ := Finset.mem_filter.mp htright
    have hxinter : x ∈ K.cellCarrier (s ∩ t) := by
      have hinter : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
        simpa only [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
      rw [← hinter]
      exact ⟨hxs, hxt⟩
    have hst : (s ∩ t).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, PlaneComplex.cellCarrier] at hxinter
      simp at hxinter
    obtain ⟨q, hq⟩ := hst
    have hRq : R q := hRw.trans
      (K.vertexGraph_reachable_of_mem_simplex hs hws (Finset.mem_of_mem_inter_left hq))
    have hnRq : ¬R q := fun h => hRz
      (h.trans (K.vertexGraph_reachable_of_mem_simplex ht
        (Finset.mem_of_mem_inter_right hq) hzt))
    exact hnRq hRq
  have hleftNonempty : (K.support ∩ A).Nonempty := by
    refine ⟨K.position u, ?_, ?_⟩
    · exact K.cellCarrier_subset_support hu
        (subset_convexHull ℝ _ ⟨u, by simp, rfl⟩)
    · exact Set.mem_iUnion₂.mpr ⟨{u}, Finset.mem_filter.mpr
        ⟨hu, u, by simp, SimpleGraph.Reachable.refl u⟩,
          subset_convexHull ℝ _ ⟨u, by simp, rfl⟩⟩
  have hrightNonempty : (K.support ∩ B).Nonempty := by
    refine ⟨K.position v, ?_, ?_⟩
    · exact K.cellCarrier_subset_support hv
        (subset_convexHull ℝ _ ⟨v, by simp, rfl⟩)
    · exact Set.mem_iUnion₂.mpr ⟨{v}, Finset.mem_filter.mpr
        ⟨hv, v, by simp, huv⟩,
          subset_convexHull ℝ _ ⟨v, by simp, rfl⟩⟩
  have hinter := (isPreconnected_closed_iff.mp hconn) A B hclosedA hclosedB hcover
    hleftNonempty hrightNonempty
  obtain ⟨x, -, hxA, hxB⟩ := hinter
  exact Set.disjoint_left.mp hdisjoint hxA hxB

end PlaneComplex

namespace BrokenLineData

variable {U : Set Plane} (B : BrokenLineData U)

/-- Every original chain vertex is a vertex of the line-arrangement mesh. -/
theorem exists_arrangementVertex_position_eq (i : Fin (B.n + 1)) :
    ∃ v : B.arrangementMesh.Vertex,
      B.arrangementMesh.toPlaneComplex.position v = B.vertex i ∧
        ({v} : Finset B.arrangementMesh.Vertex) ∈
          B.arrangementMesh.toPlaneComplex.simplexes := by
  let M := B.arrangementMesh
  have hxSupport : B.vertex i ∈ M.toPlaneComplex.support := by
    rw [B.arrangementMesh_support]
    exact PolygonalCircle.closedBall_subset_enclosingTriangle B.enclosingRadius_pos
      (B.vertex_mem_enclosingBall i)
  exact M.exists_vertex_position_eq_of_monochromatic_coordinates (B.vertex i) hxSupport
    (B.arrangementMesh_monochromatic_verticalLine i)
    (B.arrangementMesh_monochromatic_horizontalLine i)

/-- Every point of an original nondegenerate chain segment lies in an arrangement face whose
vertices all lie on that segment. -/
theorem exists_face_on_segment (i : Fin B.n) {x : Plane}
    (hx : x ∈ segment ℝ (B.vertex i.castSucc) (B.vertex i.succ)) :
    ∃ s ∈ B.arrangementMesh.toPlaneComplex.simplexes,
      x ∈ B.arrangementMesh.toPlaneComplex.cellCarrier s ∧
        ∀ v ∈ s, B.arrangementMesh.toPlaneComplex.position v ∈
          segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) := by
  let a := B.vertex i.castSucc
  let b := B.vertex i.succ
  let M := B.arrangementMesh
  change x ∈ segment ℝ a b at hx
  by_cases hab : a = b
  · have hxa : x = a := by
      rw [hab, segment_same, Set.mem_singleton_iff] at hx
      exact hx.trans hab.symm
    obtain ⟨v, hvpos, hvface⟩ := B.exists_arrangementVertex_position_eq i.castSucc
    refine ⟨{v}, hvface, ?_, ?_⟩
    · rw [hxa]
      exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, hvpos⟩
    · intro w hw
      have hwv : w = v := Finset.mem_singleton.mp hw
      subst w
      change M.toPlaneComplex.position v ∈ segment ℝ a b
      rw [hvpos]
      exact left_mem_segment ℝ a b
  · by_cases hxa : x = a
    · obtain ⟨v, hvpos, hvface⟩ := B.exists_arrangementVertex_position_eq i.castSucc
      refine ⟨{v}, hvface, ?_, ?_⟩
      · rw [hxa]
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, hvpos⟩
      · intro w hw
        have hwv : w = v := Finset.mem_singleton.mp hw
        subst w
        change M.toPlaneComplex.position v ∈ segment ℝ a b
        rw [hvpos]
        exact left_mem_segment ℝ a b
    · by_cases hxb : x = b
      · obtain ⟨v, hvpos, hvface⟩ := B.exists_arrangementVertex_position_eq i.succ
        refine ⟨{v}, hvface, ?_, ?_⟩
        · rw [hxb]
          exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self v, hvpos⟩
        · intro w hw
          have hwv : w = v := Finset.mem_singleton.mp hw
          subst w
          change M.toPlaneComplex.position v ∈ segment ℝ a b
          rw [hvpos]
          exact right_mem_segment ℝ a b
      · have hxSupport : x ∈ M.toPlaneComplex.support :=
          B.segment_subset_arrangementMesh_support i hx
        obtain ⟨s, hs, hxs, hsline⟩ := M.exists_zero_face_of_mem_support
          (B.arrangementMesh_monochromatic_segmentLine i) hxSupport
          (segmentLine_eq_zero_of_mem_segment a b hx)
        have ht : ∃ t ∈ Set.Ioo (0 : ℝ) 1, AffineMap.lineMap a b t = x := by
          rw [segment_eq_image_lineMap] at hx
          obtain ⟨t, ht, htx⟩ := hx
          refine ⟨t, ⟨?_, ?_⟩, htx⟩
          · apply lt_of_le_of_ne ht.1
            intro hzero
            apply hxa
            rw [← htx, ← hzero]
            simp
          · apply lt_of_le_of_ne ht.2
            intro hone
            apply hxb
            rw [← htx, hone]
            simp
        obtain ⟨t, ht, htx⟩ := ht
        have hxcoord0 : x 0 = (1 - t) * a 0 + t * b 0 := by
          rw [← htx]
          simp [AffineMap.lineMap_apply_module]
        have hxcoord1 : x 1 = (1 - t) * a 1 + t * b 1 := by
          rw [← htx]
          simp [AffineMap.lineMap_apply_module]
        refine ⟨s, hs, hxs, ?_⟩
        intro v hv
        have hvline := hsline v hv
        change segmentLine a b (M.toPlaneComplex.position v) = 0 at hvline
        apply mem_segment_of_segmentLine_eq_zero hab hvline
        · by_cases h0 : a 0 = b 0
          · rw [h0, Set.uIcc_self]
            have h1 : a 1 ≠ b 1 := by
              intro h1
              apply hab
              ext k
              fin_cases k
              · exact h0
              · exact h1
            have hprod : (b 1 - a 1) * (M.toPlaneComplex.position v 0 - a 0) = 0 := by
              simp only [segmentLine, Fin.isValue, AffineMap.coe_sub, AffineMap.coe_smul,
                AffineMap.coe_const, Pi.sub_apply, Pi.smul_apply, cartesianX_apply, smul_eq_mul,
                cartesianY_apply, Function.const_apply] at hvline
              rw [h0] at hvline
              ring_nf at hvline ⊢
              rw [h0]
              exact hvline
            calc
              M.toPlaneComplex.position v 0 = a 0 := sub_eq_zero.mp
                ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr h1.symm))
              _ = b 0 := h0
          · rcases lt_or_gt_of_ne h0 with hlt | hgt
            · rw [Set.uIcc_of_le hlt.le, Set.mem_Icc]
              have hxlo : 0 < verticalLine a x := by
                change 0 < x 0 - a 0
                rw [hxcoord0]
                nlinarith [ht.1, ht.2]
              have hxhi : verticalLine b x < 0 := by
                change x 0 - b 0 < 0
                rw [hxcoord0]
                nlinarith [ht.1, ht.2]
              have hlo := M.nonneg_on_face_of_monochromatic_of_pos
                (B.arrangementMesh_monochromatic_verticalLine i.castSucc) hs hxs hxlo v hv
              have hhi := M.nonpos_on_face_of_monochromatic_of_neg
                (B.arrangementMesh_monochromatic_verticalLine i.succ) hs hxs hxhi v hv
              change 0 ≤ M.toPlaneComplex.position v 0 - a 0 at hlo
              change M.toPlaneComplex.position v 0 - b 0 ≤ 0 at hhi
              constructor <;> linarith
            · rw [Set.uIcc_of_ge hgt.le, Set.mem_Icc]
              have hxhi : verticalLine a x < 0 := by
                change x 0 - a 0 < 0
                rw [hxcoord0]
                nlinarith [ht.1, ht.2]
              have hxlo : 0 < verticalLine b x := by
                change 0 < x 0 - b 0
                rw [hxcoord0]
                nlinarith [ht.1, ht.2]
              have hhi := M.nonpos_on_face_of_monochromatic_of_neg
                (B.arrangementMesh_monochromatic_verticalLine i.castSucc) hs hxs hxhi v hv
              have hlo := M.nonneg_on_face_of_monochromatic_of_pos
                (B.arrangementMesh_monochromatic_verticalLine i.succ) hs hxs hxlo v hv
              change M.toPlaneComplex.position v 0 - a 0 ≤ 0 at hhi
              change 0 ≤ M.toPlaneComplex.position v 0 - b 0 at hlo
              constructor <;> linarith
        · by_cases h1 : a 1 = b 1
          · rw [h1, Set.uIcc_self]
            have h0 : a 0 ≠ b 0 := by
              intro h0
              apply hab
              ext k
              fin_cases k
              · exact h0
              · exact h1
            have hprod : (b 0 - a 0) * (M.toPlaneComplex.position v 1 - a 1) = 0 := by
              simp only [segmentLine, Fin.isValue, AffineMap.coe_sub, AffineMap.coe_smul,
                AffineMap.coe_const, Pi.sub_apply, Pi.smul_apply, cartesianX_apply, smul_eq_mul,
                cartesianY_apply, Function.const_apply] at hvline
              rw [h1] at hvline
              ring_nf at hvline ⊢
              rw [h1]
              linarith
            calc
              M.toPlaneComplex.position v 1 = a 1 := sub_eq_zero.mp
                ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr h0.symm))
              _ = b 1 := h1
          · rcases lt_or_gt_of_ne h1 with hlt | hgt
            · rw [Set.uIcc_of_le hlt.le, Set.mem_Icc]
              have hxlo : 0 < horizontalLine a x := by
                change 0 < x 1 - a 1
                rw [hxcoord1]
                nlinarith [ht.1, ht.2]
              have hxhi : horizontalLine b x < 0 := by
                change x 1 - b 1 < 0
                rw [hxcoord1]
                nlinarith [ht.1, ht.2]
              have hlo := M.nonneg_on_face_of_monochromatic_of_pos
                (B.arrangementMesh_monochromatic_horizontalLine i.castSucc) hs hxs hxlo v hv
              have hhi := M.nonpos_on_face_of_monochromatic_of_neg
                (B.arrangementMesh_monochromatic_horizontalLine i.succ) hs hxs hxhi v hv
              change 0 ≤ M.toPlaneComplex.position v 1 - a 1 at hlo
              change M.toPlaneComplex.position v 1 - b 1 ≤ 0 at hhi
              constructor <;> linarith
            · rw [Set.uIcc_of_ge hgt.le, Set.mem_Icc]
              have hxhi : horizontalLine a x < 0 := by
                change x 1 - a 1 < 0
                rw [hxcoord1]
                nlinarith [ht.1, ht.2]
              have hxlo : 0 < horizontalLine b x := by
                change 0 < x 1 - b 1
                rw [hxcoord1]
                nlinarith [ht.1, ht.2]
              have hhi := M.nonpos_on_face_of_monochromatic_of_neg
                (B.arrangementMesh_monochromatic_horizontalLine i.castSucc) hs hxs hxhi v hv
              have hlo := M.nonneg_on_face_of_monochromatic_of_pos
                (B.arrangementMesh_monochromatic_horizontalLine i.succ) hs hxs hxlo v hv
              change M.toPlaneComplex.position v 1 - a 1 ≤ 0 at hhi
              change 0 ≤ M.toPlaneComplex.position v 1 - b 1 at hlo
              constructor <;> linarith

/-- The common arrangement of a finite segment family resolves each requested member into faces
contained in that member.  Keeping this theorem abstract in the family index prevents clients
with dependent finite index types from unfolding their entire enumeration during kernel
checking. -/
theorem exists_face_on_segmentFamily {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) {x : Plane}
    (hx : x ∈ segment ℝ (left i) (right i)) :
    ∃ s ∈ (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.simplexes,
      x ∈ (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.cellCarrier s ∧
      (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.cellCarrier s ⊆
        segment ℝ (left i) (right i) := by
  let B := segmentFamilyChain left right
  let q := segmentFamilyIndex left right i
  have hsegment : segment ℝ (B.vertex q.castSucc) (B.vertex q.succ) =
      segment ℝ (left i) (right i) := segmentFamilyChain_segment left right i
  obtain ⟨s, hs, hxs, hsSegment⟩ := B.exists_face_on_segment q (hsegment.symm ▸ hx)
  refine ⟨s, hs, hxs, ?_⟩
  apply convexHull_min _ (convex_segment _ _)
  rintro y ⟨v, hv, rfl⟩
  have hvSegment := hsSegment v hv
  rw [hsegment] at hvSegment
  exact hvSegment

/-- The geometric carrier of all listed segments of a finite broken line.  Auxiliary line
arrangements may contain many additional faces, so this is the carrier relevant to the
polygonal object itself. -/
def segmentCarrier : Set Plane :=
  ⋃ i : Fin B.n, segment ℝ (B.vertex i.castSucc) (B.vertex i.succ)

/-- The line arrangement restricted to the actual segments of a finite broken line.  This is a
canonical finite plane complex even when the listed segments cross or overlap: the ambient line
arrangement has already inserted every required intersection vertex. -/
noncomputable def carrierComplex : PlaneComplex :=
  B.arrangementMesh.toPlaneComplex.restrictToSet B.segmentCarrier

/-- The canonical complex of a broken line has exactly the union of its listed segments as
support. -/
theorem carrierComplex_support : B.carrierComplex.support = B.segmentCarrier := by
  apply Set.Subset.antisymm
  · exact B.arrangementMesh.toPlaneComplex.restrictToSet_support_subset B.segmentCarrier
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs, hxs, hsSegment⟩ := B.exists_face_on_segment i hxi
    rw [PlaneComplex.support]
    refine Set.mem_iUnion₂.mpr ⟨s, ?_, hxs⟩
    apply (B.arrangementMesh.toPlaneComplex.mem_restrictToSet_simplexes_iff
      B.segmentCarrier).mpr
    refine ⟨hs, ?_⟩
    have hfaceSegment :
        B.arrangementMesh.toPlaneComplex.cellCarrier s ⊆
          segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) := by
      apply convexHull_min _ (convex_segment _ _)
      rintro y ⟨v, hv, rfl⟩
      exact hsSegment v hv
    exact hfaceSegment.trans (Set.subset_iUnion (fun j : Fin B.n =>
      segment ℝ (B.vertex j.castSucc) (B.vertex j.succ)) i)

/-- A canonical arrangement vertex representing an original chain vertex. -/
noncomputable def arrangementVertex (i : Fin (B.n + 1)) :
    B.arrangementMesh.toPlaneComplex.Vertex :=
  Classical.choose (B.exists_arrangementVertex_position_eq i)

theorem arrangementVertex_position (i : Fin (B.n + 1)) :
    B.arrangementMesh.toPlaneComplex.position (B.arrangementVertex i) = B.vertex i :=
  (Classical.choose_spec (B.exists_arrangementVertex_position_eq i)).1

theorem arrangementVertex_face (i : Fin (B.n + 1)) :
    ({B.arrangementVertex i} : Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
      B.arrangementMesh.toPlaneComplex.simplexes :=
  (Classical.choose_spec (B.exists_arrangementVertex_position_eq i)).2

/-- The left endpoint of a listed family segment is a canonical vertex of the common
arrangement. -/
theorem segmentFamily_arrangementVertex_position_left {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.position
      ((segmentFamilyChain left right).arrangementVertex
        (segmentFamilyIndex left right i).castSucc) = left i := by
  rw [(segmentFamilyChain left right).arrangementVertex_position]
  exact segmentFamilyChain_vertex_even left right i

/-- The right endpoint of a listed family segment is a canonical vertex of the common
arrangement. -/
theorem segmentFamily_arrangementVertex_position_right {I : Type*} [Fintype I]
    (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.position
      ((segmentFamilyChain left right).arrangementVertex
        (segmentFamilyIndex left right i).succ) = right i := by
  rw [(segmentFamilyChain left right).arrangementVertex_position]
  exact segmentFamilyChain_vertex_odd left right i

/-- The part of the arrangement mesh lying wholly on one original chain segment. -/
noncomputable def segmentComplex (i : Fin B.n) : PlaneComplex :=
  B.arrangementMesh.toPlaneComplex.restrictedTo
    (segment ℝ (B.vertex i.castSucc) (B.vertex i.succ))

theorem segmentComplex_support (i : Fin B.n) :
    (B.segmentComplex i).support =
      segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) := by
  apply B.arrangementMesh.toPlaneComplex.restrictedTo_support_eq
  intro x hx
  obtain ⟨s, hs, hxs, hsseg⟩ := B.exists_face_on_segment i hx
  refine ⟨s, hs, hxs, ?_⟩
  apply convexHull_min _ (convex_segment _ _)
  rintro y ⟨v, hv, rfl⟩
  exact hsseg v hv

theorem arrangementVertex_mem_segmentComplex_left (i : Fin B.n) :
    ({B.arrangementVertex i.castSucc} : Finset (B.segmentComplex i).Vertex) ∈
      (B.segmentComplex i).simplexes := by
  apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
  refine ⟨B.arrangementVertex_face i.castSucc, ?_⟩
  apply convexHull_min _ (convex_segment _ _)
  rintro y ⟨v, hv, rfl⟩
  have hv' : v = B.arrangementVertex i.castSucc := Finset.mem_singleton.mp hv
  subst v
  rw [B.arrangementVertex_position]
  exact left_mem_segment ℝ _ _

theorem arrangementVertex_mem_segmentComplex_right (i : Fin B.n) :
    ({B.arrangementVertex i.succ} : Finset (B.segmentComplex i).Vertex) ∈
      (B.segmentComplex i).simplexes := by
  apply (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mpr
  refine ⟨B.arrangementVertex_face i.succ, ?_⟩
  apply convexHull_min _ (convex_segment _ _)
  rintro y ⟨v, hv, rfl⟩
  have hv' : v = B.arrangementVertex i.succ := Finset.mem_singleton.mp hv
  subst v
  rw [B.arrangementVertex_position]
  exact right_mem_segment ℝ _ _

/-- The line arrangement turns every original chain segment into a path in a finite
one-skeleton. -/
theorem reachable_on_segment (i : Fin B.n) :
    (B.segmentComplex i).vertexGraph.Reachable
      (B.arrangementVertex i.castSucc) (B.arrangementVertex i.succ) := by
  apply (B.segmentComplex i).vertexGraph_reachable_of_isPreconnected
  · rw [B.segmentComplex_support]
    exact (convex_segment (B.vertex i.castSucc) (B.vertex i.succ)).isPreconnected
  · exact B.arrangementVertex_mem_segmentComplex_left i
  · exact B.arrangementVertex_mem_segmentComplex_right i

theorem exists_path_on_segment (i : Fin B.n) :
    Nonempty ((B.segmentComplex i).vertexGraph.Path
      (B.arrangementVertex i.castSucc) (B.arrangementVertex i.succ)) := by
  obtain ⟨p, hp⟩ := (B.reachable_on_segment i).exists_isPath
  exact ⟨⟨p, hp⟩⟩

/-- Arrangement edges whose geometric segments lie in the prescribed open set. -/
def inSetGraph : SimpleGraph B.arrangementMesh.toPlaneComplex.Vertex where
  Adj v w := v ≠ w ∧
    ({v, w} : Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
      B.arrangementMesh.toPlaneComplex.simplexes ∧
    B.arrangementMesh.toPlaneComplex.cellCarrier {v, w} ⊆ U
  symm := ⟨by
    rintro v w ⟨hvw, hedge, hU⟩
    exact ⟨hvw.symm, by simpa [Finset.pair_comm] using hedge,
      by rw [Finset.pair_comm]; exact hU⟩⟩
  loopless := ⟨by
    rintro v ⟨hvv, -⟩
    exact hvv rfl⟩

theorem inSetGraph_adj_iff {v w : B.arrangementMesh.toPlaneComplex.Vertex} :
    B.inSetGraph.Adj v w ↔ v ≠ w ∧
      ({v, w} : Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
        B.arrangementMesh.toPlaneComplex.simplexes ∧
      B.arrangementMesh.toPlaneComplex.cellCarrier {v, w} ⊆ U := Iff.rfl

theorem inSetGraph_le_arrangementVertexGraph :
    B.inSetGraph ≤ B.arrangementMesh.toPlaneComplex.vertexGraph := by
  intro v w hvw
  rw [B.inSetGraph_adj_iff] at hvw
  rw [B.arrangementMesh.toPlaneComplex.vertexGraph_adj_iff]
  exact ⟨hvw.1, hvw.2.1⟩

theorem segmentVertexGraph_le_inSetGraph (i : Fin B.n) :
    (B.segmentComplex i).vertexGraph ≤
      B.inSetGraph := by
  intro v w hvw
  rw [(B.segmentComplex i).vertexGraph_adj_iff] at hvw
  obtain ⟨hedge, hsegment⟩ :=
    (B.arrangementMesh.toPlaneComplex.mem_restrictedTo_simplexes_iff _).mp hvw.2
  exact B.inSetGraph_adj_iff.mpr
    ⟨hvw.1, hedge, hsegment.trans (B.segment_subset i)⟩

/-- Concatenating the segment paths gives a walk through the entire broken line; Mathlib's
loop-erasure then produces a path with the same endpoints. -/
theorem exists_arrangement_path :
    Nonempty (B.inSetGraph.Path
      (B.arrangementVertex 0) (B.arrangementVertex (Fin.last B.n))) := by
  let G := B.inSetGraph
  have hwalk : ∀ k : ℕ, ∀ hk : k ≤ B.n,
      Nonempty (G.Walk (B.arrangementVertex 0)
        (B.arrangementVertex ⟨k, Nat.lt_succ_of_le hk⟩)) := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact ⟨SimpleGraph.Walk.nil⟩
    | succ k ih =>
        intro hk
        have hklt : k < B.n := Nat.lt_of_succ_le hk
        obtain ⟨p⟩ := ih (Nat.le_of_lt hklt)
        let i : Fin B.n := ⟨k, hklt⟩
        obtain ⟨q⟩ := B.exists_path_on_segment i
        have q' : G.Walk (B.arrangementVertex i.castSucc)
            (B.arrangementVertex i.succ) :=
          (q : (B.segmentComplex i).vertexGraph.Walk _ _).mapLe
            (B.segmentVertexGraph_le_inSetGraph i)
        have hpEnd : B.arrangementVertex ⟨k, Nat.lt_succ_of_le (Nat.le_of_lt hklt)⟩ =
            B.arrangementVertex i.castSucc := by rfl
        have hqEnd : B.arrangementVertex i.succ =
            B.arrangementVertex ⟨k + 1, Nat.lt_succ_of_le hk⟩ := by rfl
        rw [hpEnd] at p
        rw [← hqEnd]
        exact ⟨p.append q'⟩
  obtain ⟨p⟩ := hwalk B.n le_rfl
  have hpEnd : B.arrangementVertex ⟨B.n, Nat.lt_succ_self B.n⟩ =
      B.arrangementVertex (Fin.last B.n) := by rfl
  rw [hpEnd] at p
  exact ⟨p.toPath⟩

/-- A canonical loop-free resolution of the broken line. -/
noncomputable def resolvedPath : B.inSetGraph.Path
    (B.arrangementVertex 0) (B.arrangementVertex (Fin.last B.n)) :=
  Classical.choice B.exists_arrangement_path

/-- The `resolvedWalk` declaration. -/
noncomputable def resolvedWalk : B.inSetGraph.Walk
    (B.arrangementVertex 0) (B.arrangementVertex (Fin.last B.n)) :=
  B.resolvedPath

/-- Ordered geometric vertices of the resolved polygonal arc. -/
noncomputable def resolvedVertex
    (i : Fin (B.resolvedWalk.length + 1)) : Plane :=
  B.arrangementMesh.toPlaneComplex.position
    (B.resolvedWalk.getVert i)

theorem resolvedVertex_injective : Function.Injective B.resolvedVertex := by
  intro i j hij
  apply Fin.ext
  apply B.resolvedPath.property.getVert_injOn
  · change i.val ≤ B.resolvedWalk.length
    omega
  · change j.val ≤ B.resolvedWalk.length
    omega
  apply B.arrangementMesh.toPlaneComplex.position_injective
  exact hij

theorem resolvedVertex_start : B.resolvedVertex 0 = B.start := by
  change B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert 0) = B.start
  rw [SimpleGraph.Walk.getVert_zero]
  exact B.arrangementVertex_position 0

theorem resolvedVertex_finish :
    B.resolvedVertex (Fin.last B.resolvedWalk.length) =
      B.finish := by
  change B.arrangementMesh.toPlaneComplex.position
    (B.resolvedWalk.getVert B.resolvedWalk.length) = B.finish
  rw [SimpleGraph.Walk.getVert_length]
  exact B.arrangementVertex_position (Fin.last B.n)

theorem resolvedSegment_subset (i : Fin B.resolvedWalk.length) :
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) ⊆ U := by
  let p : B.inSetGraph.Walk _ _ := B.resolvedWalk
  have hadj := p.adj_getVert_succ i.isLt
  rw [B.inSetGraph_adj_iff] at hadj
  have hcarrier := hadj.2.2
  change segment ℝ
      (B.arrangementMesh.toPlaneComplex.position (p.getVert i.val))
      (B.arrangementMesh.toPlaneComplex.position (p.getVert (i.val + 1))) ⊆ U
  have himage : B.arrangementMesh.toPlaneComplex.position ''
      (({p.getVert i.val, p.getVert (i.val + 1)} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex) : Set _) =
      {B.arrangementMesh.toPlaneComplex.position (p.getVert i.val),
        B.arrangementMesh.toPlaneComplex.position (p.getVert (i.val + 1))} := by
    ext x
    simp [eq_comm]
  rw [PlaneComplex.cellCarrier, himage, convexHull_pair] at hcarrier
  exact hcarrier

theorem resolvedSegment_eq_cellCarrier (i : Fin B.resolvedWalk.length) :
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) =
      B.arrangementMesh.toPlaneComplex.cellCarrier
        {B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} := by
  change segment ℝ
      (B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert i.val))
      (B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert (i.val + 1))) = _
  rw [PlaneComplex.cellCarrier]
  have himage : B.arrangementMesh.toPlaneComplex.position ''
      (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex) : Set _) =
      {B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert i.val),
        B.arrangementMesh.toPlaneComplex.position (B.resolvedWalk.getVert (i.val + 1))} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

theorem resolvedEdge_mem_simplexes (i : Fin B.resolvedWalk.length) :
    ({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
        B.arrangementMesh.toPlaneComplex.simplexes := by
  have hadj := B.resolvedWalk.adj_getVert_succ i.isLt
  rw [B.inSetGraph_adj_iff] at hadj
  exact hadj.2.1

/-- Exact face-to-face intersection for the ordered segments of the resolved arc. -/
theorem resolvedSegment_inter (i j : Fin B.resolvedWalk.length) :
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) ∩
      segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ) =
    B.arrangementMesh.toPlaneComplex.cellCarrier
      (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
        {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)}) := by
  rw [B.resolvedSegment_eq_cellCarrier i, B.resolvedSegment_eq_cellCarrier j]
  simpa only [PlaneComplex.cellCarrier] using
    B.arrangementMesh.toPlaneComplex.face_inter _ (B.resolvedEdge_mem_simplexes i)
      _ (B.resolvedEdge_mem_simplexes j)

/-- The geometric carrier of the selected graph path. -/
def resolvedCarrier : Set Plane :=
  if _ : B.resolvedWalk.length = 0 then {B.resolvedVertex 0}
  else ⋃ i : Fin B.resolvedWalk.length,
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ)

theorem resolvedCarrier_subset (hstart : B.start ∈ U) : B.resolvedCarrier ⊆ U := by
  intro x hx
  unfold resolvedCarrier at hx
  split_ifs at hx with hzero
  · have hx0 : x = B.resolvedVertex 0 := hx
    rw [hx0, B.resolvedVertex_start]
    exact hstart
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact B.resolvedSegment_subset i hxi

private def IsResolvedFace (s : Finset B.arrangementMesh.toPlaneComplex.Vertex) : Prop :=
  s.Nonempty ∧
    ((B.resolvedWalk.length = 0 ∧ s ⊆ {B.resolvedWalk.getVert 0}) ∨
      ∃ i : Fin B.resolvedWalk.length,
        s ⊆ {B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)})

/-- The parent-arrangement subcomplex consisting of the chosen path edges and their vertices. -/
noncomputable def resolvedComplex : PlaneComplex := by
  classical
  let K := B.arrangementMesh.toPlaneComplex
  exact {
    Vertex := K.Vertex
    position := K.position
    position_injective := K.position_injective
    simplexes := K.simplexes.filter B.IsResolvedFace
    nonempty_of_mem := by
      intro s hs
      exact (Finset.mem_filter.mp hs).2.1
    card_le_three := by
      intro s hs
      exact K.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs t hts ht
      obtain ⟨hsK, hsne, hsPath⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      refine ⟨K.down_closed s hsK t hts ht, ht, ?_⟩
      rcases hsPath with ⟨hzero, hs0⟩ | ⟨i, hsi⟩
      · exact Or.inl ⟨hzero, hts.trans hs0⟩
      · exact Or.inr ⟨i, hts.trans hsi⟩
    affineIndependent := by
      intro s hs
      exact K.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := by
      intro s hs t ht
      exact K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

@[simp] theorem resolvedComplex_position :
    B.resolvedComplex.position = B.arrangementMesh.toPlaneComplex.position := rfl

@[simp] theorem resolvedComplex_cellCarrier
    (s : Finset B.arrangementMesh.toPlaneComplex.Vertex) :
    B.resolvedComplex.cellCarrier s =
      B.arrangementMesh.toPlaneComplex.cellCarrier s := rfl

theorem mem_resolvedComplex_simplexes_iff
    {s : Finset B.arrangementMesh.toPlaneComplex.Vertex} :
    s ∈ B.resolvedComplex.simplexes ↔
      s ∈ B.arrangementMesh.toPlaneComplex.simplexes ∧ B.IsResolvedFace s := by
  classical
  change s ∈ B.arrangementMesh.toPlaneComplex.simplexes.filter B.IsResolvedFace ↔ _
  exact Finset.mem_filter

/-- Every ordered vertex of the resolved path occurs as a zero-face of the selected complex. -/
theorem resolvedVertex_face (i : Fin (B.resolvedWalk.length + 1)) :
    ({B.resolvedWalk.getVert i.val} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈ B.resolvedComplex.simplexes := by
  classical
  by_cases hzero : B.resolvedWalk.length = 0
  · have hi : i = 0 := Fin.ext (by omega)
    subst i
    apply B.mem_resolvedComplex_simplexes_iff.mpr
    refine ⟨?_, Finset.singleton_nonempty _, Or.inl ⟨hzero, subset_rfl⟩⟩
    simpa using B.arrangementVertex_face 0
  · have hpos : 0 < B.resolvedWalk.length := Nat.pos_of_ne_zero hzero
    by_cases hi : i.val < B.resolvedWalk.length
    · let j : Fin B.resolvedWalk.length := ⟨i.val, hi⟩
      have hsubset : ({B.resolvedWalk.getVert i.val} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ⊆
          {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)} := by
        simp [j]
      have hsingleton := B.arrangementMesh.toPlaneComplex.down_closed _
        (B.resolvedEdge_mem_simplexes j) _ hsubset (Finset.singleton_nonempty _)
      exact B.mem_resolvedComplex_simplexes_iff.mpr
        ⟨hsingleton, Finset.singleton_nonempty _, Or.inr ⟨j, hsubset⟩⟩
    · have hilast : i.val = B.resolvedWalk.length := by omega
      let j : Fin B.resolvedWalk.length :=
        ⟨B.resolvedWalk.length - 1, Nat.sub_lt hpos (by omega)⟩
      have hsubset : ({B.resolvedWalk.getVert i.val} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ⊆
          {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)} := by
        intro v hv
        simp only [Finset.mem_singleton] at hv
        subst v
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        congr 1
        change i.val = B.resolvedWalk.length - 1 + 1
        omega
      have hsingleton := B.arrangementMesh.toPlaneComplex.down_closed _
        (B.resolvedEdge_mem_simplexes j) _ hsubset (Finset.singleton_nonempty _)
      exact B.mem_resolvedComplex_simplexes_iff.mpr
        ⟨hsingleton, Finset.singleton_nonempty _, Or.inr ⟨j, hsubset⟩⟩

/-- Every ordered path vertex lies in the support of the selected complex. -/
theorem resolvedVertex_mem_support (i : Fin (B.resolvedWalk.length + 1)) :
    B.resolvedComplex.position (B.resolvedWalk.getVert i.val) ∈
      B.resolvedComplex.support := by
  apply B.resolvedComplex.cellCarrier_subset_support (B.resolvedVertex_face i)
  exact subset_convexHull ℝ _ ⟨B.resolvedWalk.getVert i.val,
    Finset.mem_singleton_self _, rfl⟩

theorem resolvedComplex_card_le_two {s : Finset B.resolvedComplex.Vertex}
    (hs : s ∈ B.resolvedComplex.simplexes) : s.card ≤ 2 := by
  have hface := (B.mem_resolvedComplex_simplexes_iff.mp hs).2
  rcases hface.2 with ⟨-, hs0⟩ | ⟨i, hsi⟩
  · have hc : s.card ≤ ({B.resolvedWalk.getVert 0} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex).card :=
      Finset.card_le_card hs0
    calc
      s.card ≤ 1 := by simpa only [Finset.card_singleton] using hc
      _ ≤ 2 := by omega
  · exact (Finset.card_le_card hsi).trans Finset.card_le_two

theorem resolvedComplex_support : B.resolvedComplex.support = B.resolvedCarrier := by
  classical
  unfold resolvedCarrier
  split_ifs with hzero
  · have hpathNil : B.resolvedWalk.Nil := by simpa [SimpleGraph.Walk.length_eq_zero_iff] using hzero
    have hstartEnd : B.arrangementVertex 0 = B.arrangementVertex (Fin.last B.n) :=
      hpathNil.eq
    apply Set.Subset.antisymm
    · intro x hx
      rw [PlaneComplex.support] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨s, hs, hxs⟩ := hx
      have hface := (B.mem_resolvedComplex_simplexes_iff.mp hs).2
      have hs0 : s ⊆ {B.resolvedWalk.getVert 0} := by
        rcases hface.2 with ⟨-, hs0⟩ | ⟨i, -⟩
        · exact hs0
        · exact isEmptyElim (hzero ▸ i)
      have hcarrier : B.resolvedComplex.cellCarrier s ⊆ {B.resolvedVertex 0} := by
        apply convexHull_min _ (convex_singleton _)
        rintro y ⟨v, hv, rfl⟩
        have hv0 : v = B.resolvedWalk.getVert 0 := by
          exact Finset.mem_singleton.mp (hs0 hv)
        subst v
        rfl
      exact hcarrier hxs
    · rintro x rfl
      rw [PlaneComplex.support]
      refine Set.mem_iUnion₂.mpr ⟨{B.resolvedWalk.getVert 0}, ?_, ?_⟩
      · apply B.mem_resolvedComplex_simplexes_iff.mpr
        refine ⟨?_, ?_⟩
        · have hstart : B.resolvedWalk.getVert 0 = B.arrangementVertex 0 := by simp
          change ({B.resolvedWalk.getVert 0} :
            Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈
              B.arrangementMesh.toPlaneComplex.simplexes
          rw [hstart]
          exact B.arrangementVertex_face 0
        · exact ⟨Finset.singleton_nonempty _, Or.inl ⟨hzero, subset_rfl⟩⟩
      · exact subset_convexHull ℝ _
          ⟨B.resolvedWalk.getVert 0, Finset.mem_singleton_self _, rfl⟩
  · apply Set.Subset.antisymm
    · intro x hx
      rw [PlaneComplex.support] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨s, hs, hxs⟩ := hx
      obtain ⟨-, -, hsPath⟩ := B.mem_resolvedComplex_simplexes_iff.mp hs
      rcases hsPath with hsZero | ⟨i, hsi⟩
      · exact (hzero hsZero.1).elim
      · refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        rw [B.resolvedSegment_eq_cellCarrier i]
        exact convexHull_mono (Set.image_mono hsi) hxs
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [B.resolvedSegment_eq_cellCarrier i] at hxi
      rw [PlaneComplex.support]
      let s : Finset B.arrangementMesh.toPlaneComplex.Vertex :=
        {B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)}
      refine Set.mem_iUnion₂.mpr ⟨s, ?_, hxi⟩
      apply B.mem_resolvedComplex_simplexes_iff.mpr
      exact ⟨B.resolvedEdge_mem_simplexes i, by
        refine ⟨by simp [s], Or.inr ⟨i, ?_⟩⟩
        exact subset_rfl⟩

/-- Affine coordinate from `0` to `1` along one resolved path edge. -/
noncomputable def resolvedEdgeParameter (i : Fin B.resolvedWalk.length) :
    Plane →ᵃ[ℝ] ℝ :=
  if _ : B.resolvedVertex i.castSucc 0 ≠ B.resolvedVertex i.succ 0 then
    (B.resolvedVertex i.succ 0 - B.resolvedVertex i.castSucc 0)⁻¹ •
      (cartesianX - AffineMap.const ℝ Plane (B.resolvedVertex i.castSucc 0))
  else
    (B.resolvedVertex i.succ 1 - B.resolvedVertex i.castSucc 1)⁻¹ •
      (cartesianY - AffineMap.const ℝ Plane (B.resolvedVertex i.castSucc 1))

theorem resolvedEdgeParameter_apply_left (i : Fin B.resolvedWalk.length) :
    B.resolvedEdgeParameter i (B.resolvedVertex i.castSucc) = 0 := by
  unfold resolvedEdgeParameter
  split_ifs <;> simp

theorem resolvedEdgeParameter_apply_right (i : Fin B.resolvedWalk.length) :
    B.resolvedEdgeParameter i (B.resolvedVertex i.succ) = 1 := by
  unfold resolvedEdgeParameter
  split_ifs with h0
  · change (B.resolvedVertex i.succ 0 - B.resolvedVertex i.castSucc 0)⁻¹ *
        (B.resolvedVertex i.succ 0 - B.resolvedVertex i.castSucc 0) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr h0.symm)
  · have hne : B.resolvedVertex i.castSucc ≠ B.resolvedVertex i.succ := by
      intro heq
      exact (Fin.ne_of_lt i.castSucc_lt_succ) (B.resolvedVertex_injective heq)
    have h1 : B.resolvedVertex i.castSucc 1 ≠ B.resolvedVertex i.succ 1 := by
      intro h1
      apply hne
      exact plane_ext (not_ne_iff.mp h0) h1
    change (B.resolvedVertex i.succ 1 - B.resolvedVertex i.castSucc 1)⁻¹ *
        (B.resolvedVertex i.succ 1 - B.resolvedVertex i.castSucc 1) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr h1.symm)

theorem resolvedEdgeParameter_lineMap (i : Fin B.resolvedWalk.length) (t : ℝ) :
    B.resolvedEdgeParameter i
      (AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) t) = t := by
  rw [AffineMap.apply_lineMap, B.resolvedEdgeParameter_apply_left,
    B.resolvedEdgeParameter_apply_right]
  simp [AffineMap.lineMap_apply_module]

/-- The affine coordinate on edge `i`, shifted to the interval `[i,i+1]`. -/
noncomputable def resolvedEdgeGlobalParameter (i : Fin B.resolvedWalk.length) :
    Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane (i.val : ℝ) + B.resolvedEdgeParameter i

theorem resolvedEdgeGlobalParameter_apply_left (i : Fin B.resolvedWalk.length) :
    B.resolvedEdgeGlobalParameter i (B.resolvedVertex i.castSucc) = i.val := by
  change (i.val : ℝ) + B.resolvedEdgeParameter i (B.resolvedVertex i.castSucc) = i.val
  rw [B.resolvedEdgeParameter_apply_left]
  simp

theorem resolvedEdgeGlobalParameter_apply_right (i : Fin B.resolvedWalk.length) :
    B.resolvedEdgeGlobalParameter i (B.resolvedVertex i.succ) = i.val + 1 := by
  change (i.val : ℝ) + B.resolvedEdgeParameter i (B.resolvedVertex i.succ) = i.val + 1
  rw [B.resolvedEdgeParameter_apply_right]

theorem resolvedEdgeGlobalParameter_lineMap (i : Fin B.resolvedWalk.length) (t : ℝ) :
    B.resolvedEdgeGlobalParameter i
      (AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) t) =
        i.val + t := by
  change (i.val : ℝ) + B.resolvedEdgeParameter i
    (AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) t) = i.val + t
  rw [B.resolvedEdgeParameter_lineMap]

private theorem getVert_index_eq {r s : ℕ} (hr : r ≤ B.resolvedWalk.length)
    (hs : s ≤ B.resolvedWalk.length)
    (h : B.resolvedWalk.getVert r = B.resolvedWalk.getVert s) : r = s :=
  B.resolvedPath.property.getVert_injOn hr hs h

theorem resolvedEdge_indices_close (i j : Fin B.resolvedWalk.length)
    (hinter : (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
      {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)}).Nonempty) :
    i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨v, hv⟩ := hinter
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv.1 with hi | hi <;> rcases hv.2 with hj | hj
  · left
    apply Fin.ext
    exact B.getVert_index_eq i.isLt.le j.isLt.le (hi.symm.trans hj)
  · right; right
    exact B.getVert_index_eq i.isLt.le (by omega) (hi.symm.trans hj) |>.symm
  · right; left
    exact B.getVert_index_eq (by omega) j.isLt.le (hi.symm.trans hj)
  · left
    apply Fin.ext
    have := B.getVert_index_eq (r := i.val + 1) (s := j.val + 1)
      (by omega) (by omega) (hi.symm.trans hj)
    omega

theorem resolvedSegment_indices_close (i j : Fin B.resolvedWalk.length) {x : Plane}
    (hxi : x ∈ segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ))
    (hxj : x ∈ segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ)) :
    i = j ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hx : x ∈ B.arrangementMesh.toPlaneComplex.cellCarrier
      (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
        {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)}) := by
    rw [← B.resolvedSegment_inter i j]
    exact ⟨hxi, hxj⟩
  have hne : (({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
        {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)}).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, PlaneComplex.cellCarrier] at hx
    simp at hx
  exact B.resolvedEdge_indices_close i j hne

theorem resolvedSegment_inter_of_succ_eq (i j : Fin B.resolvedWalk.length)
    (hij : i.val + 1 = j.val) :
    segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) ∩
      segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ) =
        {B.resolvedVertex i.succ} := by
  rw [B.resolvedSegment_inter i j]
  have hshared : B.resolvedWalk.getVert (i.val + 1) = B.resolvedWalk.getVert j.val := by
    rw [hij]
  have houter : B.resolvedWalk.getVert i.val ≠
      B.resolvedWalk.getVert (j.val + 1) := by
    intro h
    have heq := B.getVert_index_eq i.isLt.le (by omega) h
    omega
  have hleft : B.resolvedWalk.getVert i.val ≠ B.resolvedWalk.getVert j.val := by
    intro h
    have heq := B.getVert_index_eq i.isLt.le j.isLt.le h
    omega
  have hright : B.resolvedWalk.getVert (i.val + 1) ≠
      B.resolvedWalk.getVert (j.val + 1) := by
    intro h
    have heq := B.getVert_index_eq (by omega) (by omega) h
    omega
  have hinter :
      ({B.resolvedWalk.getVert i.val, B.resolvedWalk.getVert (i.val + 1)} :
          Finset B.arrangementMesh.toPlaneComplex.Vertex) ∩
        {B.resolvedWalk.getVert j.val, B.resolvedWalk.getVert (j.val + 1)} =
          {B.resolvedWalk.getVert (i.val + 1)} := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hi | hi, hj | hj⟩
      · exact (hleft (hi.symm.trans hj)).elim
      · exact (houter (hi.symm.trans hj)).elim
      · exact hi
      · exact (hright (hi.symm.trans hj)).elim
    · intro hv
      exact ⟨Or.inr hv, Or.inl (hv.trans hshared)⟩
  rw [hinter, PlaneComplex.cellCarrier]
  have himage : B.arrangementMesh.toPlaneComplex.position ''
      (({B.resolvedWalk.getVert (i.val + 1)} :
        Finset B.arrangementMesh.toPlaneComplex.Vertex) : Set _) =
      {B.arrangementMesh.toPlaneComplex.position
        (B.resolvedWalk.getVert (i.val + 1))} := by
    ext x
    simp []
  rw [himage, convexHull_singleton]
  change {B.arrangementMesh.toPlaneComplex.position
      (B.resolvedWalk.getVert (i.val + 1))} = {B.resolvedVertex i.succ}
  rfl

/-- The shifted affine edge parameters agree wherever two selected path edges meet. -/
theorem resolvedEdgeGlobalParameter_agree (i j : Fin B.resolvedWalk.length) {x : Plane}
    (hxi : x ∈ segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ))
    (hxj : x ∈ segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ)) :
    B.resolvedEdgeGlobalParameter i x = B.resolvedEdgeGlobalParameter j x := by
  rcases B.resolvedSegment_indices_close i j hxi hxj with rfl | hij | hji
  · rfl
  · have hxShared : x = B.resolvedVertex i.succ := by
      have hxInter : x ∈ segment ℝ (B.resolvedVertex i.castSucc)
          (B.resolvedVertex i.succ) ∩
        segment ℝ (B.resolvedVertex j.castSucc) (B.resolvedVertex j.succ) := ⟨hxi, hxj⟩
      rw [B.resolvedSegment_inter_of_succ_eq i j hij] at hxInter
      exact hxInter
    have hvertex : B.resolvedVertex i.succ = B.resolvedVertex j.castSucc := by
      apply congrArg B.resolvedVertex
      apply Fin.ext
      exact hij
    rw [hxShared, B.resolvedEdgeGlobalParameter_apply_right, hvertex,
      B.resolvedEdgeGlobalParameter_apply_left]
    exact_mod_cast hij
  · have hxShared : x = B.resolvedVertex j.succ := by
      have hxInter : x ∈ segment ℝ (B.resolvedVertex j.castSucc)
          (B.resolvedVertex j.succ) ∩
        segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := ⟨hxj, hxi⟩
      rw [B.resolvedSegment_inter_of_succ_eq j i hji] at hxInter
      exact hxInter
    have hvertex : B.resolvedVertex j.succ = B.resolvedVertex i.castSucc := by
      apply congrArg B.resolvedVertex
      apply Fin.ext
      exact hji
    symm
    rw [hxShared, B.resolvedEdgeGlobalParameter_apply_right, hvertex,
      B.resolvedEdgeGlobalParameter_apply_left]
    exact_mod_cast hji

/-- Piecewise-affine coordinate along the whole resolved arc. -/
noncomputable def resolvedGlobalParameter (x : Plane) : ℝ :=
  by
    classical
    exact if h : ∃ i : Fin B.resolvedWalk.length,
        x ∈ segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) then
      B.resolvedEdgeGlobalParameter (Classical.choose h) x
    else 0

theorem resolvedGlobalParameter_eq_on_edge (i : Fin B.resolvedWalk.length) {x : Plane}
    (hx : x ∈ segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ)) :
    B.resolvedGlobalParameter x = B.resolvedEdgeGlobalParameter i x := by
  unfold resolvedGlobalParameter
  split_ifs with h
  · exact B.resolvedEdgeGlobalParameter_agree (Classical.choose h) i
      (Classical.choose_spec h) hx
  · exact (h ⟨i, hx⟩).elim

theorem resolvedGlobalParameter_lineMap_of_mem (i : Fin B.resolvedWalk.length)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    B.resolvedGlobalParameter
      (AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) t) =
        i.val + t := by
  rw [B.resolvedGlobalParameter_eq_on_edge i
    (lineMap_mem_segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) ht)]
  exact B.resolvedEdgeGlobalParameter_lineMap i t

theorem resolvedGlobalParameter_injectiveOn :
    Set.InjOn B.resolvedGlobalParameter B.resolvedCarrier := by
  intro x hx y hy hxy
  unfold resolvedCarrier at hx hy
  split_ifs at hx hy with hzero
  · simpa using hx.trans hy.symm
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
    rw [segment_eq_image_lineMap] at hxi hyj
    obtain ⟨t, ht, rfl⟩ := hxi
    obtain ⟨u, hu, rfl⟩ := hyj
    rw [B.resolvedGlobalParameter_lineMap_of_mem i ht,
      B.resolvedGlobalParameter_lineMap_of_mem j hu] at hxy
    by_cases hij : i.val = j.val
    · have htu : t = u := by
        have hijR : (i.val : ℝ) = j.val := by exact_mod_cast hij
        rw [hijR] at hxy
        linarith
      rw [show i = j by exact Fin.ext hij, htu]
    · rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hsucc : i.val + 1 = j.val := by
          have hle : i.val + 1 ≤ j.val := by omega
          have hle' : (j.val : ℝ) ≤ i.val + 1 := by
            linarith [ht.2, hu.1]
          have hleNat' : j.val ≤ i.val + 1 := by exact_mod_cast hle'
          exact Nat.le_antisymm hle hleNat'
        have ht1 : t = 1 := by
          have hsR : (i.val : ℝ) + 1 = j.val := by exact_mod_cast hsucc
          rw [← hsR] at hxy
          linarith [hu.1, ht.2]
        have hu0 : u = 0 := by
          have hsR : (i.val : ℝ) + 1 = j.val := by exact_mod_cast hsucc
          rw [← hsR, ht1] at hxy
          linarith
        have hvertex : B.resolvedVertex i.succ = B.resolvedVertex j.castSucc := by
          apply congrArg B.resolvedVertex
          exact Fin.ext hsucc
        simpa [ht1, hu0] using hvertex
      · have hsucc : j.val + 1 = i.val := by
          have hle : j.val + 1 ≤ i.val := by omega
          have hle' : (i.val : ℝ) ≤ j.val + 1 := by
            linarith [hu.2, ht.1]
          have hleNat' : i.val ≤ j.val + 1 := by exact_mod_cast hle'
          exact Nat.le_antisymm hle hleNat'
        have hu1 : u = 1 := by
          have hsR : (j.val : ℝ) + 1 = i.val := by exact_mod_cast hsucc
          rw [← hsR] at hxy
          linarith [ht.1, hu.2]
        have ht0 : t = 0 := by
          have hsR : (j.val : ℝ) + 1 = i.val := by exact_mod_cast hsucc
          rw [← hsR, hu1] at hxy
          linarith
        have hvertex : B.resolvedVertex j.succ = B.resolvedVertex i.castSucc := by
          apply congrArg B.resolvedVertex
          exact Fin.ext hsucc
        simpa [ht0, hu1] using hvertex.symm

theorem resolvedGlobalParameter_image :
    B.resolvedGlobalParameter '' B.resolvedCarrier =
      Set.Icc (0 : ℝ) B.resolvedWalk.length := by
  apply Set.Subset.antisymm
  · rintro r ⟨x, hx, rfl⟩
    unfold resolvedCarrier at hx
    split_ifs at hx with hzero
    · have hx0 : x = B.resolvedVertex 0 := hx
      subst x
      have hno : ¬∃ i : Fin B.resolvedWalk.length,
          B.resolvedVertex 0 ∈
            segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := by
        rintro ⟨i, -⟩
        exact isEmptyElim (hzero ▸ i)
      have hparam : B.resolvedGlobalParameter (B.resolvedVertex 0) = 0 := by
        unfold resolvedGlobalParameter
        simp [hno]
      constructor
      · rw [hparam]
      · rw [hparam, hzero]
        norm_num
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [segment_eq_image_lineMap] at hxi
      obtain ⟨t, ht, rfl⟩ := hxi
      rw [B.resolvedGlobalParameter_lineMap_of_mem i ht]
      constructor
      · exact add_nonneg (Nat.cast_nonneg _) ht.1
      · have hi : i.val + 1 ≤ B.resolvedWalk.length := i.isLt
        have hiR : (i.val : ℝ) + 1 ≤ B.resolvedWalk.length := by exact_mod_cast hi
        linarith [ht.2]
  · intro r hr
    by_cases hzero : B.resolvedWalk.length = 0
    · have hr0 : r = 0 := by
        rw [hzero] at hr
        norm_num at hr
        exact hr
      subst r
      refine ⟨B.resolvedVertex 0, ?_, ?_⟩
      · unfold resolvedCarrier
        simp [hzero]
      · have hno : ¬∃ i : Fin B.resolvedWalk.length,
            B.resolvedVertex 0 ∈
              segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := by
          rintro ⟨i, -⟩
          exact isEmptyElim (hzero ▸ i)
        unfold resolvedGlobalParameter
        simp [hno]
    · have hnpos : 0 < B.resolvedWalk.length := Nat.pos_of_ne_zero hzero
      by_cases hrn : r = B.resolvedWalk.length
      · let i : Fin B.resolvedWalk.length :=
          ⟨B.resolvedWalk.length - 1, Nat.sub_lt hnpos (by omega)⟩
        let x := B.resolvedVertex i.succ
        refine ⟨x, ?_, ?_⟩
        · unfold resolvedCarrier
          simp only [hzero, ↓reduceDIte]
          refine Set.mem_iUnion.mpr ⟨i, right_mem_segment ℝ _ _⟩
        · have hxLine : x = AffineMap.lineMap (B.resolvedVertex i.castSucc)
              (B.resolvedVertex i.succ) (1 : ℝ) := by
            change B.resolvedVertex i.succ =
              AffineMap.lineMap (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) (1 : ℝ)
            simp
          rw [hxLine]
          have hparam := B.resolvedGlobalParameter_lineMap_of_mem i
            (t := (1 : ℝ)) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
          rw [hparam]
          change ((B.resolvedWalk.length - 1 : ℕ) : ℝ) + 1 = r
          rw [hrn]
          exact_mod_cast Nat.sub_add_cancel hnpos
      · have hrlt : r < B.resolvedWalk.length := lt_of_le_of_ne hr.2 hrn
        let k : ℕ := ⌊r⌋₊
        have hklt : k < B.resolvedWalk.length := by
          exact (Nat.floor_lt hr.1).mpr hrlt
        let i : Fin B.resolvedWalk.length := ⟨k, hklt⟩
        let t : ℝ := r - k
        have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · dsimp [t, k]
            linarith [Nat.floor_le hr.1]
          · dsimp [t, k]
            linarith [Nat.lt_floor_add_one r]
        let x := AffineMap.lineMap (B.resolvedVertex i.castSucc)
          (B.resolvedVertex i.succ) t
        refine ⟨x, ?_, ?_⟩
        · unfold resolvedCarrier
          simp only [hzero, ↓reduceDIte]
          exact Set.mem_iUnion.mpr ⟨i, lineMap_mem_segment ℝ _ _ ht⟩
        · rw [show B.resolvedGlobalParameter x = i.val + t by
            exact B.resolvedGlobalParameter_lineMap_of_mem i ht]
          simp [i, t, k]

theorem resolvedGlobalParameter_start :
    B.resolvedGlobalParameter (B.resolvedVertex 0) = 0 := by
  by_cases hzero : B.resolvedWalk.length = 0
  · have hno : ¬∃ i : Fin B.resolvedWalk.length,
        B.resolvedVertex 0 ∈
          segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := by
      rintro ⟨i, -⟩
      exact isEmptyElim (hzero ▸ i)
    simp [resolvedGlobalParameter, hno]
  · let i : Fin B.resolvedWalk.length := ⟨0, Nat.pos_of_ne_zero hzero⟩
    have hleft : B.resolvedVertex 0 = B.resolvedVertex i.castSucc := by
      congr 1
    rw [hleft, B.resolvedGlobalParameter_eq_on_edge i (left_mem_segment ℝ _ _),
      B.resolvedEdgeGlobalParameter_apply_left]
    simp [i]

theorem resolvedGlobalParameter_finish :
    B.resolvedGlobalParameter (B.resolvedVertex (Fin.last B.resolvedWalk.length)) =
      B.resolvedWalk.length := by
  by_cases hzero : B.resolvedWalk.length = 0
  · have hlast : (Fin.last B.resolvedWalk.length) = 0 := Fin.ext (by simp [hzero])
    rw [hlast, B.resolvedGlobalParameter_start, hzero]
    norm_num
  · have hpos : 0 < B.resolvedWalk.length := Nat.pos_of_ne_zero hzero
    let i : Fin B.resolvedWalk.length :=
      ⟨B.resolvedWalk.length - 1, Nat.sub_lt hpos (by omega)⟩
    have hright : i.succ = Fin.last B.resolvedWalk.length := by
      apply Fin.ext
      change B.resolvedWalk.length - 1 + 1 = B.resolvedWalk.length
      omega
    rw [← hright, B.resolvedGlobalParameter_eq_on_edge i (right_mem_segment ℝ _ _),
      B.resolvedEdgeGlobalParameter_apply_right]
    dsimp [i]
    exact_mod_cast Nat.sub_add_cancel hpos

/-- Affine inclusion of the real axis into the plane. -/
def realAxisLinear : ℝ →ₗ[ℝ] Plane where
  toFun t := planePoint t 0
  map_add' := by intro x y; ext i ; fin_cases i <;> simp [planePoint]
  map_smul' := by intro c x; ext i ; fin_cases i <;> simp [planePoint]

/-- The `realAxisAffine` declaration. -/
def realAxisAffine : ℝ →ᵃ[ℝ] Plane := realAxisLinear.toAffineMap

@[simp] theorem realAxisAffine_apply (t : ℝ) : realAxisAffine t = planePoint t 0 := rfl

/-- Piecewise-affine straightening of the selected polygonal arc onto the real axis. -/
noncomputable def resolvedStraighten (x : Plane) : Plane :=
  realAxisAffine (B.resolvedGlobalParameter x)

theorem resolvedStraighten_start :
    B.resolvedStraighten (B.resolvedVertex 0) = planePoint 0 0 := by
  simp [resolvedStraighten, B.resolvedGlobalParameter_start]

theorem resolvedStraighten_finish :
    B.resolvedStraighten (B.resolvedVertex (Fin.last B.resolvedWalk.length)) =
      planePoint B.resolvedWalk.length 0 := by
  simp [resolvedStraighten, B.resolvedGlobalParameter_finish]

theorem resolvedStraighten_injectiveOn :
    Set.InjOn B.resolvedStraighten B.resolvedCarrier := by
  intro x hx y hy hxy
  apply B.resolvedGlobalParameter_injectiveOn hx hy
  have hcoord := congrArg (fun p : Plane => p 0) hxy
  exact hcoord

theorem resolvedStraighten_image :
    B.resolvedStraighten '' B.resolvedCarrier =
      segment ℝ (planePoint 0 0) (planePoint B.resolvedWalk.length 0) := by
  have himage : B.resolvedStraighten '' B.resolvedCarrier =
      realAxisAffine '' (B.resolvedGlobalParameter '' B.resolvedCarrier) := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨B.resolvedGlobalParameter y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [himage, B.resolvedGlobalParameter_image,
    ← segment_eq_Icc (show (0 : ℝ) ≤ B.resolvedWalk.length by positivity),
    image_segment (𝕜 := ℝ) realAxisAffine]
  rfl

theorem resolvedStraighten_affineOn_faces :
    ∀ s ∈ B.resolvedComplex.simplexes,
      IsAffineOn B.resolvedStraighten (B.resolvedComplex.cellCarrier s) := by
  intro s hs
  have hface := (B.mem_resolvedComplex_simplexes_iff.mp hs).2
  rcases hface.2 with ⟨hzero, hs0⟩ | ⟨i, hsi⟩
  · let g : Plane →ᵃ[ℝ] Plane :=
      realAxisAffine.comp (AffineMap.const ℝ Plane 0)
    refine ⟨g, ?_⟩
    intro x hx
    have hx0 : x = B.resolvedVertex 0 := by
      have hsubset : B.resolvedComplex.cellCarrier s ⊆ {B.resolvedVertex 0} := by
        apply convexHull_min _ (convex_singleton _)
        rintro y ⟨v, hv, rfl⟩
        have hv0 : v = B.resolvedWalk.getVert 0 := Finset.mem_singleton.mp (hs0 hv)
        subst v
        rfl
      exact hsubset hx
    subst x
    have hno : ¬∃ i : Fin B.resolvedWalk.length,
        B.resolvedVertex 0 ∈
          segment ℝ (B.resolvedVertex i.castSucc) (B.resolvedVertex i.succ) := by
      rintro ⟨i, -⟩
      exact isEmptyElim (hzero ▸ i)
    simp [resolvedStraighten, resolvedGlobalParameter, hno, g]
  · let g : Plane →ᵃ[ℝ] Plane :=
      realAxisAffine.comp (B.resolvedEdgeGlobalParameter i)
    refine ⟨g, ?_⟩
    intro x hx
    have hxEdge : x ∈ segment ℝ (B.resolvedVertex i.castSucc)
        (B.resolvedVertex i.succ) := by
      rw [B.resolvedSegment_eq_cellCarrier i]
      exact convexHull_mono (Set.image_mono hsi) hx
    change realAxisAffine (B.resolvedGlobalParameter x) =
      realAxisAffine (B.resolvedEdgeGlobalParameter i x)
    rw [B.resolvedGlobalParameter_eq_on_edge i hxEdge]

/-- The ordered broken-line data underlying the canonical simple graph path. -/
noncomputable def resolvedBrokenLine : BrokenLineData U where
  n := B.resolvedWalk.length
  vertex := B.resolvedVertex
  segment_subset := B.resolvedSegment_subset

theorem resolvedBrokenLine_start : B.resolvedBrokenLine.start = B.start :=
  B.resolvedVertex_start

theorem resolvedBrokenLine_finish : B.resolvedBrokenLine.finish = B.finish :=
  B.resolvedVertex_finish

theorem resolvedBrokenLine_vertex_injective :
    Function.Injective B.resolvedBrokenLine.vertex :=
  B.resolvedVertex_injective

end BrokenLineData

/-- A weak broken line can be resolved into a loop-free path in a finite straight-line graph,
with every graph edge contained in the same set.  This is the precise polygonal-arc form of
Moise Chapter 6, Theorem 1 used by the graph approximation argument. -/
theorem JoinedByBrokenLine.exists_polygonalArc {U : Set Plane} {a b : Plane}
    (h : JoinedByBrokenLine U a b) :
    ∃ B : BrokenLineData U,
      B.start = a ∧ B.finish = b ∧
      Nonempty (B.inSetGraph.Path
        (B.arrangementVertex 0) (B.arrangementVertex (Fin.last B.n))) := by
  obtain ⟨B, hstart, hfinish⟩ := BrokenLineData.exists_data_of_joined h
  exact ⟨B, hstart, hfinish, B.exists_arrangement_path⟩

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
