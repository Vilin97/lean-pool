/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.GraphSubdivision

/-!
# Finite marked refinements of plane graphs

This file enlarges the edge arrangement of a finite plane graph by finitely many prescribed
points.  When the marks lie in the graph support, the subordinate arrangement is a subdivision
of the graph and every mark is a vertex of that subdivision.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex) {P : Type*} [Fintype P]

/-- The `markEquiv` declaration. -/
noncomputable def markEquiv : P ≃ Fin (Fintype.card P) :=
  Fintype.equivFin P

/-- The edge chain enlarged by an arbitrary finite family of marked points. -/
noncomputable def markedEdgeChain (point : P → Plane) :
    BrokenLineData (Set.univ : Set Plane) := by
  classical
  let m := Fintype.card K.EdgeFace
  let r := Fintype.card P
  let q := Fintype.card K.Vertex
  let vertex : Fin (2 * m + r + q + 1) → Plane := fun k =>
    if hk : k.val < 2 * m then
      let i : Fin m := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then K.position (K.edgeFirst i) else K.position (K.edgeSecond i)
    else if hp : k.val < 2 * m + r then
      point (markEquiv.symm ⟨k.val - 2 * m, by omega⟩)
    else if hv : k.val < 2 * m + r + q then
      K.position (K.vertexAt ⟨k.val - (2 * m + r), by omega⟩)
    else 0
  exact {
    n := 2 * m + r + q
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

theorem markedEdgeChain_vertex_even (point : P → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.markedEdgeChain point).vertex ⟨2 * i.val, by
      change 2 * i.val < 2 * Fintype.card K.EdgeFace + Fintype.card P +
        Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeFirst i) := by
  classical
  simp only [markedEdgeChain]
  rw [dite_eq_left (by omega)]
  have hmod : (2 * i.val) % 2 = 0 := by omega
  rw [ite_eq_left hmod]
  have hdiv : 2 * i.val / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem markedEdgeChain_vertex_odd (point : P → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.markedEdgeChain point).vertex ⟨2 * i.val + 1, by
      change 2 * i.val + 1 < 2 * Fintype.card K.EdgeFace + Fintype.card P +
        Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeSecond i) := by
  classical
  simp only [markedEdgeChain]
  rw [dite_eq_left (by omega)]
  have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
  rw [ite_eq_right hmod]
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem markedEdgeChain_vertex_mark (point : P → Plane) (p : P) :
    (K.markedEdgeChain point).vertex
      ⟨2 * Fintype.card K.EdgeFace + (markEquiv p).val, by
        change 2 * Fintype.card K.EdgeFace + (markEquiv p).val <
          2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
        have hp := (markEquiv p).isLt
        omega⟩ = point p := by
  classical
  simp only [markedEdgeChain]
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + (markEquiv p).val -
      2 * Fintype.card K.EdgeFace = (markEquiv p).val := by omega
  have hfin : (⟨2 * Fintype.card K.EdgeFace + (markEquiv p).val -
      2 * Fintype.card K.EdgeFace, by omega⟩ : Fin (Fintype.card P)) = markEquiv p :=
    Fin.ext hsub
  rw [hfin, Equiv.symm_apply_apply]

theorem markedEdgeChain_vertex_original (point : P → Plane)
    (i : Fin (Fintype.card K.Vertex)) :
    (K.markedEdgeChain point).vertex
      ⟨2 * Fintype.card K.EdgeFace + Fintype.card P + i.val, by
        change 2 * Fintype.card K.EdgeFace + Fintype.card P + i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
        omega⟩ = K.position (K.vertexAt i) := by
  classical
  simp only [markedEdgeChain]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + Fintype.card P + i.val -
      (2 * Fintype.card K.EdgeFace + Fintype.card P) = i.val := by omega
  congr 2
  exact Fin.ext hsub

/-- The `markedEdgeChainIndex` declaration. -/
noncomputable def markedEdgeChainIndex (point : P → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) : Fin (K.markedEdgeChain point).n :=
  ⟨2 * i.val, by
    change 2 * i.val < 2 * Fintype.card K.EdgeFace + Fintype.card P +
      Fintype.card K.Vertex
    have hm : 0 < Fintype.card K.EdgeFace := Fintype.card_pos_iff.mpr ⟨K.edgeAt i⟩
    omega⟩

theorem markedEdgeChain_segment (point : P → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) :
    segment ℝ
        ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).castSucc)
        ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).succ) =
      K.cellCarrier (K.edgeAt i).1 := by
  rw [show (K.markedEdgeChainIndex point i).castSucc =
      ⟨2 * i.val, by
        change 2 * i.val < 2 * Fintype.card K.EdgeFace + Fintype.card P +
          Fintype.card K.Vertex + 1
        omega⟩ from rfl,
    show (K.markedEdgeChainIndex point i).succ =
      ⟨2 * i.val + 1, by
        change 2 * i.val + 1 < 2 * Fintype.card K.EdgeFace + Fintype.card P +
          Fintype.card K.Vertex + 1
        omega⟩ from rfl,
    K.markedEdgeChain_vertex_even point i, K.markedEdgeChain_vertex_odd point i,
    K.edgeAt_eq, PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

/-- The `markedEdgeArrangement` declaration. -/
noncomputable def markedEdgeArrangement (point : P → Plane) : PlaneComplex :=
  (K.markedEdgeChain point).arrangementMesh.toPlaneComplex

/-- The `markedEdgeSubdivision` declaration. -/
noncomputable def markedEdgeSubdivision (point : P → Plane) : PlaneComplex :=
  (K.markedEdgeArrangement point).subordinateTo K

theorem markedEdgeSubdivision_support_eq (point : P → Plane)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    (K.markedEdgeSubdivision point).support = K.support := by
  unfold markedEdgeSubdivision markedEdgeArrangement
  apply Set.Subset.antisymm
  · exact (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.subordinateTo_support_subset K
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
    have hscard := hgraph s hs
    have hcases : s.card = 1 ∨ s.card = 2 := by omega
    rw [PlaneComplex.support]
    simp only [Set.mem_iUnion]
    rcases hcases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hxv : x = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨i, hi⟩ := K.exists_vertexAt v
      let j : Fin ((K.markedEdgeChain point).n + 1) :=
        ⟨2 * Fintype.card K.EdgeFace + Fintype.card P + i.val, by
          change 2 * Fintype.card K.EdgeFace + Fintype.card P + i.val <
            2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
          omega⟩
      obtain ⟨w, hwpos, hwface⟩ :=
        (K.markedEdgeChain point).exists_arrangementVertex_position_eq j
      let u : Finset (K.markedEdgeChain point).arrangementMesh.Vertex := {w}
      refine ⟨u, ?_, ?_⟩
      · apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
          |>.mem_subordinateTo_simplexes_iff K).mpr
        refine ⟨hwface, {v}, hs, ?_⟩
        intro y hy
        have hyw : y = (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w := by
          change y ∈ convexHull ℝ
            ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
                Set (K.markedEdgeChain point).arrangementMesh.Vertex)) at hy
          have himage : (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
                Set (K.markedEdgeChain point).arrangementMesh.Vertex) =
              {(K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨q, hq, rfl⟩
              rw [Finset.mem_singleton.mp hq]
              exact Set.mem_singleton _
            · intro hz
              rw [Set.mem_singleton_iff] at hz
              subst z
              exact ⟨w, Finset.mem_singleton_self _, rfl⟩
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [hyw, hwpos, show (K.markedEdgeChain point).vertex j = K.position v by
          rw [K.markedEdgeChain_vertex_original point i, hi]]
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
      · rw [hxv]
        rw [show
          ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.subordinateTo K).cellCarrier u =
            (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.cellCarrier u from
          (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.subordinateTo_cellCarrier K u]
        exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
          rw [hwpos, K.markedEdgeChain_vertex_original point i, hi]⟩
    · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
      obtain ⟨i, hi⟩ := K.exists_edgeAt e
      have hsegment : segment ℝ
          ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).castSucc)
          ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).succ) =
          K.cellCarrier s := by
        rw [K.markedEdgeChain_segment point i, hi]
      obtain ⟨u, hu, hxu, huSegment⟩ :=
        (K.markedEdgeChain point).exists_face_on_segment
          (K.markedEdgeChainIndex point i) (hsegment.symm ▸ hxs)
      refine ⟨u, ?_, hxu⟩
      apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hu, s, hs, ?_⟩
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _

/-- Every point of an original graph face is covered by a marked-subdivision face lying in that
same original face. -/
theorem exists_markedEdgeSubdivision_face_at (point : P → Plane)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) {x : Plane}
    (hxs : x ∈ K.cellCarrier s) :
    ∃ u ∈ (K.markedEdgeSubdivision point).simplexes,
      x ∈ (K.markedEdgeSubdivision point).cellCarrier u ∧
      (K.markedEdgeSubdivision point).cellCarrier u ⊆ K.cellCarrier s := by
  have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
  have hsle := hgraph s hs
  rcases (show s.card = 1 ∨ s.card = 2 by omega) with hsone | hstwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
    have hxv : x = K.position v := by
      simpa [PlaneComplex.cellCarrier] using hxs
    obtain ⟨i, hi⟩ := K.exists_vertexAt v
    let j : Fin ((K.markedEdgeChain point).n + 1) :=
      ⟨2 * Fintype.card K.EdgeFace + Fintype.card P + i.val, by
        change 2 * Fintype.card K.EdgeFace + Fintype.card P + i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
        omega⟩
    obtain ⟨w, hwpos, hwface⟩ :=
      (K.markedEdgeChain point).exists_arrangementVertex_position_eq j
    let u : Finset (K.markedEdgeChain point).arrangementMesh.Vertex := {w}
    have hu : u ∈ (K.markedEdgeSubdivision point).simplexes := by
      apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hwface, {v}, hs, ?_⟩
      intro y hy
      have hyw : y = (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w := by
        change y ∈ convexHull ℝ
          ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
            (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
              Set (K.markedEdgeChain point).arrangementMesh.Vertex)) at hy
        have himage :
            (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
                Set (K.markedEdgeChain point).arrangementMesh.Vertex) =
              {(K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w} := by
          ext z
          constructor
          · rintro ⟨q, hq, hz⟩
            rw [Finset.mem_singleton.mp hq] at hz
            exact Set.mem_singleton_iff.mpr hz.symm
          · intro hz
            exact ⟨w, Finset.mem_singleton_self _, (Set.mem_singleton_iff.mp hz).symm⟩
        rw [himage, convexHull_singleton] at hy
        exact hy
      rw [hyw, hwpos, show (K.markedEdgeChain point).vertex j = K.position v by
        rw [K.markedEdgeChain_vertex_original point i, hi]]
      exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
    refine ⟨u, hu, ?_, ?_⟩
    · rw [hxv]
      change K.position v ∈ convexHull ℝ
        ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
          (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
            Set (K.markedEdgeChain point).arrangementMesh.Vertex))
      exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
        rw [hwpos, K.markedEdgeChain_vertex_original point i, hi]⟩
    · intro y hy
      have hyw : y = K.position v := by
        change y ∈ convexHull ℝ
          ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
            (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
              Set (K.markedEdgeChain point).arrangementMesh.Vertex)) at hy
        have : y = (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w := by
          have himage :
              (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
                (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
                  Set (K.markedEdgeChain point).arrangementMesh.Vertex) =
                {(K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨q, hq, hz⟩
              rw [Finset.mem_singleton.mp hq] at hz
              exact Set.mem_singleton_iff.mpr hz.symm
            · intro hz
              exact ⟨w, Finset.mem_singleton_self _, (Set.mem_singleton_iff.mp hz).symm⟩
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [this, hwpos, K.markedEdgeChain_vertex_original point i, hi]
      rw [hyw]
      exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
  · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
    obtain ⟨i, hi⟩ := K.exists_edgeAt e
    have hsegment : segment ℝ
        ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).castSucc)
        ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).succ) =
        K.cellCarrier s := by
      rw [K.markedEdgeChain_segment point i, hi]
    obtain ⟨u, hu, hxu, huSegment⟩ :=
      (K.markedEdgeChain point).exists_face_on_segment
        (K.markedEdgeChainIndex point i) (hsegment.symm ▸ hxs)
    have huCarrier :
        (K.markedEdgeSubdivision point).cellCarrier u ⊆ K.cellCarrier s := by
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _
    have huSub : u ∈ (K.markedEdgeSubdivision point).simplexes := by
      apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hu, s, hs, ?_⟩
      exact huCarrier
    refine ⟨u, huSub, hxu, ?_⟩
    exact huCarrier

/-- Restricting a marked edge subdivision to a union of original graph faces preserves exactly
that union. -/
theorem markedEdgeSubdivision_restrictToSet_support_eq (point : P → Plane)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) (A : Set Plane)
    (hA : ∀ x ∈ A, ∃ s ∈ K.simplexes,
      x ∈ K.cellCarrier s ∧ K.cellCarrier s ⊆ A) :
    ((K.markedEdgeSubdivision point).restrictToSet A).support = A := by
  apply Set.Subset.antisymm
  · exact (K.markedEdgeSubdivision point).restrictToSet_support_subset A
  · intro x hx
    obtain ⟨s, hs, hxs, hsA⟩ := hA x hx
    obtain ⟨u, hu, hxu, huSub⟩ :=
      K.exists_markedEdgeSubdivision_face_at point hgraph hs hxs
    rw [PlaneComplex.support]
    simp only [Set.mem_iUnion]
    exact ⟨u, (K.markedEdgeSubdivision point).mem_restrictToSet_simplexes_iff A |>.mpr
      ⟨hu, huSub.trans hsA⟩, hxu⟩

theorem markedEdgeSubdivision_subdivides (point : P → Plane)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    (K.markedEdgeSubdivision point).Subdivides K :=
  (K.markedEdgeArrangement point).subordinateTo_subdivides K
    (K.markedEdgeSubdivision_support_eq point hgraph)

/-- The `markedEdgeChainMarkIndex` declaration. -/
noncomputable def markedEdgeChainMarkIndex (point : P → Plane) (p : P) :
    Fin ((K.markedEdgeChain point).n + 1) :=
  ⟨2 * Fintype.card K.EdgeFace + (markEquiv p).val, by
    change 2 * Fintype.card K.EdgeFace + (markEquiv p).val <
      2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
    omega⟩

theorem markedEdgeArrangement_monochromatic_vertical (point : P → Plane) (p : P) :
    (K.markedEdgeChain point).arrangementMesh.IsMonochromatic
      (BrokenLineData.verticalLine (point p)) := by
  have h := (K.markedEdgeChain point).arrangementMesh_monochromatic_verticalLine
    (K.markedEdgeChainMarkIndex point p)
  have hj : (K.markedEdgeChain point).vertex (K.markedEdgeChainMarkIndex point p) =
      point p := K.markedEdgeChain_vertex_mark point p
  rwa [hj] at h

theorem markedEdgeArrangement_monochromatic_horizontal (point : P → Plane) (p : P) :
    (K.markedEdgeChain point).arrangementMesh.IsMonochromatic
      (BrokenLineData.horizontalLine (point p)) := by
  have h := (K.markedEdgeChain point).arrangementMesh_monochromatic_horizontalLine
    (K.markedEdgeChainMarkIndex point p)
  have hj : (K.markedEdgeChain point).vertex (K.markedEdgeChainMarkIndex point p) =
      point p := K.markedEdgeChain_vertex_mark point p
  rwa [hj] at h

/-- Every arrangement face lies on one side of a marked affine parameter on an original edge. -/
theorem markedFace_parameter_side (point : P → Plane) (p : P)
    (i : Fin (Fintype.card K.EdgeFace)) (r : ℝ)
    (hpoint : point p = AffineMap.lineMap (K.position (K.edgeFirst i))
      (K.position (K.edgeSecond i)) r)
    {u : Finset (K.markedEdgeChain point).arrangementMesh.Vertex}
    (hu : u ∈ (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.simplexes) :
    (∀ v ∈ u, K.edgeParameter i
        ((K.markedEdgeChain point).arrangementMesh.position v) ≤ r) ∨
      (∀ v ∈ u, r ≤ K.edgeParameter i
        ((K.markedEdgeChain point).arrangementMesh.position v)) := by
  let M := (K.markedEdgeChain point).arrangementMesh
  obtain ⟨-, T, hT, huT⟩ := M.mem_faces_iff.mp hu
  unfold edgeParameter
  split_ifs with hx
  · have hmono := K.markedEdgeArrangement_monochromatic_vertical point p
    rcases hmono T hT with hnonneg | hnonpos
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0
      · right
        intro v hv
        apply normalized_ge_of_line_nonneg hΔ
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 0 - point p 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hΔ) (sub_ne_zero.mpr hx.symm)
        left
        intro v hv
        apply normalized_le_of_line_nonneg_of_neg hΔ'
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 0 - point p 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0
      · left
        intro v hv
        apply normalized_le_of_line_nonpos hΔ
        have hline := hnonpos v (huT hv)
        change M.position v 0 - point p 0 ≤ 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hΔ) (sub_ne_zero.mpr hx.symm)
        right
        intro v hv
        apply normalized_ge_of_line_nonpos_of_neg hΔ'
        have hline := hnonpos v (huT hv)
        change M.position v 0 - point p 0 ≤ 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
  · have hxy : K.position (K.edgeFirst i) 1 ≠ K.position (K.edgeSecond i) 1 := by
      intro hy
      apply K.position_injective.ne (K.edgeFirst_ne_edgeSecond i)
      exact plane_ext (not_ne_iff.mp hx) hy
    have hmono := K.markedEdgeArrangement_monochromatic_horizontal point p
    rcases hmono T hT with hnonneg | hnonpos
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1
      · right
        intro v hv
        apply normalized_ge_of_line_nonneg hΔ
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 1 - point p 1 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hΔ) (sub_ne_zero.mpr hxy.symm)
        left
        intro v hv
        apply normalized_le_of_line_nonneg_of_neg hΔ'
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 1 - point p 1 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1
      · left
        intro v hv
        apply normalized_le_of_line_nonpos hΔ
        have hline := hnonpos v (huT hv)
        change M.position v 1 - point p 1 ≤ 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hΔ) (sub_ne_zero.mpr hxy.symm)
        right
        intro v hv
        apply normalized_ge_of_line_nonpos_of_neg hΔ'
        have hline := hnonpos v (huT hv)
        change M.position v 1 - point p 1 ≤ 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline

theorem markedFaceCarrier_parameter_side (point : P → Plane) (p : P)
    (i : Fin (Fintype.card K.EdgeFace)) (r : ℝ)
    (hpoint : point p = AffineMap.lineMap (K.position (K.edgeFirst i))
      (K.position (K.edgeSecond i)) r)
    {u : Finset (K.markedEdgeChain point).arrangementMesh.Vertex}
    (hu : u ∈ (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.simplexes) :
    (∀ x ∈ (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.cellCarrier u,
        K.edgeParameter i x ≤ r) ∨
      (∀ x ∈ (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.cellCarrier u,
        r ≤ K.edgeParameter i x) := by
  rcases K.markedFace_parameter_side point p i r hpoint hu with hle | hge
  · left
    intro x hx
    apply convexHull_min ?_ ((convex_Iic r).affine_preimage (K.edgeParameter i)) hx
    rintro y ⟨v, hv, rfl⟩
    exact hle v hv
  · right
    intro x hx
    apply convexHull_min ?_ ((convex_Ici r).affine_preimage (K.edgeParameter i)) hx
    rintro y ⟨v, hv, rfl⟩
    exact hge v hv

/-- In a finite complex covering an axis segment, a subsegment with no complex vertex in its
relative interior is contained in one face. -/
theorem exists_face_containing_axis_segment_of_no_vertex
    (L : PlaneComplex) {n a b : ℝ}
    (hn : 0 ≤ n) (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ n)
    (hsupport : L.support = segment ℝ (planePoint 0 0) (planePoint n 0))
    (hcard : ∀ s ∈ L.simplexes, s.card ≤ 2)
    (havoid : ∀ v : L.Vertex, L.position v 0 ≤ a ∨ b ≤ L.position v 0) :
    ∃ s ∈ L.simplexes,
      segment ℝ (planePoint a 0) (planePoint b 0) ⊆ L.cellCarrier s := by
  have axis_mem {c d r : ℝ} (hr : r ∈ segment ℝ c d) :
      planePoint r 0 ∈ segment ℝ (planePoint c 0) (planePoint d 0) := by
    rw [segment_eq_image_lineMap] at hr ⊢
    obtain ⟨t, ht, rfl⟩ := hr
    refine ⟨t, ht, ?_⟩
    ext k
    fin_cases k <;> simp [planePoint, AffineMap.lineMap_apply_module]
  let q := (a + b) / 2
  have hq : q ∈ Set.Icc (0 : ℝ) n := by
    constructor <;> dsimp [q] <;> linarith
  have hqReal : q ∈ segment ℝ (0 : ℝ) n := by
    rwa [segment_eq_Icc hn]
  have hqPlane : planePoint q 0 ∈ L.support := by
    rw [hsupport]
    exact axis_mem hqReal
  rw [PlaneComplex.support] at hqPlane
  simp only [Set.mem_iUnion] at hqPlane
  obtain ⟨s, hs, hqs⟩ := hqPlane
  by_cases habEq : a = b
  · subst b
    have hqa : q = a := by simp [q]
    rw [hqa] at hqs
    refine ⟨s, hs, ?_⟩
    intro x hx
    have hxa : x = planePoint a 0 := by simpa using hx
    rwa [hxa]
  have hablt : a < b := lt_of_le_of_ne hab habEq
  have hqne (v : L.Vertex) : planePoint q 0 ≠ L.position v := by
    intro heq
    have hcoord := congrArg (fun z : Plane => z 0) heq
    rcases havoid v with hv | hv <;> dsimp [q] at hcoord <;> linarith
  have hscard : s.card = 2 := by
    have hspos : 0 < s.card := Finset.card_pos.mpr (L.nonempty_of_mem s hs)
    have hsle := hcard s hs
    have : s.card = 1 ∨ s.card = 2 := by omega
    rcases this with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have : planePoint q 0 = L.position v := by
        simpa [PlaneComplex.cellCarrier] using hqs
      exact (hqne v this).elim
    · exact hstwo
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hscard
  have axis_eq (z : L.Vertex) (hz : z ∈ ({v, w} : Finset L.Vertex)) :
      L.position z = planePoint (L.position z 0) 0 := by
    have hzCarrier : L.position z ∈ L.cellCarrier ({v, w} : Finset L.Vertex) :=
      subset_convexHull ℝ _ ⟨z, hz, rfl⟩
    have hzSupport := L.cellCarrier_subset_support hs hzCarrier
    rw [hsupport, segment_eq_image_lineMap] at hzSupport
    obtain ⟨t, ht, hzt⟩ := hzSupport
    rw [← hzt]
    ext k
    fin_cases k <;> simp [planePoint, AffineMap.lineMap_apply_module]
  have hvAxis := axis_eq v (by simp)
  have hwAxis := axis_eq w (by simp)
  have hqSeg : planePoint q 0 ∈
      segment ℝ (planePoint (L.position v 0) 0) (planePoint (L.position w 0) 0) := by
    rw [← hvAxis, ← hwAxis, ← convexHull_pair]
    change planePoint q 0 ∈ convexHull ℝ
      (L.position '' (({v, w} : Finset L.Vertex) : Set L.Vertex)) at hqs
    have himage : L.position '' (({v, w} : Finset L.Vertex) : Set L.Vertex) =
        {L.position v, L.position w} := by
      ext z
      simp [eq_comm]
    rwa [himage] at hqs
  rw [segment_eq_image_lineMap] at hqSeg
  obtain ⟨t, ht, hqt⟩ := hqSeg
  have hqcoord := congrArg (fun z : Plane => z 0) hqt
  simp only [Fin.isValue, planePoint, AffineMap.lineMap_apply_module, PiLp.add_apply,
    PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul] at hqcoord
  rcases havoid v with hvLow | hvHigh <;> rcases havoid w with hwLow | hwHigh
  · have hqle : q ≤ a := by
      rw [← hqcoord]
      calc
        (1 - t) * L.position v 0 + t * L.position w 0 ≤ (1 - t) * a + t * a := by
          gcongr <;> linarith [ht.1, ht.2]
        _ = a := by ring
    dsimp [q] at hqle
    linarith
  · have hsub : segment ℝ (planePoint a 0) (planePoint b 0) ⊆
        segment ℝ (planePoint (L.position v 0) 0) (planePoint (L.position w 0) 0) := by
      apply (convex_segment _ _).segment_subset
      · apply axis_mem
        rw [segment_eq_Icc ((hvLow.trans hab).trans hwHigh)]
        exact ⟨hvLow, hab.trans hwHigh⟩
      · apply axis_mem
        rw [segment_eq_Icc ((hvLow.trans hab).trans hwHigh)]
        exact ⟨hvLow.trans hab, hwHigh⟩
    refine ⟨{v, w}, hs, ?_⟩
    rw [PlaneComplex.cellCarrier, show L.position '' (({v, w} : Finset L.Vertex) : Set L.Vertex) =
        {L.position v, L.position w} by ext z; simp [eq_comm], convexHull_pair, hvAxis, hwAxis]
    exact hsub
  · have hsub : segment ℝ (planePoint a 0) (planePoint b 0) ⊆
        segment ℝ (planePoint (L.position w 0) 0) (planePoint (L.position v 0) 0) := by
      apply (convex_segment _ _).segment_subset
      · apply axis_mem
        rw [segment_eq_Icc ((hwLow.trans hab).trans hvHigh)]
        exact ⟨hwLow, hab.trans hvHigh⟩
      · apply axis_mem
        rw [segment_eq_Icc ((hwLow.trans hab).trans hvHigh)]
        exact ⟨hwLow.trans hab, hvHigh⟩
    refine ⟨{v, w}, hs, ?_⟩
    rw [PlaneComplex.cellCarrier, show L.position '' (({v, w} : Finset L.Vertex) : Set L.Vertex) =
        {L.position v, L.position w} by ext z; simp [eq_comm], convexHull_pair,
      hvAxis, hwAxis]
    simpa only [segment_symm] using hsub
  · have hbq : b ≤ q := by
      rw [← hqcoord]
      calc
        b ≤ (1 - t) * b + t * b := by ring_nf; exact le_rfl
        _ ≤ (1 - t) * L.position v 0 + t * L.position w 0 := by
          gcongr <;> linarith [ht.1, ht.2]
    dsimp [q] at hbq
    linarith

/-- A genuine simplex contained in a graph face has at most two vertices. -/
theorem card_le_two_of_cellCarrier_subset_face
    {L K : PlaneComplex} {u : Finset L.Vertex} (hu : u ∈ L.simplexes)
    {t : Finset K.Vertex} (ht : t ∈ K.simplexes) (htcard : t.card ≤ 2)
    (hut : L.cellCarrier u ⊆ K.cellCarrier t) : u.card ≤ 2 := by
  by_contra hnot
  have hucard : u.card = 3 := by
    have := L.card_le_three u hu
    omega
  have hspanU : affineSpan ℝ (Set.range (fun v : u => L.position v)) = ⊤ :=
    ((L.affineIndependent u hu).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by
      simp [hucard, Plane])
  have hsubset : Set.range (fun v : u => L.position v) ⊆
      (affineSpan ℝ (K.position '' (t : Set K.Vertex)) : Set Plane) := by
    rintro x ⟨v, rfl⟩
    apply convexHull_subset_affineSpan (K.position '' (t : Set K.Vertex))
    apply hut
    exact subset_convexHull ℝ _ ⟨v.1, v.2, rfl⟩
  have hle : affineSpan ℝ (Set.range (fun v : u => L.position v)) ≤
      affineSpan ℝ (K.position '' (t : Set K.Vertex)) := affineSpan_le.mpr hsubset
  rw [hspanU] at hle
  have hspanT : affineSpan ℝ (K.position '' (t : Set K.Vertex)) = ⊤ := top_unique hle
  have himage : Set.range (fun v : t => K.position v) =
      K.position '' (t : Set K.Vertex) := by
    ext x
    simp
  rw [← himage] at hspanT
  have htthree :=
    (K.affineIndependent t ht).affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hspanT
  have : t.card = 3 := by simpa [Plane] using htthree
  omega

/-- Every prescribed mark in the graph support becomes a zero-face of the marked subdivision. -/
theorem exists_markedEdgeSubdivision_vertex (point : P → Plane) (p : P)
    (hp : point p ∈ K.support) :
    ∃ w : (K.markedEdgeSubdivision point).Vertex,
      ({w} : Finset (K.markedEdgeSubdivision point).Vertex) ∈
        (K.markedEdgeSubdivision point).simplexes ∧
      (K.markedEdgeSubdivision point).position w = point p := by
  obtain ⟨w, hwpos, hwface⟩ :=
    (K.markedEdgeChain point).exists_arrangementVertex_position_eq
      (K.markedEdgeChainMarkIndex point p)
  have hchain : (K.markedEdgeChain point).vertex
      (K.markedEdgeChainMarkIndex point p) = point p := by
    exact K.markedEdgeChain_vertex_mark point p
  rw [PlaneComplex.support] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨s, hs, hps⟩ := hp
  refine ⟨w, ?_, ?_⟩
  · apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
      |>.mem_subordinateTo_simplexes_iff K).mpr
    refine ⟨hwface, s, hs, ?_⟩
    intro y hy
    have hyw : y = (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w := by
      change y ∈ convexHull ℝ
        ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
          (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
            Set (K.markedEdgeChain point).arrangementMesh.Vertex)) at hy
      have himage : (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
          (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
            Set (K.markedEdgeChain point).arrangementMesh.Vertex) =
          {(K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w} := by
        ext z
        constructor
        · rintro ⟨q, hq, rfl⟩
          rw [Finset.mem_singleton.mp hq]
          exact Set.mem_singleton _
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          exact ⟨w, Finset.mem_singleton_self _, rfl⟩
      rw [himage, convexHull_singleton] at hy
      exact hy
    rw [hyw, hwpos, hchain]
    exact hps
  · exact hwpos.trans hchain

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
