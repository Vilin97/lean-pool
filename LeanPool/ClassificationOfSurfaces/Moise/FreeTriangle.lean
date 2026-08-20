/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ElementaryMove
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Interval.Set.Infinite

/-!
# Free triangles in finite planar meshes

This file formalizes Moise Chapter 3, Theorem 3 in the form needed by the polygonal
Schoenflies induction.  A finite planar triangle mesh with infinite frontier has an edge incident
to exactly one triangle, hence a free triangle that can be removed by a supported ambient move.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace TriangleMesh

variable (M : TriangleMesh)

/-- The geometric carrier of a maximal triangle. -/
def triangleCarrier (t : Finset M.Vertex) : Set Plane :=
  convexHull ℝ (M.position '' (t : Set M.Vertex))

/-- The two-element faces occurring in maximal triangles. -/
def edges : Finset (Finset M.Vertex) :=
  M.triangles.biUnion fun t => t.powersetCard 2

/-- Maximal triangles incident to an edge. -/
def incidentTriangles (e : Finset M.Vertex) : Finset (Finset M.Vertex) :=
  M.triangles.filter fun t => e ⊆ t

/-- A boundary edge is incident to exactly one maximal triangle. -/
def IsBoundaryEdge (e : Finset M.Vertex) : Prop :=
  e ∈ M.edges ∧ (M.incidentTriangles e).card = 1

/-- A weakly free triangle contains an incidence-one edge.  This is the boundary-edge precursor
used to find Moise's geometrically free triangles; by itself it does not exclude an additional
isolated boundary vertex. -/
def IsFreeTriangle (t : Finset M.Vertex) : Prop :=
  t ∈ M.triangles ∧ ∃ e, M.IsBoundaryEdge e ∧ e ⊆ t

/-- The three abstract edges of a maximal triangle. -/
def triangleEdges (t : Finset M.Vertex) : Finset (Finset M.Vertex) :=
  t.powersetCard 2

/-- The boundary edges belonging to a maximal triangle. -/
noncomputable def boundaryEdges (t : Finset M.Vertex) : Finset (Finset M.Vertex) :=
  by
    classical
    exact (M.triangleEdges t).filter M.IsBoundaryEdge

/-- All incidence-one edges of a finite triangle mesh. -/
noncomputable def allBoundaryEdges : Finset (Finset M.Vertex) := by
  classical
  exact M.edges.filter M.IsBoundaryEdge

theorem mem_allBoundaryEdges_iff {e : Finset M.Vertex} :
    e ∈ M.allBoundaryEdges ↔ M.IsBoundaryEdge e := by
  classical
  simp [allBoundaryEdges, IsBoundaryEdge]

/-- The finite union of the geometric carriers of all incidence-one mesh edges. -/
noncomputable def boundaryCarrier : Set Plane :=
  ⋃ e ∈ M.allBoundaryEdges, convexHull ℝ (M.position '' (e : Set M.Vertex))

theorem isCompact_boundaryCarrier : IsCompact M.boundaryCarrier := by
  classical
  exact M.allBoundaryEdges.finite_toSet.isCompact_biUnion fun e _ =>
    (e.finite_toSet.image M.position).isCompact_convexHull ℝ

theorem card_of_mem_edges {e : Finset M.Vertex} (he : e ∈ M.edges) : e.card = 2 := by
  obtain ⟨t, _, het⟩ := Finset.mem_biUnion.mp he
  exact (Finset.mem_powersetCard.mp het).2

theorem mem_incidentTriangles_iff {e t : Finset M.Vertex} :
    t ∈ M.incidentTriangles e ↔ t ∈ M.triangles ∧ e ⊆ t := by
  simp [incidentTriangles]

theorem frontier_biUnion_subset (F : Finset (Finset M.Vertex)) :
    frontier (⋃ t ∈ F, M.triangleCarrier t) ⊆
      ⋃ t ∈ F, frontier (M.triangleCarrier t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert t F ht ih =>
      simpa [ht] using (frontier_union_subset (M.triangleCarrier t)
        (⋃ u ∈ F, M.triangleCarrier u)).trans
          (Set.union_subset_union Set.inter_subset_left (Set.inter_subset_right.trans ih))

/-- Index the vertices of a maximal triangle by `Fin 3`. -/
noncomputable def triangleIndexEquiv {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    Fin 3 ≃ t :=
  Fintype.equivOfCardEq (by simpa using (M.card_triangle t ht).symm)

/-- The vertices of a maximal planar triangle form an affine basis of the plane. -/
noncomputable def triangleAffineBasis {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    AffineBasis (Fin 3) ℝ Plane := by
  let e := M.triangleIndexEquiv ht
  let p : Fin 3 → Plane := fun i => M.position (e i)
  have hp : AffineIndependent ℝ p :=
    (M.affineIndependent_triangle t ht).comp_embedding e.toEmbedding
  refine ⟨p, hp, ?_⟩
  apply hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp [Plane]

theorem range_triangleAffineBasis {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    Set.range (M.triangleAffineBasis ht) = M.position '' (t : Set M.Vertex) := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨M.triangleIndexEquiv ht i, (M.triangleIndexEquiv ht i).property, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    let w : t := ⟨v, hv⟩
    refine ⟨(M.triangleIndexEquiv ht).symm w, ?_⟩
    change M.position (M.triangleIndexEquiv ht ((M.triangleIndexEquiv ht).symm w)) =
      M.position v
    rw [Equiv.apply_symm_apply]

/-- The edge opposite an indexed vertex of a maximal triangle. -/
noncomputable def triangleEdgeOpposite {t : Finset M.Vertex} (ht : t ∈ M.triangles)
    (i : Fin 3) : Finset M.Vertex :=
  t.erase (M.triangleIndexEquiv ht i)

theorem triangleEdgeOpposite_card {t : Finset M.Vertex} (ht : t ∈ M.triangles) (i : Fin 3) :
    (M.triangleEdgeOpposite ht i).card = 2 := by
  rw [triangleEdgeOpposite, Finset.card_erase_of_mem (M.triangleIndexEquiv ht i).property,
    M.card_triangle t ht]

theorem triangleEdgeOpposite_subset {t : Finset M.Vertex} (ht : t ∈ M.triangles) (i : Fin 3) :
    M.triangleEdgeOpposite ht i ⊆ t :=
  Finset.erase_subset _ _

theorem image_compl_eq_triangleEdgeOpposite {t : Finset M.Vertex} (ht : t ∈ M.triangles)
    (i : Fin 3) :
    M.triangleAffineBasis ht '' ({i}ᶜ : Set (Fin 3)) =
      M.position '' (M.triangleEdgeOpposite ht i : Set M.Vertex) := by
  ext p
  constructor
  · rintro ⟨j, hji, rfl⟩
    refine ⟨M.triangleIndexEquiv ht j, ?_, rfl⟩
    exact Finset.mem_erase.mpr ⟨by simpa using hji, (M.triangleIndexEquiv ht j).property⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' := Finset.mem_erase.mp hv
    let w : t := ⟨v, hv'.2⟩
    refine ⟨(M.triangleIndexEquiv ht).symm w, ?_, ?_⟩
    · intro heq
      apply hv'.1
      have h := congrArg (fun j => ((M.triangleIndexEquiv ht j : t) : M.Vertex)) heq
      simpa [w] using h
    · change M.position (M.triangleIndexEquiv ht ((M.triangleIndexEquiv ht).symm w)) =
        M.position v
      rw [Equiv.apply_symm_apply]

/-- A nonvertex point on the frontier of a maximal triangle lies in one of its edges. -/
theorem exists_edge_of_mem_frontier_triangle {t : Finset M.Vertex} (ht : t ∈ M.triangles)
    {p : Plane} (hp : p ∈ frontier (M.triangleCarrier t)) :
    ∃ e : Finset M.Vertex, e.card = 2 ∧ e ⊆ t ∧
      p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
  let b := M.triangleAffineBasis ht
  have hrange := M.range_triangleAffineBasis ht
  have hclosed : IsClosed (M.triangleCarrier t) :=
    (t.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hpCarrier : p ∈ M.triangleCarrier t := hclosed.frontier_subset hp
  have hpNotInterior : p ∉ interior (M.triangleCarrier t) :=
    (mem_frontier_iff_notMem_interior hpCarrier).mp hp
  have hpHull : p ∈ convexHull ℝ (Set.range b) := by
    simpa only [b, hrange, triangleCarrier] using hpCarrier
  have hnonneg : ∀ i, 0 ≤ b.coord i p := by
    rw [b.convexHull_eq_nonneg_coord] at hpHull
    exact hpHull
  have hnotpos : ¬∀ i, 0 < b.coord i p := by
    intro hpos
    apply hpNotInterior
    rw [triangleCarrier, ← hrange, b.interior_convexHull]
    exact hpos
  push Not at hnotpos
  obtain ⟨i, hi⟩ := hnotpos
  have hzero : b.coord i p = 0 := le_antisymm hi (hnonneg i)
  let s : Finset (Fin 3) := Finset.univ.erase i
  have hsum : ∑ j ∈ s, b.coord j p = 1 := by
    have htotal := b.sum_coord_apply_eq_one p
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hzero, add_zero] at htotal
    exact htotal
  have hcenter : s.centerMass (fun j => b.coord j p) b = p := by
    rw [s.centerMass_eq_of_sum_1 _ hsum]
    calc
      (∑ j ∈ s, b.coord j p • b j) = ∑ j, b.coord j p • b j := by
        dsimp [s]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hzero, zero_smul, add_zero]
      _ = p := b.linear_combination_coord_eq_self p
  have hpEdge : p ∈ convexHull ℝ (b '' ({i}ᶜ : Set (Fin 3))) := by
    rw [← hcenter]
    apply s.centerMass_mem_convexHull
    · intro j _
      exact hnonneg j
    · rw [hsum]
      norm_num
    · intro j hj
      exact ⟨j, by simpa [s] using (Finset.mem_erase.mp hj).1, rfl⟩
  refine ⟨M.triangleEdgeOpposite ht i, M.triangleEdgeOpposite_card ht i,
    M.triangleEdgeOpposite_subset ht i, ?_⟩
  rwa [M.image_compl_eq_triangleEdgeOpposite ht i] at hpEdge

theorem oppositeCoord_eq_zero_of_mem_oppositeEdge (T : M.Triangle) (k : Fin 3)
    {p : Plane}
    (hp : p ∈ convexHull ℝ ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane)) :
    M.oppositeCoord T k p = 0 := by
  have h := hp
  rw [← M.parent_inter_oppositeCoord_zero T k] at h
  exact h.2

/-- At a nonvertex point of an edge, the two barycentric coordinates along the edge are positive. -/
theorem oppositeCoord_pos_of_mem_oppositeEdge_of_not_vertex (T : M.Triangle) (k j : Fin 3)
    (hjk : j ≠ k) {p : Plane}
    (hp : p ∈ convexHull ℝ ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane))
    (hpv : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i)) :
    0 < M.oppositeCoord T j p := by
  have hpParent : p ∈ convexHull ℝ (M.position '' (T.1 : Set M.Vertex)) := by
    rw [← M.parent_inter_oppositeCoord_zero T k] at hp
    exact hp.1
  have hnonneg := M.oppositeCoord_nonneg_of_mem_parent T j hpParent
  apply lt_of_le_of_ne hnonneg
  intro hzero'
  have hzeroj : M.oppositeCoord T j p = 0 := hzero'.symm
  have hzerok := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k hp
  let b := affineBasisOfTriangle (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  have hsum : b.coord 0 p + b.coord 1 p + b.coord 2 p = 1 := by
    simpa only [Fin.sum_univ_three] using b.sum_coord_apply_eq_one p
  change b.coord j p = 0 at hzeroj
  change b.coord k p = 0 at hzerok
  have eq_vertex_of_two_zero (r : Fin 3)
      (hz : ∀ l : Fin 3, l ≠ r → M.oppositeCoord T l p = 0) :
      p = M.position (M.orderedVertex T r) := by
    have hcoordr : M.oppositeCoord T r p = 1 := by
      fin_cases r
      · have h1 := hz 1 (by decide)
        have h2 := hz 2 (by decide)
        change b.coord 1 p = 0 at h1
        change b.coord 2 p = 0 at h2
        change b.coord 0 p = 1
        linarith
      · have h0 := hz 0 (by decide)
        have h2 := hz 2 (by decide)
        change b.coord 0 p = 0 at h0
        change b.coord 2 p = 0 at h2
        change b.coord 1 p = 1
        linarith
      · have h0 := hz 0 (by decide)
        have h1 := hz 1 (by decide)
        change b.coord 0 p = 0 at h0
        change b.coord 1 p = 0 at h1
        change b.coord 2 p = 1
        linarith
    apply b.ext_elem
    intro l
    change M.oppositeCoord T l p =
      M.oppositeCoord T l (M.position (M.orderedVertex T r))
    rw [M.oppositeCoord_vertex]
    by_cases hl : l = r
    · subst l
      simpa using hcoordr
    · simpa [hl] using hz l hl
  have hpv' : ∃ r : Fin 3, p = M.position (M.orderedVertex T r) := by
    fin_cases k <;> fin_cases j
    · exact (hjk rfl).elim
    · refine ⟨2, eq_vertex_of_two_zero 2 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, Fin.reduceEq,
          not_false_eq_true, Fin.mk_one, Fin.reduceFinMk, not_true_eq_false] at hl ⊢ <;>
        assumption
    · refine ⟨1, eq_vertex_of_two_zero 1 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true,
          Fin.mk_one, not_true_eq_false, Fin.reduceFinMk, Fin.reduceEq] at hl ⊢ <;>
        assumption
    · refine ⟨2, eq_vertex_of_two_zero 2 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, Fin.reduceEq,
          not_false_eq_true, Fin.mk_one, Fin.reduceFinMk, not_true_eq_false] at hl ⊢ <;>
        assumption
    · exact (hjk rfl).elim
    · refine ⟨0, eq_vertex_of_two_zero 0 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, not_true_eq_false, Fin.mk_one,
          one_ne_zero, not_false_eq_true, Fin.reduceFinMk, Fin.reduceEq] at hl ⊢ <;>
        assumption
    · refine ⟨1, eq_vertex_of_two_zero 1 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true,
          Fin.mk_one, not_true_eq_false, Fin.reduceFinMk, Fin.reduceEq] at hl ⊢ <;>
        assumption
    · refine ⟨0, eq_vertex_of_two_zero 0 (fun l hl => ?_)⟩
      fin_cases l <;>
        simp only [Fin.zero_eta, Fin.isValue, ne_eq, not_true_eq_false, Fin.mk_one,
          one_ne_zero, not_false_eq_true, Fin.reduceFinMk, Fin.reduceEq] at hl ⊢ <;>
        assumption
    · exact (hjk rfl).elim
  obtain ⟨r, hr⟩ := hpv'
  exact hpv r hr

theorem oppositeCoord_smul_eq_of_same_edge (T U : M.Triangle) (kT kU : Fin 3)
    (hedge : M.oppositeEdgePoints T kT = M.oppositeEdgePoints U kU) :
    (M.oppositeCoord T kT (M.position (M.orderedVertex U kU))) •
        M.oppositeCoord U kU = M.oppositeCoord T kT := by
  let bU := affineBasisOfTriangle (M.position ∘ M.orderedVertex U)
    (M.orderedVertex_affineIndependent U)
  apply AffineMap.ext_on bU.tot
  rintro x ⟨i, rfl⟩
  change M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) *
      M.oppositeCoord U kU (M.position (M.orderedVertex U i)) =
    M.oppositeCoord T kT (M.position (M.orderedVertex U i))
  by_cases hi : i = kU
  · subst i
    simp
  · have hmemU : M.position (M.orderedVertex U i) ∈ M.oppositeEdgePoints U kU := by
      unfold oppositeEdgePoints
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, rfl⟩
    have hmemT : M.position (M.orderedVertex U i) ∈ M.oppositeEdgePoints T kT := by
      rw [hedge]
      exact hmemU
    have hz := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T kT
      (subset_convexHull ℝ _ hmemT)
    simp [M.oppositeCoord_vertex U kU i, Ne.symm hi, hz]

theorem oppositeCoord_ne_zero_of_same_edge (T U : M.Triangle) (kT kU : Fin 3)
    (hedge : M.oppositeEdgePoints T kT = M.oppositeEdgePoints U kU) :
    M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) ≠ 0 := by
  intro hc
  have hrel := M.oppositeCoord_smul_eq_of_same_edge T U kT kU hedge
  rw [hc, zero_smul] at hrel
  have h := congrArg (fun f : Plane →ᵃ[ℝ] ℝ =>
    f (M.position (M.orderedVertex T kT))) hrel
  simp at h

theorem interior_triangleCarrier (T : M.Triangle) :
    interior (M.triangleCarrier T.1) =
      {p | ∀ i : Fin 3, 0 < M.oppositeCoord T i p} := by
  let b := affineBasisOfTriangle (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  have hrange : Set.range b = M.position '' (T.1 : Set M.Vertex) := by
    change Set.range (M.position ∘ M.orderedVertex T) = _
    rw [Set.range_comp, M.range_orderedVertex T]
  rw [triangleCarrier, ← hrange, b.interior_convexHull]
  rfl

theorem interior_triangleCarrier_nonempty (T : M.Triangle) :
    (interior (M.triangleCarrier T.1)).Nonempty := by
  let b := M.triangleAffineBasis T.2
  have hspan : affineSpan ℝ (Set.range b) = ⊤ := b.tot
  have hnonempty := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  simpa only [triangleCarrier, b, M.range_triangleAffineBasis T.2] using hnonempty

/-- A nondegenerate closed triangle is the closure of its Euclidean interior. -/
theorem closure_interior_triangleCarrier (T : M.Triangle) :
    closure (interior (M.triangleCarrier T.1)) = M.triangleCarrier T.1 := by
  unfold triangleCarrier
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
    (M.interior_triangleCarrier_nonempty T)]
  exact (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ |>.closure_eq

/-- The interior of a maximal triangle misses the carrier of every proper face of that
triangle.  The formulation with an arbitrary set of at most two vertices is convenient when
restricting a mesh along an existing edge. -/
theorem disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two
    (T : M.Triangle) {s : Finset M.Vertex} (hs : s ⊆ T.1) (hcard : s.card ≤ 2) :
    Disjoint (interior (M.triangleCarrier T.1))
      (convexHull ℝ (M.position '' (s : Set M.Vertex))) := by
  have hproper : s ⊂ T.1 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
    intro h
    have := congrArg Finset.card h
    rw [M.card_triangle T.1 T.2] at this
    omega
  obtain ⟨v, hvT, hvNotS⟩ := Finset.exists_of_ssubset hproper
  obtain ⟨k, hkv⟩ : ∃ k : Fin 3, M.orderedVertex T k = v := by
    have hvRange : v ∈ Set.range (M.orderedVertex T) := by
      rw [M.range_orderedVertex T]
      exact hvT
    simpa only [Set.mem_range] using hvRange
  have hsOpposite : M.position '' (s : Set M.Vertex) ⊆
      ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
    rintro p ⟨w, hw, rfl⟩
    obtain ⟨i, hiw⟩ : ∃ i : Fin 3, M.orderedVertex T i = w := by
      have hwRange : w ∈ Set.range (M.orderedVertex T) := by
        rw [M.range_orderedVertex T]
        exact hs hw
      simpa only [Set.mem_range] using hwRange
    change M.position w ∈ M.oppositeEdgePoints T k
    unfold oppositeEdgePoints
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩, ?_⟩
    · intro hik
      apply hvNotS
      rw [← hkv, ← hik, hiw]
      exact hw
    · simp only [Function.comp_apply, hiw]
  rw [Set.disjoint_left]
  intro p hpInterior hpFace
  have hpOpposite : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) :=
    convexHull_mono hsOpposite hpFace
  have hzero := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k hpOpposite
  have hpos : 0 < M.oppositeCoord T k p := by
    rw [M.interior_triangleCarrier T] at hpInterior
    exact hpInterior k
  linarith

/-- The interior of every maximal triangle misses every edge carrier of the mesh, whether or
not that edge belongs to the triangle. -/
theorem disjoint_interior_triangleCarrier_edgeCarrier (T : M.Triangle)
    {e : Finset M.Vertex} (he : e ∈ M.edges) :
    Disjoint (interior (M.triangleCarrier T.1))
      (convexHull ℝ (M.position '' (e : Set M.Vertex))) := by
  obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp he
  have heData := Finset.mem_powersetCard.mp heu
  let U : M.Triangle := ⟨u, hu⟩
  by_cases hTU : T.1 = U.1
  · apply M.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two
      T _ heData.2.le
    rw [hTU]
    exact heData.1
  have hInterCard : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ 2 := by
    by_contra h
    have hcard : (T.1 ∩ U.1 : Finset M.Vertex).card = 3 := by
      have hle : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ T.1.card :=
        Finset.card_le_card Finset.inter_subset_left
      rw [M.card_triangle T.1 T.2] at hle
      omega
    have hinterT : T.1 ∩ U.1 = T.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [hcard, M.card_triangle T.1 T.2])
    have hsubset : T.1 ⊆ U.1 := by
      rw [← hinterT]
      exact Finset.inter_subset_right
    have hEq : T.1 = U.1 := Finset.eq_of_subset_of_card_le hsubset (by
      rw [M.card_triangle T.1 T.2, M.card_triangle U.1 U.2])
    exact hTU hEq
  rw [Set.disjoint_left]
  intro p hpT hpEdge
  have hpU : p ∈ M.triangleCarrier U.1 :=
    convexHull_mono (Set.image_mono heData.1) hpEdge
  have hpInter : p ∈ convexHull ℝ
      (M.position '' ((T.1 ∩ U.1 : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← M.triangle_inter T.1 T.2 U.1 U.2]
    exact ⟨interior_subset hpT, hpU⟩
  exact Set.disjoint_left.mp
    (M.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two T
      Finset.inter_subset_left hInterCard) hpT hpInter

/-- The interior of one maximal triangle misses the full carrier of every distinct maximal
triangle. -/
theorem disjoint_interior_triangleCarrier_triangleCarrier {T U : M.Triangle}
    (hne : T.1 ≠ U.1) :
    Disjoint (interior (M.triangleCarrier T.1)) (M.triangleCarrier U.1) := by
  have hInterCard : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ 2 := by
    by_contra h
    have hcard : (T.1 ∩ U.1 : Finset M.Vertex).card = 3 := by
      have hle : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ T.1.card :=
        Finset.card_le_card Finset.inter_subset_left
      rw [M.card_triangle T.1 T.2] at hle
      omega
    have hsubset : T.1 ⊆ U.1 := by
      have hinterT : T.1 ∩ U.1 = T.1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
          rw [hcard, M.card_triangle T.1 T.2])
      rw [← hinterT]
      exact Finset.inter_subset_right
    have heq : T.1 = U.1 := Finset.eq_of_subset_of_card_le hsubset (by
      rw [M.card_triangle T.1 T.2, M.card_triangle U.1 U.2])
    exact hne heq
  rw [Set.disjoint_left]
  intro p hpT hpU
  have hpInter : p ∈ convexHull ℝ
      (M.position '' ((T.1 ∩ U.1 : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← M.triangle_inter T.1 T.2 U.1 U.2]
    exact ⟨interior_subset hpT, hpU⟩
  exact Set.disjoint_left.mp
    (M.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two T
      Finset.inter_subset_left hInterCard) hpT hpInter

/-- Maximal triangles in a face-to-face mesh have disjoint interiors. -/
theorem eq_of_interior_triangleCarrier_inter_nonempty (T U : M.Triangle)
    (hinterior : (interior (M.triangleCarrier T.1) ∩
      interior (M.triangleCarrier U.1)).Nonempty) : T.1 = U.1 := by
  let f : Finset M.Vertex := T.1 ∩ U.1
  have hfne : f.Nonempty := by
    by_contra hf
    have hfempty : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    obtain ⟨p, hpT, hpU⟩ := hinterior
    have hpInter : p ∈ convexHull ℝ (M.position '' (f : Set M.Vertex)) := by
      rw [show f = T.1 ∩ U.1 by rfl, ← M.triangle_inter T.1 T.2 U.1 U.2]
      exact ⟨interior_subset hpT, interior_subset hpU⟩
    rw [hfempty] at hpInter
    simp at hpInter
  have hfSimplex : f ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨hfne, T.1, T.2, Finset.inter_subset_left⟩
  have hOpenSubset :
      interior (M.triangleCarrier T.1) ∩ interior (M.triangleCarrier U.1) ⊆
        convexHull ℝ (M.position '' (f : Set M.Vertex)) := by
    intro p hp
    rw [show f = T.1 ∩ U.1 by rfl, ← M.triangle_inter T.1 T.2 U.1 U.2]
    exact ⟨interior_subset hp.1, interior_subset hp.2⟩
  have hfInterior :
      (interior (convexHull ℝ (M.position '' (f : Set M.Vertex)))).Nonempty := by
    obtain ⟨p, hp⟩ := hinterior
    exact ⟨p, interior_maximal hOpenSubset (isOpen_interior.inter isOpen_interior) hp⟩
  have hspan : affineSpan ℝ (M.position '' (f : Set M.Vertex)) = ⊤ :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mp hfInterior
  let e : {v // v ∈ f} ↪ {v // v ∈ T.1} :=
    ⟨fun v => ⟨v, Finset.inter_subset_left v.2⟩,
      fun a b hab => by
        apply Subtype.ext
        exact congrArg (fun x : {v // v ∈ T.1} => (x : M.Vertex)) hab⟩
  have hAI : AffineIndependent ℝ (fun v : f => M.position v) :=
    (M.affineIndependent_triangle T.1 T.2).comp_embedding e
  have hrange : Set.range (fun v : f => M.position v) =
      M.position '' (f : Set M.Vertex) := by
    ext p
    simp
  have hfcard : f.card = 3 := by
    have hspan' : affineSpan ℝ (Set.range (fun v : f => M.position v)) = ⊤ := by
      rw [hrange]
      exact hspan
    have := hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hspan'
    rw [Fintype.card_coe] at this
    have hfinrank : Module.finrank ℝ Plane = 2 := by simp [Plane]
    omega
  have hfT : f = T.1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
    rw [hfcard, M.card_triangle T.1 T.2])
  have hfU : f = U.1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
    rw [hfcard, M.card_triangle U.1 U.2])
  exact hfT.symm.trans hfU

theorem disjoint_interior_triangleCarrier {T U : M.Triangle} (hne : T.1 ≠ U.1) :
    Disjoint (interior (M.triangleCarrier T.1))
      (interior (M.triangleCarrier U.1)) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  exact Set.not_nonempty_iff_eq_empty.mp fun h =>
    hne (M.eq_of_interior_triangleCarrier_inter_nonempty T U h)

/-- Deleting a maximal triangle leaves precisely the closure of the part of the old support
outside that triangle.  This is the face-to-face form of the elementary observation used in
Moise's free-triangle removal: points on a surviving triangle are limits of points in its
interior, and the interior of a different maximal triangle misses the deleted carrier. -/
theorem eraseTriangle_support_eq_closure_diff_triangleCarrier (T : M.Triangle) :
    (M.eraseTriangle T.1).toPlaneComplex.support =
      closure (M.toPlaneComplex.support \ M.triangleCarrier T.1) := by
  apply Set.Subset.antisymm
  · intro p hp
    rw [TriangleMesh.toPlaneComplex_support] at hp
    simp only [TriangleMesh.eraseTriangle_triangles, Set.mem_iUnion] at hp
    obtain ⟨u, hu, hpU⟩ := hp
    have huData := Finset.mem_erase.mp hu
    let U : M.Triangle := ⟨u, huData.2⟩
    change p ∈ M.triangleCarrier U.1 at hpU
    rw [← M.closure_interior_triangleCarrier U] at hpU
    apply closure_mono (s := interior (M.triangleCarrier U.1)) ?_ hpU
    intro q hq
    refine ⟨?_, ?_⟩
    · rw [M.toPlaneComplex_support]
      exact Set.mem_iUnion_of_mem U.1 (Set.mem_iUnion_of_mem U.2 (interior_subset hq))
    · intro hqT
      have hinterCard : (U.1 ∩ T.1 : Finset M.Vertex).card ≤ 2 := by
        have hle := Finset.card_le_card
          (Finset.inter_subset_left : U.1 ∩ T.1 ⊆ U.1)
        rw [M.card_triangle U.1 U.2] at hle
        by_contra hcard
        have hcardEq : (U.1 ∩ T.1 : Finset M.Vertex).card = 3 := by omega
        have hinterU : U.1 ∩ T.1 = U.1 :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
            rw [hcardEq, M.card_triangle U.1 U.2])
        have hsub : U.1 ⊆ T.1 := hinterU ▸ Finset.inter_subset_right
        have hUT : U.1 = T.1 := Finset.eq_of_subset_of_card_le hsub (by
          rw [M.card_triangle U.1 U.2, M.card_triangle T.1 T.2])
        exact huData.1 hUT
      have hqInter : q ∈ convexHull ℝ
          (M.position '' ((U.1 ∩ T.1 : Finset M.Vertex) : Set M.Vertex)) := by
        rw [← M.triangle_inter U.1 U.2 T.1 T.2]
        exact ⟨interior_subset hq, hqT⟩
      exact Set.disjoint_left.mp
        (M.disjoint_interior_triangleCarrier_convexHull_of_subset_card_le_two U
          Finset.inter_subset_left hinterCard) hq hqInter
  · apply closure_minimal
    · intro p hp
      rw [M.toPlaneComplex_support] at hp
      rw [TriangleMesh.toPlaneComplex_support]
      simp only [Set.mem_sdiff, Set.mem_iUnion,
        TriangleMesh.eraseTriangle_triangles] at hp ⊢
      obtain ⟨u, hu, hpU⟩ := hp.1
      by_cases huT : u = T.1
      · exact False.elim (hp.2 (huT ▸ hpU))
      · exact ⟨u, Finset.mem_erase.mpr ⟨huT, hu⟩, hpU⟩
    · exact (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed

/-- The remaining support cannot contain an interior point of the deleted triangle. -/
theorem disjoint_eraseTriangle_support_interior_triangleCarrier (T : M.Triangle) :
    Disjoint (M.eraseTriangle T.1).toPlaneComplex.support
      (interior (M.triangleCarrier T.1)) := by
  rw [M.eraseTriangle_support_eq_closure_diff_triangleCarrier T, Set.disjoint_left]
  intro p hpClosure hpInterior
  have hpClosureCompl : p ∈ closure (M.triangleCarrier T.1)ᶜ :=
    closure_mono (by
      intro q hq
      exact hq.2) hpClosure
  rw [closure_compl] at hpClosureCompl
  exact hpClosureCompl hpInterior

/-- The frontier after deleting a maximal triangle consists of the old frontier away from the
triangle together with the exact attachment of the surviving support to that triangle. -/
theorem frontier_eraseTriangle_support (T : M.Triangle) :
    frontier (M.eraseTriangle T.1).toPlaneComplex.support =
      (frontier M.toPlaneComplex.support \ M.triangleCarrier T.1) ∪
        ((M.eraseTriangle T.1).toPlaneComplex.support ∩ M.triangleCarrier T.1) := by
  let A := M.toPlaneComplex.support
  let B := (M.eraseTriangle T.1).toPlaneComplex.support
  let K := M.triangleCarrier T.1
  have hAclosed : IsClosed A := M.toPlaneComplex.isCompact_support.isClosed
  have hBclosed : IsClosed B := (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed
  have hKclosed : IsClosed K :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hBA : B ⊆ A := M.eraseTriangle_support_subset T.1
  have hAunion : A = B ∪ K := M.support_eq_eraseTriangle_union_triangleCarrier T.2
  have hBdisjoint : Disjoint B (interior K) :=
    M.disjoint_eraseTriangle_support_interior_triangleCarrier T
  ext p
  constructor
  · intro hp
    have hpData : p ∈ B ∧ p ∉ interior B := by
      rw [hBclosed.frontier_eq] at hp
      exact hp
    by_cases hpK : p ∈ K
    · exact Or.inr ⟨hpData.1, hpK⟩
    · left
      refine ⟨?_, hpK⟩
      rw [hAclosed.frontier_eq]
      refine ⟨hBA hpData.1, ?_⟩
      intro hpIntA
      apply hpData.2
      apply interior_maximal (t := interior A ∩ Kᶜ)
      · intro q hq
        have hqA : q ∈ A := interior_subset hq.1
        rw [hAunion] at hqA
        exact hqA.resolve_right hq.2
      · exact isOpen_interior.inter hKclosed.isOpen_compl
      · exact ⟨hpIntA, hpK⟩
  · rintro (hpOld | hpAttach)
    · rw [hBclosed.frontier_eq]
      refine ⟨?_, ?_⟩
      · have hpA : p ∈ A := by
          rw [hAclosed.frontier_eq] at hpOld
          exact hpOld.1.1
        rw [hAunion] at hpA
        exact hpA.resolve_right hpOld.2
      · intro hpIntB
        have hpIntA : p ∈ interior A := interior_mono hBA hpIntB
        have hpNotIntA : p ∉ interior A := by
          rw [hAclosed.frontier_eq] at hpOld
          exact hpOld.1.2
        exact hpNotIntA hpIntA
    · rw [hBclosed.frontier_eq]
      refine ⟨hpAttach.1, ?_⟩
      intro hpIntB
      have hpClosureIntK : p ∈ closure (interior K) := by
        rw [M.closure_interior_triangleCarrier T]
        exact hpAttach.2
      have hpClosureMeet : p ∈ closure (interior B ∩ interior K) :=
        isOpen_interior.inter_closure ⟨hpIntB, hpClosureIntK⟩
      obtain ⟨q, hqB, hqK⟩ := Set.Nonempty.of_closure ⟨p, hpClosureMeet⟩
      exact Set.disjoint_left.mp hBdisjoint (interior_subset hqB) hqK

theorem triangleCarrier_eq_nonnegCoords (T : M.Triangle) :
    M.triangleCarrier T.1 = {p | ∀ i : Fin 3, 0 ≤ M.oppositeCoord T i p} := by
  let b := affineBasisOfTriangle (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  have hrange : Set.range b = M.position '' (T.1 : Set M.Vertex) := by
    change Set.range (M.position ∘ M.orderedVertex T) = _
    rw [Set.range_comp, M.range_orderedVertex T]
  rw [triangleCarrier, ← hrange, b.convexHull_eq_nonneg_coord]
  rfl

/-- A neighborhood of a relative interior point of an edge, retaining positivity of all
barycentric coordinates tangent to that edge. -/
def nonOppositeCoordNeighborhood (T : M.Triangle) (k : Fin 3) : Set Plane :=
  {p | ∀ j : Fin 3, j ≠ k → 0 < M.oppositeCoord T j p}

theorem isOpen_nonOppositeCoordNeighborhood (T : M.Triangle) (k : Fin 3) :
    IsOpen (M.nonOppositeCoordNeighborhood T k) := by
  have heq : M.nonOppositeCoordNeighborhood T k =
      ⋂ j : Fin 3, ⋂ (_ : j ≠ k), M.oppositeCoord T j ⁻¹' Set.Ioi 0 := by
    ext p
    simp [nonOppositeCoordNeighborhood]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_Ioi.preimage (M.oppositeCoord T j).continuous_of_finiteDimensional

theorem mem_nonOppositeCoordNeighborhood_of_mem_edge (T : M.Triangle) (k : Fin 3)
    {p : Plane}
    (hp : p ∈ convexHull ℝ ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane))
    (hpv : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i)) :
    p ∈ M.nonOppositeCoordNeighborhood T k := by
  intro j hj
  exact M.oppositeCoord_pos_of_mem_oppositeEdge_of_not_vertex T k j hj hp hpv

theorem triangle_inter_eq_edge {T U : M.Triangle} (hTU : T.1 ≠ U.1)
    {e : Finset M.Vertex} (hecard : e.card = 2) (heT : e ⊆ T.1) (heU : e ⊆ U.1) :
    T.1 ∩ U.1 = e := by
  have heInter : e ⊆ (T.1 ∩ U.1 : Finset M.Vertex) := fun v hv =>
    Finset.mem_inter.mpr ⟨heT hv, heU hv⟩
  have hcard : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ 2 := by
    by_contra h
    have hge : 3 ≤ (T.1 ∩ U.1 : Finset M.Vertex).card := by omega
    have hleT : (T.1 ∩ U.1 : Finset M.Vertex).card ≤ 3 := by
      have h := Finset.card_le_card
        (Finset.inter_subset_left : (T.1 ∩ U.1 : Finset M.Vertex) ⊆ T.1)
      rwa [M.card_triangle T.1 T.2] at h
    have hcard3 : (T.1 ∩ U.1 : Finset M.Vertex).card = 3 := le_antisymm hleT hge
    have hEqT : (T.1 ∩ U.1 : Finset M.Vertex) = T.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [hcard3, M.card_triangle T.1 T.2])
    have hEqU : (T.1 ∩ U.1 : Finset M.Vertex) = U.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hcard3, M.card_triangle U.1 U.2])
    exact hTU (hEqT.symm.trans hEqU)
  symm
  exact Finset.eq_of_subset_of_card_le heInter (by simpa [hecard] using hcard)

theorem oppositeCoord_negative_across_shared_edge {T U : M.Triangle} (hTU : T.1 ≠ U.1)
    {e : Finset M.Vertex} (hecard : e.card = 2) (heT : e ⊆ T.1) (heU : e ⊆ U.1)
    (kT kU : Fin 3)
    (hedgeT : M.oppositeEdgePoints T kT = e.image M.position)
    (hedgeU : M.oppositeEdgePoints U kU = e.image M.position)
    {p : Plane} (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpvT : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i))
    (hpvU : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex U i)) :
    M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) < 0 := by
  let c := M.oppositeCoord T kT (M.position (M.orderedVertex U kU))
  have hedge : M.oppositeEdgePoints T kT = M.oppositeEdgePoints U kU :=
    hedgeT.trans hedgeU.symm
  have hcne : c ≠ 0 := M.oppositeCoord_ne_zero_of_same_edge T U kT kU hedge
  apply lt_of_le_of_ne (not_lt.mp ?_) hcne
  intro hcpos
  have hEdgeSetT : convexHull ℝ ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) =
      convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [hedgeT, Finset.coe_image]
  have hEdgeSetU : convexHull ℝ ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) =
      convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [hedgeU, Finset.coe_image]
  have hpEdgeU : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) := by
    rw [hEdgeSetU]
    exact hpEdge
  have hpEdgeT : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) := by
    rw [hEdgeSetT]
    exact hpEdge
  have hpOT : p ∈ M.nonOppositeCoordNeighborhood T kT :=
    M.mem_nonOppositeCoordNeighborhood_of_mem_edge T kT hpEdgeT hpvT
  have hpOU : p ∈ M.nonOppositeCoordNeighborhood U kU :=
    M.mem_nonOppositeCoordNeighborhood_of_mem_edge U kU hpEdgeU hpvU
  let q := M.position (M.orderedVertex U kU)
  have hpclosure : p ∈ closure (openSegment ℝ p q) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ p q)
  obtain ⟨z, hzOT, hzseg⟩ := (mem_closure_iff.mp hpclosure)
    (M.nonOppositeCoordNeighborhood T kT)
    (M.isOpen_nonOppositeCoordNeighborhood T kT) hpOT
  have hzU : z ∈ interior (M.triangleCarrier U.1) := by
    rw [M.interior_triangleCarrier U]
    rw [openSegment_eq_image_lineMap] at hzseg
    obtain ⟨θ, hθ, rfl⟩ := hzseg
    intro i
    rw [AffineMap.apply_lineMap]
    by_cases hi : i = kU
    · subst i
      rw [M.oppositeCoord_eq_zero_of_mem_oppositeEdge U kU hpEdgeU,
        M.oppositeCoord_vertex]
      simp [AffineMap.lineMap_apply_module, hθ.1]
    · have hpi := hpOU i hi
      rw [M.oppositeCoord_vertex]
      simp [hi, AffineMap.lineMap_apply_module]
      nlinarith [hpi, hθ.2]
  have hzT : z ∈ interior (M.triangleCarrier T.1) := by
    rw [M.interior_triangleCarrier T]
    intro i
    by_cases hi : i = kT
    · subst i
      rw [openSegment_eq_image_lineMap] at hzseg
      obtain ⟨θ, hθ, rfl⟩ := hzseg
      rw [AffineMap.apply_lineMap,
        M.oppositeCoord_eq_zero_of_mem_oppositeEdge T kT hpEdgeT]
      change 0 < AffineMap.lineMap 0 c θ
      simp [AffineMap.lineMap_apply_module]
      nlinarith [hcpos, hθ.1]
    · exact hzOT i hi
  have hinter := M.triangle_inter T.1 T.2 U.1 U.2
  rw [M.triangle_inter_eq_edge hTU hecard heT heU] at hinter
  have hzEdge : z ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [← hinter]
    exact ⟨interior_subset hzT, interior_subset hzU⟩
  have hzZero : M.oppositeCoord T kT z = 0 := by
    apply M.oppositeCoord_eq_zero_of_mem_oppositeEdge T kT
    rw [hEdgeSetT]
    exact hzEdge
  have hzPos : 0 < M.oppositeCoord T kT z := by
    rw [M.interior_triangleCarrier T] at hzT
    exact hzT kT
  linarith

/-- A genuine geometric edge contains infinitely many points. -/
theorem edgeCarrier_infinite {e : Finset M.Vertex} (hecard : e.card = 2) :
    (convexHull ℝ (M.position '' (e : Set M.Vertex))).Infinite := by
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hecard
  have hpne : M.position v ≠ M.position w := M.position_injective.ne hvw
  rw [show M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex) =
      {M.position v, M.position w} by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨v, by simp, rfl⟩
      · exact ⟨w, by simp, rfl⟩]
  rw [convexHull_pair, segment_eq_image_lineMap]
  exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
    (AffineMap.lineMap_injective ℝ hpne).injOn

/-- Choose a relative-interior edge point which is not any vertex of the finite mesh. -/
theorem exists_nonvertex_mem_edgeCarrier {e : Finset M.Vertex} (hecard : e.card = 2) :
    ∃ p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)),
      ∀ v : M.Vertex, p ≠ M.position v := by
  let vertexPositions : Finset Plane := Finset.univ.image M.position
  obtain ⟨p, hp, hpnot⟩ := (M.edgeCarrier_infinite hecard).exists_notMem_finset
    vertexPositions
  refine ⟨p, hp, fun v hpv => ?_⟩
  apply hpnot
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hpv.symm⟩

/-- Two mesh edges containing the same nonvertex point are the same edge. -/
theorem edge_eq_of_nonvertex_mem_edgeCarriers {e f : Finset M.Vertex}
    (he : e ∈ M.edges) (hf : f ∈ M.edges) {p : Plane}
    (hpe : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpf : p ∈ convexHull ℝ (M.position '' (f : Set M.Vertex)))
    (hpv : ∀ v : M.Vertex, p ≠ M.position v) : e = f := by
  have hecard := M.card_of_mem_edges he
  have hfcard := M.card_of_mem_edges hf
  have heFace : e ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he
    have hetData := Finset.mem_powersetCard.mp het
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hecard]; omega), t, ht, hetData.1⟩
  have hfFace : f ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨t, ht, hft⟩ := Finset.mem_biUnion.mp hf
    have hftData := Finset.mem_powersetCard.mp hft
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hfcard]; omega), t, ht, hftData.1⟩
  have hface := M.toPlaneComplex.face_inter e heFace f hfFace
  change convexHull ℝ (M.position '' (e : Set M.Vertex)) ∩
      convexHull ℝ (M.position '' (f : Set M.Vertex)) =
        convexHull ℝ (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex))
    at hface
  have hpInter : p ∈ convexHull ℝ
      (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← hface]
    exact ⟨hpe, hpf⟩
  have hinterCard : (e ∩ f).card = 2 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left : e ∩ f ⊆ e)
    rw [hecard] at hle
    by_contra hne
    have hsmall : (e ∩ f).card ≤ 1 := by omega
    obtain hempty | hnonempty := (e ∩ f).eq_empty_or_nonempty
    · rw [hempty] at hpInter
      simp at hpInter
    · obtain ⟨v, hv⟩ := hnonempty
      have hsingleton : e ∩ f = {v} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hv, fun w hw => ?_⟩
        by_contra hwv
        have hvw : v ≠ w := Ne.symm hwv
        have hpairs : ({v, w} : Finset M.Vertex) ⊆ e ∩ f := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have := Finset.card_le_card hpairs
        simp [hvw] at this
        omega
      rw [hsingleton] at hpInter
      have hp : p = M.position v := by simpa using hpInter
      exact hpv v hp
  have heqE : e ∩ f = e :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hinterCard, hecard])
  have heqF : e ∩ f = f :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hinterCard, hfcard])
  exact heqE.symm.trans heqF

/-- Edge carriers in a face-to-face mesh meet in exactly the carrier of their common
vertices. -/
theorem edgeCarrier_inter_edgeCarrier {e f : Finset M.Vertex}
    (he : e ∈ M.edges) (hf : f ∈ M.edges) :
    convexHull ℝ (M.position '' (e : Set M.Vertex)) ∩
        convexHull ℝ (M.position '' (f : Set M.Vertex)) =
      convexHull ℝ (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex)) := by
  have heFace : e ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he
    have hetData := Finset.mem_powersetCard.mp het
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hetData.2]; omega), t, ht, hetData.1⟩
  have hfFace : f ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨t, ht, hft⟩ := Finset.mem_biUnion.mp hf
    have hftData := Finset.mem_powersetCard.mp hft
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [hftData.2]; omega), t, ht, hftData.1⟩
  exact M.toPlaneComplex.face_inter e heFace f hfFace

/-- A used mesh vertex lying on an edge carrier is one of that edge's abstract endpoints. -/
theorem vertex_mem_edge_of_position_mem_edgeCarrier {v : M.Vertex} {e t : Finset M.Vertex}
    (ht : t ∈ M.triangles) (hvt : v ∈ t) (he : e ∈ M.edges)
    (hv : M.position v ∈ convexHull ℝ (M.position '' (e : Set M.Vertex))) : v ∈ e := by
  have hvFace : {v} ∈ M.toPlaneComplex.simplexes := by
    change ({v} : Finset M.Vertex) ∈ M.faces
    exact M.mem_faces_iff.mpr ⟨by simp, t, ht, by simpa using hvt⟩
  have heFace : e ∈ M.toPlaneComplex.simplexes := by
    obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp he
    have heuData := Finset.mem_powersetCard.mp heu
    exact M.mem_faces_iff.mpr
      ⟨Finset.card_pos.mp (by rw [heuData.2]; omega), u, hu, heuData.1⟩
  have hface := M.toPlaneComplex.face_inter {v} hvFace e heFace
  change convexHull ℝ (M.position '' (({v} : Finset M.Vertex) : Set M.Vertex)) ∩
      convexHull ℝ (M.position '' (e : Set M.Vertex)) =
        convexHull ℝ
          (M.position '' ((({v} : Finset M.Vertex) ∩ e : Finset M.Vertex) : Set M.Vertex))
    at hface
  by_contra hve
  have hinter : ({v} : Finset M.Vertex) ∩ e = ∅ := by
    simp [hve]
  have hp : M.position v ∈
      convexHull ℝ (M.position '' ((({v} : Finset M.Vertex) ∩ e : Finset M.Vertex) :
        Set M.Vertex)) := by
    rw [← hface]
    exact ⟨by simp, hv⟩
  rw [hinter] at hp
  simp at hp

/-- In a face-to-face planar mesh, once one incident triangle is fixed there is at most one
other triangle incident to the same edge. -/
theorem incidentTriangle_eq_of_ne {e t u v : Finset M.Vertex} (hecard : e.card = 2)
    (ht : t ∈ M.incidentTriangles e) (hu : u ∈ M.incidentTriangles e)
    (hv : v ∈ M.incidentTriangles e) (hut : u ≠ t) (hvt : v ≠ t) : u = v := by
  by_contra huv
  have htData := M.mem_incidentTriangles_iff.mp ht
  have huData := M.mem_incidentTriangles_iff.mp hu
  have hvData := M.mem_incidentTriangles_iff.mp hv
  let T : M.Triangle := ⟨t, htData.1⟩
  let U : M.Triangle := ⟨u, huData.1⟩
  let V : M.Triangle := ⟨v, hvData.1⟩
  obtain ⟨kT, hedgeT⟩ := M.exists_oppositeEdgePoints_eq T htData.2 hecard
  obtain ⟨kU, hedgeU⟩ := M.exists_oppositeEdgePoints_eq U huData.2 hecard
  obtain ⟨kV, hedgeV⟩ := M.exists_oppositeEdgePoints_eq V hvData.2 hecard
  obtain ⟨p, hpEdge, hpv⟩ := M.exists_nonvertex_mem_edgeCarrier hecard
  have hcTU : M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) < 0 :=
    M.oppositeCoord_negative_across_shared_edge hut.symm hecard htData.2 huData.2
      kT kU hedgeT hedgeU hpEdge (fun i => hpv (M.orderedVertex T i))
        (fun i => hpv (M.orderedVertex U i))
  have hcTV : M.oppositeCoord T kT (M.position (M.orderedVertex V kV)) < 0 :=
    M.oppositeCoord_negative_across_shared_edge hvt.symm hecard htData.2 hvData.2
      kT kV hedgeT hedgeV hpEdge (fun i => hpv (M.orderedVertex T i))
        (fun i => hpv (M.orderedVertex V i))
  have hcUV : M.oppositeCoord U kU (M.position (M.orderedVertex V kV)) < 0 :=
    M.oppositeCoord_negative_across_shared_edge huv hecard huData.2 hvData.2
      kU kV hedgeU hedgeV hpEdge (fun i => hpv (M.orderedVertex U i))
        (fun i => hpv (M.orderedVertex V i))
  have hrel := M.oppositeCoord_smul_eq_of_same_edge T U kT kU
    (hedgeT.trans hedgeU.symm)
  have hrelV := congrArg (fun f : Plane →ᵃ[ℝ] ℝ =>
    f (M.position (M.orderedVertex V kV))) hrel
  change M.oppositeCoord T kT (M.position (M.orderedVertex U kU)) *
      M.oppositeCoord U kU (M.position (M.orderedVertex V kV)) =
    M.oppositeCoord T kT (M.position (M.orderedVertex V kV)) at hrelV
  nlinarith

/-- Every geometric edge of a face-to-face planar mesh is incident to at most two triangles. -/
theorem card_incidentTriangles_le_two {e : Finset M.Vertex} (hecard : e.card = 2) :
    (M.incidentTriangles e).card ≤ 2 := by
  by_contra hcard
  have hthree : 2 < (M.incidentTriangles e).card := by omega
  obtain ⟨t, u, v, ht, hu, hv, htu, htv, huv⟩ := Finset.two_lt_card_iff.mp hthree
  have huv' := M.incidentTriangle_eq_of_ne hecard ht hu hv htu.symm htv.symm
  exact huv huv'

/-- If a nonvertex point of an edge of `t` also belongs to `u`, then `u` contains the whole
edge.  This is the face-to-face property upgraded from geometry to incidence. -/
theorem edge_subset_of_nonvertex_mem_triangleCarrier {e t u : Finset M.Vertex} {p : Plane}
    (hecard : e.card = 2) (het : e ⊆ t) (ht : t ∈ M.triangles)
    (hu : u ∈ M.triangles)
    (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpU : p ∈ M.triangleCarrier u) (hpv : ∀ v : M.Vertex, p ≠ M.position v) :
    e ⊆ u := by
  have hpT : p ∈ M.triangleCarrier t :=
    convexHull_mono (Set.image_mono het) hpEdge
  have hinter := M.triangle_inter t ht u hu
  have hpInter : p ∈ convexHull ℝ (M.position '' ((t ∩ u : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← hinter]
    exact ⟨hpT, hpU⟩
  let f : Finset M.Vertex := t ∩ u
  have hfne : f.Nonempty := by
    by_contra hf
    have hfempty : f = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    rw [show (t ∩ u : Finset M.Vertex) = f by rfl, hfempty] at hpInter
    simp at hpInter
  have heSimplex : e ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by omega), t, ht, het⟩
  have hfSimplex : f ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨hfne, t, ht, by exact Finset.inter_subset_left⟩
  have hface := M.toPlaneComplex.face_inter e heSimplex f hfSimplex
  change convexHull ℝ (M.position '' (e : Set M.Vertex)) ∩
      convexHull ℝ (M.position '' (f : Set M.Vertex)) =
    convexHull ℝ (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex)) at hface
  have hpCommon : p ∈
      convexHull ℝ (M.position '' ((e ∩ f : Finset M.Vertex) : Set M.Vertex)) := by
    rw [← hface]
    exact ⟨hpEdge, by simpa only [f] using hpInter⟩
  by_contra hsub
  have hcardCommon : (e ∩ f).card ≤ 1 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left : e ∩ f ⊆ e)
    rw [hecard] at hle
    by_contra hnot
    have hcardeq : (e ∩ f).card = 2 := by omega
    have heq : e ∩ f = e := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
      rw [hcardeq, hecard])
    apply hsub
    intro v hv
    have hvinter : v ∈ e ∩ f := by rw [heq]; exact hv
    exact (Finset.mem_inter.mp (Finset.mem_inter.mp hvinter).2).2
  obtain hempty | hnonempty := (e ∩ f).eq_empty_or_nonempty
  · rw [hempty] at hpCommon
    simp at hpCommon
  · obtain ⟨v, hv⟩ := hnonempty
    have hsingleton : e ∩ f = {v} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hv, fun w hw => ?_⟩
      have hcardPair : ({v, w} : Finset M.Vertex).card ≤ 1 :=
        (Finset.card_le_card (show ({v, w} : Finset M.Vertex) ⊆ e ∩ f by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)).trans hcardCommon
      by_contra hwv
      have hvw : v ≠ w := Ne.symm hwv
      have hcardTwo : ({v, w} : Finset M.Vertex).card = 2 := by simp [hvw]
      omega
    rw [hsingleton] at hpCommon
    have hpEq : p = M.position v := by
      simpa using hpCommon
    exact hpv v hpEq

/-- Every nonvertex point of an incidence-one edge lies on the support frontier. -/
theorem mem_frontier_of_mem_boundaryEdge {e : Finset M.Vertex} (he : M.IsBoundaryEdge e)
    {p : Plane} (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpv : ∀ v : M.Vertex, p ≠ M.position v) :
    p ∈ frontier M.toPlaneComplex.support := by
  classical
  obtain ⟨t, ht, hetPower⟩ := Finset.mem_biUnion.mp he.1
  have hetData := Finset.mem_powersetCard.mp hetPower
  have het : e ⊆ t := hetData.1
  have hecard : e.card = 2 := hetData.2
  have htinc : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, het⟩
  let A := M.triangleCarrier t
  let B := ⋃ u ∈ M.triangles.erase t, M.triangleCarrier u
  have hBcompact : IsCompact B := by
    exact (M.triangles.erase t).finite_toSet.isCompact_biUnion fun u _ =>
      (u.finite_toSet.image M.position).isCompact_convexHull ℝ
  have hpNotB : p ∉ B := by
    intro hpB
    simp only [B, Set.mem_iUnion] at hpB
    obtain ⟨u, huErase, hpU⟩ := hpB
    have huData := Finset.mem_erase.mp huErase
    have heu : e ⊆ u := M.edge_subset_of_nonvertex_mem_triangleCarrier hecard het ht
      huData.2 hpEdge hpU hpv
    have huinc : u ∈ M.incidentTriangles e :=
      M.mem_incidentTriangles_iff.mpr ⟨huData.2, heu⟩
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp he.2
    have htw : t = w := by
      rw [hw] at htinc
      simpa using htinc
    have huw : u = w := by
      rw [hw] at huinc
      simpa using huinc
    exact huData.1 (huw.trans htw.symm)
  have hsupport : M.toPlaneComplex.support = A ∪ B := by
    rw [M.toPlaneComplex_support]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union, A, B]
    constructor
    · rintro ⟨u, hu, hxu⟩
      by_cases hut : u = t
      · left
        rwa [hut] at hxu
      · right
        exact ⟨u, Finset.mem_erase.mpr ⟨hut, hu⟩, hxu⟩
    · rintro (hxt | ⟨u, hu, hxu⟩)
      · exact ⟨t, ht, hxt⟩
      · exact ⟨u, (Finset.mem_erase.mp hu).2, hxu⟩
  let T : M.Triangle := ⟨t, ht⟩
  obtain ⟨k, hedge⟩ := M.exists_oppositeEdgePoints_eq T het hecard
  have hpOpposite : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
    rw [hedge, Finset.coe_image]
    exact hpEdge
  have hpA : p ∈ A := convexHull_mono (Set.image_mono het) hpEdge
  have hpNotInteriorA : p ∉ interior A := by
    rw [M.interior_triangleCarrier T]
    intro hpos
    have hz := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k hpOpposite
    linarith [hpos k]
  have hpFrontierA : p ∈ frontier A :=
    (mem_frontier_iff_notMem_interior hpA).mpr hpNotInteriorA
  have hpSupport : p ∈ M.toPlaneComplex.support := by
    rw [hsupport]
    exact Or.inl hpA
  have hpNotInteriorSupport : p ∉ interior M.toPlaneComplex.support := by
    intro hpInterior
    let O := interior M.toPlaneComplex.support ∩ Bᶜ
    have hOopen : IsOpen O := isOpen_interior.inter hBcompact.isClosed.isOpen_compl
    have hpO : p ∈ O := ⟨hpInterior, hpNotB⟩
    have hOsub : O ⊆ A := by
      intro x hx
      have hxsupport : x ∈ M.toPlaneComplex.support := interior_subset hx.1
      rw [hsupport] at hxsupport
      rcases hxsupport with hxA | hxB
      · exact hxA
      · exact False.elim (hx.2 hxB)
    have hpInteriorA : p ∈ interior A := interior_maximal hOsub hOopen hpO
    exact Set.disjoint_left.mp disjoint_interior_frontier hpInteriorA hpFrontierA
  rw [M.toPlaneComplex.isCompact_support.isClosed.frontier_eq]
  exact ⟨hpSupport, hpNotInteriorSupport⟩

/-- The whole carrier of an incidence-one edge lies in the support frontier, including endpoints. -/
theorem boundaryEdgeCarrier_subset_frontier {e : Finset M.Vertex} (he : M.IsBoundaryEdge e) :
    convexHull ℝ (M.position '' (e : Set M.Vertex)) ⊆
      frontier M.toPlaneComplex.support := by
  classical
  have hecard := M.card_of_mem_edges he.1
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hecard
  let a := M.position v
  let b := M.position w
  have hab : a ≠ b := M.position_injective.ne hvw
  have himage : M.position '' (({v, w} : Finset M.Vertex) : Set M.Vertex) = {a, b} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [a, b]
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨v, by simp, rfl⟩
      · exact ⟨w, by simp, rfl⟩
  rw [himage, convexHull_pair]
  let line : ℝ → Plane := AffineMap.lineMap a b
  let bad : Set ℝ := line ⁻¹' Set.range M.position
  have hbadFinite : bad.Finite := by
    apply Set.Finite.preimage (AffineMap.lineMap_injective ℝ hab).injOn
    exact Set.finite_range M.position
  have hdense : Dense badᶜ := hbadFinite.countable.dense_compl ℝ
  let good : Set ℝ := Set.Ioo (0 : ℝ) 1 ∩ badᶜ
  have hIooGood : Set.Ioo (0 : ℝ) 1 ⊆ closure good := by
    exact hdense.open_subset_closure_inter isOpen_Ioo
  have hgoodImage : line '' good ⊆ frontier M.toPlaneComplex.support := by
    rintro p ⟨c, hc, rfl⟩
    apply M.mem_frontier_of_mem_boundaryEdge he
    · rw [himage, convexHull_pair]
      exact lineMap_mem_segment ℝ a b ⟨hc.1.1.le, hc.1.2.le⟩
    · intro x hx
      apply hc.2
      exact ⟨x, hx.symm⟩
  intro p hp
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  have hcClosureIoo : c ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hc
  have hcClosureGood : c ∈ closure good := by
    have : c ∈ closure (closure good) := closure_mono hIooGood hcClosureIoo
    simpa using this
  have hlineContinuous : Continuous line := by
    exact AffineMap.lineMap_continuous
  have hmemClosureImage : line c ∈ closure (line '' good) :=
    image_closure_subset_closure_image hlineContinuous ⟨c, hcClosureGood, rfl⟩
  exact (closure_minimal hgoodImage isClosed_frontier) hmemClosureImage

theorem boundaryCarrier_subset_frontier :
    M.boundaryCarrier ⊆ frontier M.toPlaneComplex.support := by
  intro p hp
  simp only [boundaryCarrier, Set.mem_iUnion] at hp
  obtain ⟨e, he, hpe⟩ := hp
  exact M.boundaryEdgeCarrier_subset_frontier
    (M.mem_allBoundaryEdges_iff.mp he) hpe

theorem card_triangleEdges {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    (M.triangleEdges t).card = 3 := by
  simp [triangleEdges, M.card_triangle t ht]

theorem boundaryEdges_subset_triangleEdges (t : Finset M.Vertex) :
    M.boundaryEdges t ⊆ M.triangleEdges t := by
  classical
  intro e he
  exact (Finset.mem_filter.mp (show e ∈ (M.triangleEdges t).filter M.IsBoundaryEdge by
    simpa [boundaryEdges] using he)).1

theorem mem_boundaryEdges_iff {e t : Finset M.Vertex} :
    e ∈ M.boundaryEdges t ↔ e ⊆ t ∧ e.card = 2 ∧ M.IsBoundaryEdge e := by
  classical
  simp [boundaryEdges, triangleEdges, Finset.mem_powersetCard]
  tauto

theorem boundaryEdges_nonempty_of_isFreeTriangle {t : Finset M.Vertex}
    (ht : M.IsFreeTriangle t) : (M.boundaryEdges t).Nonempty := by
  obtain ⟨htM, e, he, het⟩ := ht
  exact ⟨e, M.mem_boundaryEdges_iff.mpr
    ⟨het, M.card_of_mem_edges he.1, he⟩⟩

/-- A non-boundary edge of a maximal triangle has exactly two incident triangles. -/
theorem card_incidentTriangles_eq_two_of_not_boundary {e t : Finset M.Vertex}
    (ht : t ∈ M.triangles) (hecard : e.card = 2) (het : e ⊆ t)
    (he : ¬M.IsBoundaryEdge e) : (M.incidentTriangles e).card = 2 := by
  have htinc : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, het⟩
  have hpos : 0 < (M.incidentTriangles e).card := Finset.card_pos.mpr ⟨t, htinc⟩
  have hle := M.card_incidentTriangles_le_two hecard
  have hne : (M.incidentTriangles e).card ≠ 1 := by
    intro hcard
    apply he
    refine ⟨?_, hcard⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨t, ht, Finset.mem_powersetCard.mpr ⟨het, hecard⟩⟩
  omega

/-- Two maximal triangles are edge-neighbors if they contain a common two-vertex face. -/
def AreEdgeNeighbors (t u : Finset M.Vertex) : Prop :=
  ∃ e : Finset M.Vertex, e.card = 2 ∧ e ⊆ t ∧ e ⊆ u

/-- A triangle with an edge-neighbor cannot have all three edges on the boundary. -/
theorem card_boundaryEdges_le_two_of_neighbor {t u : Finset M.Vertex}
    (ht : t ∈ M.triangles) (hu : u ∈ M.triangles) (htu : t ≠ u)
    (hneigh : M.AreEdgeNeighbors t u) : (M.boundaryEdges t).card ≤ 2 := by
  by_contra hcard
  have hthree : (M.boundaryEdges t).card = 3 := by
    have hle := Finset.card_le_card (M.boundaryEdges_subset_triangleEdges t)
    rw [M.card_triangleEdges ht] at hle
    omega
  have hall : M.boundaryEdges t = M.triangleEdges t :=
    Finset.eq_of_subset_of_card_le (M.boundaryEdges_subset_triangleEdges t) (by
      rw [hthree, M.card_triangleEdges ht])
  obtain ⟨e, hecard, het, heu⟩ := hneigh
  have heBoundary : M.IsBoundaryEdge e := by
    have heTri : e ∈ M.triangleEdges t :=
      Finset.mem_powersetCard.mpr ⟨het, hecard⟩
    rw [← hall] at heTri
    exact (M.mem_boundaryEdges_iff.mp heTri).2.2
  have htinc : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, het⟩
  have huinc : u ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨hu, heu⟩
  have htwo : 2 ≤ (M.incidentTriangles e).card := by
    exact Finset.one_lt_card.mpr ⟨t, htinc, u, huinc, htu⟩
  rw [heBoundary.2] at htwo
  omega

/-- Two distinct face-to-face triangles fill a neighborhood of every nonvertex point of their
common edge. -/
theorem mem_interior_union_triangleCarrier_of_shared_edge {T U : M.Triangle}
    (hTU : T.1 ≠ U.1) {e : Finset M.Vertex} (hecard : e.card = 2)
    (heT : e ⊆ T.1) (heU : e ⊆ U.1) {p : Plane}
    (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpvT : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i))
    (hpvU : ∀ i : Fin 3, p ≠ M.position (M.orderedVertex U i)) :
    p ∈ interior (M.triangleCarrier T.1 ∪ M.triangleCarrier U.1) := by
  obtain ⟨kT, hedgeT⟩ := M.exists_oppositeEdgePoints_eq T heT hecard
  obtain ⟨kU, hedgeU⟩ := M.exists_oppositeEdgePoints_eq U heU hecard
  have hEdgeSetT : convexHull ℝ ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) =
      convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [hedgeT, Finset.coe_image]
  have hEdgeSetU : convexHull ℝ ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) =
      convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
    rw [hedgeU, Finset.coe_image]
  have hpEdgeT : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) := by
    rw [hEdgeSetT]
    exact hpEdge
  have hpEdgeU : p ∈ convexHull ℝ
      ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) := by
    rw [hEdgeSetU]
    exact hpEdge
  let c := M.oppositeCoord T kT (M.position (M.orderedVertex U kU))
  have hc : c < 0 := M.oppositeCoord_negative_across_shared_edge hTU hecard heT heU
    kT kU hedgeT hedgeU hpEdge hpvT hpvU
  have hrel := M.oppositeCoord_smul_eq_of_same_edge T U kT kU
    (hedgeT.trans hedgeU.symm)
  let O := M.nonOppositeCoordNeighborhood T kT ∩
    M.nonOppositeCoordNeighborhood U kU
  have hOpen : IsOpen O :=
    (M.isOpen_nonOppositeCoordNeighborhood T kT).inter
      (M.isOpen_nonOppositeCoordNeighborhood U kU)
  have hpO : p ∈ O := ⟨
    M.mem_nonOppositeCoordNeighborhood_of_mem_edge T kT hpEdgeT hpvT,
    M.mem_nonOppositeCoordNeighborhood_of_mem_edge U kU hpEdgeU hpvU⟩
  have hOsub : O ⊆ M.triangleCarrier T.1 ∪ M.triangleCarrier U.1 := by
    intro x hx
    by_cases hfx : 0 ≤ M.oppositeCoord T kT x
    · left
      rw [M.triangleCarrier_eq_nonnegCoords T]
      intro i
      by_cases hi : i = kT
      · simpa [hi] using hfx
      · exact (hx.1 i hi).le
    · right
      rw [M.triangleCarrier_eq_nonnegCoords U]
      intro i
      by_cases hi : i = kU
      · subst i
        have hrelx := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f x) hrel
        change c * M.oppositeCoord U kU x = M.oppositeCoord T kT x at hrelx
        have hfx' : M.oppositeCoord T kT x < 0 := lt_of_not_ge hfx
        nlinarith
      · exact (hx.2 i hi).le
  exact interior_maximal hOsub hOpen hpO

theorem orderedVertex_ne_of_not_mem_edgeVertices (T : M.Triangle) (k : Fin 3)
    {e : Finset M.Vertex}
    (hedge : M.oppositeEdgePoints T k = e.image M.position)
    {p : Plane} (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpNotVertices : p ∉ M.position '' (e : Set M.Vertex)) :
    ∀ i : Fin 3, p ≠ M.position (M.orderedVertex T i) := by
  intro i hpi
  by_cases hi : i = k
  · subst i
    have hpEdge' : p ∈ convexHull ℝ
        ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
      rw [hedge, Finset.coe_image]
      exact hpEdge
    have hz := M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k hpEdge'
    rw [hpi, M.oppositeCoord_vertex] at hz
    simp at hz
  · apply hpNotVertices
    have hmemOpposite : M.position (M.orderedVertex T i) ∈
        M.oppositeEdgePoints T k := by
      unfold oppositeEdgePoints
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, rfl⟩
    rw [hedge] at hmemOpposite
    obtain ⟨v, hve, hv⟩ := Finset.mem_image.mp hmemOpposite
    exact ⟨v, hve, hv.trans hpi.symm⟩

/-- The shared-edge neighborhood theorem only needs the point to avoid the two endpoints of
the common edge; unrelated retained mesh vertices are irrelevant. -/
theorem mem_interior_union_triangleCarrier_of_shared_edge_of_not_mem_edgeVertices
    {T U : M.Triangle} (hTU : T.1 ≠ U.1)
    {e : Finset M.Vertex} (hecard : e.card = 2)
    (heT : e ⊆ T.1) (heU : e ⊆ U.1) {p : Plane}
    (hpEdge : p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)))
    (hpNotVertices : p ∉ M.position '' (e : Set M.Vertex)) :
    p ∈ interior (M.triangleCarrier T.1 ∪ M.triangleCarrier U.1) := by
  obtain ⟨kT, hedgeT⟩ := M.exists_oppositeEdgePoints_eq T heT hecard
  obtain ⟨kU, hedgeU⟩ := M.exists_oppositeEdgePoints_eq U heU hecard
  exact M.mem_interior_union_triangleCarrier_of_shared_edge hTU hecard heT heU hpEdge
    (M.orderedVertex_ne_of_not_mem_edgeVertices T kT hedgeT hpEdge hpNotVertices)
    (M.orderedVertex_ne_of_not_mem_edgeVertices U kU hedgeU hpEdge hpNotVertices)

/-- Every non-endpoint point of a non-boundary mesh edge is interior to the mesh support. -/
theorem edgeCarrier_diff_vertices_subset_interior_support
    {e t : Finset M.Vertex} (ht : t ∈ M.triangles)
    (hecard : e.card = 2) (heT : e ⊆ t) (heNotBoundary : ¬M.IsBoundaryEdge e) :
    convexHull ℝ (M.position '' (e : Set M.Vertex)) \
        (M.position '' (e : Set M.Vertex)) ⊆ interior M.toPlaneComplex.support := by
  intro p hp
  have hcard := M.card_incidentTriangles_eq_two_of_not_boundary
    ht hecard heT heNotBoundary
  have htIncident : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, heT⟩
  have hother : ∃ u ∈ M.incidentTriangles e, u ≠ t := by
    by_contra h
    push Not at h
    have hsingleton : M.incidentTriangles e = {t} := by
      ext u
      constructor
      · exact fun hu => Finset.mem_singleton.mpr (h u hu)
      · intro hu
        rw [Finset.mem_singleton.mp hu]
        exact htIncident
    rw [hsingleton] at hcard
    simp at hcard
  obtain ⟨u, huIncident, hut⟩ := hother
  have huData := M.mem_incidentTriangles_iff.mp huIncident
  let T : M.Triangle := ⟨t, ht⟩
  let U : M.Triangle := ⟨u, huData.1⟩
  have hpInteriorUnion :=
    M.mem_interior_union_triangleCarrier_of_shared_edge_of_not_mem_edgeVertices
      (T := T) (U := U) hut.symm hecard heT huData.2 hp.1 hp.2
  have hUnionSubset : M.triangleCarrier T.1 ∪ M.triangleCarrier U.1 ⊆
      M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.union_subset
      (Set.subset_iUnion_of_subset T.1
        (Set.subset_iUnion_of_subset T.2 (by rfl)))
      (Set.subset_iUnion_of_subset U.1
        (Set.subset_iUnion_of_subset U.2 (by rfl)))
  exact interior_mono hUnionSubset hpInteriorUnion

/-- Every nonvertex point of the support frontier lies on an incidence-one mesh edge. -/
theorem exists_boundaryEdge_through_frontier_point {p : Plane}
    (hpFrontier : p ∈ frontier M.toPlaneComplex.support)
    (hpv : ∀ v : M.Vertex, p ≠ M.position v) :
    ∃ t ∈ M.triangles, ∃ e : Finset M.Vertex,
      M.IsBoundaryEdge e ∧ e ⊆ t ∧
        p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
  classical
  have hpFrontierUnion : p ∈ frontier (⋃ t ∈ M.triangles, M.triangleCarrier t) := by
    rw [M.toPlaneComplex_support] at hpFrontier
    simpa only [triangleCarrier] using hpFrontier
  have hpTriangleFrontier := M.frontier_biUnion_subset M.triangles hpFrontierUnion
  simp only [Set.mem_iUnion] at hpTriangleFrontier
  obtain ⟨t, ht, hpT⟩ := hpTriangleFrontier
  obtain ⟨e, hecard, heT, hpEdge⟩ := M.exists_edge_of_mem_frontier_triangle ht hpT
  have heEdges : e ∈ M.edges := by
    apply Finset.mem_biUnion.mpr
    exact ⟨t, ht, Finset.mem_powersetCard.mpr ⟨heT, hecard⟩⟩
  have htIncident : t ∈ M.incidentTriangles e :=
    M.mem_incidentTriangles_iff.mpr ⟨ht, heT⟩
  have hIncidentCard : (M.incidentTriangles e).card = 1 := by
    by_contra hne
    have hother : ∃ u ∈ M.incidentTriangles e, u ≠ t := by
      by_contra h
      push Not at h
      have hsingleton : M.incidentTriangles e = {t} := by
        ext u
        constructor
        · intro hu
          exact Finset.mem_singleton.mpr (h u hu)
        · intro hu
          rw [Finset.mem_singleton.mp hu]
          exact htIncident
      apply hne
      rw [hsingleton]
      simp
    obtain ⟨u, huIncident, hut⟩ := hother
    have huData := M.mem_incidentTriangles_iff.mp huIncident
    let T : M.Triangle := ⟨t, ht⟩
    let U : M.Triangle := ⟨u, huData.1⟩
    have hpInteriorUnion : p ∈ interior
        (M.triangleCarrier T.1 ∪ M.triangleCarrier U.1) :=
      M.mem_interior_union_triangleCarrier_of_shared_edge
        (T := T) (U := U) hut.symm hecard heT huData.2 hpEdge
          (fun i => hpv (M.orderedVertex T i))
          (fun i => hpv (M.orderedVertex U i))
    have hUnionSubset : M.triangleCarrier T.1 ∪ M.triangleCarrier U.1 ⊆
        M.toPlaneComplex.support := by
      change M.triangleCarrier t ∪ M.triangleCarrier u ⊆ M.toPlaneComplex.support
      rw [M.toPlaneComplex_support]
      exact Set.union_subset
        (Set.subset_iUnion_of_subset t
          (Set.subset_iUnion_of_subset ht (by rfl)))
        (Set.subset_iUnion_of_subset u
          (Set.subset_iUnion_of_subset huData.1 (by rfl)))
    have hpInteriorSupport : p ∈ interior M.toPlaneComplex.support :=
      interior_mono hUnionSubset hpInteriorUnion
    exact (Set.disjoint_left.1 disjoint_interior_frontier hpInteriorSupport hpFrontier)
  exact ⟨t, ht, e, ⟨heEdges, hIncidentCard⟩, heT, hpEdge⟩

theorem mem_frontier_iff_exists_boundaryEdge_of_nonvertex {p : Plane}
    (hpv : ∀ v : M.Vertex, p ≠ M.position v) :
    p ∈ frontier M.toPlaneComplex.support ↔
      ∃ e : Finset M.Vertex, M.IsBoundaryEdge e ∧
        p ∈ convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
  constructor
  · intro hp
    obtain ⟨-, -, e, he, -, hpe⟩ :=
      M.exists_boundaryEdge_through_frontier_point hp hpv
    exact ⟨e, he, hpe⟩
  · rintro ⟨e, he, hpe⟩
    exact M.mem_frontier_of_mem_boundaryEdge he hpe hpv

/-- Away from mesh vertices, a triangle's frontier trace is exactly the union of its
incidence-one edges.  Extra isolated frontier vertices are precisely the obstruction addressed
by Moise's cutting induction. -/
theorem frontier_inter_triangleCarrier_diff_vertices {t : Finset M.Vertex}
    (ht : t ∈ M.triangles) :
    (frontier M.toPlaneComplex.support ∩ M.triangleCarrier t) \ Set.range M.position =
      (⋃ e ∈ M.boundaryEdges t,
        convexHull ℝ (M.position '' (e : Set M.Vertex))) \ Set.range M.position := by
  ext p
  constructor
  · rintro ⟨⟨hpFrontier, hpT⟩, hpNotVertex⟩
    have hpv : ∀ v : M.Vertex, p ≠ M.position v := by
      intro v hp
      exact hpNotVertex ⟨v, hp.symm⟩
    obtain ⟨e, he, hpEdge⟩ :=
      (M.mem_frontier_iff_exists_boundaryEdge_of_nonvertex hpv).mp hpFrontier
    obtain ⟨u, hu, heuPower⟩ := Finset.mem_biUnion.mp he.1
    have heuData := Finset.mem_powersetCard.mp heuPower
    have het : e ⊆ t := M.edge_subset_of_nonvertex_mem_triangleCarrier heuData.2
      heuData.1 hu ht hpEdge hpT hpv
    have heBoundary : e ∈ M.boundaryEdges t :=
      M.mem_boundaryEdges_iff.mpr ⟨het, heuData.2, he⟩
    exact ⟨Set.mem_iUnion_of_mem e (Set.mem_iUnion_of_mem heBoundary hpEdge), hpNotVertex⟩
  · rintro ⟨hpUnion, hpNotVertex⟩
    simp only [Set.mem_iUnion] at hpUnion
    obtain ⟨e, heBoundary, hpEdge⟩ := hpUnion
    have heData := M.mem_boundaryEdges_iff.mp heBoundary
    have hpv : ∀ v : M.Vertex, p ≠ M.position v := by
      intro v hp
      exact hpNotVertex ⟨v, hp.symm⟩
    refine ⟨⟨M.mem_frontier_of_mem_boundaryEdge heData.2.2 hpEdge hpv, ?_⟩,
      hpNotVertex⟩
    exact convexHull_mono (Set.image_mono heData.1) hpEdge

/-- No mesh vertex contributes an isolated point to this triangle's frontier trace. -/
def HasNoIsolatedFrontierVertex (t : Finset M.Vertex) : Prop :=
  ∀ v : M.Vertex, M.position v ∈ frontier M.toPlaneComplex.support →
    M.position v ∈ M.triangleCarrier t →
      ∃ e ∈ M.boundaryEdges t,
        M.position v ∈ convexHull ℝ (M.position '' (e : Set M.Vertex))

/-- An isolated point in a triangle's frontier trace must be one of the triangle's own
vertices.  This remains valid when the mesh vertex type contains unused retained vertices. -/
theorem vertex_mem_triangle_of_frontier_not_mem_boundaryEdges (T : M.Triangle)
    (v : M.Vertex) (hvFrontier : M.position v ∈ frontier M.toPlaneComplex.support)
    (hvTriangle : M.position v ∈ M.triangleCarrier T.1)
    (hvBoundary : ∀ e ∈ M.boundaryEdges T.1,
      M.position v ∉ convexHull ℝ (M.position '' (e : Set M.Vertex))) :
    v ∈ T.1 := by
  have htriangleSubset : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1
      (Set.subset_iUnion_of_subset T.2 (by rfl))
  have hvNotInterior : M.position v ∉ interior (M.triangleCarrier T.1) := by
    intro hvInterior
    have hvSupportInterior := interior_mono htriangleSubset hvInterior
    exact Set.disjoint_left.mp disjoint_interior_frontier hvSupportInterior hvFrontier
  have htriangleClosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hvTriangleFrontier : M.position v ∈ frontier (M.triangleCarrier T.1) := by
    rw [htriangleClosed.frontier_eq]
    exact ⟨hvTriangle, hvNotInterior⟩
  obtain ⟨e, hecard, heT, hvEdge⟩ :=
    M.exists_edge_of_mem_frontier_triangle T.2 hvTriangleFrontier
  have hvEdgeVertices : M.position v ∈ M.position '' (e : Set M.Vertex) := by
    by_contra hvNotVertices
    by_cases heBoundary : M.IsBoundaryEdge e
    · have heMem : e ∈ M.boundaryEdges T.1 :=
        M.mem_boundaryEdges_iff.mpr ⟨heT, hecard, heBoundary⟩
      exact hvBoundary e heMem hvEdge
    · have hcard := M.card_incidentTriangles_eq_two_of_not_boundary
          T.2 hecard heT heBoundary
      have hTIncident : T.1 ∈ M.incidentTriangles e :=
        M.mem_incidentTriangles_iff.mpr ⟨T.2, heT⟩
      have hother : ∃ u ∈ M.incidentTriangles e, u ≠ T.1 := by
        by_contra h
        push Not at h
        have hsingleton : M.incidentTriangles e = {T.1} := by
          ext u
          constructor
          · exact fun hu => Finset.mem_singleton.mpr (h u hu)
          · intro hu
            rw [Finset.mem_singleton.mp hu]
            exact hTIncident
        rw [hsingleton] at hcard
        simp at hcard
      obtain ⟨u, huIncident, huT⟩ := hother
      have huData := M.mem_incidentTriangles_iff.mp huIncident
      let U : M.Triangle := ⟨u, huData.1⟩
      have hvInteriorUnion :=
        M.mem_interior_union_triangleCarrier_of_shared_edge_of_not_mem_edgeVertices
          (T := T) (U := U) huT.symm hecard heT huData.2 hvEdge hvNotVertices
      have hUnionSubset : M.triangleCarrier T.1 ∪ M.triangleCarrier U.1 ⊆
          M.toPlaneComplex.support := by
        rw [M.toPlaneComplex_support]
        exact Set.union_subset
          (Set.subset_iUnion_of_subset T.1
            (Set.subset_iUnion_of_subset T.2 (by rfl)))
          (Set.subset_iUnion_of_subset U.1
            (Set.subset_iUnion_of_subset U.2 (by rfl)))
      have hvSupportInterior := interior_mono hUnionSubset hvInteriorUnion
      exact Set.disjoint_left.mp disjoint_interior_frontier hvSupportInterior hvFrontier
  obtain ⟨w, hwe, hwv⟩ := hvEdgeVertices
  have hw : w = v := M.position_injective (hwv.trans rfl)
  rw [← hw]
  exact heT hwe

/-- If two edges of a maximal triangle are boundary edges, every frontier vertex on that
triangle lies on one of them. -/
theorem hasNoIsolatedFrontierVertex_of_boundaryEdges_card_two (T : M.Triangle)
    (hcard : (M.boundaryEdges T.1).card = 2) :
    M.HasNoIsolatedFrontierVertex T.1 := by
  intro v hvFrontier hvTriangle
  by_contra hexists
  push Not at hexists
  have hvT := M.vertex_mem_triangle_of_frontier_not_mem_boundaryEdges
    T v hvFrontier hvTriangle hexists
  obtain ⟨e, f, hef, hboundary⟩ := Finset.card_eq_two.mp hcard
  have heMem : e ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have hfMem : f ∈ M.boundaryEdges T.1 := by rw [hboundary]; simp
  have heData := M.mem_boundaryEdges_iff.mp heMem
  have hfData := M.mem_boundaryEdges_iff.mp hfMem
  have hvNotE : v ∉ e := by
    intro hve
    exact hexists e heMem (subset_convexHull ℝ _ ⟨v, hve, rfl⟩)
  have hvNotF : v ∉ f := by
    intro hvf
    exact hexists f hfMem (subset_convexHull ℝ _ ⟨v, hvf, rfl⟩)
  have heraseCard : (T.1.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hvT, M.card_triangle T.1 T.2]
  have heErase : e = T.1.erase v :=
    Finset.eq_of_subset_of_card_le
      (fun w hw => Finset.mem_erase.mpr
        ⟨fun hwv => hvNotE (hwv ▸ hw), heData.1 hw⟩)
      (by rw [heData.2.1, heraseCard])
  have hfErase : f = T.1.erase v :=
    Finset.eq_of_subset_of_card_le
      (fun w hw => Finset.mem_erase.mpr
        ⟨fun hwv => hvNotF (hwv ▸ hw), hfData.1 hw⟩)
      (by rw [hfData.2.1, heraseCard])
  exact hef (heErase.trans hfErase.symm)

theorem frontier_inter_triangleCarrier_eq_boundaryEdges {t : Finset M.Vertex}
    (ht : t ∈ M.triangles) (hvertices : M.HasNoIsolatedFrontierVertex t) :
    frontier M.toPlaneComplex.support ∩ M.triangleCarrier t =
      ⋃ e ∈ M.boundaryEdges t,
        convexHull ℝ (M.position '' (e : Set M.Vertex)) := by
  apply Set.Subset.antisymm
  · intro p hp
    by_cases hpVertex : p ∈ Set.range M.position
    · obtain ⟨v, rfl⟩ := hpVertex
      obtain ⟨e, he, hpe⟩ := hvertices v hp.1 hp.2
      exact Set.mem_iUnion_of_mem e (Set.mem_iUnion_of_mem he hpe)
    · have hpDiff : p ∈
          (frontier M.toPlaneComplex.support ∩ M.triangleCarrier t) \
            Set.range M.position := ⟨hp, hpVertex⟩
      rw [M.frontier_inter_triangleCarrier_diff_vertices ht] at hpDiff
      exact hpDiff.1
  · intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨e, he, hpe⟩ := hp
    have heData := M.mem_boundaryEdges_iff.mp he
    exact ⟨M.boundaryEdgeCarrier_subset_frontier heData.2.2 hpe,
      convexHull_mono (Set.image_mono heData.1) hpe⟩

/-- An infinite frontier of a finite face-to-face planar mesh contains a boundary edge.  This is
the weak free-triangle existence theorem used at the start of Moise's finite induction. -/
theorem exists_free_triangle (hfrontier : (frontier M.toPlaneComplex.support).Infinite) :
    ∃ t, M.IsFreeTriangle t := by
  classical
  let vertexPositions : Finset Plane := Finset.univ.image M.position
  obtain ⟨p, hpFrontier, hpNotVertex⟩ :=
    hfrontier.exists_notMem_finset vertexPositions
  have hpv : ∀ v : M.Vertex, p ≠ M.position v := by
    intro v hpv
    apply hpNotVertex
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hpv.symm⟩
  obtain ⟨t, ht, e, he, het, -⟩ :=
    M.exists_boundaryEdge_through_frontier_point hpFrontier hpv
  exact ⟨t, ht, e, he, het⟩

/-- The frontier of every nonempty finite planar triangle mesh is infinite. -/
theorem frontier_infinite_of_triangles_nonempty (hne : M.triangles.Nonempty) :
    (frontier M.toPlaneComplex.support).Infinite := by
  classical
  obtain ⟨t, ht⟩ := hne
  let T : M.Triangle := ⟨t, ht⟩
  have hcarrierInterior : (interior (M.triangleCarrier t)).Nonempty := by
    let b := M.triangleAffineBasis ht
    have hrange := M.range_triangleAffineBasis ht
    have hspan : affineSpan ℝ (Set.range b) = ⊤ := b.tot
    have hnonempty := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
    simpa only [triangleCarrier, b, hrange] using hnonempty
  have hcarrierSubset : M.triangleCarrier t ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset t
      (Set.subset_iUnion_of_subset ht (by rfl))
  have hinterior : (interior M.toPlaneComplex.support).Nonempty :=
    hcarrierInterior.mono (interior_mono hcarrierSubset)
  have hsupportClosed : IsClosed M.toPlaneComplex.support :=
    M.toPlaneComplex.isCompact_support.isClosed
  have hsupportNe : M.toPlaneComplex.support ≠ Set.univ :=
    M.toPlaneComplex.isCompact_support.ne_univ
  obtain ⟨q, hq⟩ : (M.toPlaneComplex.supportᶜ).Nonempty :=
    Set.nonempty_compl.mpr hsupportNe
  have hqInterior : q ∈ interior M.toPlaneComplex.supportᶜ := by
    rw [hsupportClosed.isOpen_compl.interior_eq]
    exact hq
  intro hfinite
  have hconnected : IsConnected ((frontier M.toPlaneComplex.support)ᶜ) :=
    hfinite.countable.isConnected_compl_of_one_lt_rank (by
      apply Module.one_lt_rank_of_one_lt_finrank
      simp [Plane])
  have hdecomp : (frontier M.toPlaneComplex.support)ᶜ =
      interior M.toPlaneComplex.support ∪ interior M.toPlaneComplex.supportᶜ :=
    compl_frontier_eq_union_interior
  have hdisjoint : Disjoint (interior M.toPlaneComplex.support)
      (interior M.toPlaneComplex.supportᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  obtain ⟨p, hpInterior⟩ := hinterior
  have hpComplFrontier : p ∈ (frontier M.toPlaneComplex.support)ᶜ := by
    rw [hdecomp]
    exact Or.inl hpInterior
  have hallInterior : (frontier M.toPlaneComplex.support)ᶜ ⊆
      interior M.toPlaneComplex.support :=
    hconnected.isPreconnected.subset_left_of_subset_union isOpen_interior isOpen_interior
      hdisjoint (by rw [hdecomp]) ⟨p, hpComplFrontier, hpInterior⟩
  have hqComplFrontier : q ∈ (frontier M.toPlaneComplex.support)ᶜ := by
    rw [hdecomp]
    exact Or.inr hqInterior
  exact Set.disjoint_left.mp hdisjoint (hallInterior hqComplFrontier) hqInterior

theorem exists_free_triangle_of_triangles_nonempty (hne : M.triangles.Nonempty) :
    ∃ t, M.IsFreeTriangle t :=
  M.exists_free_triangle (M.frontier_infinite_of_triangles_nonempty hne)

end TriangleMesh

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
