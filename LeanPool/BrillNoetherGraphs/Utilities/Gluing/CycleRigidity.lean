/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoEdgeConnectedRigidity
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator

/-!
# Rigidity of a subdivided cycle

A metric cycle in the subdivision model is represented by two distinct core
slots joining two core vertices, each assigned an arbitrary positive integral
length.  This file proves that every such subdivision has no one-edge cut and
therefore satisfies the pointed genus-one rigidity interface.
-/

@[expose] public section

namespace Utilities

open Finset
open Certificate

/-! ## Two-regular connected graphs have no one-edge cuts -/

/-- The contribution to the degree of `v` from vertices inside `S`. -/
def internalDegree (H : CFGraph) (S : Finset H.V) (v : H.V) : ℤ :=
  ∑ w ∈ S, (numEdges H v w : ℤ)

/-- The sum of all directed internal edge multiplicities of `S`. -/
def internalMultiplicity (H : CFGraph) (S : Finset H.V) : ℤ :=
  ∑ v ∈ S, internalDegree H S v

theorem vertex_degree_eq_internalDegree_add_outdeg_S
    (H : CFGraph) (S : Finset H.V) (v : H.V) :
    vertexDegree H v = internalDegree H S v + outdegreeSet H S v := by
  let f : H.V → ℤ := fun w => (numEdges H v w : ℤ)
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset H.V) (fun w => w ∈ S) f
  have hInside :
      (Finset.univ.filter fun w : H.V => w ∈ S) = S := by
    ext w
    simp
  have hOutside :
      (Finset.univ.filter fun w : H.V => ¬w ∈ S) =
        Finset.univ.filter fun w : H.V => w ∉ S := by
    rfl
  rw [hInside, hOutside] at hSplit
  simpa [vertexDegree, internalDegree, outdeg_S_eq_sum_filter, f] using hSplit.symm

/-- Restricted handshaking: the directed internal multiplicity is even. -/
theorem internalMultiplicity_even (H : CFGraph) (S : Finset H.V) :
    Even (internalMultiplicity H S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact Even.zero
  | @insert a S ha inductionHypothesis =>
      let cross : ℤ := ∑ w ∈ S, (numEdges H a w : ℤ)
      have hSymm :
          (∑ v ∈ S, (numEdges H v a : ℤ)) = cross := by
        unfold cross
        apply Finset.sum_congr rfl
        intro v _hv
        rw [num_edges_symmetric]
      have hExpand :
          internalMultiplicity H (insert a S) =
            cross + cross + internalMultiplicity H S := by
        unfold internalMultiplicity internalDegree
        rw [Finset.sum_insert ha]
        rw [Finset.sum_insert ha]
        simp only [num_edges_self_zero, Nat.cast_zero, zero_add]
        have hInner (v : H.V) :
            (∑ w ∈ insert a S, (numEdges H v w : ℤ)) =
              (numEdges H v a : ℤ) +
                ∑ w ∈ S, (numEdges H v w : ℤ) := by
          rw [Finset.sum_insert ha]
        simp_rw [hInner]
        rw [Finset.sum_add_distrib, hSymm]
        change cross + (cross + internalMultiplicity H S) =
          cross + cross + internalMultiplicity H S
        ring
      obtain ⟨k, hk⟩ := inductionHypothesis
      refine ⟨cross + k, ?_⟩
      rw [hExpand, hk]
      ring

/-- Sum the degree decomposition over a vertex set. -/
theorem sum_vertex_degree_eq_internalMultiplicity_add_cutMultiplicity
    (H : CFGraph) (S : Finset H.V) :
    (∑ v ∈ S, vertexDegree H v) =
      internalMultiplicity H S + cutMultiplicity H S := by
  calc
    (∑ v ∈ S, vertexDegree H v) =
        ∑ v ∈ S, (internalDegree H S v + outdegreeSet H S v) := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact vertex_degree_eq_internalDegree_add_outdeg_S H S v
    _ = internalMultiplicity H S + cutMultiplicity H S := by
      rw [Finset.sum_add_distrib]
      rfl

/-- A nontrivial cut in a connected graph has positive outgoing
multiplicity. -/
theorem cutMultiplicity_pos_of_connected
    {H : CFGraph} (hConnected : graphConnected H)
    (S : Finset H.V) (hNonempty : S.Nonempty) (hProper : S ≠ Finset.univ) :
    0 < cutMultiplicity H S := by
  obtain ⟨inside, hInside⟩ := hNonempty
  have hOutsideExists : ∃ outside : H.V, outside ∉ S := by
    by_contra hnot
    push Not at hnot
    apply hProper
    ext vertex
    simp [hnot vertex]
  obtain ⟨outside, hOutside⟩ := hOutsideExists
  obtain ⟨x, hxS, y, hyS, hxy⟩ :=
    hConnected S ⟨inside, outside, hInside, hOutside⟩
  have hEdgeOut :
      (numEdges H x y : ℤ) ≤ outdegreeSet H S x := by
    unfold outdegreeSet
    apply Finset.single_le_sum
      (fun z _ => Int.natCast_nonneg (numEdges H x z))
    simp [hyS]
  have hVertexOut : outdegreeSet H S x ≤ cutMultiplicity H S := by
    unfold cutMultiplicity
    apply Finset.single_le_sum
      (fun z _ => outdeg_S_nonneg H S z) hxS
  have hEdgePositive : 0 < (numEdges H x y : ℤ) := by
    exact_mod_cast hxy
  omega

/-- Every connected two-regular loopless multigraph satisfies the two-edge
cut condition. -/
theorem twoEdgeCutCondition_of_connected_vertexDegree_two
    {H : CFGraph} (hConnected : graphConnected H)
    (hDegree : ∀ vertex : H.V, vertexDegree H vertex = 2) :
    TwoEdgeCutCondition H := by
  intro S hNonempty hProper
  have hPositive := cutMultiplicity_pos_of_connected
    hConnected S hNonempty hProper
  have hDegreeSum :
      (∑ v ∈ S, vertexDegree H v) = 2 * (S.card : ℤ) := by
    calc
      (∑ v ∈ S, vertexDegree H v) = ∑ _v ∈ S, (2 : ℤ) := by
        apply Finset.sum_congr rfl
        intro v _hv
        exact hDegree v
      _ = 2 * (S.card : ℤ) := by
        simp only [sum_const, Int.nsmul_eq_mul]
        ring
  obtain ⟨k, hk⟩ := internalMultiplicity_even H S
  have hDecomposition :=
    sum_vertex_degree_eq_internalMultiplicity_add_cutMultiplicity H S
  rw [hDegreeSum, hk] at hDecomposition
  have hEvenCut : Even (cutMultiplicity H S) := by
    refine ⟨(S.card : ℤ) - k, ?_⟩
    omega
  obtain ⟨q, hq⟩ := hEvenCut
  omega

/-! ## The explicit two-path cycle subdivision -/

namespace TwoPathCycle

/-- The ordered core with two parallel slots from vertex `0` to vertex `1`. -/
def core : ExplicitPotential.Core 2 2 where
  tail := fun _ => 0
  head := fun _ => 1

theorem core_connected : core.Connected := by
  exact core.connectedCheck_eq_true_iff.mp (by decide)

/-- Two positive subdivided paths with common endpoints. -/
def spec (length : Fin 2 → ℕ) (hLength : ∀ edge, 0 < length edge) :
    SubdivisionGraph.Spec 2 2 where
  core := core
  length := length
  core_nonempty := by decide
  core_loopless := by decide
  length_pos := hLength

variable (length : Fin 2 → ℕ) (hLength : ∀ edge, 0 < length edge)

theorem connected : graphConnected (spec length hLength).graph := by
  apply (spec length hLength).graph_connected_of_coreConnected
  exact core_connected

@[simp] theorem genus_one : genus (spec length hLength).graph = 1 := by
  rw [(spec length hLength).genus_graph]
  norm_num

end TwoPathCycle

/-! ## Valence calculation for the explicit cycle -/

namespace Certificate.SubdivisionGraph.Spec

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- A core vertex has one incident unit edge for every core slot incident to
it.  Parallel slots are retained separately. -/
theorem vertex_degree_coreVertex_eq_incidentSlots (vertex : Fin n) :
    vertexDegree spec.graph (spec.coreVertex vertex) =
      ∑ edge : Fin p,
        ((if spec.core.tail edge = vertex then 1 else 0) +
          if spec.core.head edge = vertex then 1 else 0) := by
  classical
  rw [vertexDegree]
  simp_rw [spec.num_edges_eq_sum_steps]
  push_cast
  rw [Finset.sum_comm]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro edge _hEdge
  let first : Fin (spec.length edge) := ⟨0, spec.length_pos edge⟩
  let last : Fin (spec.length edge) :=
    ⟨spec.length edge - 1, by have := spec.length_pos edge; omega⟩
  have hFirstSum :
      (∑ offset : Fin (spec.length edge),
        if offset.val = 0 then (1 : ℤ) else 0) = 1 := by
    calc
      (∑ offset : Fin (spec.length edge),
          if offset.val = 0 then (1 : ℤ) else 0) =
          (if first.val = 0 then (1 : ℤ) else 0) := by
        apply Fintype.sum_eq_single first
        intro offset hne
        rw [if_neg]
        intro hzero
        apply hne
        apply Fin.ext
        exact hzero
      _ = 1 := by simp [first]
  have hLastValue : last.val + 1 = spec.length edge := by
    dsimp [last]
    have := spec.length_pos edge
    omega
  have hLastSum :
      (∑ offset : Fin (spec.length edge),
        if offset.val + 1 = spec.length edge then (1 : ℤ) else 0) = 1 := by
    calc
      (∑ offset : Fin (spec.length edge),
          if offset.val + 1 = spec.length edge then (1 : ℤ) else 0) =
          (if last.val + 1 = spec.length edge then (1 : ℤ) else 0) := by
        apply Fintype.sum_eq_single last
        intro offset hne
        rw [if_neg]
        intro hlast
        apply hne
        apply Fin.ext
        dsimp [last]
        omega
      _ = 1 := by simp [hLastValue]
  have hNeighborSum (offset : Fin (spec.length edge)) :
      (∑ neighbor : spec.Vertex,
        if spec.unitEdge ⟨edge, offset⟩ =
              (spec.coreVertex vertex, neighbor) ∨
            spec.unitEdge ⟨edge, offset⟩ =
              (neighbor, spec.coreVertex vertex)
        then (1 : ℤ) else 0) =
      (if spec.stepLeft edge offset = spec.coreVertex vertex then 1 else 0) +
        if spec.stepRight edge offset = spec.coreVertex vertex then 1 else 0 := by
    have hne := spec.stepLeft_ne_stepRight edge offset
    by_cases hLeft : spec.stepLeft edge offset = spec.coreVertex vertex
    · have hRight : spec.stepRight edge offset ≠ spec.coreVertex vertex := by
        intro h
        exact hne (hLeft.trans h.symm)
      rw [if_pos hLeft, if_neg hRight]
      simp only [unitEdge, Prod.mk.injEq]
      simp [hLeft, hRight]
    · by_cases hRight : spec.stepRight edge offset = spec.coreVertex vertex
      · rw [if_neg hLeft, if_pos hRight]
        simp only [unitEdge, Prod.mk.injEq]
        simp [hLeft, hRight]
      · rw [if_neg hLeft, if_neg hRight]
        simp only [unitEdge, Prod.mk.injEq]
        simp [hLeft, hRight]
  simp_rw [hNeighborSum]
  rw [Finset.sum_add_distrib]
  simp_rw [spec.stepLeft_eq_coreVertex_iff edge,
    spec.stepRight_eq_coreVertex_iff edge]
  have hFirstPart :
      (∑ offset : Fin (spec.length edge),
        if offset.val = 0 ∧ spec.core.tail edge = vertex then (1 : ℤ)
          else 0) =
        if spec.core.tail edge = vertex then 1 else 0 := by
    by_cases hTail : spec.core.tail edge = vertex
    · simp only [hTail, and_true, if_true]
      exact hFirstSum
    · simp [hTail]
  have hLastPart :
      (∑ offset : Fin (spec.length edge),
        if offset.val + 1 = spec.length edge ∧
            spec.core.head edge = vertex then (1 : ℤ) else 0) =
        if spec.core.head edge = vertex then 1 else 0 := by
    by_cases hHead : spec.core.head edge = vertex
    · simp only [hHead, and_true, if_true]
      exact hLastSum
    · simp [hHead]
  rw [hFirstPart, hLastPart]

/-- Every interior subdivision vertex has valence exactly two. -/
theorem vertex_degree_interiorVertex_eq_two
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    vertexDegree spec.graph (spec.interiorVertex edge offset) = 2 := by
  classical
  let previous := spec.previousVertex edge offset
  let next := spec.nextVertex edge offset
  have hDistinct : previous ≠ next :=
    spec.previousVertex_ne_nextVertex edge offset
  have hPreviousPositive :
      0 < numEdges spec.graph (spec.interiorVertex edge offset) previous := by
    exact spec.previous_num_edges_pos edge offset
  have hNextPositive :
      0 < numEdges spec.graph (spec.interiorVertex edge offset) next := by
    exact spec.next_num_edges_pos edge offset
  have hPreviousLe := spec.num_edges_interior_le_one edge offset previous
  have hNextLe := spec.num_edges_interior_le_one edge offset next
  have hPrevious :
      numEdges spec.graph (spec.interiorVertex edge offset) previous = 1 := by
    omega
  have hNext :
      numEdges spec.graph (spec.interiorVertex edge offset) next = 1 := by
    omega
  have hOther (vertex : spec.Vertex)
      (hPrev : vertex ≠ previous) (hNextVertex : vertex ≠ next) :
      numEdges spec.graph (spec.interiorVertex edge offset) vertex = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hPositive
    rcases (spec.interior_num_edges_pos_iff edge offset vertex).mp hPositive with
      h | h
    · exact hPrev h
    · exact hNextVertex h
  rw [vertexDegree]
  have hTerm (vertex : spec.Vertex) :
      (numEdges spec.graph (spec.interiorVertex edge offset) vertex : ℤ) =
        if vertex = previous then 1 else if vertex = next then 1 else 0 := by
    by_cases hPrev : vertex = previous
    · subst vertex
      simp [hPrevious]
    · by_cases hNextVertex : vertex = next
      · subst vertex
        simp [hPrev, hNext]
      · simp [hPrev, hNextVertex, hOther vertex hPrev hNextVertex]
  simp_rw [hTerm]
  calc
    (∑ vertex : spec.Vertex,
        if vertex = previous then (1 : ℤ)
        else if vertex = next then 1 else 0) =
        ∑ vertex : spec.Vertex,
          ((if vertex = previous then (1 : ℤ) else 0) +
            if vertex = next then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro vertex _hVertex
      by_cases hPrev : vertex = previous <;>
        by_cases hNextVertex : vertex = next <;>
          simp [hPrev, hNextVertex, hDistinct, hDistinct.symm]
    _ = 2 := by
      rw [Finset.sum_add_distrib]
      simp

end Certificate.SubdivisionGraph.Spec

/-! ## Cycle cut condition and pointed rigidity -/

namespace TwoPathCycle

variable (length : Fin 2 → ℕ) (hLength : ∀ edge, 0 < length edge)

theorem vertex_degree_two
    (vertex : (spec length hLength).graph.V) :
    vertexDegree (spec length hLength).graph vertex = 2 := by
  rcases vertex with coreVertex | interior
  · change vertexDegree (spec length hLength).graph
      ((spec length hLength).coreVertex coreVertex) = 2
    rw [(spec length hLength).vertex_degree_coreVertex_eq_incidentSlots]
    fin_cases coreVertex <;> simp [spec, core]
  · obtain ⟨edge, offset⟩ := interior
    exact (spec length hLength).vertex_degree_interiorVertex_eq_two edge offset

theorem twoEdgeCutCondition :
    TwoEdgeCutCondition (spec length hLength).graph :=
  twoEdgeCutCondition_of_connected_vertexDegree_two
    (connected length hLength) (vertex_degree_two length hLength)

theorem exists_vertex_ne
    (marked : (spec length hLength).graph.V) :
    ∃ other : (spec length hLength).graph.V, other ≠ marked := by
  let left := (spec length hLength).coreVertex (0 : Fin 2)
  let right := (spec length hLength).coreVertex (1 : Fin 2)
  by_cases hLeft : left ≠ marked
  · exact ⟨left, hLeft⟩
  · refine ⟨right, ?_⟩
    intro hRight
    have hLR : left = right := (not_ne_iff.mp hLeft).trans hRight.symm
    exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj hLR)

/-- Every marked vertex of every positive two-path subdivision is a pointed
rigid genus-one graph. -/
theorem pointedGenusOneRigid
    (marked : (spec length hLength).graph.V) :
    PointedGenusOneRigid (spec length hLength).graph marked :=
  pointedGenusOneRigid_of_twoEdgeCutCondition marked
    (connected length hLength) (genus_one length hLength)
    (exists_vertex_ne length hLength marked)
    (twoEdgeCutCondition length hLength)

end TwoPathCycle

end Utilities
