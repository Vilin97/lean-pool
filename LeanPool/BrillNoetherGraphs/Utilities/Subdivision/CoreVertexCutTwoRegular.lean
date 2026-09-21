/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCutGenus
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.CycleRigidity

/-!
# Two-regular genus-one factors cut from a subdivided core

The genus checker records the Euler characteristic of each core side.  This
module supplies the complementary local check needed to recognize a cycle:
every retained core vertex has two incident retained **slot occurrences**.
The count is made on `Fin p`, so parallel slots are never collapsed.

The checked condition lifts uniformly through arbitrary positive subdivision
lengths.  Core vertices retain the checked incident-slot degree, while every
interior path vertex has degree two.  Together with core connectedness and a
checked side genus of one, this constructs a `PointedGenusOneRigid` witness.
-/

namespace Utilities.Certificate

open Finset
open ExplicitPotential

namespace CoreVertexCut.Data

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

/-- Number of incidences of retained ordered slots at a named-side core
vertex.  A parallel slot contributes separately; each endpoint contributes
one incidence. -/
def leftIncidentDegree (c : CoreVertexCut.Data core) (vertex : Fin n) : ℕ :=
  ∑ edge ∈ c.leftSlots,
    ((if core.tail edge = vertex then 1 else 0) +
      if core.head edge = vertex then 1 else 0)

/-- Number of incidences of retained ordered slots at a complementary-side
core vertex. -/
def rightIncidentDegree (c : CoreVertexCut.Data core) (vertex : Fin n) : ℕ :=
  ∑ edge ∈ c.rightSlots,
    ((if core.tail edge = vertex then 1 else 0) +
      if core.head edge = vertex then 1 else 0)

/-- Every core vertex retained by the named side has retained degree two. -/
def LeftTwoRegular (c : CoreVertexCut.Data core) : Prop :=
  ∀ vertex : Fin n, vertex ∈ c.left → c.leftIncidentDegree vertex = 2

/-- Every core vertex retained by the complementary side has retained degree
two. -/
def RightTwoRegular (c : CoreVertexCut.Data core) : Prop :=
  ∀ vertex : Fin n, vertex ∈ c.right → c.rightIncidentDegree vertex = 2

instance leftTwoRegularDecidable (c : CoreVertexCut.Data core) :
    Decidable c.LeftTwoRegular := by
  unfold LeftTwoRegular
  infer_instance

instance rightTwoRegularDecidable (c : CoreVertexCut.Data core) :
    Decidable c.RightTwoRegular := by
  unfold RightTwoRegular
  infer_instance

/-- Transparent finite replay of `LeftTwoRegular`. -/
def leftTwoRegularCheck (c : CoreVertexCut.Data core) : Bool :=
  ExplicitPotential.allFin fun vertex : Fin n =>
    decide (vertex ∈ c.left → c.leftIncidentDegree vertex = 2)

/-- Transparent finite replay of `RightTwoRegular`. -/
def rightTwoRegularCheck (c : CoreVertexCut.Data core) : Bool :=
  ExplicitPotential.allFin fun vertex : Fin n =>
    decide (vertex ∈ c.right → c.rightIncidentDegree vertex = 2)

@[simp] theorem leftTwoRegularCheck_eq_true_iff
    (c : CoreVertexCut.Data core) :
    c.leftTwoRegularCheck = true ↔ c.LeftTwoRegular := by
  rw [leftTwoRegularCheck, ExplicitPotential.allFin_eq_true_iff]
  constructor
  · intro h vertex hVertex
    exact (decide_eq_true_eq.mp (h vertex)) hVertex
  · intro h vertex
    exact decide_eq_true_eq.mpr (h vertex)

@[simp] theorem rightTwoRegularCheck_eq_true_iff
    (c : CoreVertexCut.Data core) :
    c.rightTwoRegularCheck = true ↔ c.RightTwoRegular := by
  rw [rightTwoRegularCheck, ExplicitPotential.allFin_eq_true_iff]
  constructor
  · intro h vertex hVertex
    exact (decide_eq_true_eq.mp (h vertex)) hVertex
  · intro h vertex
    exact decide_eq_true_eq.mpr (h vertex)

/-! ## Induced-factor degree calculations -/

-- v4.33: `backward.isDefEq.respectTransparency` now defaults to `true`, so unifying
-- instance-implicit arguments through the semireducible cut/induced-subgraph
-- constructions no longer unfolds them; use the previous transparency locally.
/-- Vertex degree in an induced graph is the ambient internal degree over its
inducing set. -/
private theorem vertex_degree_inducedSubgraph_eq_internalDegree
    (G : CFGraph) (S : Finset G.V) (hS : S.Nonempty)
    (vertex : (inducedSubgraph G S hS).V) :
    vertex_degree (inducedSubgraph G S hS) vertex =
      internalDegree G S vertex.val := by
  classical
  unfold vertex_degree internalDegree
  simp_rw [num_edges_inducedSubgraph]
  exact (Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun neighbor => (num_edges G vertex.val neighbor : ℤ))).symm

-- v4.33: `backward.isDefEq.respectTransparency` now defaults to `true`, so unifying
-- instance-implicit arguments through the semireducible cut/induced-subgraph
-- constructions no longer unfolds them; use the previous transparency locally.
/-- Generic core-vertex calculation for a side described by endpoint
membership. -/
private theorem vertex_degree_induced_coreVertex_eq_incidentSlots
    (spec : SubdivisionGraph.Spec n p)
    (side : Finset (Fin n)) (sideVertices : Finset spec.Vertex)
    (hSideNonempty : sideVertices.Nonempty)
    (hCore : ∀ vertex : Fin n,
      spec.coreVertex vertex ∈ sideVertices ↔ vertex ∈ side)
    (hStep : ∀ edge : Fin p, ∀ offset : Fin (spec.length edge),
      spec.stepLeft edge offset ∈ sideVertices ∧
          spec.stepRight edge offset ∈ sideVertices ↔
        spec.core.tail edge ∈ side ∧ spec.core.head edge ∈ side)
    (vertex : Fin n) (hVertex : vertex ∈ side) :
    vertex_degree (inducedSubgraph spec.graph sideVertices hSideNonempty)
        ⟨spec.coreVertex vertex, (hCore vertex).mpr hVertex⟩ =
      (∑ edge : Fin p,
        if spec.core.tail edge ∈ side ∧ spec.core.head edge ∈ side then
          ((if spec.core.tail edge = vertex then 1 else 0) +
            if spec.core.head edge = vertex then 1 else 0)
        else 0 : ℕ) := by
  classical
  rw [vertex_degree_inducedSubgraph_eq_internalDegree]
  unfold internalDegree
  simp_rw [spec.num_edges_eq_sum_steps]
  push_cast
  rw [Finset.sum_comm]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro edge _hEdge
  have hNeighborSum (offset : Fin (spec.length edge)) :
      (∑ neighbor ∈ sideVertices,
        if spec.unitEdge ⟨edge, offset⟩ =
              (spec.coreVertex vertex, neighbor) ∨
            spec.unitEdge ⟨edge, offset⟩ =
              (neighbor, spec.coreVertex vertex)
        then (1 : ℤ) else 0) =
      (if spec.stepLeft edge offset = spec.coreVertex vertex ∧
            spec.stepRight edge offset ∈ sideVertices then 1 else 0) +
        if spec.stepRight edge offset = spec.coreVertex vertex ∧
            spec.stepLeft edge offset ∈ sideVertices then 1 else 0 := by
    have hDistinct := spec.stepLeft_ne_stepRight edge offset
    simp only [SubdivisionGraph.Spec.unitEdge, Prod.mk.injEq]
    by_cases hLeft : spec.stepLeft edge offset = spec.coreVertex vertex
    · have hRight : spec.stepRight edge offset ≠ spec.coreVertex vertex := by
        intro h
        exact hDistinct (hLeft.trans h.symm)
      simp [hLeft, hRight]
    · by_cases hRight : spec.stepRight edge offset = spec.coreVertex vertex
      · simp [hLeft, hRight]
      · simp [hLeft, hRight]
  simp_rw [hNeighborSum]
  have hBoth (offset : Fin (spec.length edge)) :
      (spec.stepLeft edge offset = spec.coreVertex vertex ∧
          spec.stepRight edge offset ∈ sideVertices) ↔
        (spec.stepLeft edge offset = spec.coreVertex vertex ∧
          (spec.core.tail edge ∈ side ∧ spec.core.head edge ∈ side)) := by
    constructor
    · rintro ⟨hLeft, hRightMem⟩
      refine ⟨hLeft, (hStep edge offset).mp ?_⟩
      constructor
      · rw [hLeft]
        exact (hCore vertex).mpr hVertex
      · exact hRightMem
    · rintro ⟨hLeft, hSlot⟩
      exact ⟨hLeft, (hStep edge offset).mpr hSlot |>.2⟩
  have hBoth' (offset : Fin (spec.length edge)) :
      (spec.stepRight edge offset = spec.coreVertex vertex ∧
          spec.stepLeft edge offset ∈ sideVertices) ↔
        (spec.stepRight edge offset = spec.coreVertex vertex ∧
          (spec.core.tail edge ∈ side ∧ spec.core.head edge ∈ side)) := by
    constructor
    · rintro ⟨hRight, hLeftMem⟩
      refine ⟨hRight, (hStep edge offset).mp ?_⟩
      constructor
      · exact hLeftMem
      · rw [hRight]
        exact (hCore vertex).mpr hVertex
    · rintro ⟨hRight, hSlot⟩
      exact ⟨hRight, (hStep edge offset).mpr hSlot |>.1⟩
  simp_rw [hBoth, hBoth']
  by_cases hSlot : spec.core.tail edge ∈ side ∧ spec.core.head edge ∈ side
  · simp only [hSlot, and_true, if_true]
    rw [Finset.sum_add_distrib]
    simp_rw [spec.stepLeft_eq_coreVertex_iff edge,
      spec.stepRight_eq_coreVertex_iff edge]
    have hFirst :
        (∑ offset : Fin (spec.length edge),
          if offset.val = 0 ∧ spec.core.tail edge = vertex
          then (1 : ℤ) else 0) =
          if spec.core.tail edge = vertex then 1 else 0 := by
      by_cases hTail : spec.core.tail edge = vertex
      · let first : Fin (spec.length edge) :=
          ⟨0, spec.length_pos edge⟩
        calc
          (∑ offset : Fin (spec.length edge),
              if offset.val = 0 ∧ spec.core.tail edge = vertex
              then (1 : ℤ) else 0) =
              (if first.val = 0 ∧ spec.core.tail edge = vertex
                then (1 : ℤ) else 0) := by
            apply Fintype.sum_eq_single first
            intro offset hne
            rw [if_neg]
            intro hzero
            apply hne
            apply Fin.ext
            exact hzero.1
          _ = if spec.core.tail edge = vertex then 1 else 0 := by
            simp [first, hTail]
      · simp [hTail]
    have hLast :
        (∑ offset : Fin (spec.length edge),
          if offset.val + 1 = spec.length edge ∧ spec.core.head edge = vertex
          then (1 : ℤ) else 0) =
          if spec.core.head edge = vertex then 1 else 0 := by
      by_cases hHead : spec.core.head edge = vertex
      · let last : Fin (spec.length edge) :=
          ⟨spec.length edge - 1, by
            have := spec.length_pos edge
            omega⟩
        have hLastValue : last.val + 1 = spec.length edge := by
          dsimp [last]
          have := spec.length_pos edge
          omega
        calc
          (∑ offset : Fin (spec.length edge),
              if offset.val + 1 = spec.length edge ∧
                  spec.core.head edge = vertex
              then (1 : ℤ) else 0) =
              (if last.val + 1 = spec.length edge ∧
                  spec.core.head edge = vertex
                then (1 : ℤ) else 0) := by
            apply Fintype.sum_eq_single last
            intro offset hne
            rw [if_neg]
            intro hlast
            apply hne
            apply Fin.ext
            dsimp [last]
            omega
          _ = if spec.core.head edge = vertex then 1 else 0 := by
            simp [hLastValue, hHead]
      · simp [hHead]
    rw [hFirst, hLast]
  · simp [hSlot]

variable (spec : SubdivisionGraph.Spec n p)
variable (c : CoreVertexCut.Data spec.core)

/-- The core vertices in the derived subdivision side are exactly the core
vertices in `right`. -/
@[simp] theorem mem_rightVertices_core (vertex : Fin n) :
    spec.coreVertex vertex ∈ c.rightVertices spec ↔ vertex ∈ c.right := by
  rw [c.mem_rightVertices_iff spec, c.mem_right_iff]
  constructor
  · rintro (hEqual | hNotLeft)
    · exact Or.inl (Sum.inl.inj hEqual)
    · exact Or.inr (by simpa using hNotLeft)
  · rintro (hEqual | hNotLeft)
    · exact Or.inl (congrArg Sum.inl hEqual)
    · exact Or.inr (by simpa using hNotLeft)

/-- Under valid cut data, an interior belongs to the derived subdivision side
exactly when its parent slot lies wholly in the derived core side. -/
theorem mem_rightVertices_interior_iff (h : c.Valid)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.interiorVertex edge offset ∈ c.rightVertices spec ↔
      c.RightSlot edge := by
  rw [c.mem_rightVertices_iff spec]
  have hNe : spec.interiorVertex edge offset ≠ spec.coreVertex c.glue := by
    simp [SubdivisionGraph.Spec.interiorVertex,
      SubdivisionGraph.Spec.coreVertex]
  simp only [hNe, false_or]
  rw [c.mem_leftVertices_interior spec]
  constructor
  · intro hNotLeft
    rcases c.leftSlot_or_rightSlot h edge with hLeft | hRight
    · exact False.elim (hNotLeft hLeft)
    · exact hRight
  · intro hRight hLeft
    exact c.not_leftSlot_and_rightSlot spec.core_loopless edge
      ⟨hLeft, hRight⟩

/-- A unit step lies wholly in the derived subdivision side exactly when its
parent slot lies wholly in the derived core side. -/
theorem step_mem_rightVertices_iff (h : c.Valid) (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    spec.stepLeft edge offset ∈ c.rightVertices spec ∧
        spec.stepRight edge offset ∈ c.rightVertices spec ↔
      c.RightSlot edge := by
  have hCoreEq (first second : Fin n) :
      spec.coreVertex first = spec.coreVertex second ↔ first = second := by
    simp [SubdivisionGraph.Spec.coreVertex]
  unfold SubdivisionGraph.Spec.stepLeft SubdivisionGraph.Spec.stepRight
  split_ifs with hzero hlast
  · simp [RightSlot, hCoreEq, c.mem_leftVertices_core spec]
  · simp [RightSlot, hCoreEq, c.mem_leftVertices_core spec,
      c.mem_rightVertices_interior_iff spec h]
  · simp [RightSlot, hCoreEq, c.mem_leftVertices_core spec,
      c.mem_rightVertices_interior_iff spec h]
  · simp [RightSlot, c.mem_rightVertices_interior_iff spec h]

/-- Named-factor core vertices have exactly the finite retained incidence
count, independently of subdivision lengths. -/
theorem leftGraph_vertex_degree_coreVertex (h : c.Valid)
    (vertex : Fin n) (hVertex : vertex ∈ c.left) :
    vertex_degree (c.toOneVertexCut spec h).leftGraph
        ⟨spec.coreVertex vertex, c.mem_leftVertices_core spec vertex |>.mpr hVertex⟩ =
      (c.leftIncidentDegree vertex : ℤ) := by
  rw [leftIncidentDegree, leftSlots, Finset.sum_filter]
  exact vertex_degree_induced_coreVertex_eq_incidentSlots spec c.left
    (c.leftVertices spec) (c.toOneVertexCut spec h).left_nonempty
    (c.mem_leftVertices_core spec)
    (c.step_mem_leftVertices_iff spec) vertex hVertex

/-- Complementary-factor core vertices have exactly the finite retained
incidence count, independently of subdivision lengths. -/
theorem rightGraph_vertex_degree_coreVertex (h : c.Valid)
    (vertex : Fin n) (hVertex : vertex ∈ c.right) :
    vertex_degree (c.toOneVertexCut spec h).rightGraph
        ⟨spec.coreVertex vertex, c.mem_rightVertices_core spec vertex |>.mpr hVertex⟩ =
      (c.rightIncidentDegree vertex : ℤ) := by
  rw [rightIncidentDegree, rightSlots, Finset.sum_filter]
  exact vertex_degree_induced_coreVertex_eq_incidentSlots spec c.right
    (c.rightVertices spec) (c.toOneVertexCut spec h).right_nonempty
    (c.mem_rightVertices_core spec)
    (c.step_mem_rightVertices_iff spec h) vertex hVertex

-- v4.33: `backward.isDefEq.respectTransparency` now defaults to `true`, so unifying
-- instance-implicit arguments through the semireducible cut/induced-subgraph
-- constructions no longer unfolds them; use the previous transparency locally.
/-- An interior path vertex has degree two in any induced side which retains
its whole parent slot. -/
private theorem vertex_degree_induced_interiorVertex_eq_two
    (sideVertices : Finset spec.Vertex) (hSideNonempty : sideVertices.Nonempty)
    (slot : Fin p → Prop)
    (hStep : ∀ edge : Fin p, ∀ offset : Fin (spec.length edge),
      spec.stepLeft edge offset ∈ sideVertices ∧
          spec.stepRight edge offset ∈ sideVertices ↔ slot edge)
    (edge : Fin p) (offset : Fin (spec.length edge - 1))
    (hSlot : slot edge) :
    vertex_degree (inducedSubgraph spec.graph sideVertices hSideNonempty)
        ⟨spec.interiorVertex edge offset, by
          have hEnds := (hStep edge (spec.previousStep edge offset)).mpr hSlot
          simpa using hEnds.2⟩ = 2 := by
  have hPreviousMem : spec.previousVertex edge offset ∈ sideVertices := by
    exact ((hStep edge (spec.previousStep edge offset)).mpr hSlot).1
  have hNextMem : spec.nextVertex edge offset ∈ sideVertices := by
    exact ((hStep edge (spec.nextStep edge offset)).mpr hSlot).2
  have hOut :
      outdeg_S spec.graph sideVertices
        (spec.interiorVertex edge offset) = 0 := by
    unfold outdeg_S
    apply Finset.sum_eq_zero
    intro neighbor hNeighbor
    have hNeighborNot : neighbor ∉ sideVertices := by
      simpa using hNeighbor
    have hZero :
        num_edges spec.graph (spec.interiorVertex edge offset) neighbor = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hPositive
      rcases (spec.interior_num_edges_pos_iff edge offset neighbor).mp
          hPositive with hPrevious | hNext
      · exact hNeighborNot (hPrevious ▸ hPreviousMem)
      · exact hNeighborNot (hNext ▸ hNextMem)
    simp [hZero]
  rw [vertex_degree_inducedSubgraph_eq_internalDegree]
  have hDecomposition :=
    vertex_degree_eq_internalDegree_add_outdeg_S spec.graph sideVertices
      (spec.interiorVertex edge offset)
  rw [hOut, add_zero] at hDecomposition
  rw [← hDecomposition]
  exact spec.vertex_degree_interiorVertex_eq_two edge offset

/-- A checked two-regular named core side remains two-regular after every
positive subdivision. -/
theorem leftGraph_vertex_degree_two (h : c.Valid) (hRegular : c.LeftTwoRegular) :
    ∀ vertex : (c.toOneVertexCut spec h).leftGraph.V,
      vertex_degree (c.toOneVertexCut spec h).leftGraph vertex = 2 := by
  rintro ⟨vertex, hVertex⟩
  rcases vertex with coreVertex | interior
  · have hCore : coreVertex ∈ c.left :=
      (c.mem_leftVertices_core spec coreVertex).mp hVertex
    let named : (c.toOneVertexCut spec h).leftGraph.V :=
      ⟨spec.coreVertex coreVertex,
        (c.mem_leftVertices_core spec coreVertex).mpr hCore⟩
    have hEqual :
        (⟨Sum.inl coreVertex, hVertex⟩ :
          (c.toOneVertexCut spec h).leftGraph.V) = named := by
      apply Subtype.ext
      rfl
    rw [hEqual]
    exact c.leftGraph_vertex_degree_coreVertex spec h coreVertex hCore |>.trans
      (by exact_mod_cast hRegular coreVertex hCore)
  · obtain ⟨edge, offset⟩ := interior
    have hSlot : c.LeftSlot edge :=
      (c.mem_leftVertices_interior spec edge offset).mp hVertex
    exact vertex_degree_induced_interiorVertex_eq_two spec
      (c.leftVertices spec) (c.toOneVertexCut spec h).left_nonempty
      c.LeftSlot (c.step_mem_leftVertices_iff spec) edge offset hSlot

/-- A checked two-regular complementary core side remains two-regular after
every positive subdivision. -/
theorem rightGraph_vertex_degree_two (h : c.Valid)
    (hRegular : c.RightTwoRegular) :
    ∀ vertex : (c.toOneVertexCut spec h).rightGraph.V,
      vertex_degree (c.toOneVertexCut spec h).rightGraph vertex = 2 := by
  rintro ⟨vertex, hVertex⟩
  rcases vertex with coreVertex | interior
  · have hCore : coreVertex ∈ c.right :=
      (c.mem_rightVertices_core spec coreVertex).mp hVertex
    let named : (c.toOneVertexCut spec h).rightGraph.V :=
      ⟨spec.coreVertex coreVertex,
        (c.mem_rightVertices_core spec coreVertex).mpr hCore⟩
    have hEqual :
        (⟨Sum.inl coreVertex, hVertex⟩ :
          (c.toOneVertexCut spec h).rightGraph.V) = named := by
      apply Subtype.ext
      rfl
    rw [hEqual]
    exact c.rightGraph_vertex_degree_coreVertex spec h coreVertex hCore |>.trans
      (by exact_mod_cast hRegular coreVertex hCore)
  · obtain ⟨edge, offset⟩ := interior
    have hSlot : c.RightSlot edge :=
      (c.mem_rightVertices_interior_iff spec h edge offset).mp hVertex
    exact vertex_degree_induced_interiorVertex_eq_two spec
      (c.rightVertices spec) (c.toOneVertexCut spec h).right_nonempty
      c.RightSlot (c.step_mem_rightVertices_iff spec h) edge offset hSlot

end CoreVertexCut.Data

universe uTwoRegular

/-- A loopless graph in which every vertex has degree two has a vertex other
than any prescribed mark. -/
theorem exists_vertex_ne_of_vertexDegree_two
    (H : CFGraph.{uTwoRegular}) (marked : H.V)
    (hDegree : ∀ vertex : H.V, vertex_degree H vertex = 2) :
    ∃ other : H.V, other ≠ marked := by
  by_contra hNoOther
  push Not at hNoOther
  have hZero : vertex_degree H marked = 0 := by
    rw [vertex_degree]
    apply Finset.sum_eq_zero
    intro vertex _hVertex
    rw [hNoOther vertex]
    simp
  rw [hDegree marked] at hZero
  omega

namespace CoreVertexCut.Data

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

/-- Exact finite conditions which make the named factor a pointed rigid
genus-one graph. -/
def LeftRigidConditions (c : CoreVertexCut.Data core) : Prop :=
  c.Valid ∧ core.Connected ∧ c.LeftTwoRegular ∧ c.leftGenus = 1

/-- Exact finite conditions which make the complementary factor a pointed
rigid genus-one graph. -/
def RightRigidConditions (c : CoreVertexCut.Data core) : Prop :=
  c.Valid ∧ core.Connected ∧ c.RightTwoRegular ∧ c.rightGenus = 1

/-- Single executable check for a named pointed rigid genus-one factor. -/
def leftRigidCheck (c : CoreVertexCut.Data core) : Bool :=
  c.check && core.connectedCheck && c.leftTwoRegularCheck &&
    decide (c.leftGenus = 1)

/-- Single executable check for a complementary pointed rigid genus-one
factor. -/
def rightRigidCheck (c : CoreVertexCut.Data core) : Bool :=
  c.check && core.connectedCheck && c.rightTwoRegularCheck &&
    decide (c.rightGenus = 1)

@[simp] theorem leftRigidCheck_eq_true_iff (c : CoreVertexCut.Data core) :
    c.leftRigidCheck = true ↔ c.LeftRigidConditions := by
  simp only [leftRigidCheck, Bool.and_eq_true, check_eq_true_iff,
    ExplicitPotential.Core.connectedCheck_eq_true_iff,
    leftTwoRegularCheck_eq_true_iff, decide_eq_true_eq]
  simp [LeftRigidConditions, and_assoc]

@[simp] theorem rightRigidCheck_eq_true_iff (c : CoreVertexCut.Data core) :
    c.rightRigidCheck = true ↔ c.RightRigidConditions := by
  simp only [rightRigidCheck, Bool.and_eq_true, check_eq_true_iff,
    ExplicitPotential.Core.connectedCheck_eq_true_iff,
    rightTwoRegularCheck_eq_true_iff, decide_eq_true_eq]
  simp [RightRigidConditions, and_assoc]

variable (spec : SubdivisionGraph.Spec n p)
variable (c : CoreVertexCut.Data spec.core)

/-- Finite core conditions construct pointed genus-one rigidity on the named
factor, uniformly in all positive subdivision lengths. -/
theorem leftPointedGenusOneRigid (h : c.LeftRigidConditions) :
    PointedGenusOneRigid (c.toOneVertexCut spec h.1).leftGraph
      (c.toOneVertexCut spec h.1).leftGlue := by
  let cut := c.toOneVertexCut spec h.1
  have hConnectedAmbient : graph_connected spec.graph :=
    spec.graph_connected_of_coreConnected h.2.1
  have hConnected : graph_connected cut.leftGraph :=
    cut.graph_connected_left_of_connected hConnectedAmbient
  have hDegree : ∀ vertex : cut.leftGraph.V,
      vertex_degree cut.leftGraph vertex = 2 :=
    c.leftGraph_vertex_degree_two spec h.1 h.2.2.1
  apply pointedGenusOneRigid_of_twoEdgeCutCondition cut.leftGlue hConnected
  · rw [c.leftGraph_genus spec h.1, h.2.2.2]
  · exact exists_vertex_ne_of_vertexDegree_two cut.leftGraph cut.leftGlue hDegree
  · exact twoEdgeCutCondition_of_connected_vertexDegree_two hConnected hDegree

/-- Finite core conditions construct pointed genus-one rigidity on the
complementary factor, uniformly in all positive subdivision lengths. -/
theorem rightPointedGenusOneRigid (h : c.RightRigidConditions) :
    PointedGenusOneRigid (c.toOneVertexCut spec h.1).rightGraph
      (c.toOneVertexCut spec h.1).rightGlue := by
  let cut := c.toOneVertexCut spec h.1
  have hConnectedAmbient : graph_connected spec.graph :=
    spec.graph_connected_of_coreConnected h.2.1
  have hConnected : graph_connected cut.rightGraph :=
    cut.graph_connected_right_of_connected hConnectedAmbient
  have hDegree : ∀ vertex : cut.rightGraph.V,
      vertex_degree cut.rightGraph vertex = 2 :=
    c.rightGraph_vertex_degree_two spec h.1 h.2.2.1
  apply pointedGenusOneRigid_of_twoEdgeCutCondition cut.rightGlue hConnected
  · rw [c.rightGraph_genus spec h.1, h.2.2.2]
  · exact exists_vertex_ne_of_vertexDegree_two cut.rightGraph cut.rightGlue hDegree
  · exact twoEdgeCutCondition_of_connected_vertexDegree_two hConnected hDegree

/-- Checker-facing named-factor rigidity constructor. -/
theorem leftPointedGenusOneRigid_of_check (hCheck : c.leftRigidCheck = true) :
    PointedGenusOneRigid
      (c.cutOfCheck spec ((check_eq_true_iff c).mpr
        ((leftRigidCheck_eq_true_iff c).mp hCheck).1)).leftGraph
      (c.cutOfCheck spec ((check_eq_true_iff c).mpr
        ((leftRigidCheck_eq_true_iff c).mp hCheck).1)).leftGlue := by
  exact c.leftPointedGenusOneRigid spec
    ((leftRigidCheck_eq_true_iff c).mp hCheck)

/-- Checker-facing complementary-factor rigidity constructor. -/
theorem rightPointedGenusOneRigid_of_check (hCheck : c.rightRigidCheck = true) :
    PointedGenusOneRigid
      (c.cutOfCheck spec ((check_eq_true_iff c).mpr
        ((rightRigidCheck_eq_true_iff c).mp hCheck).1)).rightGraph
      (c.cutOfCheck spec ((check_eq_true_iff c).mpr
        ((rightRigidCheck_eq_true_iff c).mp hCheck).1)).rightGlue := by
  exact c.rightPointedGenusOneRigid spec
    ((rightRigidCheck_eq_true_iff c).mp hCheck)

/-! ## Closed non-unit parallel-slot regression -/

private def twoCyclesCore : ExplicitPotential.Core 3 4 where
  tail
    | 0 => 0
    | 1 => 0
    | 2 => 1
    | 3 => 1
  head
    | 0 => 1
    | 1 => 1
    | 2 => 2
    | 3 => 2

private def twoCyclesCut : CoreVertexCut.Data twoCyclesCore where
  glue := 1
  left := {0, 1}

private def twoCyclesSpec : SubdivisionGraph.Spec 3 4 where
  core := twoCyclesCore
  length
    | 0 => 2
    | 1 => 3
    | 2 => 4
    | 3 => 5
  core_nonempty := by decide
  core_loopless := by decide
  length_pos := by decide

private theorem twoCyclesCut_leftRigidCheck :
    twoCyclesCut.leftRigidCheck = true := by decide

private theorem twoCyclesCut_rightRigidCheck :
    twoCyclesCut.rightRigidCheck = true := by decide

private theorem twoCyclesCut_leftRigid :
    PointedGenusOneRigid
      (twoCyclesCut.cutOfCheck twoCyclesSpec
        ((check_eq_true_iff twoCyclesCut).mpr
          ((leftRigidCheck_eq_true_iff twoCyclesCut).mp
            twoCyclesCut_leftRigidCheck).1)).leftGraph
      (twoCyclesCut.cutOfCheck twoCyclesSpec
        ((check_eq_true_iff twoCyclesCut).mpr
          ((leftRigidCheck_eq_true_iff twoCyclesCut).mp
            twoCyclesCut_leftRigidCheck).1)).leftGlue :=
  twoCyclesCut.leftPointedGenusOneRigid_of_check twoCyclesSpec
    twoCyclesCut_leftRigidCheck

private theorem twoCyclesCut_rightRigid :
    PointedGenusOneRigid
      (twoCyclesCut.cutOfCheck twoCyclesSpec
        ((check_eq_true_iff twoCyclesCut).mpr
          ((rightRigidCheck_eq_true_iff twoCyclesCut).mp
            twoCyclesCut_rightRigidCheck).1)).rightGraph
      (twoCyclesCut.cutOfCheck twoCyclesSpec
        ((check_eq_true_iff twoCyclesCut).mpr
          ((rightRigidCheck_eq_true_iff twoCyclesCut).mp
            twoCyclesCut_rightRigidCheck).1)).rightGlue :=
  twoCyclesCut.rightPointedGenusOneRigid_of_check twoCyclesSpec
    twoCyclesCut_rightRigidCheck

end CoreVertexCut.Data

end Utilities.Certificate
