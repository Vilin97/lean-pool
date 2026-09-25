/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ExplicitPotentialRankOne
import Mathlib.Tactic

/-!
# The embedded core is a strong separator of a subdivision

This module supplies the graph-theoretic part of an explicit-potential rank
certificate.  Every component left after removing an enlargement of the embedded
core is a contiguous interval in the interior of one subdivided edge.  Such an
interval has two boundary vertices, at most one boundary edge at each reached
vertex, and the elementary path-cut property required by
`StrongSeparator.ExpansionCell`.
-/

-- `Certificate` is a structure inside a namespace already ending in `Certificate`;
-- renaming either would ripple through every consumer.  Lean v4.33 added
-- `linter.dupNamespace`, which flags exactly this shape.
namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph.Spec

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-! ## Vertices along one subdivided edge -/

/-- Positions from the tail (`0`) through the head (`length`). -/
abbrev PathPosition (edge : Fin p) := Fin (spec.length edge + 1)

/-- The vertex at a path position. -/
def pathVertex (edge : Fin p) (position : spec.PathPosition edge) :
    spec.Vertex :=
  if hzero : position.val = 0 then
    spec.coreVertex (spec.core.tail edge)
  else if hlast : position.val = spec.length edge then
    spec.coreVertex (spec.core.head edge)
  else
    spec.interiorVertex edge
      ⟨position.val - 1, by
        have hle : position.val ≤ spec.length edge := by
          have := position.isLt
          omega
        omega⟩

/-- Position of the left endpoint of a unit step. -/
def stepLeftPosition (edge : Fin p) (offset : Fin (spec.length edge)) :
    spec.PathPosition edge :=
  ⟨offset.val, by have := offset.isLt; omega⟩

/-- Position of the right endpoint of a unit step. -/
def stepRightPosition (edge : Fin p) (offset : Fin (spec.length edge)) :
    spec.PathPosition edge :=
  ⟨offset.val + 1, by have := offset.isLt; omega⟩

@[simp] theorem pathVertex_zero (edge : Fin p) :
    spec.pathVertex edge ⟨0, by omega⟩ =
      spec.coreVertex (spec.core.tail edge) := by
  simp [pathVertex]

@[simp] theorem pathVertex_length (edge : Fin p) :
    spec.pathVertex edge
        ⟨spec.length edge, by omega⟩ =
      spec.coreVertex (spec.core.head edge) := by
  have hpos := spec.length_pos edge
  simp [pathVertex, hpos.ne']

@[simp] theorem pathVertex_stepLeftPosition (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    spec.pathVertex edge (spec.stepLeftPosition edge offset) =
      spec.stepLeft edge offset := by
  unfold pathVertex stepLeftPosition stepLeft
  by_cases hzero : offset.val = 0
  · simp [hzero]
  · have hlast : offset.val ≠ spec.length edge := by
      have := offset.isLt
      omega
    simp [hzero, hlast]

@[simp] theorem pathVertex_stepRightPosition (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    spec.pathVertex edge (spec.stepRightPosition edge offset) =
      spec.stepRight edge offset := by
  unfold pathVertex stepRightPosition stepRight
  by_cases hlast : offset.val + 1 = spec.length edge
  · have hpos := spec.length_pos edge
    simp [hlast, hpos.ne']
  · simp [hlast]

/-- Distinct positions on one loopless core slot give distinct subdivision
vertices, including its two core endpoints. -/
theorem pathVertex_injective (edge : Fin p) :
    Function.Injective (spec.pathVertex edge) := by
  intro left right hEqual
  unfold pathVertex at hEqual
  by_cases hLeftZero : left.val = 0
  · rw [dif_pos hLeftZero] at hEqual
    by_cases hRightZero : right.val = 0
    · exact Fin.ext (hLeftZero.trans hRightZero.symm)
    · rw [dif_neg hRightZero] at hEqual
      by_cases hRightLast : right.val = spec.length edge
      · rw [dif_pos hRightLast] at hEqual
        have hEnds : spec.core.tail edge = spec.core.head edge :=
          Sum.inl.inj hEqual
        exact (spec.core_loopless edge hEnds).elim
      · rw [dif_neg hRightLast] at hEqual
        simp [coreVertex, interiorVertex] at hEqual
  · rw [dif_neg hLeftZero] at hEqual
    by_cases hLeftLast : left.val = spec.length edge
    · rw [dif_pos hLeftLast] at hEqual
      by_cases hRightZero : right.val = 0
      · rw [dif_pos hRightZero] at hEqual
        have hEnds : spec.core.head edge = spec.core.tail edge :=
          Sum.inl.inj hEqual
        exact (spec.core_loopless edge hEnds.symm).elim
      · rw [dif_neg hRightZero] at hEqual
        by_cases hRightLast : right.val = spec.length edge
        · exact Fin.ext (hLeftLast.trans hRightLast.symm)
        · rw [dif_neg hRightLast] at hEqual
          simp [coreVertex, interiorVertex] at hEqual
    · rw [dif_neg hLeftLast] at hEqual
      by_cases hRightZero : right.val = 0
      · rw [dif_pos hRightZero] at hEqual
        simp [coreVertex, interiorVertex] at hEqual
      · rw [dif_neg hRightZero] at hEqual
        by_cases hRightLast : right.val = spec.length edge
        · rw [dif_pos hRightLast] at hEqual
          simp [coreVertex, interiorVertex] at hEqual
        · rw [dif_neg hRightLast] at hEqual
          apply Fin.ext
          have hSigma := Sum.inr.inj hEqual
          have hOffsets : left.val - 1 = right.val - 1 :=
            congrArg (fun interior : spec.Interior => interior.2.val) hSigma
          omega

/-- Consecutive positions are joined by the corresponding unit step. -/
theorem consecutive_num_edges_pos (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    0 < numEdges spec.graph
      (spec.pathVertex edge (spec.stepLeftPosition edge offset))
      (spec.pathVertex edge (spec.stepRightPosition edge offset)) := by
  simpa using spec.unitStep_num_edges_pos edge offset

/-- A numerical path position is strictly internal to its edge. -/
def IsInteriorPosition (edge : Fin p) (position : spec.PathPosition edge) :
    Prop :=
  0 < position.val ∧ position.val < spec.length edge

/-- Interior-vertex coordinate represented by an internal path position. -/
def interiorOffsetOfPosition (edge : Fin p)
    (position : spec.PathPosition edge)
    (hInterior : spec.IsInteriorPosition edge position) :
    Fin (spec.length edge - 1) :=
  ⟨position.val - 1, by
    change 0 < position.val ∧ position.val < spec.length edge at hInterior
    omega⟩

/-- Predecessor of a positive path position. -/
def previousPathPosition (edge : Fin p)
    (position : spec.PathPosition edge) (hPositive : 0 < position.val) :
    spec.PathPosition edge :=
  ⟨position.val - 1, by
    have := position.isLt
    omega⟩

/-- Successor of a position strictly before the head. -/
def nextPathPosition (edge : Fin p)
    (position : spec.PathPosition edge)
    (hBeforeHead : position.val < spec.length edge) :
    spec.PathPosition edge :=
  ⟨position.val + 1, by omega⟩

theorem pathVertex_eq_interiorVertex (edge : Fin p)
    (position : spec.PathPosition edge)
    (hInterior : spec.IsInteriorPosition edge position) :
    spec.pathVertex edge position =
      spec.interiorVertex edge
        (spec.interiorOffsetOfPosition edge position hInterior) := by
  unfold pathVertex interiorOffsetOfPosition IsInteriorPosition at *
  rw [dif_neg hInterior.1.ne', dif_neg (ne_of_lt hInterior.2)]

theorem previousVertex_eq_pathVertex (edge : Fin p)
    (position : spec.PathPosition edge)
    (hInterior : spec.IsInteriorPosition edge position) :
    spec.previousVertex edge
        (spec.interiorOffsetOfPosition edge position hInterior) =
      spec.pathVertex edge
        (spec.previousPathPosition edge position hInterior.1) := by
  change 0 < position.val ∧ position.val < spec.length edge at hInterior
  unfold previousVertex
  rw [← spec.pathVertex_stepLeftPosition edge
    (spec.previousStep edge
      (spec.interiorOffsetOfPosition edge position hInterior))]
  apply congrArg (spec.pathVertex edge)
  apply Fin.ext
  simp only [stepLeftPosition, previousStep, interiorOffsetOfPosition,
    previousPathPosition]

theorem nextVertex_eq_pathVertex (edge : Fin p)
    (position : spec.PathPosition edge)
    (hInterior : spec.IsInteriorPosition edge position) :
    spec.nextVertex edge
        (spec.interiorOffsetOfPosition edge position hInterior) =
      spec.pathVertex edge
        (spec.nextPathPosition edge position hInterior.2) := by
  change 0 < position.val ∧ position.val < spec.length edge at hInterior
  unfold nextVertex
  rw [← spec.pathVertex_stepRightPosition edge
    (spec.nextStep edge
      (spec.interiorOffsetOfPosition edge position hInterior))]
  apply congrArg (spec.pathVertex edge)
  apply Fin.ext
  simp only [stepRightPosition, nextStep, interiorOffsetOfPosition,
    nextPathPosition]
  omega

/-- At an internal path position, positivity of an edge multiplicity is
equivalent to being the immediately preceding or following path vertex. -/
theorem pathVertex_num_edges_pos_iff (edge : Fin p)
    (position : spec.PathPosition edge)
    (hInterior : spec.IsInteriorPosition edge position)
    (vertex : spec.Vertex) :
    0 < numEdges spec.graph (spec.pathVertex edge position) vertex ↔
      vertex = spec.pathVertex edge
          (spec.previousPathPosition edge position hInterior.1) ∨
        vertex = spec.pathVertex edge
          (spec.nextPathPosition edge position hInterior.2) := by
  rw [spec.pathVertex_eq_interiorVertex edge position hInterior,
    spec.interior_num_edges_pos_iff]
  rw [spec.previousVertex_eq_pathVertex edge position hInterior,
    spec.nextVertex_eq_pathVertex edge position hInterior]

/-- The two path neighbors of an interior subdivision vertex are distinct. -/
theorem previousVertex_ne_nextVertex (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    spec.previousVertex edge offset ≠ spec.nextVertex edge offset := by
  let position : spec.PathPosition edge :=
    ⟨offset.val + 1, by
      have := offset.isLt
      have hpos := spec.length_pos edge
      omega⟩
  have hInterior : spec.IsInteriorPosition edge position := by
    change 0 < position.val ∧ position.val < spec.length edge
    dsimp [position]
    have := offset.isLt
    omega
  rw [show offset = spec.interiorOffsetOfPosition edge position hInterior by
    apply Fin.ext
    simp [position, interiorOffsetOfPosition]]
  rw [spec.previousVertex_eq_pathVertex edge position hInterior,
    spec.nextVertex_eq_pathVertex edge position hInterior]
  intro hEqual
  have hPositions := spec.pathVertex_injective edge hEqual
  have hValues := congrArg Fin.val hPositions
  simp only [previousPathPosition, nextPathPosition] at hValues
  omega

/-- Exact classification of unit steps incident to one interior vertex. -/
theorem unitEdge_incident_interior_iff (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) (vertex : spec.Vertex)
    (step : spec.Step) :
    (spec.unitEdge step = (spec.interiorVertex edge offset, vertex) ∨
      spec.unitEdge step = (vertex, spec.interiorVertex edge offset)) ↔
      (step = ⟨edge, spec.nextStep edge offset⟩ ∧
        vertex = spec.nextVertex edge offset) ∨
      (step = ⟨edge, spec.previousStep edge offset⟩ ∧
        vertex = spec.previousVertex edge offset) := by
  constructor
  · rintro (hForward | hBackward)
    · simp only [unitEdge, Prod.mk.injEq] at hForward
      have hStep :=
        (spec.stepLeft_eq_interiorVertex_iff step edge offset).mp hForward.1
      exact Or.inl ⟨hStep, by
        subst step
        exact hForward.2.symm⟩
    · simp only [unitEdge, Prod.mk.injEq] at hBackward
      have hStep :=
        (spec.stepRight_eq_interiorVertex_iff step edge offset).mp hBackward.2
      exact Or.inr ⟨hStep, by
        subst step
        exact hBackward.1.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · left
      simp [unitEdge, nextVertex]
    · right
      simp [unitEdge, previousVertex]

/-- Every edge incident to an interior subdivision vertex has multiplicity at
most one.  Parallel core slots cannot create parallel edges here because the
interior vertex remembers its own slot. -/
theorem num_edges_interior_le_one (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) (vertex : spec.Vertex) :
    numEdges spec.graph (spec.interiorVertex edge offset) vertex ≤ 1 := by
  rw [spec.num_edges_eq_card_filter_steps]
  apply Finset.card_le_one_iff.mpr
  intro first second hFirst hSecond
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hFirst hSecond
  have hClassFirst :=
    (spec.unitEdge_incident_interior_iff edge offset vertex first).mp hFirst
  have hClassSecond :=
    (spec.unitEdge_incident_interior_iff edge offset vertex second).mp hSecond
  rcases hClassFirst with hFirstNext | hFirstPrevious <;>
    rcases hClassSecond with hSecondNext | hSecondPrevious
  · exact hFirstNext.1.trans hSecondNext.1.symm
  · exfalso
    apply spec.previousVertex_ne_nextVertex edge offset
    exact hSecondPrevious.2.symm.trans hFirstNext.2
  · exfalso
    apply spec.previousVertex_ne_nextVertex edge offset
    exact hFirstPrevious.2.symm.trans hSecondNext.2
  · exact hFirstPrevious.1.trans hSecondPrevious.1.symm

/-! ## Complement intervals -/

/-- A nonempty open path interval whose endpoints lie in `R` and whose
interior is disjoint from `R`. -/
structure ComplementInterval (R : Finset spec.Vertex) where
  edge : Fin p
  left : spec.PathPosition edge
  right : spec.PathPosition edge
  center : spec.PathPosition edge
  left_lt_center : left.val < center.val
  center_lt_right : center.val < right.val
  left_mem : spec.pathVertex edge left ∈ R
  right_mem : spec.pathVertex edge right ∈ R
  interior_not_mem : ∀ position : spec.PathPosition edge,
    left.val < position.val → position.val < right.val →
      spec.pathVertex edge position ∉ R

namespace ComplementInterval

variable {spec : SubdivisionGraph.Spec n p} {R : Finset spec.Vertex}
    (interval : spec.ComplementInterval R)

/-- Positions in the open interval. -/
def positions : Finset (spec.PathPosition interval.edge) :=
  Finset.univ.filter fun position =>
    interval.left.val < position.val ∧
      position.val < interval.right.val

/-- Vertices in the complementary path interval. -/
def carrier : Finset spec.Vertex :=
  interval.positions.image (spec.pathVertex interval.edge)

@[simp] theorem mem_positions_iff
    (position : spec.PathPosition interval.edge) :
    position ∈ interval.positions ↔
      interval.left.val < position.val ∧
        position.val < interval.right.val := by
  simp [positions]

theorem mem_carrier_iff (vertex : spec.Vertex) :
    vertex ∈ interval.carrier ↔
      ∃ position : spec.PathPosition interval.edge,
        interval.left.val < position.val ∧
        position.val < interval.right.val ∧
        spec.pathVertex interval.edge position = vertex := by
  simp only [carrier, Finset.mem_image, mem_positions_iff]
  constructor
  · rintro ⟨position, hPosition, rfl⟩
    exact ⟨position, hPosition.1, hPosition.2, rfl⟩
  · rintro ⟨position, hLeft, hRight, rfl⟩
    exact ⟨position, ⟨hLeft, hRight⟩, rfl⟩

theorem position_isInterior
    {position : spec.PathPosition interval.edge}
    (hLeft : interval.left.val < position.val)
    (hRight : position.val < interval.right.val) :
    spec.IsInteriorPosition interval.edge position := by
  change 0 < position.val ∧ position.val < spec.length interval.edge
  have hRightBound := interval.right.isLt
  constructor <;> omega

theorem carrier_nonempty : interval.carrier.Nonempty := by
  refine ⟨spec.pathVertex interval.edge interval.center, ?_⟩
  exact (interval.mem_carrier_iff _).mpr
    ⟨interval.center, interval.left_lt_center,
      interval.center_lt_right, rfl⟩

theorem carrier_disjoint : Disjoint interval.carrier R := by
  apply Finset.disjoint_left.mpr
  intro vertex hCarrier hR
  obtain ⟨position, hLeft, hRight, rfl⟩ :=
    (interval.mem_carrier_iff vertex).mp hCarrier
  exact interval.interior_not_mem position hLeft hRight hR

/-- First vertex of the open interval. -/
def firstPosition : spec.PathPosition interval.edge :=
  ⟨interval.left.val + 1, by
    have := interval.center.isLt
    have hLeft := interval.left_lt_center
    omega⟩

/-- Final vertex of the open interval. -/
def lastPosition : spec.PathPosition interval.edge :=
  ⟨interval.right.val - 1, by
    have := interval.right.isLt
    omega⟩

theorem firstPosition_mem : interval.firstPosition ∈ interval.positions := by
  rw [interval.mem_positions_iff]
  simp only [firstPosition]
  have hLeft := interval.left_lt_center
  have hRight := interval.center_lt_right
  omega

theorem lastPosition_mem : interval.lastPosition ∈ interval.positions := by
  rw [interval.mem_positions_iff]
  simp only [lastPosition]
  have hLeft := interval.left_lt_center
  have hRight := interval.center_lt_right
  omega

theorem firstVertex_mem :
    spec.pathVertex interval.edge interval.firstPosition ∈ interval.carrier := by
  exact Finset.mem_image.mpr ⟨interval.firstPosition,
    interval.firstPosition_mem, rfl⟩

theorem lastVertex_mem :
    spec.pathVertex interval.edge interval.lastPosition ∈ interval.carrier := by
  exact Finset.mem_image.mpr ⟨interval.lastPosition,
    interval.lastPosition_mem, rfl⟩

/-- The left endpoint is a boundary vertex of the interval carrier. -/
theorem left_boundary :
    StrongSeparator.IsBoundary spec.graph interval.carrier
      (spec.pathVertex interval.edge interval.left) := by
  let offset : Fin (spec.length interval.edge) :=
    ⟨interval.left.val, by
      have := interval.right.isLt
      have hLeft := interval.left_lt_center
      have hRight := interval.center_lt_right
      omega⟩
  refine ⟨spec.pathVertex interval.edge interval.firstPosition,
    interval.firstVertex_mem, ?_⟩
  have hEdge := spec.consecutive_num_edges_pos interval.edge offset
  have hLeftPosition : spec.stepLeftPosition interval.edge offset =
      interval.left := by
    apply Fin.ext
    rfl
  have hRightPosition : spec.stepRightPosition interval.edge offset =
      interval.firstPosition := by
    apply Fin.ext
    rfl
  simpa [hLeftPosition, hRightPosition] using hEdge

/-- Every edge leaving an open complement interval lands in `R`. -/
theorem closed {x y : spec.Vertex} (hx : x ∈ interval.carrier)
    (hy : y ∉ interval.carrier) (hxy : 0 < numEdges spec.graph x y) :
    y ∈ R := by
  obtain ⟨position, hLeft, hRight, rfl⟩ :=
    (interval.mem_carrier_iff x).mp hx
  have hInterior := interval.position_isInterior hLeft hRight
  change 0 < position.val ∧
    position.val < spec.length interval.edge at hInterior
  rw [spec.pathVertex_num_edges_pos_iff interval.edge position hInterior y]
    at hxy
  rcases hxy with hPrevious | hNext
  · let previous :=
      spec.previousPathPosition interval.edge position hInterior.1
    have hPreviousLe : interval.left.val ≤ previous.val := by
      simp only [previous, previousPathPosition]
      omega
    have hPreviousLt : previous.val < interval.right.val := by
      simp only [previous, previousPathPosition]
      omega
    have hPreviousEq : previous = interval.left := by
      apply Fin.ext
      by_contra hne
      have hStrict : interval.left.val < previous.val := by omega
      apply hy
      rw [hPrevious]
      exact (interval.mem_carrier_iff _).mpr
        ⟨previous, hStrict, hPreviousLt, rfl⟩
    rw [hPrevious]
    have hPositionEq :
        spec.previousPathPosition interval.edge position hInterior.1 =
          interval.left := by
      apply Fin.ext
      have hValue := congrArg Fin.val hPreviousEq
      simpa [previous, previousPathPosition] using hValue
    rw [hPositionEq]
    exact interval.left_mem
  · let next := spec.nextPathPosition interval.edge position hInterior.2
    have hNextGt : interval.left.val < next.val := by
      simp only [next, nextPathPosition]
      omega
    have hNextLe : next.val ≤ interval.right.val := by
      simp only [next, nextPathPosition]
      omega
    have hNextEq : next = interval.right := by
      apply Fin.ext
      by_contra hne
      have hStrict : next.val < interval.right.val := by omega
      apply hy
      rw [hNext]
      exact (interval.mem_carrier_iff _).mpr
        ⟨next, hNextGt, hStrict, rfl⟩
    rw [hNext]
    have hPositionEq :
        spec.nextPathPosition interval.edge position hInterior.2 =
          interval.right := by
      apply Fin.ext
      have hValue := congrArg Fin.val hNextEq
      simpa [next, nextPathPosition] using hValue
    rw [hPositionEq]
    exact interval.right_mem

/-- A reached vertex adjacent to the carrier is one of its two boundary
vertices, and the adjacent carrier vertex is the corresponding endpoint. -/
theorem reached_neighbor_classification {x y : spec.Vertex}
    (hx : x ∈ interval.carrier) (hy : y ∈ R)
    (hyx : 0 < numEdges spec.graph y x) :
    (x = spec.pathVertex interval.edge interval.firstPosition ∧
      y = spec.pathVertex interval.edge interval.left) ∨
    (x = spec.pathVertex interval.edge interval.lastPosition ∧
      y = spec.pathVertex interval.edge interval.right) := by
  obtain ⟨position, hLeft, hRight, rfl⟩ :=
    (interval.mem_carrier_iff x).mp hx
  have hInterior := interval.position_isInterior hLeft hRight
  change 0 < position.val ∧
    position.val < spec.length interval.edge at hInterior
  have hxy :
      0 < numEdges spec.graph (spec.pathVertex interval.edge position) y := by
    rwa [num_edges_symmetric]
  rw [spec.pathVertex_num_edges_pos_iff interval.edge position hInterior y]
    at hxy
  rcases hxy with hPrevious | hNext
  · let previous :=
      spec.previousPathPosition interval.edge position hInterior.1
    have hPreviousVal : previous.val = interval.left.val := by
      by_contra hne
      change position.val - 1 ≠ interval.left.val at hne
      have hOpenLeft : interval.left.val < previous.val := by
        change interval.left.val < position.val - 1
        omega
      have hOpenRight : previous.val < interval.right.val := by
        change position.val - 1 < interval.right.val
        omega
      have hNotR := interval.interior_not_mem previous hOpenLeft hOpenRight
      apply hNotR
      rwa [hPrevious] at hy
    left
    constructor
    · apply congrArg (spec.pathVertex interval.edge)
      apply Fin.ext
      simp only [firstPosition]
      simp only [previous, previousPathPosition] at hPreviousVal
      omega
    · rw [hPrevious]
      apply congrArg (spec.pathVertex interval.edge)
      apply Fin.ext
      exact hPreviousVal
  · let next := spec.nextPathPosition interval.edge position hInterior.2
    have hNextVal : next.val = interval.right.val := by
      by_contra hne
      change position.val + 1 ≠ interval.right.val at hne
      have hOpenLeft : interval.left.val < next.val := by
        change interval.left.val < position.val + 1
        omega
      have hOpenRight : next.val < interval.right.val := by
        change position.val + 1 < interval.right.val
        omega
      have hNotR := interval.interior_not_mem next hOpenLeft hOpenRight
      apply hNotR
      rwa [hNext] at hy
    right
    constructor
    · apply congrArg (spec.pathVertex interval.edge)
      apply Fin.ext
      simp only [lastPosition]
      simp only [next, nextPathPosition] at hNextVal
      omega
    · rw [hNext]
      apply congrArg (spec.pathVertex interval.edge)
      apply Fin.ext
      exact hNextVal

/-- A vertex of `R` has at most one neighboring vertex in this carrier. -/
theorem reached_carrier_neighbor_unique {y x z : spec.Vertex}
    (hy : y ∈ R) (hx : x ∈ interval.carrier)
    (hz : z ∈ interval.carrier)
    (hyx : 0 < numEdges spec.graph y x)
    (hyz : 0 < numEdges spec.graph y z) : x = z := by
  rcases interval.reached_neighbor_classification hx hy hyx with
      hXLeft | hXRight <;>
    rcases interval.reached_neighbor_classification hz hy hyz with
      hZLeft | hZRight
  · exact hXLeft.1.trans hZLeft.1.symm
  · exfalso
    have hEndpoints : interval.left = interval.right :=
      spec.pathVertex_injective interval.edge
        (hXLeft.2.symm.trans hZRight.2)
    have hValues := congrArg Fin.val hEndpoints
    have hLeft := interval.left_lt_center
    have hRight := interval.center_lt_right
    omega
  · exfalso
    have hEndpoints : interval.left = interval.right :=
      spec.pathVertex_injective interval.edge
        (hZLeft.2.symm.trans hXRight.2)
    have hValues := congrArg Fin.val hEndpoints
    have hLeft := interval.left_lt_center
    have hRight := interval.center_lt_right
    omega
  · exact hXRight.1.trans hZRight.1.symm

/-- Exact multiplicities and uniqueness of the boundary neighbor give the
one-edge condition required by a strong-separator expansion cell. -/
theorem oneEdge {y : spec.Vertex} (hy : y ∈ R) :
    StrongSeparator.intoMultiplicity spec.graph interval.carrier y ≤ 1 := by
  unfold StrongSeparator.intoMultiplicity
  by_cases hExists :
      ∃ x ∈ interval.carrier, 0 < numEdges spec.graph y x
  · obtain ⟨chosen, hChosenCarrier, hChosenPositive⟩ := hExists
    calc
      (∑ x ∈ interval.carrier, (numEdges spec.graph y x : ℤ)) =
          (numEdges spec.graph y chosen : ℤ) := by
        apply Finset.sum_eq_single chosen
        · intro x hx hne
          have hNotPositive : ¬0 < numEdges spec.graph y x := by
            intro hPositive
            exact hne (interval.reached_carrier_neighbor_unique hy hx
              hChosenCarrier hPositive hChosenPositive)
          simp [Nat.eq_zero_of_not_pos hNotPositive]
        · intro hChosenNotCarrier
          exact (hChosenNotCarrier hChosenCarrier).elim
      _ ≤ 1 := by
        obtain ⟨position, hLeft, hRight, hChosen⟩ :=
          (interval.mem_carrier_iff chosen).mp hChosenCarrier
        subst chosen
        have hInterior := interval.position_isInterior hLeft hRight
        rw [spec.pathVertex_eq_interiorVertex interval.edge position hInterior,
          num_edges_symmetric]
        exact_mod_cast spec.num_edges_interior_le_one interval.edge
          (spec.interiorOffsetOfPosition interval.edge position hInterior) y
  · have hZero (x : spec.Vertex) (hx : x ∈ interval.carrier) :
        numEdges spec.graph y x = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hPositive
      exact hExists ⟨x, hx, hPositive⟩
    have hSumZero :
        (∑ x ∈ interval.carrier, (numEdges spec.graph y x : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hZero x hx]
    rw [hSumZero]
    norm_num

/-- Along the path from the left endpoint to the right endpoint, membership
in any finite set must change across some unit step when the left endpoint is
inside and the right endpoint is outside. -/
theorem exists_crossing_step (A : Finset spec.Vertex)
    (hLeftA : spec.pathVertex interval.edge interval.left ∈ A)
    (hRightNotA : spec.pathVertex interval.edge interval.right ∉ A) :
    ∃ offset : Fin (spec.length interval.edge),
      interval.left.val ≤ offset.val ∧
      offset.val < interval.right.val ∧
      spec.pathVertex interval.edge
          (spec.stepLeftPosition interval.edge offset) ∈ A ∧
      spec.pathVertex interval.edge
          (spec.stepRightPosition interval.edge offset) ∉ A := by
  let candidates : Finset (spec.PathPosition interval.edge) :=
    Finset.univ.filter fun position =>
      interval.left.val ≤ position.val ∧
      position.val < interval.right.val ∧
      spec.pathVertex interval.edge position ∈ A
  have hLeftRight : interval.left.val < interval.right.val :=
    lt_trans interval.left_lt_center interval.center_lt_right
  have hCandidates : candidates.Nonempty := by
    refine ⟨interval.left, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hLeftRight, hLeftA⟩
  let chosen : spec.PathPosition interval.edge :=
    candidates.max' hCandidates
  have hChosenMem : chosen ∈ candidates :=
    candidates.max'_mem hCandidates
  have hChosenProperties :
      interval.left.val ≤ chosen.val ∧
      chosen.val < interval.right.val ∧
      spec.pathVertex interval.edge chosen ∈ A := by
    simpa [candidates] using hChosenMem
  have hChosenBeforeHead : chosen.val < spec.length interval.edge := by
    have hRightBound := interval.right.isLt
    omega
  let offset : Fin (spec.length interval.edge) :=
    ⟨chosen.val, hChosenBeforeHead⟩
  have hLeftPosition : spec.stepLeftPosition interval.edge offset = chosen := by
    apply Fin.ext
    rfl
  let successor : spec.PathPosition interval.edge :=
    spec.stepRightPosition interval.edge offset
  have hSuccessorVal : successor.val = chosen.val + 1 := rfl
  have hSuccessorNotA : spec.pathVertex interval.edge successor ∉ A := by
    intro hSuccessorA
    by_cases hSuccessorRight : successor = interval.right
    · exact hRightNotA (hSuccessorRight ▸ hSuccessorA)
    · have hSuccessorLt : successor.val < interval.right.val := by
        have hSuccessorLe : successor.val ≤ interval.right.val := by
          omega
        have hValueNe : successor.val ≠ interval.right.val := by
          intro hValue
          apply hSuccessorRight
          apply Fin.ext
          exact hValue
        omega
      have hSuccessorMem : successor ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, hSuccessorLt, hSuccessorA⟩
        omega
      have hMax := candidates.le_max' successor hSuccessorMem
      have hMaxValues : successor.val ≤ chosen.val := hMax
      omega
  refine ⟨offset, hChosenProperties.1, hChosenProperties.2.1, ?_, ?_⟩
  · simpa [hLeftPosition] using hChosenProperties.2.2
  · exact hSuccessorNotA

/-- The open interval has the path-cut property required by
`StrongSeparator.ExpansionCell`. -/
theorem pathCut {t : spec.Vertex} (htR : t ∈ R)
    (htBoundary : StrongSeparator.IsBoundary spec.graph interval.carrier t)
    (A : Finset spec.Vertex)
    (hLeftA : spec.pathVertex interval.edge interval.left ∈ A)
    (htNotA : t ∉ A) :
    (∃ x ∈ interval.carrier, x ∉ A ∧
      ∃ y ∈ A, 0 < numEdges spec.graph x y) ∨
    (∃ x ∈ interval.carrier, x ∈ A ∧
      ∃ y, y ∉ A ∧ 0 < numEdges spec.graph x y) := by
  obtain ⟨neighbor, hNeighborCarrier, htNeighbor⟩ := htBoundary
  rcases interval.reached_neighbor_classification hNeighborCarrier htR
      htNeighbor with hLeftBoundary | hRightBoundary
  · exfalso
    apply htNotA
    rw [hLeftBoundary.2]
    exact hLeftA
  · have hRightNotA :
        spec.pathVertex interval.edge interval.right ∉ A := by
      intro hRightA
      apply htNotA
      rw [hRightBoundary.2]
      exact hRightA
    obtain ⟨offset, hOffsetLeft, hOffsetRight, hStepLeftA,
        hStepRightNotA⟩ :=
      interval.exists_crossing_step A hLeftA hRightNotA
    let leftPosition := spec.stepLeftPosition interval.edge offset
    let rightPosition := spec.stepRightPosition interval.edge offset
    have hEdge := spec.consecutive_num_edges_pos interval.edge offset
    by_cases hRightEndpoint : rightPosition = interval.right
    · right
      refine ⟨spec.pathVertex interval.edge leftPosition, ?_, hStepLeftA,
        spec.pathVertex interval.edge rightPosition, hStepRightNotA, hEdge⟩
      apply (interval.mem_carrier_iff _).mpr
      have hGap : interval.left.val + 1 < interval.right.val := by
        have hLeft := interval.left_lt_center
        have hRight := interval.center_lt_right
        omega
      have hRightEndpointVal := congrArg Fin.val hRightEndpoint
      change offset.val + 1 = interval.right.val at hRightEndpointVal
      refine ⟨leftPosition, ?_, hOffsetRight, rfl⟩
      simp only [leftPosition, stepLeftPosition]
      omega
    · left
      refine ⟨spec.pathVertex interval.edge rightPosition, ?_,
        hStepRightNotA, spec.pathVertex interval.edge leftPosition,
        hStepLeftA, ?_⟩
      · apply (interval.mem_carrier_iff _).mpr
        refine ⟨rightPosition, ?_, ?_, rfl⟩
        · simp only [rightPosition, stepRightPosition]
          omega
        · have hRightLe : rightPosition.val ≤ interval.right.val := by
            simp only [rightPosition, stepRightPosition]
            omega
          have hValueNe : rightPosition.val ≠ interval.right.val := by
            intro hValue
            apply hRightEndpoint
            apply Fin.ext
            exact hValue
          omega
      · rwa [num_edges_symmetric]

/-- Every complement interval supplies exactly the transparent cell consumed
by the strong-separator rank theorem. -/
def expansionCell : StrongSeparator.ExpansionCell spec.graph R where
  carrier := interval.carrier
  nonempty := interval.carrier_nonempty
  disjoint := interval.carrier_disjoint
  anchor := spec.pathVertex interval.edge interval.left
  anchor_mem := interval.left_mem
  anchor_boundary := interval.left_boundary
  closed := by
    intro x y hx hy hxy
    exact interval.closed hx hy hxy
  oneEdge := by
    intro y hy
    exact interval.oneEdge hy
  pathCut := by
    intro t ht hBoundary A hAnchorA htNotA
    exact interval.pathCut ht hBoundary A hAnchorA htNotA

end ComplementInterval

/-! ## Selecting a maximal complement interval -/

/-- Every proper enlargement of the embedded core omits a nonempty open
interval on some edge slot.  The endpoints are chosen by finite max/min, so
the construction is valid for arbitrary (not necessarily connected) `R`. -/
theorem exists_complementInterval
    (R : Finset spec.Vertex)
    (hCore : ExplicitPotential.Certificate.coreVertices spec ⊆ R)
    (hProper : R ≠ Finset.univ) :
    Nonempty (spec.ComplementInterval R) := by
  classical
  have hOutside : ∃ vertex : spec.Vertex, vertex ∉ R := by
    by_contra hAll
    push Not at hAll
    apply hProper
    exact Finset.eq_univ_of_forall hAll
  obtain ⟨vertex, hVertexOutside⟩ := hOutside
  rcases vertex with core | interior
  · exfalso
    exact hVertexOutside
      (hCore (ExplicitPotential.Certificate.coreVertex_mem_coreVertices
        spec core))
  · rcases interior with ⟨edge, offset⟩
    let center : spec.PathPosition edge :=
      ⟨offset.val + 1, by
        have := offset.isLt
        have hLength := spec.length_pos edge
        omega⟩
    have hCenterInterior : spec.IsInteriorPosition edge center := by
      change 0 < center.val ∧ center.val < spec.length edge
      dsimp [center]
      have := offset.isLt
      omega
    have hCenterOffset :
        spec.interiorOffsetOfPosition edge center hCenterInterior = offset := by
      apply Fin.ext
      simp [center, interiorOffsetOfPosition]
    have hCenterOutside : spec.pathVertex edge center ∉ R := by
      rw [spec.pathVertex_eq_interiorVertex edge center hCenterInterior,
        hCenterOffset]
      exact hVertexOutside
    let leftCandidates : Finset (spec.PathPosition edge) :=
      Finset.univ.filter fun position =>
        position.val < center.val ∧ spec.pathVertex edge position ∈ R
    let zero : spec.PathPosition edge := ⟨0, by omega⟩
    have hZeroR : spec.pathVertex edge zero ∈ R := by
      rw [show zero = ⟨0, by omega⟩ by apply Fin.ext; rfl,
        spec.pathVertex_zero]
      exact hCore
        (ExplicitPotential.Certificate.coreVertex_mem_coreVertices spec
          (spec.core.tail edge))
    have hLeftCandidates : leftCandidates.Nonempty := by
      refine ⟨zero, ?_⟩
      simp only [leftCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simp [zero, center], hZeroR⟩
    let left : spec.PathPosition edge :=
      leftCandidates.max' hLeftCandidates
    have hLeftMem : left ∈ leftCandidates :=
      leftCandidates.max'_mem hLeftCandidates
    have hLeftProperties :
        left.val < center.val ∧ spec.pathVertex edge left ∈ R := by
      simpa [leftCandidates] using hLeftMem
    let rightCandidates : Finset (spec.PathPosition edge) :=
      Finset.univ.filter fun position =>
        center.val < position.val ∧ spec.pathVertex edge position ∈ R
    let endpoint : spec.PathPosition edge :=
      ⟨spec.length edge, by omega⟩
    have hEndpointR : spec.pathVertex edge endpoint ∈ R := by
      rw [show endpoint = ⟨spec.length edge, by omega⟩ by
        apply Fin.ext
        rfl, spec.pathVertex_length]
      exact hCore
        (ExplicitPotential.Certificate.coreVertex_mem_coreVertices spec
          (spec.core.head edge))
    have hRightCandidates : rightCandidates.Nonempty := by
      refine ⟨endpoint, ?_⟩
      simp only [rightCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hEndpointR⟩
      change center.val < spec.length edge
      exact hCenterInterior.2
    let right : spec.PathPosition edge :=
      rightCandidates.min' hRightCandidates
    have hRightMem : right ∈ rightCandidates :=
      rightCandidates.min'_mem hRightCandidates
    have hRightProperties :
        center.val < right.val ∧ spec.pathVertex edge right ∈ R := by
      simpa [rightCandidates] using hRightMem
    refine ⟨{
      edge := edge
      left := left
      right := right
      center := center
      left_lt_center := hLeftProperties.1
      center_lt_right := hRightProperties.1
      left_mem := hLeftProperties.2
      right_mem := hRightProperties.2
      interior_not_mem := ?_
    }⟩
    intro position hLeftPosition hPositionRight hPositionR
    by_cases hPositionCenterLeft : position.val < center.val
    · have hPositionCandidate : position ∈ leftCandidates := by
        simp only [leftCandidates, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨hPositionCenterLeft, hPositionR⟩
      have hMax := leftCandidates.le_max' position hPositionCandidate
      have hMaxValues : position.val ≤ left.val := hMax
      omega
    · by_cases hCenterPosition : center.val < position.val
      · have hPositionCandidate : position ∈ rightCandidates := by
          simp only [rightCandidates, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨hCenterPosition, hPositionR⟩
        have hMin := rightCandidates.min'_le position hPositionCandidate
        have hMinValues : right.val ≤ position.val := hMin
        omega
      · have hPositionEq : position = center := by
          apply Fin.ext
          omega
        exact hCenterOutside (hPositionEq ▸ hPositionR)

/-- The embedded core vertices form a strong separator in every subdivision
graph.  No connectedness hypothesis is needed for this local statement; graph
connectedness enters only when the strong-separator rank theorem is applied. -/
theorem coreVertices_strongSeparatorCertificate :
    StrongSeparator.StrongSeparatorCertificate spec.graph
      (ExplicitPotential.Certificate.coreVertices spec) := by
  intro R hCore _hRNonempty hProper
  obtain ⟨interval⟩ := spec.exists_complementInterval R hCore hProper
  exact ⟨interval.expansionCell⟩

end SubdivisionGraph.Spec

namespace ExplicitPotential.Certificate

variable {m n p : ℕ}

/-- A checked explicit-potential record now proves rank-one existence on its
connected subdivision with no separately supplied separator hypothesis. -/
theorem bnExists_on_subdivision_of_valid
    (certificate : ExplicitPotential.Certificate m n p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) (degree : ℤ)
    (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hConnected : graphConnected
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph) :
    BNExists
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
      1 degree := by
  apply certificate.bnExists_of_valid_of_strongSeparator point core_nonempty
    degree hValid hCone hConnected
  exact SubdivisionGraph.Spec.coreVertices_strongSeparatorCertificate
    (certificate.subdivisionSpec point core_nonempty hValid hCone)

end ExplicitPotential.Certificate

end Utilities.Certificate
