/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionGraph
public import Mathlib.Tactic

/-!
# Connectivity of positive subdivisions

The explicit-potential checker works with a finite ordered core and then
replaces every edge slot by a path of positive integral length.  This file
keeps the connectivity trust boundary finite: `ExplicitPotential.Core.Connected`
is a cut certificate on the ordered core slots, and
`SubdivisionGraph.Spec.graph_connected_of_coreConnected` proves that every
positive subdivision of such a core is connected.

The proof uses only the cut definition of `graphConnected`.  If no subdivided
unit edge crosses a cut, membership is constant along each subdivided path.
It is therefore constant on the core by core connectedness, and then constant
on every interior vertex as well.
-/

@[expose] public section

namespace Utilities.Certificate

open Finset

namespace ExplicitPotential.Core

variable {n p : ℕ}

/-- Cut connectedness for an ordered loopless core.  Edge slots, rather than
endpoint pairs, are quantified so parallel edges are retained exactly. -/
def Connected (core : ExplicitPotential.Core n p) : Prop :=
  ∀ S : Finset (Fin n),
    (∃ v w : Fin n, v ∈ S ∧ w ∉ S) →
      ∃ edge : Fin p,
        (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
        (core.head edge ∈ S ∧ core.tail edge ∉ S)

/-- Exact finite Boolean checker for core connectedness. -/
def connectedCheck (core : ExplicitPotential.Core n p) : Bool :=
  AffineCover.allFinset Finset.univ fun S : Finset (Fin n) =>
    decide ((∃ v w : Fin n, v ∈ S ∧ w ∉ S) →
      ∃ edge : Fin p,
        (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
        (core.head edge ∈ S ∧ core.tail edge ∉ S))

@[simp] theorem connectedCheck_eq_true_iff
    (core : ExplicitPotential.Core n p) :
    core.connectedCheck = true ↔ core.Connected := by
  simp [connectedCheck, Connected]

end ExplicitPotential.Core

namespace SubdivisionGraph.Spec

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- If no edge crosses a vertex cut, membership is constant along every
subdivided core edge. -/
theorem coreEndpoints_mem_iff_of_noCrossing
    (A : Finset spec.graph.V)
    (hNoCrossing : ∀ x ∈ A, ∀ y ∉ A, numEdges spec.graph x y = 0)
    (edge : Fin p) :
    spec.coreVertex (spec.core.tail edge) ∈ A ↔
      spec.coreVertex (spec.core.head edge) ∈ A := by
  have hStep (offset : Fin (spec.length edge)) :
      spec.stepLeft edge offset ∈ A ↔
        spec.stepRight edge offset ∈ A := by
    constructor
    · intro hLeft
      by_contra hRight
      have hZero := hNoCrossing _ hLeft _ hRight
      have hPositive := spec.unitStep_num_edges_pos edge offset
      omega
    · intro hRight
      by_contra hLeft
      have hZero := hNoCrossing _ hRight _ hLeft
      have hPositive := spec.unitStep_num_edges_pos edge offset
      rw [num_edges_symmetric] at hPositive
      omega
  have hPrefix : ∀ k : ℕ, ∀ hk : k < spec.length edge,
      spec.coreVertex (spec.core.tail edge) ∈ A ↔
        spec.stepRight edge ⟨k, hk⟩ ∈ A := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa using hStep ⟨0, hk⟩
    | succ k inductionHypothesis =>
        intro hk
        have hkPrevious : k < spec.length edge := by omega
        have hkInterior : k < spec.length edge - 1 := by omega
        let interior : Fin (spec.length edge - 1) := ⟨k, hkInterior⟩
        have hConsecutive :
            spec.stepRight edge ⟨k, hkPrevious⟩ =
              spec.stepLeft edge ⟨k + 1, hk⟩ := by
          rw [spec.stepRight_before_last edge interior,
            spec.stepLeft_after_zero edge interior]
        exact (inductionHypothesis hkPrevious).trans (by
          rw [hConsecutive]
          exact hStep ⟨k + 1, hk⟩)
  have hLast : spec.length edge - 1 < spec.length edge := by
    have := spec.length_pos edge
    omega
  simpa using hPrefix (spec.length edge - 1) hLast

/-- If no edge crosses a vertex cut, an interior vertex lies on the same side
as the tail of its core edge. -/
theorem coreTail_mem_iff_interior_mem_of_noCrossing
    (A : Finset spec.graph.V)
    (hNoCrossing : ∀ x ∈ A, ∀ y ∉ A, numEdges spec.graph x y = 0)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    spec.coreVertex (spec.core.tail edge) ∈ A ↔
      spec.interiorVertex edge offset ∈ A := by
  have hStep (step : Fin (spec.length edge)) :
      spec.stepLeft edge step ∈ A ↔
        spec.stepRight edge step ∈ A := by
    constructor
    · intro hLeft
      by_contra hRight
      have hZero := hNoCrossing _ hLeft _ hRight
      have hPositive := spec.unitStep_num_edges_pos edge step
      omega
    · intro hRight
      by_contra hLeft
      have hZero := hNoCrossing _ hRight _ hLeft
      have hPositive := spec.unitStep_num_edges_pos edge step
      rw [num_edges_symmetric] at hPositive
      omega
  have hPrefix : ∀ k : ℕ, ∀ hk : k < spec.length edge,
      spec.coreVertex (spec.core.tail edge) ∈ A ↔
        spec.stepRight edge ⟨k, hk⟩ ∈ A := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa using hStep ⟨0, hk⟩
    | succ k inductionHypothesis =>
        intro hk
        have hkPrevious : k < spec.length edge := by omega
        have hkInterior : k < spec.length edge - 1 := by omega
        let interior : Fin (spec.length edge - 1) := ⟨k, hkInterior⟩
        have hConsecutive :
            spec.stepRight edge ⟨k, hkPrevious⟩ =
              spec.stepLeft edge ⟨k + 1, hk⟩ := by
          rw [spec.stepRight_before_last edge interior,
            spec.stepLeft_after_zero edge interior]
        exact (inductionHypothesis hkPrevious).trans (by
          rw [hConsecutive]
          exact hStep ⟨k + 1, hk⟩)
  have hOffset : offset.val < spec.length edge := by
    have := offset.isLt
    omega
  have hPath := hPrefix offset.val hOffset
  simpa using hPath

/-- Positive subdivision preserves connectedness of the ordered core. -/
theorem graph_connected_of_coreConnected
    (hCoreConnected : spec.core.Connected) :
    graphConnected spec.graph := by
  intro A hSplit
  by_contra hCrossing
  push Not at hCrossing
  have hNoCrossing :
      ∀ x ∈ A, ∀ y ∉ A, numEdges spec.graph x y = 0 := by
    intro x hx y hy
    have hNotPositive := hCrossing x hx y hy
    omega
  let coreSide : Finset (Fin n) :=
    Finset.univ.filter fun vertex => spec.coreVertex vertex ∈ A
  by_cases hCoreSplit :
      ∃ v w : Fin n, v ∈ coreSide ∧ w ∉ coreSide
  · obtain ⟨edge, hEdge⟩ := hCoreConnected coreSide hCoreSplit
    have hEndpoints :=
      spec.coreEndpoints_mem_iff_of_noCrossing A hNoCrossing edge
    rcases hEdge with hEdge | hEdge
    · have hTail : spec.coreVertex (spec.core.tail edge) ∈ A := by
        simpa [coreSide] using hEdge.1
      have hHead : spec.coreVertex (spec.core.head edge) ∉ A := by
        simpa [coreSide] using hEdge.2
      exact hHead (hEndpoints.mp hTail)
    · have hHead : spec.coreVertex (spec.core.head edge) ∈ A := by
        simpa [coreSide] using hEdge.1
      have hTail : spec.coreVertex (spec.core.tail edge) ∉ A := by
        simpa [coreSide] using hEdge.2
      exact hTail (hEndpoints.mpr hHead)
  · let base : Fin n := ⟨0, spec.core_nonempty⟩
    have hCoreUniform (vertex : Fin n) :
        spec.coreVertex vertex ∈ A ↔ spec.coreVertex base ∈ A := by
      by_cases hVertex : spec.coreVertex vertex ∈ A <;>
        by_cases hBase : spec.coreVertex base ∈ A
      · simp [hVertex, hBase]
      · exfalso
        apply hCoreSplit
        exact ⟨vertex, base, by simpa [coreSide] using hVertex,
          by simpa [coreSide] using hBase⟩
      · exfalso
        apply hCoreSplit
        exact ⟨base, vertex, by simpa [coreSide] using hBase,
          by simpa [coreSide] using hVertex⟩
      · simp [hVertex, hBase]
    have hAllUniform (vertex : spec.graph.V) :
        vertex ∈ A ↔ spec.coreVertex base ∈ A := by
      rcases vertex with vertex | interior
      · exact hCoreUniform vertex
      · rcases interior with ⟨edge, offset⟩
        exact (spec.coreTail_mem_iff_interior_mem_of_noCrossing
          A hNoCrossing edge offset).symm.trans
            (hCoreUniform (spec.core.tail edge))
    obtain ⟨x, y, hx, hy⟩ := hSplit
    have hBaseMem := (hAllUniform x).mp hx
    have hBaseNotMem : spec.coreVertex base ∉ A := by
      intro hBaseMem'
      exact hy ((hAllUniform y).mpr hBaseMem')
    exact hBaseNotMem hBaseMem

end SubdivisionGraph.Spec

end Utilities.Certificate
