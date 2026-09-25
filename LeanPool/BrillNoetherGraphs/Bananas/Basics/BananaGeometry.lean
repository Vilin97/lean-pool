/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Basics.BananaBasics
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionTwoEdgeCut
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.CycleRigidity

/-!
# Global geometry of banana graphs

This file records structural facts about bananas which follow directly from
their presentation as positive subdivisions of a two-vertex parallel-edge
core.
-/

@[expose] public section

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

private theorem fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- The two-vertex core underlying every banana is connected. -/
theorem core_connected {g : ℕ} (B : Banana g) : B.core.Connected := by
  intro S hSplit
  obtain ⟨v, w, hv, hw⟩ := hSplit
  have hDifferentSides :
      ((0 : Fin 2) ∈ S ∧ (1 : Fin 2) ∉ S) ∨
        ((1 : Fin 2) ∈ S ∧ (0 : Fin 2) ∉ S) := by
    fin_cases v <;> fin_cases w <;> simp_all
  let edge : Fin (g + 1) := ⟨0, by omega⟩
  refine ⟨edge, ?_⟩
  rcases hDifferentSides with hSides | hSides <;>
    rcases fin_two_cases (B.core.tail edge) with hTail | hTail
  · left
    have hHead := head_eq_other_of_tail B edge hTail
    simpa [hTail, hHead] using hSides
  · right
    have hHead : B.core.head edge = 0 := by
      rcases fin_two_cases (B.core.head edge) with hHead | hHead
      · exact hHead
      · exfalso
        apply B.core_loopless edge
        simp [hTail, hHead]
    simpa [hTail, hHead] using hSides
  · right
    have hHead := head_eq_other_of_tail B edge hTail
    simpa [hTail, hHead] using hSides
  · left
    have hHead : B.core.head edge = 0 := by
      rcases fin_two_cases (B.core.head edge) with hHead | hHead
      · exact hHead
      · exfalso
        apply B.core_loopless edge
        simp [hTail, hHead]
    simpa [hTail, hHead] using hSides

/-- Every positive-length banana graph is connected. -/
theorem graphConnected {g : ℕ} (B : Banana g) :
    _root_.graphConnected B.graph :=
  B.graph_connected_of_coreConnected (core_connected B)

/-- With at least two strands, the parallel-edge core has no one-edge cut. -/
theorem core_twoEdgeConnected {g : ℕ} (hg : 1 ≤ g) (B : Banana g) :
    Utilities.Certificate.ExplicitPotential.Core.TwoEdgeConnected B.core := by
  classical
  intro S hNonempty hProper
  obtain ⟨inside, hInside⟩ := hNonempty
  obtain ⟨outside, hOutside⟩ : ∃ outside : Fin 2, outside ∉ S := by
    by_contra! hAll
    apply hProper
    ext vertex
    simp [hAll vertex]
  have hOpposite : inside ≠ outside := by
    intro h
    subst outside
    exact hOutside hInside
  have hCrosses (edge : Fin (g + 1)) :
      (B.core.tail edge ∈ S ∧ B.core.head edge ∉ S) ∨
        (B.core.head edge ∈ S ∧ B.core.tail edge ∉ S) := by
    rcases fin_two_cases inside with hInside0 | hInside1 <;>
      rcases fin_two_cases outside with hOutside0 | hOutside1
    · exact (hOpposite (hInside0.trans hOutside0.symm)).elim
    · rcases fin_two_cases (B.core.tail edge) with hTail | hTail <;>
        rcases fin_two_cases (B.core.head edge) with hHead | hHead
      · exact (B.core_loopless edge (by simp [hTail, hHead])).elim
      · left
        constructor
        · simpa [hTail, hInside0] using hInside
        · simpa [hHead, hOutside1] using hOutside
      · right
        constructor
        · simpa [hHead, hInside0] using hInside
        · simpa [hTail, hOutside1] using hOutside
      · exact (B.core_loopless edge (by simp [hTail, hHead])).elim
    · rcases fin_two_cases (B.core.tail edge) with hTail | hTail <;>
        rcases fin_two_cases (B.core.head edge) with hHead | hHead
      · exact (B.core_loopless edge (by simp [hTail, hHead])).elim
      · right
        constructor
        · simpa [hHead, hInside1] using hInside
        · simpa [hTail, hOutside0] using hOutside
      · left
        constructor
        · simpa [hTail, hInside1] using hInside
        · simpa [hHead, hOutside0] using hOutside
      · exact (B.core_loopless edge (by simp [hTail, hHead])).elim
    · exact (hOpposite (hInside1.trans hOutside1.symm)).elim
  have hFilter :
      ((Finset.univ : Finset (Fin (g + 1))).filter fun edge =>
        (B.core.tail edge ∈ S ∧ B.core.head edge ∉ S) ∨
          (B.core.head edge ∈ S ∧ B.core.tail edge ∉ S)) = Finset.univ := by
    ext edge
    simp [hCrosses edge]
  rw [hFilter]
  simp
  omega

/-- Thus a nontrivial banana has no bridge in its subdivided graph. -/
theorem graph_twoEdgeCutCondition {g : ℕ} (hg : 1 ≤ g) (B : Banana g) :
    TwoEdgeCutCondition B.graph :=
  _root_.Utilities.Certificate.SubdivisionGraph.Spec.twoEdgeCutCondition_graph_of_coreTwoEdgeConnected B
    (core_twoEdgeConnected hg B)

/-- Distinct vertices of a nontrivial banana represent distinct degree-one
divisor classes. -/
theorem not_linearEquiv_one_chip_sub {g : ℕ} (hg : 1 ≤ g) (B : Banana g)
    {p q : B.graph.V} (hpq : p ≠ q) :
    ¬ linearEquiv B.graph (oneChip q - oneChip p) 0 :=
  not_linear_equiv_one_chip_sub_of_twoEdgeCutCondition
    (graphConnected B) (graph_twoEdgeCutCondition hg B) hpq

/-- Convenient orientation of degree-one rigidity for an ordered marked pair. -/
theorem marks_not_linearEquiv {g : ℕ} (hg : 1 ≤ g) (B : Banana g)
    {u v : B.graph.V} (huv : u ≠ v) :
    ¬ linearEquiv B.graph (oneChip u - oneChip v) 0 :=
  not_linearEquiv_one_chip_sub hg B huv.symm

/-- The subdivision model has the advertised genus. -/
@[simp] theorem genus_graph {g : ℕ} (B : Banana g) :
    genus B.graph = g := by
  rw [SubdivisionGraph.Spec.genus_graph]
  omega

/-- The canonical divisor of a genus-`g` banana is supported at its two
multivalent endpoints, with coefficient `g - 1` at each endpoint.  The
coefficient is an integer, so this also correctly covers the genus-zero
single-strand case. -/
theorem canonical_divisor_eq_endpoints {g : ℕ} (B : Banana g) :
    canonicalDivisor B.graph =
      ((g : ℤ) - 1) •
        (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) := by
  classical
  funext vertex
  rcases vertex with coreVertex | interior
  · change vertexDegree B.graph (B.coreVertex coreVertex) - 2 = _
    rw [B.vertex_degree_coreVertex_eq_incidentSlots]
    have hIncident :
        (∑ edge : Fin (g + 1),
          ((if B.core.tail edge = coreVertex then (1 : ℤ) else 0) +
            if B.core.head edge = coreVertex then (1 : ℤ) else 0)) =
          (g : ℤ) + 1 := by
      have hTerm (edge : Fin (g + 1)) :
          ((if B.core.tail edge = coreVertex then (1 : ℤ) else 0) +
            if B.core.head edge = coreVertex then (1 : ℤ) else 0) = 1 := by
        rcases fin_two_cases (B.core.tail edge) with hTail | hTail <;>
          rcases fin_two_cases (B.core.head edge) with hHead | hHead
        · exfalso
          apply B.core_loopless edge
          simp [hTail, hHead]
        · fin_cases coreVertex <;> simp [hTail, hHead]
        · fin_cases coreVertex <;> simp [hTail, hHead]
        · exfalso
          apply B.core_loopless edge
          simp [hTail, hHead]
      calc
        (∑ edge : Fin (g + 1),
          ((if B.core.tail edge = coreVertex then (1 : ℤ) else 0) +
            if B.core.head edge = coreVertex then (1 : ℤ) else 0)) =
            ∑ _edge : Fin (g + 1), (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro edge _
              exact hTerm edge
        _ = (g : ℤ) + 1 := by simp
    rw [hIncident]
    fin_cases coreVertex <;>
      simp [leftEndpoint, rightEndpoint, oneChip,
        SubdivisionGraph.Spec.coreVertex] <;> ring
  · change vertexDegree B.graph
        (B.interiorVertex interior.1 interior.2) - 2 = _
    rw [B.vertex_degree_interiorVertex_eq_two]
    simp [leftEndpoint, rightEndpoint, oneChip,
      SubdivisionGraph.Spec.coreVertex]

end Bananas
