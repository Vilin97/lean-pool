/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.TopologicalVertices
import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessDegreeOneClasses

/-!
# Structural genus-two preliminaries

The graph-theoretic opening of Theorem 4.13 starts by suppressing no leaves:
the no-bridge condition already forces every vertex of a nontrivial graph to
have valence at least two.  This module records that reduction and its sharp
genus-two topological-vertex bound.
-/

namespace Bananas

open Utilities

private theorem cutMultiplicity_singleton_eq_vertex_degree
    (G : CFGraph) (v : G.V) :
    cutMultiplicity G ({v} : Finset G.V) = vertex_degree G v := by
  classical
  unfold cutMultiplicity
  rw [Finset.sum_singleton, outdeg_S_eq_sum_filter]
  unfold vertex_degree
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro w _ hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not,
    Finset.mem_singleton] at hw
  subst hw
  simp

/-- A nontrivial graph satisfying the no-bridge cut condition has minimum
valence two. -/
theorem hasMinimumValenceTwo_of_twoEdgeCutCondition
    (G : CFGraph) (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) :
    HasMinimumValenceTwo G := by
  intro v
  obtain ⟨p, q, hpq⟩ := hNontrivial
  obtain ⟨w, hw⟩ : ∃ w : G.V, w ≠ v := by
    by_cases hvp : v = p
    · subst v
      exact ⟨q, hpq.symm⟩
    · exact ⟨p, Ne.symm hvp⟩
  have hProper : ({v} : Finset G.V) ≠ Finset.univ := by
    intro hAll
    have hwMem : w ∈ ({v} : Finset G.V) := by
      rw [hAll]
      exact Finset.mem_univ w
    exact hw (Finset.mem_singleton.mp hwMem)
  have hCutSingleton := hCut ({v} : Finset G.V)
    ⟨v, Finset.mem_singleton_self v⟩ hProper
  rw [cutMultiplicity_singleton_eq_vertex_degree] at hCutSingleton
  exact hCutSingleton

/-- A nontrivial bridgeless genus-two graph has at most two vertices of
valence at least three.  Equality is the theta-core numerology; the strict
case is the vertex-wedge-of-cycles branch of Theorem 4.13. -/
theorem card_topologicalVertices_le_two_of_bridgeless_genus_two
    (G : CFGraph) (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) (hGenus : genus G = 2) :
    (topologicalVertices G).card ≤ 2 := by
  have hBound := card_topologicalVertices_le G
    (hasMinimumValenceTwo_of_twoEdgeCutCondition G hCut hNontrivial)
  rw [hGenus] at hBound
  norm_num at hBound
  exact_mod_cast hBound

/-- Genus two forces at least one topological vertex once every vertex has
valence at least two. -/
theorem topologicalVertices_nonempty_of_bridgeless_genus_two
    (G : CFGraph) (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) (hGenus : genus G = 2) :
    (topologicalVertices G).Nonempty := by
  let hMin : HasMinimumValenceTwo G :=
    hasMinimumValenceTwo_of_twoEdgeCutCondition G hCut hNontrivial
  by_contra hEmpty
  have hNoTop : ∀ v : G.V, ¬ 3 ≤ vertex_degree G v := by
    intro v hv
    have : v ∈ topologicalVertices G := by
      simp [topologicalVertices, hv]
    simp [Finset.not_nonempty_iff_eq_empty.mp hEmpty] at this
  have hDegTwo : ∀ v : G.V, vertex_degree G v = 2 := by
    intro v
    have hLower := hMin v
    have hUpper := hNoTop v
    omega
  have hSum := sum_vertex_degree_sub_two G
  have hZero : (∑ v : G.V, (vertex_degree G v - 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    rw [hDegTwo]
    norm_num
  rw [hZero, hGenus] at hSum
  norm_num at hSum

/-- Before suppressing bivalent paths, a nontrivial bridgeless genus-two
graph has either one or two topological vertices. -/
theorem card_topologicalVertices_eq_one_or_two_of_bridgeless_genus_two
    (G : CFGraph) (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) (hGenus : genus G = 2) :
    (topologicalVertices G).card = 1 ∨ (topologicalVertices G).card = 2 := by
  have hNonempty := topologicalVertices_nonempty_of_bridgeless_genus_two
    G hCut hNontrivial hGenus
  have hPositive : 0 < (topologicalVertices G).card := Finset.card_pos.mpr hNonempty
  have hUpper := card_topologicalVertices_le_two_of_bridgeless_genus_two
    G hCut hNontrivial hGenus
  omega

end Bananas
