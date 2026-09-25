/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessGenusTwoTopology

/-!
# Degree shapes of bridgeless genus-two cores

The topological-vertex bound reduces a bridgeless genus-two graph to one of
two numerical possibilities.  This file records the corresponding exact
valence shapes.  It is deliberately independent of any bivalent-suppression
construction: those shapes are invariants of the original graph as well.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- If a nontrivial bridgeless genus-two graph has one topological vertex,
that vertex has valence four and every other vertex is bivalent. -/
theorem exists_degree_four_vertex_of_unique_topological_of_bridgeless_genus_two
    (G : CFGraph) (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) (hGenus : genus G = 2)
    (hCard : (topologicalVertices G).card = 1) :
    ∃ w : G.V, vertexDegree G w = 4 ∧
      ∀ v : G.V, v ≠ w → vertexDegree G v = 2 := by
  classical
  obtain ⟨w, hTop⟩ := Finset.card_eq_one.mp hCard
  let hMin := hasMinimumValenceTwo_of_twoEdgeCutCondition G hCut hNontrivial
  have hTopW : 3 ≤ vertexDegree G w := by
    have : w ∈ topologicalVertices G := by rw [hTop]; simp
    simpa [topologicalVertices] using this
  have hOther : ∀ v : G.V, v ≠ w → vertexDegree G v = 2 := by
    intro v hv
    have hNotTop : ¬ 3 ≤ vertexDegree G v := by
      intro hDegree
      have : v ∈ topologicalVertices G := by simpa [topologicalVertices] using hDegree
      rw [hTop] at this
      exact hv (Finset.mem_singleton.mp this)
    have hLower := hMin v
    omega
  refine ⟨w, ?_, hOther⟩
  have hSum := sum_vertex_degree_sub_two G
  have hSumVal : (∑ v : G.V, (vertexDegree G v - 2)) = vertexDegree G w - 2 := by
    apply Finset.sum_eq_single w
    · intro v _ hv
      rw [hOther v hv]
      norm_num
    · simp
  rw [hSumVal, hGenus] at hSum
  omega

/-- If a nontrivial bridgeless genus-two graph has two topological vertices,
they are both trivalent and every remaining vertex is bivalent. -/
theorem exists_two_trivalent_vertices_of_two_topological_of_bridgeless_genus_two
    (G : CFGraph) (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) (hGenus : genus G = 2)
    (hCard : (topologicalVertices G).card = 2) :
    ∃ w₁ w₂ : G.V, w₁ ≠ w₂ ∧
      vertexDegree G w₁ = 3 ∧ vertexDegree G w₂ = 3 ∧
      ∀ v : G.V, v ≠ w₁ → v ≠ w₂ → vertexDegree G v = 2 := by
  classical
  obtain ⟨w₁, w₂, hNe, hTop⟩ := Finset.card_eq_two.mp hCard
  let hMin := hasMinimumValenceTwo_of_twoEdgeCutCondition G hCut hNontrivial
  have hTop₁ : 3 ≤ vertexDegree G w₁ := by
    have : w₁ ∈ topologicalVertices G := by rw [hTop]; simp
    simpa [topologicalVertices] using this
  have hTop₂ : 3 ≤ vertexDegree G w₂ := by
    have : w₂ ∈ topologicalVertices G := by rw [hTop]; simp
    simpa [topologicalVertices] using this
  have hOther : ∀ v : G.V, v ≠ w₁ → v ≠ w₂ → vertexDegree G v = 2 := by
    intro v hv₁ hv₂
    have hNotTop : ¬ 3 ≤ vertexDegree G v := by
      intro hDegree
      have : v ∈ topologicalVertices G := by simpa [topologicalVertices] using hDegree
      rw [hTop] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact hv₁ h
      · exact hv₂ h
    have hLower := hMin v
    omega
  have hSum := sum_vertex_degree_sub_two G
  have hSumVal : (∑ v : G.V, (vertexDegree G v - 2)) =
      (vertexDegree G w₁ - 2) + (vertexDegree G w₂ - 2) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₁)]
    rw [Finset.sum_eq_single w₂]
    · intro v hV hv
      have hv₁ : v ≠ w₁ := (Finset.mem_erase.mp hV).1
      rw [hOther v hv₁ hv]
      norm_num
    · intro hNot
      exfalso
      apply hNot
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact hNe.symm
  rw [hSumVal, hGenus] at hSum
  refine ⟨w₁, w₂, hNe, ?_, ?_, hOther⟩ <;> omega

end Bananas
