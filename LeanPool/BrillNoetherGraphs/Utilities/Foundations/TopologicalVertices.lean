/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.Basic

/-!
# Topological vertices

After grafted trees have been pruned, the low-genus classification treats
vertices of valence at least three as topological vertices. The
minimum-valence-two hypothesis is essential for bounding their number in terms
of the genus.
-/

@[expose] public section

namespace Utilities

/-- The vertices of valence at least three. -/
def topologicalVertices (G : CFGraph) : Finset G.V :=
  Finset.univ.filter fun v => 3 ≤ vertexDegree G v

/-- Every vertex has valence at least two. This is the structural condition
obtained after pruning grafted trees. -/
def HasMinimumValenceTwo (G : CFGraph) : Prop :=
  ∀ v : G.V, 2 ≤ vertexDegree G v

/-- Connectivity across a singleton cut gives positive valence whenever the
graph has a vertex distinct from each chosen vertex.  The genus-specific
leafless-normalization arguments supply the second-vertex hypothesis from
their edge-count identities; keeping that argument separate makes this
singleton-cut step reusable at every genus. -/
theorem vertex_degree_pos_of_connected_of_exists_vertex_ne
    {G : CFGraph} (hConnected : graphConnected G)
    (hOther : ∀ vertex : G.V, ∃ other : G.V, other ≠ vertex)
    (vertex : G.V) :
    0 < vertexDegree G vertex := by
  obtain ⟨other, hOther⟩ := hOther vertex
  have hSplit :
      ∃ inside outside : G.V,
        inside ∈ ({vertex} : Finset G.V) ∧ outside ∉ ({vertex} : Finset G.V) := by
    exact ⟨vertex, other, by simp, by simpa [Ne.symm hOther]⟩
  obtain ⟨inside, hInside, outside, _hOutside, hEdge⟩ :=
    hConnected ({vertex} : Finset G.V) hSplit
  have hInsideEq : inside = vertex := by simpa using hInside
  subst inside
  unfold vertexDegree
  apply Finset.sum_pos'
  · intro neighbor _hNeighbor
    positivity
  · refine ⟨outside, Finset.mem_univ outside, ?_⟩
    exact_mod_cast hEdge

/-- A connected leafless graph with at least two vertices has minimum valence
two.  This is the common first step before suppressing bivalent chains in a
loop-aware normalizer. -/
theorem hasMinimumValenceTwo_of_leafless_of_exists_vertex_ne
    {G : CFGraph} (hConnected : graphConnected G)
    (hOther : ∀ vertex : G.V, ∃ other : G.V, other ≠ vertex)
    (hLeafless : ∀ vertex : G.V, vertexDegree G vertex ≠ 1) :
    HasMinimumValenceTwo G := by
  intro vertex
  have hPositive :=
    vertex_degree_pos_of_connected_of_exists_vertex_ne hConnected hOther vertex
  have hNotOne := hLeafless vertex
  omega

/-- Every vertex is bivalent or trivalent. -/
def IsTopologicallyTrivalent (G : CFGraph) : Prop :=
  ∀ v : G.V, vertexDegree G v = 2 ∨ vertexDegree G v = 3

/-- The sum of the valence excesses over two is `2g - 2`. -/
theorem sum_vertex_degree_sub_two (G : CFGraph) :
    (∑ v : G.V, (vertexDegree G v - 2)) = 2 * genus G - 2 := by
  rw [Finset.sum_sub_distrib, sum_vertex_degree_eq_twice_card_edges]
  simp only [Finset.sum_const, Finset.card_univ, Int.nsmul_eq_mul, genus]
  ring

/-- A graph of minimum valence two has at most `2g - 2` topological
vertices. -/
theorem card_topologicalVertices_le
    (G : CFGraph) (hMin : HasMinimumValenceTwo G) :
    ((topologicalVertices G).card : ℤ) ≤ 2 * genus G - 2 := by
  calc
    ((topologicalVertices G).card : ℤ) =
        ∑ v : G.V, if 3 ≤ vertexDegree G v then (1 : ℤ) else 0 := by
      simp [topologicalVertices]
    _ ≤ ∑ v : G.V, (vertexDegree G v - 2) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hTopological : 3 ≤ vertexDegree G v
      · simp only [hTopological, ↓reduceIte]
        omega
      · simp only [hTopological, ↓reduceIte, Int.sub_nonneg]
        exact hMin v
    _ = 2 * genus G - 2 := sum_vertex_degree_sub_two G

/-- In a bivalent/trivalent graph, the number of trivalent vertices is exactly
`2g - 2`. -/
theorem card_topologicalVertices_eq_of_topologicallyTrivalent
    (G : CFGraph) (hTri : IsTopologicallyTrivalent G) :
    ((topologicalVertices G).card : ℤ) = 2 * genus G - 2 := by
  calc
    ((topologicalVertices G).card : ℤ) =
        ∑ v : G.V, if 3 ≤ vertexDegree G v then (1 : ℤ) else 0 := by
      simp [topologicalVertices]
    _ = ∑ v : G.V, (vertexDegree G v - 2) := by
      apply Finset.sum_congr rfl
      intro v _
      rcases hTri v with hDegree | hDegree
      · simp [hDegree]
      · simp [hDegree]
    _ = 2 * genus G - 2 := sum_vertex_degree_sub_two G

/-- A topologically trivalent genus-four graph has six topological vertices. -/
theorem card_topologicalVertices_eq_six_of_genus_four
    (G : CFGraph) (hTri : IsTopologicallyTrivalent G)
    (hGenus : genus G = 4) :
    (topologicalVertices G).card = 6 := by
  have hCard := card_topologicalVertices_eq_of_topologicallyTrivalent G hTri
  rw [hGenus] at hCard
  norm_num at hCard
  exact_mod_cast hCard

/-- A topologically trivalent genus-five graph has eight topological vertices. -/
theorem card_topologicalVertices_eq_eight_of_genus_five
    (G : CFGraph) (hTri : IsTopologicallyTrivalent G)
    (hGenus : genus G = 5) :
    (topologicalVertices G).card = 8 := by
  have hCard := card_topologicalVertices_eq_of_topologicallyTrivalent G hTri
  rw [hGenus] at hCard
  norm_num at hCard
  exact_mod_cast hCard

end Utilities
