/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — counting **all three** pairs of edges of a tripartite sub-triple

`Nibble.AX1.interedges_card_le_tripleGraph_edges` (`Nibble.TripleEdges`) bounds the number of edges
of `tripleGraph G A B C` from below by the edges of *one* of its three pairs.  The covering clause
of a sub-triple design needs the sharp form: the `2`-cliques of the tripartite graph are exactly the
cross edges, so the three interedge sets are disjoint and all three count.

* `Nibble.AX1.three_interedges_card_le_tripleGraph_edges` — the injection from the disjoint union of
  the three interedge sets;
* `Nibble.AX1.three_edgeDensity_mul_le_tripleGraph_edges` — its density form, the lower bound `Elo`
  used by the design.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapDesign


/-! # TripleEdges -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The `A`–`B` edges of `G` are edges of the tripartite graph of `(A, B, C)`.**  They inject
into its `2`-cliques (injectively, because `A` and `B` are disjoint, so an unordered pair
determines which endpoint lies in `A`). -/
theorem interedges_card_le_tripleGraph_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (hAB : Disjoint A B) :
    (#(G.interedges A B) : ℝ) ≤ (#((tripleGraph G A B C).cliqueFinset 2) : ℝ) := by
  classical
  have hcard : #(G.interedges A B) ≤ #((tripleGraph G A B C).cliqueFinset 2) := by
    refine Finset.card_le_card_of_injOn (fun p => ({p.1, p.2} : Finset V)) ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_coe, SimpleGraph.mk_mem_interedges_iff] at hp
      obtain ⟨hx, hy, hadj⟩ := hp
      have hne : x ≠ y := hadj.ne
      have hadj' : (tripleGraph G A B C).Adj x y := ⟨hadj, Or.inl ⟨hx, hy⟩⟩
      simpa only [Finset.mem_coe] using
        (pair_mem_cliqueFinset_two (tripleGraph G A B C) hne).mpr hadj'
    · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' heq
      simp only [Finset.mem_coe, SimpleGraph.mk_mem_interedges_iff] at hp hp'
      obtain ⟨hx, hy, -⟩ := hp
      obtain ⟨hx', hy', -⟩ := hp'
      have hxy : x ≠ y := fun h => (Finset.disjoint_left.mp hAB hx) (h ▸ hy)
      have hpairs : ({x, y} : Finset V) = ({x', y'} : Finset V) := heq
      have hxmem : x ∈ ({x', y'} : Finset V) := by
        rw [← hpairs]; simp
      have hymem : y ∈ ({x', y'} : Finset V) := by
        rw [← hpairs]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem hymem
      rcases hxmem with rfl | rfl
      · rcases hymem with rfl | rfl
        · exact absurd rfl hxy
        · rfl
      · exact absurd hy' (Finset.disjoint_left.mp hAB hx)
  exact_mod_cast hcard

/-- **Density form of `Nibble.AX1.interedges_card_le_tripleGraph_edges`.** -/
theorem edgeDensity_mul_le_tripleGraph_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (hAB : Disjoint A B) :
    (G.edgeDensity A B : ℝ) * (#A : ℝ) * (#B : ℝ)
      ≤ (#((tripleGraph G A B C).cliqueFinset 2) : ℝ) := by
  classical
  have hdef : (G.edgeDensity A B : ℝ) = (#(G.interedges A B) : ℝ) / ((#A : ℝ) * (#B : ℝ)) := by
    rw [SimpleGraph.edgeDensity_def]; push_cast; ring
  rcases Nat.eq_zero_or_pos #A with hA | hA
  · have : (#A : ℝ) = 0 := by exact_mod_cast hA
    rw [this]
    simp
  rcases Nat.eq_zero_or_pos #B with hB | hB
  · have : (#B : ℝ) = 0 := by exact_mod_cast hB
    rw [this]
    simp
  have hA' : (0 : ℝ) < (#A : ℝ) := by exact_mod_cast hA
  have hB' : (0 : ℝ) < (#B : ℝ) := by exact_mod_cast hB
  have hmul : (G.edgeDensity A B : ℝ) * (#A : ℝ) * (#B : ℝ) = (#(G.interedges A B) : ℝ) := by
    rw [hdef]; field_simp
  rw [hmul]
  exact interedges_card_le_tripleGraph_edges G A B C hAB

end Nibble.AX1

end


/-! # TripleEdgesThree -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The union of the three interedge sets of a triple, as a set of ordered pairs. -/
private noncomputable def crossPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) : Finset (V × V) :=
  G.interedges A B ∪ G.interedges A C ∪ G.interedges B C

omit [Fintype V] in
private theorem mem_crossPairs {G : SimpleGraph V} [DecidableRel G.Adj] {A B C : Finset V}
    {x y : V} : (x, y) ∈ crossPairs G A B C ↔
      (x ∈ A ∧ y ∈ B ∧ G.Adj x y) ∨ (x ∈ A ∧ y ∈ C ∧ G.Adj x y)
        ∨ (x ∈ B ∧ y ∈ C ∧ G.Adj x y) := by
  simp only [crossPairs, Finset.mem_union, SimpleGraph.mk_mem_interedges_iff]
  tauto

/-- **All three pairs of a sub-triple contribute to its edge count.** -/
theorem three_interedges_card_le_tripleGraph_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    #(G.interedges A B) + #(G.interedges A C) + #(G.interedges B C)
      ≤ #((tripleGraph G A B C).cliqueFinset 2) := by
  classical
  have hnA : ∀ {v : V}, v ∈ A → v ∉ B := fun hv => Finset.disjoint_left.mp hAB hv
  have hnA' : ∀ {v : V}, v ∈ A → v ∉ C := fun hv => Finset.disjoint_left.mp hAC hv
  have hnB : ∀ {v : V}, v ∈ B → v ∉ C := fun hv => Finset.disjoint_left.mp hBC hv
  -- the three interedge sets are pairwise disjoint
  have hd12 : Disjoint (G.interedges A B) (G.interedges A C) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    rw [SimpleGraph.mk_mem_interedges_iff] at h1 h2
    exact hnB h1.2.1 h2.2.1
  have hd13 : Disjoint (G.interedges A B) (G.interedges B C) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    rw [SimpleGraph.mk_mem_interedges_iff] at h1 h2
    exact hnA h1.1 h2.1
  have hd23 : Disjoint (G.interedges A C) (G.interedges B C) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    rw [SimpleGraph.mk_mem_interedges_iff] at h1 h2
    exact hnA h1.1 h2.1
  have hcard : #(crossPairs G A B C)
      = #(G.interedges A B) + #(G.interedges A C) + #(G.interedges B C) := by
    unfold crossPairs
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint hd12]
    exact Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun p => ({p.1, p.2} : Finset V)) ?_ ?_
  · rintro ⟨x, y⟩ hp
    rw [Finset.mem_coe] at hp
    have hp' := mem_crossPairs.mp hp
    have hadj : G.Adj x y := by rcases hp' with h | h | h <;> exact h.2.2
    have hcross : crossAdj A B C x y := by
      rcases hp' with h | h | h
      · exact Or.inl ⟨h.1, h.2.1⟩
      · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1⟩))))
    have : (tripleGraph G A B C).Adj x y := ⟨hadj, hcross⟩
    simpa only [Finset.mem_coe] using
      (pair_mem_cliqueFinset_two (tripleGraph G A B C) hadj.ne).mpr this
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' heq
    rw [Finset.mem_coe] at hp hp'
    have h1 := mem_crossPairs.mp hp
    have h2 := mem_crossPairs.mp hp'
    have hne : x ≠ y := by rcases h1 with h | h | h <;> exact h.2.2.ne
    have hpairs : ({x, y} : Finset V) = ({x', y'} : Finset V) := heq
    have hxmem : x ∈ ({x', y'} : Finset V) := by rw [← hpairs]; simp
    have hymem : y ∈ ({x', y'} : Finset V) := by rw [← hpairs]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem hymem
    rcases hxmem with hx1 | hx1
    · subst hx1
      rcases hymem with hy1 | hy1
      · exact absurd hy1.symm hne
      · subst hy1; rfl
    · -- the swapped case is impossible: it would put a vertex in two of the three parts
      exfalso
      have hyx' : y = x' := by
        rcases hymem with hy1 | hy1
        · exact hy1
        · exact absurd (hy1.trans hx1.symm) (Ne.symm hne)
      rw [← hyx', ← hx1] at h2
      rcases h1 with h | h | h <;> rcases h2 with h' | h' | h'
      · exact hnA h'.1 h.2.1
      · exact hnA h'.1 h.2.1
      · exact hnA' h.1 h'.2.1
      · exact hnA' h'.1 h.2.1
      · exact hnA' h'.1 h.2.1
      · exact hnA' h.1 h'.2.1
      · exact hnA' h'.1 h.2.1
      · exact hnA' h'.1 h.2.1
      · exact hnB h.1 h'.2.1

omit [Fintype V] [DecidableEq V] in
/-- The density of a pair times its area is the number of interedges (as a bound). -/
private theorem edgeDensity_mul_le_card_interedges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (G.edgeDensity A B : ℝ) * (#A : ℝ) * (#B : ℝ) ≤ (#(G.interedges A B) : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos #A with hA | hA
  · have : (#A : ℝ) = 0 := by exact_mod_cast hA
    rw [this]; simp
  rcases Nat.eq_zero_or_pos #B with hB | hB
  · have : (#B : ℝ) = 0 := by exact_mod_cast hB
    rw [this]; simp
  have hA' : (0 : ℝ) < (#A : ℝ) := by exact_mod_cast hA
  have hB' : (0 : ℝ) < (#B : ℝ) := by exact_mod_cast hB
  have hdef : (G.edgeDensity A B : ℝ) = (#(G.interedges A B) : ℝ) / ((#A : ℝ) * (#B : ℝ)) := by
    rw [SimpleGraph.edgeDensity_def]; push_cast; ring
  have hcancel : (#(G.interedges A B) : ℝ) / ((#A : ℝ) * (#B : ℝ)) * (#A : ℝ) * (#B : ℝ)
      = (#(G.interedges A B) : ℝ) := by field_simp
  rw [hdef, hcancel]

/-- **Density form**: the lower bound for the number of edges of a sub-triple used by the design. -/
theorem three_edgeDensity_mul_le_tripleGraph_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (G.edgeDensity A B : ℝ) * (#A : ℝ) * (#B : ℝ) + (G.edgeDensity A C : ℝ) * (#A : ℝ) * (#C : ℝ)
        + (G.edgeDensity B C : ℝ) * (#B : ℝ) * (#C : ℝ)
      ≤ (#((tripleGraph G A B C).cliqueFinset 2) : ℝ) := by
  have h1 := edgeDensity_mul_le_card_interedges G A B
  have h2 := edgeDensity_mul_le_card_interedges G A C
  have h3 := edgeDensity_mul_le_card_interedges G B C
  have h4 : ((#(G.interedges A B) + #(G.interedges A C) + #(G.interedges B C) : ℕ) : ℝ)
      ≤ (#((tripleGraph G A B C).cliqueFinset 2) : ℝ) := by
    exact_mod_cast three_interedges_card_le_tripleGraph_edges G A B C hAB hAC hBC
  push_cast at h4
  linarith

end Nibble.AX1
