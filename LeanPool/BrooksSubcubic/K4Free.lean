/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Tactic.Push

/-!
# Subcubic Brooks theorem: K4Free

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- In a K₄-free graph, a degree-3 vertex has two non-adjacent neighbours. -/
theorem exists_nonadj_pair_of_cubic_K4free (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK4 : G.CliqueFree 4) {v₀ : V} (hdeg : G.degree v₀ = 3) :
    ∃ a b, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b := by
  classical
  have hcard : (G.neighborFinset v₀).card = 3 := by rw [G.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard
  have hmem : ∀ w ∈ G.neighborFinset v₀, G.Adj v₀ w := fun w hw => by
    rw [mem_neighborFinset] at hw
    exact hw
  have ha : G.Adj v₀ a := hmem a (by rw [hset]; exact Finset.mem_insert_self _ _)
  have hb : G.Adj v₀ b := hmem b (by rw [hset]; simp)
  have hc : G.Adj v₀ c := hmem c (by rw [hset]; simp)
  by_contra hcon
  push Not at hcon
  have hnab : G.Adj a b := hcon a b ha hb hab
  have hnac : G.Adj a c := hcon a c ha hc hac
  have hnbc : G.Adj b c := hcon b c hb hc hbc
  have hv0a : v₀ ≠ a := ha.ne
  have hv0b : v₀ ≠ b := hb.ne
  have hv0c : v₀ ≠ c := hc.ne
  refine hK4 {v₀, a, b, c} ?_
  refine ⟨?_, ?_⟩
  · intro y hy z hz hyz
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hy hz
    rcases hy with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hyz
        | assumption
        | (exact ha) | (exact hb) | (exact hc)
        | (exact hnab) | (exact hnac) | (exact hnbc)
        | (exact ha.symm) | (exact hb.symm) | (exact hc.symm)
        | (exact hnab.symm) | (exact hnac.symm) | (exact hnbc.symm)
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hbc]
    · simp [hac, hab]
    · simp [hv0a, hv0b, hv0c]

end BrooksSubcubic
end
