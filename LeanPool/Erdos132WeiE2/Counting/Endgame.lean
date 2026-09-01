/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Finite counting endgame for six distances

This module turns the ordered distance values and exclusion cases into the final cardinality bound.
-/

namespace LeanPool.Erdos132WeiE2.Counting

lemma six_le_card_of_values (V : Finset ℝ) (eB eA eC Q RA RB : ℝ)
    (hmemB : eB ∈ V) (hmemA : eA ∈ V) (hmemC : eC ∈ V) (hmemQ : Q ∈ V)
    (hmem1 : (1 : ℝ) ∈ V) (hmemRA : RA ∈ V) (hmemRB : RB ∈ V)
    (o1 : eB < eA) (o2 : eA < eC) (o3 : eC < Q) (o4 : Q < 1)
    (rA1 : eA < RA) (rA2 : RA < 1) (rB1 : eB < RB) (rB2 : RB < RA)
    (x1 : ¬(RA = Q ∧ RB = eC)) (x2 : ¬(RA = Q ∧ RB = eA))
    (x3 : ¬(RA = eC ∧ RB = eA)) :
    6 ≤ V.card := by
  classical
  let S : Finset ℝ := {eB, eA, eC, Q, 1}
  have hBnot : eB ∉ ({eA, eC, Q, (1 : ℝ)} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have hAnot : eA ∉ ({eC, Q, (1 : ℝ)} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · linarith
    constructor <;> linarith
  have hCnot : eC ∉ ({Q, (1 : ℝ)} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> linarith
  have hQnot : Q ∉ ({(1 : ℝ)} : Finset ℝ) := by
    simpa only [Finset.mem_singleton] using ne_of_lt o4
  have hScard : S.card = 5 := by
    simp [S, hBnot, hAnot, hCnot, hQnot]
  have hSsub : S ⊆ V := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact hmemB
    · exact hmemA
    · exact hmemC
    · exact hmemQ
    · exact hmem1
  by_contra hcard
  have hVcard : V.card < 6 := Nat.lt_of_not_ge hcard
  have hRAin : RA ∈ S := by
    by_contra hnot
    have hinsSub : insert RA S ⊆ V := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact hmemRA
      · exact hSsub hz
    have hinsCard : (insert RA S).card = 6 := by
      rw [Finset.card_insert_of_notMem hnot, hScard]
    have := Finset.card_le_card hinsSub
    omega
  have hRBin : RB ∈ S := by
    by_contra hnot
    have hinsSub : insert RB S ⊆ V := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact hmemRB
      · exact hSsub hz
    have hinsCard : (insert RB S).card = 6 := by
      rw [Finset.card_insert_of_notMem hnot, hScard]
    have := Finset.card_le_card hinsSub
    omega
  have hRAcases : RA = eC ∨ RA = Q := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hRAin
    rcases hRAin with h | h | h | h | h
    · exfalso; linarith
    · exfalso; linarith
    · exact Or.inl h
    · exact Or.inr h
    · exfalso; linarith
  rcases hRAcases with hRAeC | hRAQ
  · have hRBeA : RB = eA := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hRBin
      rcases hRBin with h | h | h | h | h
      · exfalso; linarith
      · exact h
      · exfalso; linarith
      · exfalso; linarith
      · exfalso; linarith
    exact x3 ⟨hRAeC, hRBeA⟩
  · have hRBcases : RB = eA ∨ RB = eC := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hRBin
      rcases hRBin with h | h | h | h | h
      · exfalso; linarith
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; linarith
      · exfalso; linarith
    rcases hRBcases with hRBeA | hRBeC
    · exact x2 ⟨hRAQ, hRBeA⟩
    · exact x1 ⟨hRAQ, hRBeC⟩

end LeanPool.Erdos132WeiE2.Counting
