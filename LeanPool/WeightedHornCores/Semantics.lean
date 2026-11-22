/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import Mathlib.Data.Finset.Card

/-!
# Bounded certificates for Horn entailment

An atom is forced at budget `n` if some subformula of at most `n` clauses entails it.
Certificates for all premises of a clause can be combined by taking their union.
-/

@[expose] public section

namespace WeightedHornCores

/-- A Horn clause. An absent head denotes a denial. -/
structure Clause (α : Type*) where
  /-- The atoms required to trigger the clause. -/
  body : Finset α
  /-- The conclusion, or `none` for contradiction. -/
  head : Option α
  deriving DecidableEq

variable {α : Type*}

/-- An assignment satisfies a clause if its body implies its head. -/
def Clause.Holds (c : Clause α) (s : Set α) : Prop :=
  (∀ x ∈ c.body, x ∈ s) → match c.head with
    | none => False
    | some x => x ∈ s

/-- A model satisfies every clause of the formula. -/
def Models (F : Finset (Clause α)) (s : Set α) : Prop := ∀ c ∈ F, c.Holds s

/-- Restrict a model to a subformula. -/
theorem Models.mono {F K : Finset (Clause α)} {s : Set α} (hs : Models F s) (hK : K ⊆ F) :
    Models K s := fun c hc => hs c (hK hc)

/-- Atoms entailed by a subformula using at most `n` clauses. -/
def Forced (F : Finset (Clause α)) (n : ℕ) : Set α :=
  {x | ∃ K ⊆ F, K.card ≤ n ∧ ∀ s, Models K s → x ∈ s}

/-- Increasing the budget preserves every entailment certificate. -/
theorem forced_mono {F : Finset (Clause α)} {m n : ℕ} (h : m ≤ n) : Forced F m ⊆ Forced F n := by
  rintro x ⟨K, hK, hcard, hx⟩
  exact ⟨K, hK, hcard.trans h, hx⟩

private theorem body_certificate {F : Finset (Clause α)} {k : ℕ} {b : Finset α}
    (hb : ∀ x ∈ b, x ∈ Forced F k) :
    ∃ K ⊆ F, K.card ≤ b.card * k ∧ ∀ s, Models K s → ∀ x ∈ b, x ∈ s := by
  classical
  induction b using Finset.induction_on with
  | empty => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | @insert a b ha ih =>
    obtain ⟨A, hA, hsizeA, hforceA⟩ := hb a (Finset.mem_insert_self a b)
    obtain ⟨B, hB, hsizeB, hforceB⟩ := ih fun x hx => hb x (Finset.mem_insert_of_mem hx)
    refine ⟨A ∪ B, Finset.union_subset hA hB, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha, Nat.succ_mul]
      have := Finset.card_union_le A B
      omega
    · intro s hs x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hforceA s (hs.mono Finset.subset_union_left)
      · exact hforceB s (hs.mono Finset.subset_union_right) x hx

private theorem clause_certificate {F : Finset (Clause α)} {c : Clause α} {k : ℕ}
    (hc : c ∈ F) (hbody : ∀ y ∈ c.body, y ∈ Forced F k) :
    ∃ K ⊆ F, K.card ≤ 1 + c.body.card * k ∧ ∀ s, Models K s →
      match c.head with
      | none => False
      | some x => x ∈ s := by
  classical
  obtain ⟨B, hB, hsize, hforce⟩ := body_certificate hbody
  refine ⟨insert c B, Finset.insert_subset hc hB, ?_, ?_⟩
  · have := Finset.card_insert_le c B
    omega
  · intro s hs
    exact hs c (Finset.mem_insert_self c B) (hforce s (hs.mono (Finset.subset_insert c B)))

/-- One clause plus certificates for its premises force its head. -/
theorem force_head {F : Finset (Clause α)} {c : Clause α} {x : α} {k : ℕ}
    (hc : c ∈ F) (hh : c.head = some x) (hbody : ∀ y ∈ c.body, y ∈ Forced F k) :
    x ∈ Forced F (1 + c.body.card * k) := by
  obtain ⟨K, hK, hsize, hforce⟩ := clause_certificate hc hbody
  exact ⟨K, hK, hsize, by simpa only [hh] using hforce⟩

/-- One denial plus certificates for its premises form an unsatisfiable core. -/
theorem core_of_denial {F : Finset (Clause α)} {c : Clause α} {k : ℕ}
    (hc : c ∈ F) (hh : c.head = none) (hbody : ∀ y ∈ c.body, y ∈ Forced F k) :
    ∃ K ⊆ F, K.card ≤ 1 + c.body.card * k ∧ ¬ ∃ s, Models K s := by
  obtain ⟨K, hK, hsize, hforce⟩ := clause_certificate hc hbody
  refine ⟨K, hK, hsize, ?_⟩
  rintro ⟨s, hs⟩
  simpa only [hh] using hforce s hs

end WeightedHornCores
