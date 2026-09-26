/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Normalization

/-! # Target-free bounded search on the observed finite set -/

public section

namespace GenLimit.FiniteWitness

variable {α : Type*} [Encodable α] [DecidableEq α]

/-- A tentative bad extension: its output is unconfirmed by the entire sample. -/
@[expose] def Candidate (F : List α → α) (S : Finset α) (n : ℕ)
    (p : List α) (k : ℕ) (q : List α) : Prop :=
  p <+: q ∧ p.length < q.length ∧ q.toFinset ⊆ S ∧ q.length ≤ 2 * n ∧
    checkpoint (↑S : Set α) (k + 1) ⊆ q.toFinset ∧ F q ∉ S

/-- Bounded iteration; an empty candidate set leaves the current word fixed. -/
@[expose] noncomputable def sampleRun (F : List α → α) (S : Finset α) (n : ℕ) : ℕ → List α
  | 0 => []
  | k + 1 => by
      classical
      exact if h : ∃ q, Candidate F S n (sampleRun F S n k) k q then
        leastCode _ h else sampleRun F S n k

theorem sampleRun_next {F : List α → α} {S : Finset α} {n k : ℕ}
    (h : ∃ q, Candidate F S n (sampleRun F S n k) k q) :
    Candidate F S n (sampleRun F S n k) k (sampleRun F S n (k + 1)) := by
  classical
  simp only [sampleRun, dite_eq_left h]
  exact leastCode_spec _ h

theorem sampleRun_prefix (F : List α → α) (S : Finset α) (n k : ℕ) :
    sampleRun F S n k <+: sampleRun F S n (k + 1) := by
  classical
  by_cases h : ∃ q, Candidate F S n (sampleRun F S n k) k q
  · exact (sampleRun_next h).1
  · simp only [sampleRun, dite_eq_right h]
    exact List.prefix_refl _

theorem sampleRun_content (F : List α → α) (S : Finset α) (n k : ℕ) :
    (sampleRun F S n k).toFinset ⊆ S := by
  classical
  induction k with
  | zero => simp [sampleRun]
  | succ k ih =>
      by_cases h : ∃ q, Candidate F S n (sampleRun F S n k) k q
      · exact (sampleRun_next h).2.2.1
      · simpa only [sampleRun, dite_eq_right h] using ih

theorem sampleRun_length (F : List α → α) (S : Finset α) (n k : ℕ) :
    (sampleRun F S n k).length ≤ 2 * n := by
  classical
  induction k with
  | zero => simp [sampleRun]
  | succ k ih =>
      by_cases h : ∃ q, Candidate F S n (sampleRun F S n k) k q
      · exact (sampleRun_next h).2.2.2.1
      · simpa only [sampleRun, dite_eq_right h] using ih

theorem sampleRun_preserves_fresh {F : List α → α} {S : Finset α} {n k j : ℕ}
    (hk : F (sampleRun F S n k) ∉ S) (hkj : k ≤ j) :
    F (sampleRun F S n j) ∉ S := by
  classical
  induction j, hkj using Nat.le_induction with
  | base => exact hk
  | succ j _ ih =>
      by_cases h : ∃ q, Candidate F S n (sampleRun F S n j) j q
      · exact (sampleRun_next h).2.2.2.2.2
      · simpa only [sampleRun, dite_eq_right h] using ih

/-- The normalized output function is fixed before a target is selected. -/
@[expose] noncomputable def normalized (F : List α → α) (S : Finset α) : α :=
  F (sampleRun F S S.card S.card)

end GenLimit.FiniteWitness
