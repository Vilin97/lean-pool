/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.Card

/-! # Reachability in a finite type

To decide `◃⁺` we compute, for a decidable relation on a finite type, the set of all
elements reachable in at least one step. Because `reachStep` only grows sets, after
`Fintype.card α` iterations we must have reached a fixed point, which then is exactly
the set of `Relation.TransGen`-successors. -/

public section

namespace PDL

namespace FinReach

variable {α : Type*} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- One step of computing the set of elements reachable via `r`. -/
def reachStep (s : Finset α) : Finset α :=
  s ∪ Finset.univ.filter (fun b => ∃ a ∈ s, r a b)

/-- The set of all elements reachable from `a` in at least one `r`-step. -/
def reachSet (a : α) : Finset α :=
  (reachStep r)^[Fintype.card α] (Finset.univ.filter (fun b => r a b))

lemma subset_reachStep (s : Finset α) : s ⊆ reachStep r s := by
  intro x hx
  simp [reachStep, hx]

lemma reachStep_iterate_mono (s : Finset α) {m n : ℕ} (h : m ≤ n) :
    (reachStep r)^[m] s ⊆ (reachStep r)^[n] s := by
  induction n with
  | zero => simp_all
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · rw [Function.iterate_succ_apply']
      exact (ih (Nat.lt_succ_iff.mp h')).trans (subset_reachStep r _)
    · exact subset_rfl

/-- As soon as the iteration stops growing it stays the same forever. -/
lemma reachStep_iterate_eq_of_eq (s : Finset α) {m : ℕ}
    (h : (reachStep r)^[m + 1] s = (reachStep r)^[m] s) :
    ∀ k, m ≤ k → (reachStep r)^[k] s = (reachStep r)^[m] s := by
  intro k hk
  induction k with
  | zero =>
    have : m = 0 := by omega
    subst this
    rfl
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with h' | rfl
    · have hik := ih (Nat.lt_succ_iff.mp h')
      rw [Function.iterate_succ_apply', hik, ← Function.iterate_succ_apply' (reachStep r) m s, h]
    · rfl

/-- As long as the iteration is still growing it gains at least one element per step. -/
lemma card_le_card_iterate (s : Finset α) :
    ∀ n, (∀ m < n, (reachStep r)^[m + 1] s ≠ (reachStep r)^[m] s) →
      n ≤ ((reachStep r)^[n] s).card := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hgrow
    have h1 : n ≤ ((reachStep r)^[n] s).card := ih (fun m hm => hgrow m (by omega))
    have hsub : (reachStep r)^[n] s ⊆ (reachStep r)^[n + 1] s :=
      reachStep_iterate_mono r s (by omega)
    have hss : (reachStep r)^[n] s ⊂ (reachStep r)^[n + 1] s :=
      ssubset_of_subset_of_ne hsub (Ne.symm (hgrow n (by omega)))
    have := Finset.card_lt_card hss
    omega

/-- After `Fintype.card α` steps the iteration has reached a fixed point. -/
lemma reachStep_iterate_card_fixed (s : Finset α) :
    reachStep r ((reachStep r)^[Fintype.card α] s) = (reachStep r)^[Fintype.card α] s := by
  set N := Fintype.card α with hN
  by_cases hgrow : ∀ m < N + 1, (reachStep r)^[m + 1] s ≠ (reachStep r)^[m] s
  · exfalso
    have h1 := card_le_card_iterate r s (N + 1) (fun m hm => hgrow m (by omega))
    have h2 : ((reachStep r)^[N + 1] s).card ≤ N := by
      rw [hN]
      simpa using Finset.card_le_univ ((reachStep r)^[N + 1] s)
    omega
  · push Not at hgrow
    obtain ⟨m, hm, heq⟩ := hgrow
    have h1 := reachStep_iterate_eq_of_eq r s heq N (by omega)
    have h2 := reachStep_iterate_eq_of_eq r s heq (N + 1) (by omega)
    rw [← Function.iterate_succ_apply' (reachStep r) N s, h1, h2]

lemma transGen_of_mem_iterate (a : α) : ∀ (n : ℕ) (b : α),
    b ∈ (reachStep r)^[n] (Finset.univ.filter (fun b => r a b)) → Relation.TransGen r a b := by
  intro n
  induction n with
  | zero =>
    intro b h
    simp only [Function.iterate_zero, id_eq, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Relation.TransGen.single h
  | succ n ih =>
    intro b h
    rw [Function.iterate_succ_apply'] at h
    simp only [reachStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases h with h | ⟨c, hc, hcb⟩
    · exact ih b h
    · exact (ih c hc).tail hcb

/-- The transitive closure of `r` is computed by `reachSet`. -/
theorem mem_reachSet_iff (a b : α) : b ∈ reachSet r a ↔ Relation.TransGen r a b := by
  constructor
  · exact transGen_of_mem_iterate r a _ b
  · intro h
    induction h with
    | single hab => exact reachStep_iterate_mono r _ (Nat.zero_le _) (by simp [hab])
    | tail _ hcb ih =>
      rw [reachSet, ← reachStep_iterate_card_fixed r]
      simp only [reachStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨_, ih, hcb⟩

/-- The transitive closure of a decidable relation on a finite type is decidable. -/
def decidableTransGen (a b : α) : Decidable (Relation.TransGen r a b) :=
  decidable_of_iff _ (mem_reachSet_iff r a b)

end FinReach

end PDL
