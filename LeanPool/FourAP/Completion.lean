/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
import LeanPool.FourAP.Basic

/-!
# Reading a finite prefix and its completion

These elementary bookkeeping facts make precise the paper's statements that
“the terms ... which lie in `P` form an initial segment” and that extending a
prefix does not move any of its old entries. They are independent of the special
binary order.
-/
namespace FourAP

variable {R : ℕ → ℕ → Prop} {P Q : List ℕ} {a b c : ℕ}

/-- The completion of a word beginning with `t`: `t` comes first, and deleting
it leaves the completion of the remaining word. This is bookkeeping for the
paper's operation of putting a finite word before the binary-ordered tail. -/
theorem completion_cons (R : ℕ → ℕ → Prop) (P : List ℕ) (t a b : ℕ) :
    Completion R (t :: P) a b ↔
      (a = t ∧ b ≠ t) ∨ (a ≠ t ∧ b ≠ t ∧ Completion R P a b) := by
  simp only [Completion, List.idxOf_cons, beq_iff_eq, List.mem_cons]
  by_cases ha : a = t <;> by_cases hb : b = t <;> simp_all [eq_comm]

/-- In `𝒞(P)`, each entry of `P` precedes every unused integer. -/
theorem completion_mem_notMem (ha : a ∈ P) (hb : b ∉ P) :
    Completion R P a b := by
  left
  rw [List.idxOf_eq_length hb]
  exact List.idxOf_lt_length_of_mem ha

/-- On the unused integers, `𝒞(P)` agrees with the background order. -/
theorem completion_of_notMem (ha : a ∉ P) (hb : b ∉ P) :
    Completion R P a b ↔ R a b := by
  simp [Completion, ha, hb]

/-- No entry outside the prefix can precede an entry inside it. -/
theorem completion_mem_left (h : Completion R P a b) (hb : b ∈ P) : a ∈ P := by
  rcases h with h | ⟨_, hn, _⟩
  · exact List.idxOf_lt_length_iff.mp (Nat.lt_trans h (List.idxOf_lt_length_of_mem hb))
  · exact (hn hb).elim

/-- A completion is asymmetric whenever its background order is asymmetric. -/
theorem completion_asymm (hR : ∀ ⦃x y⦄, R x y → ¬ R y x)
    (h : Completion R P a b) : ¬ Completion R P b a := by
  rintro (h' | ⟨hb, ha, h'⟩)
  · rcases h with h | ⟨ha, hb, _⟩
    · omega
    · rw [List.idxOf_eq_length ha, List.idxOf_eq_length hb] at h'
      omega
  · rcases h with h | ⟨_, _, h⟩
    · rw [List.idxOf_eq_length ha, List.idxOf_eq_length hb] at h
      omega
    · exact hR h h'

/-- The completed order is irreflexive whenever the background order is.
Together with the next two lemmas, this verifies that the paper's `𝒞(P)` is
a strict linear order rather than merely a relation. -/
theorem completion_irrefl (hR : ∀ x, ¬ R x x) (a : ℕ) :
    ¬ Completion R P a a := by
  rintro (h | ⟨_, _, h⟩)
  · exact (Nat.lt_irrefl _ h)
  · exact hR a h

/-- Concatenating the finite prefix and its background-ordered complement
preserves transitivity, as required by the paper's definition of `𝒞(P)`. -/
theorem completion_trans (hR : ∀ ⦃x y z⦄, R x y → R y z → R x z)
    (hab : Completion R P a b) (hbc : Completion R P b c) :
    Completion R P a c := by
  rcases hab with hab | ⟨ha, hb, hab⟩
  · rcases hbc with hbc | ⟨hb, hc, _⟩
    · exact Or.inl (Nat.lt_trans hab hbc)
    · left
      rwa [List.idxOf_eq_length hc, ← List.idxOf_eq_length hb]
  · rcases hbc with hbc | ⟨_, hc, hbc⟩
    · have hlen : P.idxOf c ≤ P.length := List.idxOf_le_length
      rw [List.idxOf_eq_length hb] at hbc
      omega
    · exact Or.inr ⟨ha, hc, hR hab hbc⟩

/-- Every two distinct entries are comparable in `𝒞(P)` when they are
comparable in the background order. Thus the finite-prefix construction in
the paper indeed defines a strict linear order. -/
theorem completion_total (hR : ∀ ⦃x y⦄, x ≠ y → R x y ∨ R y x)
    (hne : a ≠ b) : Completion R P a b ∨ Completion R P b a := by
  by_cases ha : a ∈ P
  · by_cases hb : b ∈ P
    · have hidx : P.idxOf a ≠ P.idxOf b := fun h => hne ((List.idxOf_inj ha).mp h)
      rcases lt_or_gt_of_ne hidx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl (completion_mem_notMem ha hb)
  · by_cases hb : b ∈ P
    · exact Or.inr (completion_mem_notMem hb ha)
    · rcases hR hne with h | h
      · exact Or.inl (Or.inr ⟨ha, hb, h⟩)
      · exact Or.inr (Or.inr ⟨hb, ha, h⟩)

/-- Prefix extension preserves all comparisons whose first entry was already
placed. This is used twice in the contradiction argument in Lemma 2. -/
theorem completion_prefix_left (hp : P.IsPrefix Q) (ha : a ∈ P)
    (h : Completion R Q a b) : Completion R P a b := by
  obtain ⟨S, rfl⟩ := hp
  by_cases hb : b ∈ P
  · rcases h with h | ⟨hn, _, _⟩
    · left
      simpa only [List.idxOf_append, ite_eq_left ha, ite_eq_left hb] using h
    · exact (hn (List.mem_append_left S ha)).elim
  · exact completion_mem_notMem ha hb

/-- In an extended completion, the old word is still an initial segment. -/
theorem completion_prefix_mem_left (hp : P.IsPrefix Q) (hb : b ∈ P)
    (h : Completion R Q a b) : a ∈ P := by
  obtain ⟨S, rfl⟩ := hp
  rcases h with h | ⟨_, hn, _⟩
  · by_contra ha
    rw [List.idxOf_append, List.idxOf_append, ite_eq_right ha, ite_eq_left hb] at h
    have := List.idxOf_lt_length_of_mem hb
    omega
  · exact (hn (List.mem_append_left S hb)).elim

end FourAP
