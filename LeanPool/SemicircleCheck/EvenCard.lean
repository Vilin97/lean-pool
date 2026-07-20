/-
Copyright (c) 2026 Wondermonger-daydreaming. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wondermonger-daydreaming
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Finset.Card

/-!
  EVEN CARDINALITY FROM A FIXED-POINT-FREE INVOLUTION

  A finite set closed under a fixed-point-free involution has even cardinality.
  This is the small combinatorial lemma later used in the Catalan recurrence.
-/

open Equiv Equiv.Perm

/-- A finite set closed under a fixed-point-free involution has even cardinality.

Proof by strong induction: pick any `x ∈ S`, remove the pair `{x, p x}`,
show the remainder is still closed under `p`, and recurse. -/
lemma even_card_of_fpf_closed {α : Type*}
    {p : Perm α} (hinv : ∀ x, p (p x) = x) (hfpf : ∀ x, p x ≠ x)
    (S : Finset α) (h_closed : ∀ x ∈ S, p x ∈ S) :
    Even S.card := by
  classical
  revert h_closed
  induction S using Finset.strongInduction with
  | H S ih =>
    intro h_closed
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨0, by simp⟩
    · have hpx : p x ∈ S := h_closed x hx
      have hne : x ≠ p x := fun h => hfpf x h.symm
      let S' := (S.erase x).erase (p x)
      have hS'_ss : S' ⊂ S := by
        refine ⟨fun y hy => ?_, fun h => ?_⟩
        · simp only [S', Finset.mem_erase] at hy
          exact hy.2.2
        · have : x ∈ S' := h hx
          simp [S', Finset.mem_erase] at this
      have hS'_closed : ∀ y ∈ S', p y ∈ S' := by
        intro y hy
        simp only [S', Finset.mem_erase] at hy ⊢
        refine ⟨?_, ?_, h_closed y hy.2.2⟩
        · intro h
          exact hy.2.1 (p.injective h)
        · intro h
          exact hy.1 (by rw [← hinv y, h])
      have hS'_even := ih S' hS'_ss hS'_closed
      have hpx_erase : p x ∈ S.erase x :=
        Finset.mem_erase.mpr ⟨hne.symm, hpx⟩
      have hcard : S.card = S'.card + 2 := by
        set c := (S.erase x).card
        have h1 : c = S.card - 1 := Finset.card_erase_of_mem hx
        have h2 : S'.card = c - 1 := Finset.card_erase_of_mem hpx_erase
        have h3 : ({x, p x} : Finset α).card ≤ S.card :=
          Finset.card_le_card (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption)
        rw [Finset.card_pair hne] at h3
        have h4 : 1 ≤ c := Finset.card_pos.mpr ⟨p x, hpx_erase⟩
        omega
      rw [hcard]
      obtain ⟨k, hk⟩ := hS'_even
      exact ⟨k + 1, by omega⟩
