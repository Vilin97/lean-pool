/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# A fixed-point-free involution halves a finset

A finset carrying a fixed-point-free involution is the disjoint
union of two-element orbits, so its cardinality is even, and the
same holds of a finite type (`even_fintypeCard_of_involution`).  This
is the counting behind every parity statement about matched flags:
edges match flags in pairs, chords match labels in pairs, and a
directed matching matches its points in pairs.
-/

@[expose] public section

namespace RS

/-- **A fixed-point-free involution halves a finset.** -/
theorem even_card_of_involution {γ : Type} (t : Finset γ) :
    ∀ i : γ → γ, (∀ x ∈ t, i x ∈ t) → (∀ x ∈ t, i (i x) = x) →
      (∀ x ∈ t, i x ≠ x) → Even t.card := by
  classical
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro i hmem hinv hne
    rcases Finset.eq_empty_or_nonempty t with rfl | ⟨x, hx⟩
    · rw [Finset.card_empty]
      exact ⟨0, rfl⟩
    · have hix := hmem x hx
      have hxne : x ≠ i x := fun h => hne x hx h.symm
      have hsub : {x, i x} ⊆ t := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · rw [Finset.mem_singleton.mp hy]; exact hix
      have hssub : t \ {x, i x} ⊂ t :=
        Finset.sdiff_ssubset hsub (by simp)
      have hmem' : ∀ y ∈ t \ {x, i x}, i y ∈ t \ {x, i x} := by
        intro y hy
        rw [Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_singleton] at hy ⊢
        push Not at hy ⊢
        obtain ⟨hyt, hyx, hyix⟩ := hy
        refine ⟨hmem y hyt, ?_, ?_⟩
        · intro h
          exact hyix (by rw [← hinv y hyt, h])
        · intro h
          have := hinv y hyt
          rw [h, hinv x hx] at this
          exact hyx this.symm
      have hinv' : ∀ y ∈ t \ {x, i x}, i (i y) = y := fun y hy =>
        hinv y (Finset.mem_sdiff.mp hy).1
      have hne' : ∀ y ∈ t \ {x, i x}, i y ≠ y := fun y hy =>
        hne y (Finset.mem_sdiff.mp hy).1
      have heven := ih _ hssub i hmem' hinv' hne'
      have hcard : t.card = (t \ {x, i x}).card + 2 := by
        have hh := Finset.card_sdiff_add_card_eq_card hsub
        rw [Finset.card_pair hxne] at hh
        omega
      obtain ⟨r, hr⟩ := heven
      exact ⟨r + 1, by omega⟩

/-- **The `Fintype` form**: a type carrying a fixed-point-free
involution has even cardinality. -/
theorem even_fintypeCard_of_involution {X : Type} [Fintype X]
    (i : X → X) (hinv : ∀ x, i (i x) = x) (hne : ∀ x, i x ≠ x) :
    Even (Fintype.card X) := by
  classical
  have := even_card_of_involution (Finset.univ : Finset X) i
    (fun x _ => Finset.mem_univ _) (fun x _ => hinv x)
    (fun x _ => hne x)
  rwa [Finset.card_univ] at this

end RS
