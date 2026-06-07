/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

/-! # Wires

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

def Wires (V : Type u) (I : ℕ) := Vector V I

instance [Preorder V] : Preorder (Wires V I) where
  le a b := ∀ i : Fin I, a.get i ≤ b.get i
  le_refl _ _ := le_refl _
  le_trans _ _ _ h₁ h₂ i := le_trans (h₁ i) (h₂ i)
  lt_iff_le_not_ge _ _ := by rfl

lemma Wires.ext : ∀ {n} {a b : Wires V n}, (∀ i : Fin n, a.get i = b.get i) → a = b := by
  intro n a b h; apply Vector.ext; intro i hi; exact h ⟨i, hi⟩

@[simp]
lemma Wires.get_ofFn :
    ∀ {n : ℕ} {α : Type u} (f : Fin n → α) (i : Fin n), (Vector.ofFn f).get i = f i := by
  intro n α f i
  simp only [Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]; congr 1

@[simp]
lemma Wires.get_cast {n m : ℕ} (h : n = m) (v : Wires V n) (i : Fin m) :
    (v.cast h).get i = v.get ⟨i.val, h ▸ i.isLt⟩ := by
  subst h; rfl

end Circuit
