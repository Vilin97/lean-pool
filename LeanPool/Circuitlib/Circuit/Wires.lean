/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

import Mathlib.Data.Nat.Notation
import Mathlib.Order.Defs.PartialOrder

/-! # Wires

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- A bundle of `I` wires, each carrying a value of type `V`. -/
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

lemma Wires.get_append_left {n m : ℕ} (a : Wires V n) (b : Wires V m) (i : Fin n) :
    (a.append b).get (Fin.castAdd m i) = a.get i := by
  unfold Wires at a b
  simp only [Vector.get, Fin.val_cast, Fin.val_castAdd, Vector.getElem_toArray]
  exact Vector.getElem_append_left i.isLt

lemma Wires.get_append_right {n m : ℕ} (a : Wires V n) (b : Wires V m) (i : Fin m) :
    (a.append b).get (Fin.natAdd n i) = b.get i := by
  unfold Wires at a b
  simp only [Vector.get, Fin.val_cast, Fin.val_natAdd, Vector.getElem_toArray]
  have h := Vector.getElem_append_right (xs := a) (ys := b) (i := n + i.val) (by omega) (by omega)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

lemma Wires.get_append {n m : ℕ} (a : Wires V n) (b : Wires V m) (i : Fin (n + m)) :
    (a.append b).get i =
      if h : i.val < n then a.get ⟨i.val, h⟩ else b.get ⟨i.val - n, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Wires.get_append_left, Fin.val_castAdd, j.isLt]
  · rw [Wires.get_append_right, dif_neg (by simp : ¬ (Fin.natAdd n j).val < n)]
    exact congrArg b.get (Fin.ext (by simp))

lemma Wires.get_take {n k : ℕ} (a : Wires V n) (i : Fin (min k n)) :
    (a.take k).get i = a.get ⟨i.val, by omega⟩ := by
  unfold Wires at a
  simp only [Vector.get, Fin.val_cast, Vector.getElem_toArray, Vector.getElem_take]

lemma Wires.get_drop {n k : ℕ} (a : Wires V n) (i : Fin (n - k)) :
    (a.drop k).get i = a.get ⟨k + i.val, by omega⟩ := by
  unfold Wires at a
  simp [Vector.get]

/-! The lemmas above are stated for `Wires`. `Vector.cast`, `Vector.take`, `Vector.drop` and
`Vector.append` all report their results at type `Vector`, and `simp` matches argument types up to
reducible unfolding only, so the same facts are restated below for `Vector`-typed arguments. -/

lemma Wires.get_cast_vector {n m : ℕ} (h : n = m) (v : Vector V n) (i : Fin m) :
    (v.cast h).get i = v.get ⟨i.val, h ▸ i.isLt⟩ :=
  Wires.get_cast h v i

lemma Wires.get_append_vector {n m : ℕ} (a : Vector V n) (b : Vector V m) (i : Fin (n + m)) :
    (a.append b).get i =
      if h : i.val < n then a.get ⟨i.val, h⟩ else b.get ⟨i.val - n, by omega⟩ :=
  Wires.get_append a b i

lemma Wires.get_append_wires_vector {n m : ℕ} (a : Wires V n) (b : Vector V m) (i : Fin (n + m)) :
    (a.append b).get i =
      if h : i.val < n then a.get ⟨i.val, h⟩ else b.get ⟨i.val - n, by omega⟩ :=
  Wires.get_append a b i

lemma Wires.get_append_vector_wires {n m : ℕ} (a : Vector V n) (b : Wires V m) (i : Fin (n + m)) :
    (a.append b).get i =
      if h : i.val < n then a.get ⟨i.val, h⟩ else b.get ⟨i.val - n, by omega⟩ :=
  Wires.get_append a b i

lemma Wires.get_take_vector {n k : ℕ} (a : Vector V n) (i : Fin (min k n)) :
    (a.take k).get i = a.get ⟨i.val, by omega⟩ :=
  Wires.get_take a i

lemma Wires.get_drop_vector {n k : ℕ} (a : Vector V n) (i : Fin (n - k)) :
    (a.drop k).get i = a.get ⟨k + i.val, by omega⟩ :=
  Wires.get_drop a i

end Circuit
