/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourExtendSwap
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BraidWord

/-!
# The colour-side braiding word

The word of signed adjacent swaps on the colouring model, with
its evaluation: acting on a coordinate function reindexes the
colouring along the word's permutation and multiplies by the
word's Koszul sign, computed stepwise along the colouring's own
trajectory.
-/

namespace RS

open CategoryTheory

variable {k ℓ : ℕ}

/-- The colour-side braiding word. -/
noncomputable def colourSwapWord (k ℓ : ℕ) {n : ℕ} :
    List (Fin n) →
      (colourPower k ℓ (n + 1) ⟶ colourPower k ℓ (n + 1))
  | [] => 𝟙 _
  | i :: w => colourSwapWord k ℓ w ≫
      colourSwap k ℓ (n + 1) i.val (by omega)

/-- The Koszul sign of a word along a colouring's trajectory:
each step contributes the adjacent sign at the colouring reached
so far. -/
def wordSign {n : ℕ} :
    List (Fin n) → MixedColouring k ℓ (n + 1) → ℂ
  | [], _ => 1
  | i :: w, c =>
      adjSign c ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ *
        wordSign w (c ∘ _root_.Equiv.swap
          (⟨i.val, by omega⟩ : Fin (n + 1))
          ⟨i.val + 1, by omega⟩)

/-- The permutation of a word of adjacent swaps. -/
def wordPerm {n : ℕ} :
    List (Fin n) → _root_.Equiv.Perm (Fin (n + 1))
  | [] => 1
  | i :: w => _root_.Equiv.swap
      (⟨i.val, by omega⟩ : Fin (n + 1))
      ⟨i.val + 1, by omega⟩ * (wordPerm w)

/-- **The word evaluation**: the colour word acts on even
coordinate functions by the word sign and the word reindex. -/
theorem colourSwapWord_evenMap {n : ℕ} (w : List (Fin n))
    (F : (colourPower k ℓ (n + 1)).even)
    (c : {c : MixedColouring k ℓ (n + 1) // c.IsEven}) :
    ((colourSwapWord k ℓ w) : SuperVect.Hom _ _).evenMap F c =
      wordSign w c.val *
        F ⟨c.val ∘ wordPerm w, c.prop.comp _⟩ := by
  induction w generalizing c with
  | nil =>
    show F c = 1 * F ⟨c.val ∘ (1 : _root_.Equiv.Perm
      (Fin (n + 1))), c.prop.comp _⟩
    rw [one_mul]
    exact congrArg F (Subtype.ext rfl)
  | cons i w ih =>
    show ((colourSwap k ℓ (n + 1) i.val (by omega)) :
        SuperVect.Hom _ _).evenMap
        (((colourSwapWord k ℓ w) :
          SuperVect.Hom _ _).evenMap F) c = _
    show adjSign c.val ⟨i.val, by omega⟩
        ⟨i.val + 1, by omega⟩ *
      (((colourSwapWord k ℓ w) :
        SuperVect.Hom _ _).evenMap F)
        ⟨c.val ∘ _root_.Equiv.swap
          (⟨i.val, by omega⟩ : Fin (n + 1))
          ⟨i.val + 1, by omega⟩, c.prop.comp _⟩ = _
    rw [ih]
    show adjSign c.val ⟨i.val, by omega⟩
        ⟨i.val + 1, by omega⟩ *
      (wordSign w (c.val ∘ _root_.Equiv.swap
          (⟨i.val, by omega⟩ : Fin (n + 1))
          ⟨i.val + 1, by omega⟩) *
        F ⟨(c.val ∘ _root_.Equiv.swap
            (⟨i.val, by omega⟩ : Fin (n + 1))
            ⟨i.val + 1, by omega⟩) ∘ wordPerm w, _⟩) = _
    rw [← mul_assoc]
    show (adjSign c.val ⟨i.val, by omega⟩
        ⟨i.val + 1, by omega⟩ *
      wordSign w (c.val ∘ _root_.Equiv.swap
          (⟨i.val, by omega⟩ : Fin (n + 1))
          ⟨i.val + 1, by omega⟩)) *
      F ⟨(c.val ∘ _root_.Equiv.swap
          (⟨i.val, by omega⟩ : Fin (n + 1))
          ⟨i.val + 1, by omega⟩) ∘ wordPerm w, _⟩ =
      wordSign (i :: w) c.val *
        F ⟨c.val ∘ wordPerm (i :: w), c.prop.comp _⟩
    refine congrArg₂ (fun a b => a * b) rfl ?_
    exact congrArg F (Subtype.ext (funext (fun j => rfl)))

/-- The word evaluation on odd coordinate functions uses the same
word sign and permutation of positions. -/
theorem colourSwapWord_oddMap {n : ℕ} (w : List (Fin n))
    (F : (colourPower k ℓ (n + 1)).odd)
    (c : {c : MixedColouring k ℓ (n + 1) // ¬ c.IsEven}) :
    ((colourSwapWord k ℓ w) : SuperVect.Hom _ _).oddMap F c =
      wordSign w c.val *
        F ⟨c.val ∘ wordPerm w,
          MixedColouring.not_isEven_comp c.prop _⟩ := by
  induction w generalizing c with
  | nil =>
    show F c = 1 * F ⟨c.val ∘ (1 : _root_.Equiv.Perm
      (Fin (n + 1))), MixedColouring.not_isEven_comp c.prop _⟩
    rw [one_mul]
    exact congrArg F (Subtype.ext rfl)
  | cons i w ih =>
    change adjSign c.val ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ *
      ((colourSwapWord k ℓ w) : SuperVect.Hom _ _).oddMap F
        ⟨c.val ∘ _root_.Equiv.swap
          (⟨i.val, by omega⟩ : Fin (n + 1))
          ⟨i.val + 1, by omega⟩,
          MixedColouring.not_isEven_comp c.prop _⟩ = _
    rw [ih, ← mul_assoc]
    rfl

end RS
