/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.WhiskerAdditive
public import LeanPool.RegtsSevenster.RS.Definitions

/-!
# A vanishing tensor power forces a vanishing object

Deligne's 1.17 (Catégories tensorielles, 2002): in a symmetric
monoidal preadditive category, an object `X` with a right dual
whose `n`-th tensor power vanishes for some `n ≠ 0` vanishes
itself.

The descent step is `isZero_tensorPow_pred`: a vanishing
`(n + 2)`-nd power forces a vanishing `(n + 1)`-st power.  Writing
the `(n + 1)`-st power as `P ⊗ X`, the triangle identity for the
exact pairing `(X, Xᘁ)`, whiskered on the left by `P`, factors the
identity of `P ⊗ X` through `P ⊗ ((X ⊗ Xᘁ) ⊗ X)`; associators and
one braiding identify that object with the `(n + 2)`-nd power
tensored with `Xᘁ`, which is zero because tensoring preserves zero
objects over a preadditive monoidal structure.  Downward induction
and the left unitor then give the theorem.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {A : Type u}

/-- The descent step at a general left factor: if `(P ⊗ X) ⊗ X`
vanishes, so does `P ⊗ X`.  The identity of `P ⊗ X` factors
through `P ⊗ ((X ⊗ Xᘁ) ⊗ X)` by the triangle identity for the
pairing `(X, Xᘁ)` whiskered by `P`, and that object is zero,
being isomorphic to `((P ⊗ X) ⊗ X) ⊗ Xᘁ` by associators and the
braiding `β_ Xᘁ X`. -/
theorem isZero_tensorObj_of_isZero_tensorObj
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [MonoidalPreadditive A]
    (X : A)
    [HasRightDual X] {P : A}
    (h : Limits.IsZero ((P ⊗ X) ⊗ X)) :
    Limits.IsZero (P ⊗ X) := by
  have hmid : Limits.IsZero (P ⊗ ((X ⊗ Xᘁ) ⊗ X)) :=
    (isZero_whiskerRight h (Xᘁ)).of_iso
      (whiskerLeftIso P (α_ X (Xᘁ) X) ≪≫
        (α_ P X ((Xᘁ) ⊗ X)).symm ≪≫
        whiskerLeftIso (P ⊗ X) (β_ (Xᘁ) X) ≪≫
        (α_ (P ⊗ X) X (Xᘁ)).symm)
  rw [Limits.IsZero.iff_id_eq_zero]
  have key : (P ◁ ((λ_ X).inv ≫ η_ X (Xᘁ) ▷ X)) ≫
      (P ◁ ((α_ X (Xᘁ) X).hom ≫ X ◁ ε_ X (Xᘁ) ≫ (ρ_ X).hom)) =
      𝟙 (P ⊗ X) := by
    rw [← whiskerLeft_comp]
    simp
  rw [← key,
    hmid.eq_zero_of_src
      (P ◁ ((α_ X (Xᘁ) X).hom ≫ X ◁ ε_ X (Xᘁ) ≫ (ρ_ X).hom)),
    comp_zero]

/-- Deligne 1.17, descent: a vanishing `(n + 2)`-nd tensor power
forces a vanishing `(n + 1)`-st tensor power. -/
theorem isZero_tensorPow_pred
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [MonoidalPreadditive A]
    (X : A) [HasRightDual X] {n : ℕ}
    (h : Limits.IsZero (tensorPow A X (n + 2))) :
    Limits.IsZero (tensorPow A X (n + 1)) :=
  isZero_tensorObj_of_isZero_tensorObj (P := tensorPow A X n) X h

/-- **Deligne 1.17** (Catégories tensorielles): a vanishing tensor
power forces a vanishing object — if `X ^ ⊗ n = 0` for some
`n ≠ 0`, then `X = 0`. -/
theorem isZero_of_isZero_tensorPow
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [MonoidalPreadditive A]
    (X : A) [HasRightDual X] {n : ℕ}
    (hn : n ≠ 0) (h : Limits.IsZero (tensorPow A X n)) :
    Limits.IsZero X := by
  induction n with
  | zero => exact absurd rfl hn
  | succ m ih =>
    cases m with
    | zero => exact h.of_iso (λ_ X).symm
    | succ k =>
      exact ih k.succ_ne_zero (isZero_tensorPow_pred X h)

end RS
