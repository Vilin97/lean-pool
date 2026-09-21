/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Whiskering against negation, zero and binary biproducts

Mathlib records that whiskering in a preadditive monoidal category
is additive (`MonoidalPreadditive.whiskerLeft_add`,
`MonoidalPreadditive.add_whiskerRight`) and that it kills the zero
morphism, but not the consequences the development uses everywhere:
whiskering commutes with negation, a tensor product with a zero
object is a zero object, and tensoring distributes over a binary
biproduct on either side.  All hold in any preadditive monoidal
category, so they live here rather than in any of the files that
consume them.

Mathlib's `Limits.Functor.mapBiprod` at `tensorLeft B` is the same
isomorphism, but its `PreservesBinaryBiproduct` hypothesis is not an
instance for `tensorLeft`, so the distributors are built here
directly.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {C : Type u}

/-- Whiskering on the left commutes with negation. -/
@[simp]
theorem whiskerLeft_neg [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C]
    (X : C) {Y Z : C} (f : Y ⟶ Z) :
    X ◁ (-f) = -(X ◁ f) :=
  (tensorLeft X).map_neg

/-- Whiskering on the right commutes with negation. -/
@[simp]
theorem neg_whiskerRight [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C]
    {X Y : C} (f : X ⟶ Y) (Z : C) :
    (-f) ▷ Z = -(f ▷ Z) :=
  (tensorRight Z).map_neg

/-- Tensoring a zero object on the right with any object gives a
zero object. -/
theorem isZero_whiskerRight
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C]
    {X : C} (h : IsZero X) (V : C) :
    IsZero (X ⊗ V) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  rw [show 𝟙 (X ⊗ V) = 𝟙 X ▷ V from
    (MonoidalCategory.id_whiskerRight X V).symm, h,
    MonoidalPreadditive.zero_whiskerRight]

/-- Tensoring any object with a zero object on the right gives a
zero object. -/
theorem isZero_whiskerLeft [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C]
    (V : C) {Y : C} (h : IsZero Y) :
    IsZero (V ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  rw [show 𝟙 (V ⊗ Y) = V ◁ 𝟙 Y from
    (MonoidalCategory.whiskerLeft_id V Y).symm, h,
    MonoidalPreadditive.whiskerLeft_zero]

/-! ## Distributivity over a binary biproduct -/

section Distributors

/-- **Tensoring on the left distributes over a binary
biproduct.** -/
noncomputable def tensorBiprodIso
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (B X Y : C) :
    B ⊗ (X ⊞ Y) ≅ (B ⊗ X) ⊞ (B ⊗ Y) where
  hom := biprod.lift (B ◁ biprod.fst) (B ◁ biprod.snd)
  inv := biprod.desc (B ◁ biprod.inl) (B ◁ biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalPreadditive.whiskerLeft_add, biprod.total,
      MonoidalCategory.whiskerLeft_id]
  inv_hom_id := by
    ext <;> simp [← MonoidalCategory.whiskerLeft_comp]

/-- **Tensoring on the right distributes over a binary
biproduct.** -/
noncomputable def biprodTensorIso
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (X Y B : C) :
    (X ⊞ Y) ⊗ B ≅ (X ⊗ B) ⊞ (Y ⊗ B) where
  hom := biprod.lift (biprod.fst ▷ B) (biprod.snd ▷ B)
  inv := biprod.desc (biprod.inl ▷ B) (biprod.inr ▷ B)
  hom_inv_id := by
    rw [biprod.lift_desc, ← comp_whiskerRight, ← comp_whiskerRight,
      ← MonoidalPreadditive.add_whiskerRight, biprod.total,
      MonoidalCategory.id_whiskerRight]
  inv_hom_id := by
    ext <;> simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
theorem inl_tensorBiprodIso_hom
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (B X Y : C) :
    (B ◁ biprod.inl) ≫ (tensorBiprodIso B X Y).hom = biprod.inl := by
  ext <;> simp [tensorBiprodIso, ← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem inr_tensorBiprodIso_hom
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (B X Y : C) :
    (B ◁ biprod.inr) ≫ (tensorBiprodIso B X Y).hom = biprod.inr := by
  ext <;> simp [tensorBiprodIso, ← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
theorem inl_tensorBiprodIso_inv
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (B X Y : C) :
    biprod.inl ≫ (tensorBiprodIso B X Y).inv = B ◁ biprod.inl := by
  simp [tensorBiprodIso]

@[reassoc (attr := simp)]
theorem inr_tensorBiprodIso_inv
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (B X Y : C) :
    biprod.inr ≫ (tensorBiprodIso B X Y).inv = B ◁ biprod.inr := by
  simp [tensorBiprodIso]

@[reassoc (attr := simp)]
theorem inl_biprodTensorIso_hom
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (X Y B : C) :
    (biprod.inl ▷ B) ≫ (biprodTensorIso X Y B).hom = biprod.inl := by
  ext <;> simp [biprodTensorIso, ← comp_whiskerRight]

@[reassoc (attr := simp)]
theorem inr_biprodTensorIso_hom
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (X Y B : C) :
    (biprod.inr ▷ B) ≫ (biprodTensorIso X Y B).hom = biprod.inr := by
  ext <;> simp [biprodTensorIso, ← comp_whiskerRight]

@[reassoc (attr := simp)]
theorem inl_biprodTensorIso_inv
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (X Y B : C) :
    biprod.inl ≫ (biprodTensorIso X Y B).inv = biprod.inl ▷ B := by
  simp [biprodTensorIso]

@[reassoc (attr := simp)]
theorem inr_biprodTensorIso_inv
    [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [Limits.HasBinaryBiproducts C]
    (X Y B : C) :
    biprod.inr ≫ (biprodTensorIso X Y B).inv = biprod.inr ▷ B := by
  simp [biprodTensorIso]

end Distributors

end RS
