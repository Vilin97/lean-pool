/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreePow

/-!
# A section of the free collapse

The free collapse `freeCollapse A V n` of `Deligne/FreePow.lean`
multiplies the heads of a word of free letters `A ⊗ V` to the front
of the word.  From arity one upwards it is a split epimorphism: the
section carries the head of `A ⊗ V ^ ⊗ n` into the topmost letter
and fills every other letter with the unit of `A`.

The bookkeeping is carried by two auxiliary constructions.  The
*unit word* is the empty product of units in a monoid power; folding
it returns the unit, by the left unit law alone.  The *unit power*
inserts the unit into every letter of an ambient power; shuffling it
separates the unit word from the ambient word.  With those two in
hand the composite of the insertion and the collapse is a
symmetric-monoidal identity: the braiding introduced by the
insertion cancels the braiding hidden inside the middle-four
interchange, and the folded unit word contributes only a left
unitor.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Unit words and unit-filled powers -/

/-- The unit word: the empty product of units in an ambient
power. -/
noncomputable def unitWord [Category.{v} D] [MonoidalCategory D]
    (A : D) [MonObj A] :
    (n : ℕ) → (𝟙_ D ⟶ tensorPow D A n)
  | 0 => 𝟙 (𝟙_ D)
  | n + 1 => (ρ_ (𝟙_ D)).inv ≫ (unitWord A n ⊗ₘ η[A])

@[simp] theorem unitWord_zero [Category.{v} D] [MonoidalCategory D]
    (A : D) [MonObj A] :
    unitWord A 0 = 𝟙 (𝟙_ D) := rfl

/-- Insert the monoid unit into every letter of an ambient
power. -/
noncomputable def freeUnitPow [Category.{v} D] [MonoidalCategory D]
    (A : D) [MonObj A] (V : D) :
    (n : ℕ) → (tensorPow D V n ⟶ tensorPow D (A ⊗ V) n)
  | 0 => 𝟙 (𝟙_ D)
  | n + 1 => freeUnitPow A V n ⊗ₘ ((λ_ V).inv ≫ (η[A] ▷ V))

@[simp] theorem unitPow_zero [Category.{v} D] [MonoidalCategory D]
    (A : D) [MonObj A] (V : D) :
    freeUnitPow A V 0 = 𝟙 (𝟙_ D) := rfl

section Fold

/-- Folding a word of units gives the unit. -/
theorem unitWord_muFold
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A : D) [MonObj A] (n : ℕ) :
    unitWord A n ≫ muFold A n = η[A] := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
      change ((ρ_ (𝟙_ D)).inv ≫ (unitWord A n ⊗ₘ η[A])) ≫
          ((muFold A n ▷ A) ≫ μ[A]) = η[A]
      rw [Category.assoc, ← Category.assoc (unitWord A n ⊗ₘ η[A]),
        ← MonoidalCategory.tensorHom_id (muFold A n) A,
        tensorHom_comp_tensorHom, ih, Category.comp_id,
        MonoidalCategory.tensorHom_def', Category.assoc,
        MonObj.one_mul, ← unitors_inv_equal,
        ← leftUnitor_inv_naturality_assoc, Iso.inv_hom_id,
        Category.comp_id]

end Fold

/-! ## The unit power through the shuffle -/

section Shuffle

/-- Two unit-inserted legs are merged by the interchange into a
single unit pair in front of the ambient pair. -/
private theorem unitPair_tensorμ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    {X₁ Y₁ : D} (g : 𝟙_ D ⟶ X₁)
    (h : 𝟙_ D ⟶ Y₁) (X₂ Y₂ : D) :
    (((λ_ X₂).inv ≫ (g ▷ X₂)) ⊗ₘ ((λ_ Y₂).inv ≫ (h ▷ Y₂))) ≫
        tensorμ X₁ X₂ Y₁ Y₂ =
      (λ_ (X₂ ⊗ Y₂)).inv ≫
        (((ρ_ (𝟙_ D)).inv ≫ (g ⊗ₘ h)) ▷ (X₂ ⊗ Y₂)) := by
  have hkey : ((λ_ X₂).inv ⊗ₘ (λ_ Y₂).inv) ≫
      tensorμ (𝟙_ D) X₂ (𝟙_ D) Y₂ =
        (λ_ (X₂ ⊗ Y₂)).inv ≫ ((λ_ (𝟙_ D)).inv ▷ (X₂ ⊗ Y₂)) := by
    rw [tensorμ, braiding_tensorUnit_right]
    monoidal
  rw [← tensorHom_comp_tensorHom, Category.assoc,
    ← MonoidalCategory.tensorHom_id g X₂,
    ← MonoidalCategory.tensorHom_id h Y₂,
    tensorμ_natural g (𝟙 X₂) h (𝟙 Y₂), ← Category.assoc, hkey,
    id_tensorHom_id, MonoidalCategory.tensorHom_id,
    MonoidalCategory.comp_whiskerRight, unitors_inv_equal,
    Category.assoc]

/-- Shuffling a word of unit-filled letters separates the unit
word from the ambient word. -/
theorem unitPow_plainShuffle
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (A : D) [MonObj A] (V : D) (n : ℕ) :
    freeUnitPow A V n ≫ (plainShuffle A V n).hom =
      (λ_ (tensorPow D V n)).inv ≫
        (unitWord A n ▷ tensorPow D V n) := by
  induction n with
  | zero =>
      change 𝟙 (𝟙_ D) ≫ (λ_ (𝟙_ D)).inv =
        (λ_ (𝟙_ D)).inv ≫ (𝟙 (𝟙_ D) ▷ 𝟙_ D)
      rw [Category.id_comp, MonoidalCategory.id_whiskerRight,
        Category.comp_id]
  | succ n ih =>
      change (freeUnitPow A V n ⊗ₘ ((λ_ V).inv ≫ (η[A] ▷ V))) ≫
          (((plainShuffle A V n).hom ▷ (A ⊗ V)) ≫
            tensorμ (tensorPow D A n) (tensorPow D V n) A V) =
        (λ_ (tensorPow D V n ⊗ V)).inv ≫
          (((ρ_ (𝟙_ D)).inv ≫ (unitWord A n ⊗ₘ η[A])) ▷
            (tensorPow D V n ⊗ V))
      rw [← Category.assoc,
        ← MonoidalCategory.tensorHom_id (plainShuffle A V n).hom
          (A ⊗ V), tensorHom_comp_tensorHom, ih, Category.comp_id]
      exact unitPair_tensorμ (unitWord A n) η[A]
        (tensorPow D V n) V

end Shuffle

/-! ## The free insertion -/

section Insert

/-- With the unit in the first slot, the interchange is a single
braiding, conjugated by associators. -/
private theorem unitTensorμ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (P A V : D) :
    ((λ_ P).inv ▷ (A ⊗ V)) ≫ tensorμ (𝟙_ D) P A V ≫
        ((λ_ A).hom ▷ (P ⊗ V)) =
      (α_ P A V).inv ≫ ((β_ P A).hom ▷ V) ≫ (α_ A P V).hom := by
  have h₁ : tensorμ (𝟙_ D) P A V =
      (α_ (𝟙_ D) P (A ⊗ V)).hom ≫
        (𝟙_ D ◁ ((α_ P A V).inv ≫ ((β_ P A).hom ▷ V) ≫
          (α_ A P V).hom)) ≫ (α_ (𝟙_ D) A (P ⊗ V)).inv := by
    rw [tensorμ]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  have h₂ : ((λ_ P).inv ▷ (A ⊗ V)) ≫ (α_ (𝟙_ D) P (A ⊗ V)).hom =
      (λ_ (P ⊗ (A ⊗ V))).inv := by monoidal
  have h₃ : (α_ (𝟙_ D) A (P ⊗ V)).inv ≫ ((λ_ A).hom ▷ (P ⊗ V)) =
      (λ_ (A ⊗ (P ⊗ V))).hom := by monoidal
  rw [h₁]
  simp only [Category.assoc]
  rw [← Category.assoc, h₂, h₃, ← Category.assoc,
    ← leftUnitor_inv_naturality, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **The free insertion**: carry the head into the top letter of
the word and fill every other letter with the unit. -/
noncomputable def freeInsert
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (A : D) [MonObj A] (V : D) (n : ℕ) :
    A ⊗ tensorPow D V (n + 1) ⟶ tensorPow D (A ⊗ V) (n + 1) :=
  (α_ A (tensorPow D V n) V).inv ≫
    ((β_ A (tensorPow D V n)).hom ▷ V) ≫
    (α_ (tensorPow D V n) A V).hom ≫
    (freeUnitPow A V n ▷ (A ⊗ V))

/-- **The free insertion is a section of the free collapse.** -/
theorem freeInsert_freeCollapse
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (A : D) [MonObj A] [IsCommMonObj A]
    (V : D) (n : ℕ) :
    freeInsert A V n ≫ freeCollapse A V (n + 1) =
      𝟙 (A ⊗ tensorPow D V (n + 1)) := by
  have hA : (unitWord A n ▷ A) ≫ ((muFold A n ▷ A) ≫ μ[A]) =
      (λ_ A).hom := by
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
      unitWord_muFold, MonObj.one_mul]
  have hcol : freeCollapse A V (n + 1) =
      ((plainShuffle A V n).hom ▷ (A ⊗ V)) ≫
        tensorμ (tensorPow D A n) (tensorPow D V n) A V ≫
          (((muFold A n ▷ A) ≫ μ[A]) ▷ (tensorPow D V n ⊗ V)) :=
    (freeCollapse_shuffle A V (n + 1)).trans
      ((eq_whisker (plainShuffle_succ_hom A V n) _).trans
        (Category.assoc _ _ _))
  have hhead : ((unitWord A n ▷ tensorPow D V n) ▷ (A ⊗ V)) ≫
      tensorμ (tensorPow D A n) (tensorPow D V n) A V ≫
        (((muFold A n ▷ A) ≫ μ[A]) ▷ (tensorPow D V n ⊗ V)) =
      tensorμ (𝟙_ D) (tensorPow D V n) A V ≫
        ((λ_ A).hom ▷ (tensorPow D V n ⊗ V)) := by
    rw [← MonoidalCategory.tensorHom_id (unitWord A n)
        (tensorPow D V n), tensorμ_natural_left_assoc,
      MonoidalCategory.id_whiskerRight,
      MonoidalCategory.tensorHom_id,
      ← MonoidalCategory.comp_whiskerRight, hA]
  rw [hcol]
  change ((α_ A (tensorPow D V n) V).inv ≫
      ((β_ A (tensorPow D V n)).hom ▷ V) ≫
      (α_ (tensorPow D V n) A V).hom ≫
      (freeUnitPow A V n ▷ (A ⊗ V))) ≫
      (((plainShuffle A V n).hom ▷ (A ⊗ V)) ≫
        tensorμ (tensorPow D A n) (tensorPow D V n) A V ≫
          (((muFold A n ▷ A) ≫ μ[A]) ▷ (tensorPow D V n ⊗ V))) =
    𝟙 (A ⊗ (tensorPow D V n ⊗ V))
  simp only [Category.assoc]
  rw [← Category.assoc (freeUnitPow A V n ▷ (A ⊗ V)),
    ← MonoidalCategory.comp_whiskerRight, unitPow_plainShuffle,
    MonoidalCategory.comp_whiskerRight, Category.assoc, hhead,
    unitTensorμ, Iso.hom_inv_id_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    SymmetricCategory.symmetry, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id]

end Insert

end RS
