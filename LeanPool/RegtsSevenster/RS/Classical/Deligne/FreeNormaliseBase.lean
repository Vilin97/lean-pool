/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreePowInsert

/-!
# The one-letter normalisation

At arity one the collapse and the insertion are mutually inverse:
the single head is already at the front, and re-inserting it puts
it back where it was.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The one-letter normalisation is trivial.** -/
theorem freeCollapse_freeInsert_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) :
    freeCollapse A V 1 ≫ freeInsert A V 0 =
      𝟙 (tensorPow D (A ⊗ V) 1) := by
  have key : ((((λ_ (𝟙_ D)).inv ≫ (η[A] ▷ 𝟙_ D)) ▷ (A ⊗ V)) ≫
      (tensorμ A (𝟙_ D) A V ≫ (μ[A] ▷ (𝟙_ D ⊗ V)))) ≫
      ((α_ A (𝟙_ D) V).inv ≫ ((β_ A (𝟙_ D)).hom ▷ V) ≫
        (α_ (𝟙_ D) A V).hom ≫ (𝟙 (𝟙_ D) ▷ (A ⊗ V))) =
      𝟙 (𝟙_ D ⊗ (A ⊗ V)) := by
    rw [MonoidalCategory.id_whiskerRight, Category.comp_id,
      MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    rw [← MonoidalCategory.tensorHom_id η[A] (𝟙_ D),
      tensorμ_natural_left_assoc,
      ← MonoidalCategory.tensorHom_id (μ[A]) (𝟙_ D ⊗ V),
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      MonObj.one_mul, MonoidalCategory.id_whiskerRight,
      Category.comp_id]
    rw [show ((λ_ A).hom ⊗ₘ 𝟙 (𝟙_ D ⊗ V)) =
        ((λ_ A).hom ⊗ₘ (λ_ V).hom) ≫ (𝟙 A ⊗ₘ (λ_ V).inv) by
      rw [MonoidalCategory.tensorHom_comp_tensorHom,
        Category.comp_id, Iso.hom_inv_id]]
    simp only [Category.assoc]
    have hbr : (β_ A (𝟙_ D)).hom = (ρ_ A).hom ≫ (λ_ A).inv := by
      rw [← braiding_leftUnitor A, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [← tensor_left_unitality_assoc, hbr]
    monoidal
  exact key

end RS
