/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorMuBraid

/-!
# The tensorμ interchange associativity

The mixed associativity of the middle-four interchange: shuffling
first and regrouping equals regrouping blockwise and shuffling
twice.  This is the symmetric-category companion of Mathlib's
`tensor_associativity`, with the shuffle on the other side; one
adjacent symmetry cancellation dissolves the doubled crossing.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {D : Type u}

/-- Mixed associativity of the interchange: shuffling the first two
pairs and regrouping against `Z₁ ⊗ Z₂` agrees with regrouping
blockwise and shuffling twice.  The two block braidings on the right
decompose into four elementary crossings, of which the adjacent pair
`β_ X₂ Z₁ ≫ β_ Z₁ X₂` cancels by the symmetry axiom; one exchange of
the disjoint surviving crossings then matches the left-hand side. -/
@[reassoc]
theorem tensorMu_assoc_swap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X₁ Y₁ X₂ Y₂ Z₁ Z₂ : D) :
    (tensorμ X₁ Y₁ X₂ Y₂ ▷ (Z₁ ⊗ Z₂)) ≫
      (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
      ((X₁ ⊗ X₂) ◁ tensorμ Y₁ Y₂ Z₁ Z₂) =
    tensorμ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) Z₁ Z₂ ≫
      ((α_ X₁ Y₁ Z₁).hom ⊗ₘ (α_ X₂ Y₂ Z₂).hom) ≫
      tensorμ X₁ (Y₁ ⊗ Z₁) X₂ (Y₂ ⊗ Z₂) := by
  symm
  calc
    tensorμ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) Z₁ Z₂ ≫
        ((α_ X₁ Y₁ Z₁).hom ⊗ₘ (α_ X₂ Y₂ Z₂).hom) ≫
        tensorμ X₁ (Y₁ ⊗ Z₁) X₂ (Y₂ ⊗ Z₂)
        = 𝟙 _ ⊗≫ X₁ ◁ Y₁ ◁ X₂ ◁ (β_ Y₂ Z₁).hom ▷ Z₂ ⊗≫
            X₁ ◁ Y₁ ◁ ((β_ X₂ Z₁).hom ≫ (β_ Z₁ X₂).hom) ▷ (Y₂ ⊗ Z₂) ⊗≫
            X₁ ◁ (β_ Y₁ X₂).hom ▷ ((Z₁ ⊗ Y₂) ⊗ Z₂) ⊗≫ 𝟙 _ := by
          dsimp only [tensorμ]
          rw [BraidedCategory.braiding_tensor_left_hom X₂ Y₂ Z₁,
            BraidedCategory.braiding_tensor_left_hom Y₁ Z₁ X₂]
          monoidal
    _ = 𝟙 _ ⊗≫ X₁ ◁ ((Y₁ ⊗ X₂) ◁ ((β_ Y₂ Z₁).hom ▷ Z₂) ≫
            (β_ Y₁ X₂).hom ▷ ((Z₁ ⊗ Y₂) ⊗ Z₂)) ⊗≫ 𝟙 _ := by
          rw [SymmetricCategory.symmetry X₂ Z₁]
          monoidal
    _ = (tensorμ X₁ Y₁ X₂ Y₂ ▷ (Z₁ ⊗ Z₂)) ≫
          (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)).hom ≫
          ((X₁ ⊗ X₂) ◁ tensorμ Y₁ Y₂ Z₁ Z₂) := by
          rw [whisker_exchange (β_ Y₁ X₂).hom ((β_ Y₂ Z₁).hom ▷ Z₂)]
          dsimp only [tensorμ]
          monoidal

/-- The inverse-associator companion of `tensorMu_assoc_swap`:
shuffling the last two pairs and regrouping against `Z₁ ⊗ Z₂` agrees
with regrouping blockwise and shuffling twice.  The two block
braidings on the right decompose into four elementary crossings, of
which the adjacent pair `β_ Z₂ Y₁ ≫ β_ Y₁ Z₂` cancels by the symmetry
axiom; one exchange of the disjoint surviving crossings then matches
the left-hand side. -/
@[reassoc]
theorem tensorMu_assoc_swap_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (Z₁ Z₂ X₁ Y₁ X₂ Y₂ : D) :
    ((Z₁ ⊗ Z₂) ◁ tensorμ X₁ Y₁ X₂ Y₂) ≫
      (α_ (Z₁ ⊗ Z₂) (X₁ ⊗ X₂) (Y₁ ⊗ Y₂)).inv ≫
      (tensorμ Z₁ Z₂ X₁ X₂ ▷ (Y₁ ⊗ Y₂)) =
    tensorμ Z₁ Z₂ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) ≫
      ((α_ Z₁ X₁ Y₁).inv ⊗ₘ (α_ Z₂ X₂ Y₂).inv) ≫
      tensorμ (Z₁ ⊗ X₁) Y₁ (Z₂ ⊗ X₂) Y₂ := by
  symm
  calc
    tensorμ Z₁ Z₂ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) ≫
        ((α_ Z₁ X₁ Y₁).inv ⊗ₘ (α_ Z₂ X₂ Y₂).inv) ≫
        tensorμ (Z₁ ⊗ X₁) Y₁ (Z₂ ⊗ X₂) Y₂
        = 𝟙 _ ⊗≫ Z₁ ◁ (β_ Z₂ X₁).hom ▷ ((Y₁ ⊗ X₂) ⊗ Y₂) ⊗≫
            Z₁ ◁ X₁ ◁ ((β_ Z₂ Y₁).hom ≫ (β_ Y₁ Z₂).hom) ▷ (X₂ ⊗ Y₂) ⊗≫
            Z₁ ◁ X₁ ◁ Z₂ ◁ (β_ Y₁ X₂).hom ▷ Y₂ ⊗≫ 𝟙 _ := by
          dsimp only [tensorμ]
          rw [BraidedCategory.braiding_tensor_right_hom Z₂ X₁ Y₁,
            BraidedCategory.braiding_tensor_right_hom Y₁ Z₂ X₂]
          monoidal
    _ = 𝟙 _ ⊗≫ Z₁ ◁ ((β_ Z₂ X₁).hom ▷ ((Y₁ ⊗ X₂) ⊗ Y₂) ≫
            (X₁ ⊗ Z₂) ◁ ((β_ Y₁ X₂).hom ▷ Y₂)) ⊗≫ 𝟙 _ := by
          rw [SymmetricCategory.symmetry Z₂ Y₁]
          monoidal
    _ = ((Z₁ ⊗ Z₂) ◁ tensorμ X₁ Y₁ X₂ Y₂) ≫
          (α_ (Z₁ ⊗ Z₂) (X₁ ⊗ X₂) (Y₁ ⊗ Y₂)).inv ≫
          (tensorμ Z₁ Z₂ X₁ X₂ ▷ (Y₁ ⊗ Y₂)) := by
          rw [← whisker_exchange (β_ Z₂ X₁).hom ((β_ Y₁ X₂).hom ▷ Y₂)]
          dsimp only [tensorμ]
          monoidal

end RS
