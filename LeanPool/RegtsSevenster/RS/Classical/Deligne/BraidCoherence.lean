/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorMuBraid

/-!
# A braid-coherence identity for the interchange prefix

Both sides of the identity proved here are words in associators and
braidings realising the same permutation of the four strands
`(P, q₁, R, q₂) ↦ (q₁, q₂, P, R)`: the left-hand side crosses `R`
past the second `Q`-strand and then `P` past both `Q`-strands, while
the right-hand side crosses the first `Q`-strand past `R` (inside
`tensorμ`) and then the block `P ⊗ R` past `Q ⊗ Q`.  The surplus
adjacent pair of crossings `β_ Q R ≫ β_ R Q` cancels by the symmetry
axiom, and the residual pure-associator words close by coherence.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {D : Type u}

/-- Pure braid coherence for the interchange prefix: braiding the
third strand past the fourth, reassociating, and braiding `P` past
the two `Q`-strands as a block agrees with interchanging via
`tensorμ`, braiding the block `P ⊗ R` past `Q ⊗ Q`, and
reassociating. -/
@[reassoc]
theorem braid_prefix_coherence
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (P Q R : D) :
    ((P ⊗ Q) ◁ (β_ R Q).hom) ≫
      (α_ (P ⊗ Q) Q R).inv ≫
      ((α_ P Q Q).hom ▷ R) ≫
      ((β_ P (Q ⊗ Q)).hom ▷ R) =
      tensorμ P Q R Q ≫
        (β_ (P ⊗ R) (Q ⊗ Q)).hom ≫
        (α_ (Q ⊗ Q) P R).inv := by
  symm
  calc
    tensorμ P Q R Q ≫ (β_ (P ⊗ R) (Q ⊗ Q)).hom ≫
        (α_ (Q ⊗ Q) P R).inv
        = 𝟙 _ ⊗≫ P ◁ (((β_ Q R).hom ≫ (β_ R Q).hom) ▷ Q) ⊗≫
            P ◁ Q ◁ (β_ R Q).hom ⊗≫
            (β_ P (Q ⊗ Q)).hom ▷ R ⊗≫ 𝟙 _ := by
          dsimp only [tensorμ]
          rw [BraidedCategory.braiding_tensor_left_hom P R (Q ⊗ Q),
            BraidedCategory.braiding_tensor_right_hom R Q Q]
          monoidal
    _ = 𝟙 _ ⊗≫ (P ⊗ Q) ◁ (β_ R Q).hom ⊗≫
            (β_ P (Q ⊗ Q)).hom ▷ R ⊗≫ 𝟙 _ := by
          rw [SymmetricCategory.symmetry Q R]
          monoidal
    _ = ((P ⊗ Q) ◁ (β_ R Q).hom) ≫ (α_ (P ⊗ Q) Q R).inv ≫
          ((α_ P Q Q).hom ▷ R) ≫ ((β_ P (Q ⊗ Q)).hom ▷ R) := by
          monoidal

end RS
