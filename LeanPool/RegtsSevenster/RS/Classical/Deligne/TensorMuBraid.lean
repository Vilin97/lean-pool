/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# The interchange `tensorμ` intertwines the braidings

In a symmetric monoidal category the interchange morphism
`tensorμ a b c d : (a ⊗ b) ⊗ (c ⊗ d) ⟶ (a ⊗ c) ⊗ (b ⊗ d)` makes the
tensor product a braided functor: braiding the two tensor pairs and
then interchanging agrees with interchanging and then braiding
slotwise.  Mathlib records only the diagonal special case
`SymmetricCategory.tensorμ_braid_swap`; this file proves the general
four-object statement.

The proof decomposes the block braiding `β_ (a ⊗ b) (c ⊗ d)` into the
four elementary crossings `β_ b c`, `β_ b d`, `β_ a c`, `β_ a d` via
the hexagon identities; the crossing `β_ d a` supplied by
`tensorμ c d a b` then cancels `β_ a d` by the symmetry axiom, and one
exchange of the disjoint crossings `β_ a c` and `β_ b d` produces the
right-hand side.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {D : Type u}

/-- In a symmetric category the interchange `tensorμ` makes the tensor
product a braided functor: braiding the tensor pairs and then
interchanging equals interchanging and then braiding slotwise. -/
@[reassoc]
theorem tensorμ_braiding
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (a b c d : D) :
    (β_ (a ⊗ b) (c ⊗ d)).hom ≫ tensorμ c d a b =
      tensorμ a b c d ≫ ((β_ a c).hom ⊗ₘ (β_ b d).hom) := by
  calc
    (β_ (a ⊗ b) (c ⊗ d)).hom ≫ tensorμ c d a b
        = 𝟙 _ ⊗≫ a ◁ (β_ b c).hom ▷ d ⊗≫
            ((a ⊗ c) ◁ (β_ b d).hom ≫ (β_ a c).hom ▷ (d ⊗ b)) ⊗≫
            c ◁ ((β_ a d).hom ≫ (β_ d a).hom) ▷ b ⊗≫ 𝟙 _ := by
          dsimp only [tensorμ]
          rw [BraidedCategory.braiding_tensor_left_hom a b (c ⊗ d),
            BraidedCategory.braiding_tensor_right_hom b c d,
            BraidedCategory.braiding_tensor_right_hom a c d]
          monoidal
    _ = 𝟙 _ ⊗≫ a ◁ (β_ b c).hom ▷ d ⊗≫
            ((β_ a c).hom ▷ (b ⊗ d) ≫ (c ⊗ a) ◁ (β_ b d).hom) ⊗≫
            𝟙 _ := by
          rw [SymmetricCategory.symmetry,
            whisker_exchange (β_ a c).hom (β_ b d).hom]
          monoidal
    _ = tensorμ a b c d ≫ ((β_ a c).hom ⊗ₘ (β_ b d).hom) := by
          dsimp only [tensorμ]
          rw [tensorHom_def]
          monoidal

/-- Slide an evaluation cap through a crossing: braiding `P` across
`Q` and then capping `P` against `X` equals braiding `Q` across `X`
and capping on the far side.  Uses the hexagon, naturality of the
braiding against the cap, and the symmetry axiom. -/
private lemma braiding_evaluation_slide
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (P Q X : D) [ExactPairing X P] :
    (β_ P Q).hom ▷ X ⊗≫ Q ◁ ε_ X P ⊗≫ 𝟙 Q =
      𝟙 ((P ⊗ Q) ⊗ X) ⊗≫ P ◁ (β_ Q X).hom ⊗≫ ε_ X P ▷ Q ⊗≫ 𝟙 Q := by
  calc
    (β_ P Q).hom ▷ X ⊗≫ Q ◁ ε_ X P ⊗≫ 𝟙 Q
        = 𝟙 _ ⊗≫ P ◁ ((β_ Q X).hom ≫ (β_ X Q).hom) ⊗≫
            (β_ P Q).hom ▷ X ⊗≫ Q ◁ ε_ X P ⊗≫ 𝟙 Q := by
          rw [SymmetricCategory.symmetry Q X]
          monoidal
    _ = 𝟙 _ ⊗≫ P ◁ (β_ Q X).hom ⊗≫
            ((β_ (P ⊗ X) Q).hom ≫ Q ◁ ε_ X P) ⊗≫ 𝟙 Q := by
          rw [BraidedCategory.braiding_tensor_left_hom P X Q]
          monoidal
    _ = 𝟙 _ ⊗≫ P ◁ (β_ Q X).hom ⊗≫
            (ε_ X P ▷ Q ≫ (β_ (𝟙_ D) Q).hom) ⊗≫ 𝟙 Q := by
          rw [BraidedCategory.braiding_naturality_left (ε_ X P) Q]
    _ = 𝟙 ((P ⊗ Q) ⊗ X) ⊗≫ P ◁ (β_ Q X).hom ⊗≫ ε_ X P ▷ Q ⊗≫ 𝟙 Q := by
          rw [braiding_tensorUnit_left]
          monoidal

/-- The tensor evaluation of `ExactPairing.tensor` is compatible with
the braidings: crossing the two dual pairs converts the arc nesting of
the double evaluation, inner `(Q, Y)`/outer `(P, X)` against inner
`(P, X)`/outer `(Q, Y)`. -/
@[reassoc]
theorem tensor_evaluation_braiding
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (X Y P Q : D)
    [ExactPairing X P] [ExactPairing Y Q] :
    ε_ (Y ⊗ X) (P ⊗ Q) =
      ((β_ P Q).hom ▷ (Y ⊗ X)) ≫
        ((Q ⊗ P) ◁ (β_ Y X).hom) ≫ ε_ (X ⊗ Y) (Q ⊗ P) := by
  symm
  calc
    ((β_ P Q).hom ▷ (Y ⊗ X)) ≫
        ((Q ⊗ P) ◁ (β_ Y X).hom) ≫ ε_ (X ⊗ Y) (Q ⊗ P)
        = 𝟙 _ ⊗≫ (P ⊗ Q) ◁ (β_ Y X).hom ⊗≫
            ((β_ P Q).hom ▷ X ⊗≫ Q ◁ ε_ X P ⊗≫ 𝟙 Q) ▷ Y ⊗≫ ε_ Y Q := by
          rw [ExactPairing.tensor_evaluation, ← whisker_exchange_assoc]
          monoidal
    _ = 𝟙 _ ⊗≫ P ◁ (β_ (Q ⊗ Y) X).hom ⊗≫
            ε_ X P ▷ (Q ⊗ Y) ⊗≫ ε_ Y Q := by
          rw [braiding_evaluation_slide,
            BraidedCategory.braiding_tensor_left_hom Q Y X]
          monoidal
    _ = 𝟙 _ ⊗≫ P ◁ (β_ (Q ⊗ Y) X).hom ⊗≫
            ((P ⊗ X) ◁ ε_ Y Q ≫ ε_ X P ▷ 𝟙_ D) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange (ε_ X P) (ε_ Y Q)]
          monoidal
    _ = 𝟙 _ ⊗≫ P ◁ (ε_ Y Q ▷ X ≫ (β_ (𝟙_ D) X).hom) ⊗≫
            ε_ X P ⊗≫ 𝟙 _ := by
          rw [BraidedCategory.braiding_naturality_left (ε_ Y Q) X]
          monoidal
    _ = ε_ (Y ⊗ X) (P ⊗ Q) := by
          rw [ExactPairing.tensor_evaluation, braiding_tensorUnit_left]
          monoidal

end RS
