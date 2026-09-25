/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorMuBraid

/-!
# The twist-shuffle coherence

The pure braid identity of the twist shuffle: routing the scalar
out of the first twisted factor, through the interchange, and
back into the middle equals associating it into the second factor
and interchanging.  Two crossings cancel by symmetry.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {D : Type u}

/-- The twist-shuffle coherence: extracting `A` from the twisted
factor `V ⊗ R`, interchanging, and reinserting it between `R` and
`S` agrees with associating `A` into `W ⊗ S` and interchanging.
The block braiding `β_ (V ⊗ R) A` contributes crossings of `A` past
`R` and past `V`; the latter cancels against `β_ A V` by symmetry,
the former is conjugated through the interchange block by
naturality of the braiding and cancels against `(β_ R A).inv`, and
the residual word is the interchange of `V ⊗ R` with
`W ⊗ (A ⊗ S)`. -/
@[reassoc]
theorem twist_shuffle_coherence
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (V R A W S : D) :
    (β_ (V ⊗ R) A).hom ▷ (W ⊗ S) ≫
      (α_ A V R).inv ▷ (W ⊗ S) ≫
      (β_ A V).hom ▷ R ▷ (W ⊗ S) ≫
      (α_ V A R).hom ▷ (W ⊗ S) ≫
      tensorμ V (A ⊗ R) W S ≫
      ((V ⊗ W) ◁ ((β_ R A).inv ▷ S)) ≫
      ((V ⊗ W) ◁ (α_ R A S).hom) =
      (α_ (V ⊗ R) A (W ⊗ S)).hom ≫
      ((V ⊗ R) ◁ (α_ A W S).inv) ≫
      ((V ⊗ R) ◁ ((β_ A W).hom ▷ S)) ≫
      ((V ⊗ R) ◁ (α_ W A S).hom) ≫
      tensorμ V R W (A ⊗ S) := by
  calc
    (β_ (V ⊗ R) A).hom ▷ (W ⊗ S) ≫
        (α_ A V R).inv ▷ (W ⊗ S) ≫
        (β_ A V).hom ▷ R ▷ (W ⊗ S) ≫
        (α_ V A R).hom ▷ (W ⊗ S) ≫
        tensorμ V (A ⊗ R) W S ≫
        ((V ⊗ W) ◁ ((β_ R A).inv ▷ S)) ≫
        ((V ⊗ W) ◁ (α_ R A S).hom)
        = 𝟙 _ ⊗≫ (V ◁ (β_ R A).hom) ▷ (W ⊗ S) ⊗≫
            (((β_ V A).hom ≫ (β_ A V).hom) ▷ R) ▷ (W ⊗ S) ⊗≫
            V ◁ ((β_ (A ⊗ R) W).hom ▷ S) ⊗≫
            (V ⊗ W) ◁ ((β_ R A).inv ▷ S) ⊗≫ 𝟙 _ := by
          dsimp only [tensorμ]
          rw [BraidedCategory.braiding_tensor_left_hom V R A]
          monoidal
    _ = 𝟙 _ ⊗≫
            V ◁ (((β_ R A).hom ▷ W ≫ (β_ (A ⊗ R) W).hom) ▷ S) ⊗≫
            (V ⊗ W) ◁ ((β_ R A).inv ▷ S) ⊗≫ 𝟙 _ := by
          rw [SymmetricCategory.symmetry V A]
          monoidal
    _ = 𝟙 _ ⊗≫ V ◁ ((β_ (R ⊗ A) W).hom ▷ S) ⊗≫
            (V ⊗ W) ◁ (((β_ R A).hom ≫ (β_ A R).hom) ▷ S) ⊗≫
            𝟙 _ := by
          rw [← SymmetricCategory.braiding_swap_eq_inv_braiding R A,
            BraidedCategory.braiding_naturality_left (β_ R A).hom W]
          monoidal
    _ = 𝟙 _ ⊗≫ V ◁ ((β_ (R ⊗ A) W).hom ▷ S) ⊗≫ 𝟙 _ := by
          rw [SymmetricCategory.symmetry R A]
          monoidal
    _ = (α_ (V ⊗ R) A (W ⊗ S)).hom ≫
          ((V ⊗ R) ◁ (α_ A W S).inv) ≫
          ((V ⊗ R) ◁ ((β_ A W).hom ▷ S)) ≫
          ((V ⊗ R) ◁ (α_ W A S).hom) ≫
          tensorμ V R W (A ⊗ S) := by
          dsimp only [tensorμ]
          rw [BraidedCategory.braiding_tensor_left_hom R A W]
          monoidal

/-- The twist-act coherence: extracting `A` from the twisted factor
`V ⊗ R` before the interchange agrees with interchanging first and
then extracting `A` from the product `V ⊗ W`.  Both words consist
of the crossings of `A` past `V`, of `R` past `W`, and of `A` past
`W`, each occurring exactly once; the two sides differ only in the
order of the first two, which act on disjoint factors and are
exchanged as whiskerings. -/
@[reassoc]
theorem twist_act_coherence
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (A V R W S : D) :
    (α_ A (V ⊗ R) (W ⊗ S)).inv ≫
      (α_ A V R).inv ▷ (W ⊗ S) ≫
      ((β_ A V).hom ▷ R) ▷ (W ⊗ S) ≫
      (α_ V A R).hom ▷ (W ⊗ S) ≫
      tensorμ V (A ⊗ R) W S =
      A ◁ tensorμ V R W S ≫
      (α_ A (V ⊗ W) (R ⊗ S)).inv ≫
      ((β_ A (V ⊗ W)).hom ▷ (R ⊗ S)) ≫
      (α_ (V ⊗ W) A (R ⊗ S)).hom ≫
      ((V ⊗ W) ◁ (α_ A R S).inv) := by
  calc
    (α_ A (V ⊗ R) (W ⊗ S)).inv ≫
        (α_ A V R).inv ▷ (W ⊗ S) ≫
        ((β_ A V).hom ▷ R) ▷ (W ⊗ S) ≫
        (α_ V A R).hom ▷ (W ⊗ S) ≫
        tensorμ V (A ⊗ R) W S
        = 𝟙 _ ⊗≫
            ((β_ A V).hom ▷ ((R ⊗ W) ⊗ S) ≫
              (V ⊗ A) ◁ ((β_ R W).hom ▷ S)) ⊗≫
            V ◁ (((β_ A W).hom ▷ R) ▷ S) ⊗≫ 𝟙 _ := by
          dsimp only [tensorμ]
          rw [BraidedCategory.braiding_tensor_left_hom A R W]
          monoidal
    _ = 𝟙 _ ⊗≫
            ((A ⊗ V) ◁ ((β_ R W).hom ▷ S) ≫
              (β_ A V).hom ▷ ((W ⊗ R) ⊗ S)) ⊗≫
            V ◁ (((β_ A W).hom ▷ R) ▷ S) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
    _ = A ◁ tensorμ V R W S ≫
          (α_ A (V ⊗ W) (R ⊗ S)).inv ≫
          ((β_ A (V ⊗ W)).hom ▷ (R ⊗ S)) ≫
          (α_ (V ⊗ W) A (R ⊗ S)).hom ≫
          ((V ⊗ W) ◁ (α_ A R S).inv) := by
          dsimp only [tensorμ]
          rw [BraidedCategory.braiding_tensor_right_hom A V W]
          monoidal

end RS
