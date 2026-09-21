/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModTensor
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorMuBraid

/-!
# Coherence of the free-module shuffle

The shuffle `freeModShuffle R V W : (R ⊗ V) ⊗ (R ⊗ W) ⟶ R ⊗ (V ⊗ W)`
of `RS.freeModTensor` obeys the coherence of a monoidal structure.
The four identities recorded here are pure identities of the ambient
braided monoidal category: no coequalizer and no module theory
appears in any of them, and everything is stated in raw
`R ⊗ V` language.

* `freeModShuffle_assoc`: associativity, against the reassociation
  of the generators.
* `freeModShuffle_unit_left`: filling the first algebra slot with
  the unit leaves the left action of the free module.
* `freeModShuffle_unit_right`: filling the second algebra slot with
  the unit leaves the braided right action of the free module.
* `freeModShuffle_braiding`: the shuffle commutes with the
  braiding.

The first two need only a monoid `R`; the third needs `R`
commutative.  The fourth needs the ambient braiding to be a
symmetry: the two legs differ, in a merely braided category, by the
double twist of the leading algebra factor past the second
generator, and that double twist is not the identity.  Accordingly
`freeModShuffle_braiding` is stated over a `SymmetricCategory`, as
is the interchange identity `RS.tensorμ_braiding` behind it.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Associativity -/

section Assoc

variable {D : Type u}

/-- Two multiplications, with a reassociation of the generators
carried past them. -/
@[reassoc]
theorem mul_mul_whiskerRight
    [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    {P Q : D} (g : P ⟶ Q) :
    (μ[R] ▷ R) ▷ P ≫ μ[R] ▷ P ≫ R ◁ g =
      ((α_ R R R).hom ⊗ₘ g) ≫ (R ◁ μ[R]) ▷ Q ≫ μ[R] ▷ Q := by
  rw [tensorHom_def]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc (R ◁ μ[R]) g]
  rw [whisker_exchange μ[R] g, ← comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    MonObj.mul_assoc]
  simp only [Category.assoc]

/-- **Associativity of the shuffle**: shuffling the first two free
modules and then the third agrees, up to the reassociation of the
generators, with shuffling the last two and then the first. -/
@[reassoc]
theorem freeModShuffle_assoc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R]
    (V W Z : D) :
    (freeModShuffle R V W ▷ (R ⊗ Z)) ≫ freeModShuffle R (V ⊗ W) Z
        ≫ (R ◁ (α_ V W Z).hom)
      = (α_ (R ⊗ V) (R ⊗ W) (R ⊗ Z)).hom ≫
          ((R ⊗ V) ◁ freeModShuffle R W Z) ≫
            freeModShuffle R V (W ⊗ Z) := by
  simp only [freeModShuffle, comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% whiskerRight_mul_tensorμ R (V ⊗ W) Z,
    reassoc_of% whiskerLeft_mul_tensorμ R V (W ⊗ Z),
    ← tensor_associativity_assoc R V R W R Z,
    mul_mul_whiskerRight R (α_ V W Z).hom]

end Assoc

/-! ## Unitality -/

section Unit

variable {D : Type u}

/-- Interchanging against a leading unit is a reassociation. -/
@[reassoc]
theorem rightUnitor_inv_whiskerRight_tensorμ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    (W : D) :
    (ρ_ R).inv ▷ (R ⊗ W) ≫ tensorμ R (𝟙_ D) R W =
      (α_ R R W).inv ≫ (R ⊗ R) ◁ (λ_ W).inv := by
  simp only [tensorμ, braiding_tensorUnit_left]
  monoidal

/-- **Left unitality of the shuffle**: filling the first generator
slot with the unit turns the shuffle into the left action of the
free module, written out. -/
@[reassoc]
theorem freeModShuffle_unit_left
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R]
    (W : D) :
    ((ρ_ R).inv ▷ (R ⊗ W)) ≫ freeModShuffle R (𝟙_ D) W
      = ((α_ R R W).inv ≫ μ[R] ▷ W) ≫ (R ◁ (λ_ W).inv) := by
  rw [freeModShuffle, ← Category.assoc,
    rightUnitor_inv_whiskerRight_tensorμ, Category.assoc,
    whisker_exchange μ[R] (λ_ W).inv, Category.assoc]

/-- Interchanging against a trailing unit is the slide. -/
@[reassoc]
theorem whiskerLeft_rightUnitor_inv_tensorμ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    (V : D) :
    (R ⊗ V) ◁ (ρ_ R).inv ≫ tensorμ R V R (𝟙_ D) =
      freeModSlide R V ≫ (R ⊗ R) ◁ (ρ_ V).inv := by
  simp only [tensorμ, freeModSlide, Category.assoc]
  monoidal

end Unit

section Comm

variable {D : Type u}

/-- **Right unitality of the shuffle**: filling the second
generator slot with the unit turns the shuffle into the braided
right action of the free module, written out. -/
@[reassoc]
theorem freeModShuffle_unit_right
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    (V : D) :
    ((R ⊗ V) ◁ (ρ_ R).inv) ≫ freeModShuffle R V (𝟙_ D)
      = ((β_ (R ⊗ V) R).hom ≫ (α_ R R V).inv ≫ μ[R] ▷ V) ≫
          (R ◁ (ρ_ V).inv) := by
  rw [braiding_free_mul, freeModShuffle, ← Category.assoc,
    whiskerLeft_rightUnitor_inv_tensorμ, Category.assoc,
    whisker_exchange μ[R] (ρ_ V).inv, Category.assoc]

end Comm

/-! ## Compatibility with the braiding -/

section Symmetric

variable {D : Type u}

end Symmetric

section Braiding

variable {D : Type u}

/-- **The shuffle commutes with the braiding**: swapping the two
free modules and shuffling agrees with shuffling and swapping the
two generators.  Commutativity of `R` swaps the algebra factors;
the symmetry of the ambient braiding untwists the generators. -/
@[reassoc]
theorem freeModShuffle_braiding
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    (V W : D) :
    (β_ (R ⊗ V) (R ⊗ W)).hom ≫ freeModShuffle R W V
      = freeModShuffle R V W ≫ (R ◁ (β_ V W).hom) := by
  simp only [freeModShuffle, Category.assoc]
  rw [← Category.assoc, tensorμ_braiding, Category.assoc,
    tensorHom_def, Category.assoc,
    whisker_exchange μ[R] (β_ V W).hom, ← comp_whiskerRight_assoc,
    IsCommMonObj.mul_comm]

end Braiding

end RS
