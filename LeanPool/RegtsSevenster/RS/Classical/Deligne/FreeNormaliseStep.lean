/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreePowInsert
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeSlide

/-!
# The normalisation step for a word of free letters

Gathering every head of a word of free letters `A ⊗ V` onto its last
letter can be done one letter at a time: normalise all but the last
letter, and then slide the head so gathered one place along.  That
is `freeCollapse_freeInsert_succ`.

Both sides of the identity begin by collapsing the first `k + 1`
letters, so the whole statement reduces to the last two letters:
absorbing a fresh head and inserting on the top letter is inserting
on the penultimate letter and sliding.  What is left is braiding
bookkeeping around a single multiplication, organised here by the
*head swap* — carrying a head factor past a block and landing it on
the tail of that block.  The interchange is a head swap under a head
(`tensorμ_headSwap`), a head swap past a two-block splits into two
head swaps (`headSwap_tensor_block`), and the slide window is itself
a head swap followed by the action (`freeSlideWin_eq`).  The two
products are formed in the same order on both sides, so no
commutativity is needed for the step.
-/

namespace RS

open CategoryTheory MonoidalCategory
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Carrying a head past a block -/

section HeadSwap

/-- **The head swap**: carry the head factor past a block and land
it on the tail of that block. -/
private noncomputable def headSwap
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (B P V : D) :
    B ⊗ (P ⊗ V) ⟶ P ⊗ (B ⊗ V) :=
  (α_ B P V).inv ≫ ((β_ B P).hom ▷ V) ≫ (α_ P B V).hom

/-- The head swap is natural in the head. -/
@[reassoc]
private theorem headSwap_naturality
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    {B B' : D} (f : B ⟶ B')
    (P V : D) :
    (f ▷ (P ⊗ V)) ≫ headSwap B' P V =
      headSwap B P V ≫ (P ◁ (f ▷ V)) := by
  rw [headSwap, headSwap, associator_inv_naturality_left_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left,
    MonoidalCategory.comp_whiskerRight_assoc,
    associator_naturality_middle, Category.assoc, Category.assoc]

/-- **Splitting the block**: carrying a head past a two-block is
carrying it past each block in turn. -/
@[reassoc]
private theorem headSwap_tensor_block
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (B P V W : D) :
    (α_ B (P ⊗ V) W).hom ≫ headSwap B (P ⊗ V) W =
      (headSwap B P V ▷ W) ≫ (α_ P (B ⊗ V) W).hom ≫
        (P ◁ ((α_ B V W).hom ≫ headSwap B V W)) ≫
        (α_ P V (B ⊗ W)).inv := by
  simp only [headSwap, BraidedCategory.braiding_tensor_right_hom]
  monoidal

end HeadSwap

section HeadSwapSymm

/-- **The interchange is a head swap under a head**: gathering two
heads and then carrying the pair past a block is carrying the first
head past the block and gathering afterwards.  The two braidings the
interchange introduces below the block cancel by symmetry. -/
@[reassoc]
private theorem tensorμ_headSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (B P C V : D) :
    tensorμ B P C V ≫ headSwap (B ⊗ C) P V =
      (α_ B P (C ⊗ V)).hom ≫ headSwap B P (C ⊗ V) ≫
        (P ◁ (α_ B C V).inv) := by
  calc tensorμ B P C V ≫ headSwap (B ⊗ C) P V
      = 𝟙 _ ⊗≫ (B ◁ ((β_ P C).hom ≫ (β_ C P).hom) ▷ V) ⊗≫
          ((β_ B P).hom ▷ C ▷ V) ⊗≫ 𝟙 _ := by
        simp only [tensorμ, headSwap,
          BraidedCategory.braiding_tensor_left_hom]
        monoidal
    _ = _ := by
        rw [SymmetricCategory.symmetry]
        simp only [headSwap, MonoidalCategory.whiskerLeft_id,
          MonoidalCategory.id_whiskerRight]
        monoidal

end HeadSwapSymm

/-! ## The two-letter step -/

section Step

/-- **The slide window as a head swap**: the window carries the head
of the first letter past the ambient factor and acts with it on the
second letter, leaving the unit behind. -/
private theorem freeSlideWin_eq
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D) :
    freeSlideWin A V =
      (α_ A V (A ⊗ V)).hom ≫ headSwap A V (A ⊗ V) ≫
        (V ◁ ((α_ A A V).inv ≫ (μ[A] ▷ V))) ≫
        (((λ_ V).inv ≫ (η[A] ▷ V)) ▷ (A ⊗ V)) := by
  simp only [headSwap, Category.assoc, Iso.hom_inv_id_assoc]
  show (((β_ A V).hom ≫ (((λ_ V).inv ≫ (η[A] ▷ V)) ▷ A)) ▷
      (A ⊗ V)) ≫ ((α_ (A ⊗ V) A (A ⊗ V)).hom ≫
        ((A ⊗ V) ◁ ((α_ A A V).inv ≫ (μ[A] ▷ V)))) = _
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
    associator_naturality_left_assoc, ← whisker_exchange]

/-- **Absorbing a head, then inserting on the top letter**: the same
as inserting on the penultimate letter and sliding.  This is the
whole content of the normalisation step, with the lower block left
generic. -/
@[reassoc]
private theorem freeModShuffle_headSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D)
    (P : D) :
    freeModShuffle A (P ⊗ V) V ≫ headSwap A (P ⊗ V) V ≫
        ((P ◁ ((λ_ V).inv ≫ (η[A] ▷ V))) ▷ (A ⊗ V)) =
      (headSwap A P V ▷ (A ⊗ V)) ≫ (α_ P (A ⊗ V) (A ⊗ V)).hom ≫
        (P ◁ freeSlideWin A V) ≫ (α_ P (A ⊗ V) (A ⊗ V)).inv := by
  rw [freeModShuffle, Category.assoc, headSwap_naturality_assoc,
    tensorμ_headSwap_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    headSwap_tensor_block_assoc,
    ← associator_inv_naturality_right_assoc,
    ← associator_inv_naturality_middle,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [← freeSlideWin_eq]

/-- The step with the insertion of the lower block carried along,
spelt out as the free insertion spells it. -/
private theorem freeModShuffle_insert
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D)
    {P Q : D} (u : P ⟶ Q) :
    freeModShuffle A (P ⊗ V) V ≫
        ((α_ A (P ⊗ V) V).inv ≫ ((β_ A (P ⊗ V)).hom ▷ V) ≫
          (α_ (P ⊗ V) A V).hom ≫
          ((u ⊗ₘ ((λ_ V).inv ≫ (η[A] ▷ V))) ▷ (A ⊗ V))) =
      (((α_ A P V).inv ≫ ((β_ A P).hom ▷ V) ≫ (α_ P A V).hom ≫
          (u ▷ (A ⊗ V))) ▷ (A ⊗ V)) ≫
        (α_ Q (A ⊗ V) (A ⊗ V)).hom ≫ (Q ◁ freeSlideWin A V) ≫
        (α_ Q (A ⊗ V) (A ⊗ V)).inv := by
  have h : freeModShuffle A (P ⊗ V) V ≫ headSwap A (P ⊗ V) V ≫
      ((u ⊗ₘ ((λ_ V).inv ≫ (η[A] ▷ V))) ▷ (A ⊗ V)) =
      ((headSwap A P V ≫ (u ▷ (A ⊗ V))) ▷ (A ⊗ V)) ≫
        (α_ Q (A ⊗ V) (A ⊗ V)).hom ≫ (Q ◁ freeSlideWin A V) ≫
        (α_ Q (A ⊗ V) (A ⊗ V)).inv := by
    rw [MonoidalCategory.tensorHom_def',
      MonoidalCategory.comp_whiskerRight, freeModShuffle_headSwap_assoc,
      MonoidalCategory.comp_whiskerRight, Category.assoc,
      associator_naturality_left_assoc, ← whisker_exchange_assoc,
      associator_inv_naturality_left]
  simpa only [headSwap, Category.assoc] using h

end Step

/-! ## The normalisation step -/

section Normalise

/-- **The normalisation step**: gathering every head of a word of
free letters onto the last letter is gathering the heads of all but
the last onto the penultimate letter and then sliding that head one
place along. -/
theorem freeCollapse_freeInsert_succ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (A : D) [MonObj A]
    [IsCommMonObj A] (V : D) (k : ℕ) :
    freeCollapse A V (k + 2) ≫ freeInsert A V (k + 1) =
      ((freeCollapse A V (k + 1) ≫ freeInsert A V k) ▷ (A ⊗ V)) ≫
        freeSlideTop A V k := by
  have hstep : freeModShuffle A (tensorPow D V (k + 1)) V ≫
      freeInsert A V (k + 1) =
      (freeInsert A V k ▷ (A ⊗ V)) ≫ freeSlideTop A V k :=
    freeModShuffle_insert A V (freeUnitPow A V k)
  refine Eq.trans (eq_whisker (freeCollapse_succ A V (k + 1)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hstep) ?_
  exact Eq.trans (Category.assoc _ _ _).symm
    (eq_whisker (MonoidalCategory.comp_whiskerRight _ _ _).symm _)

end Normalise

end RS
