/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PowMerge

/-!
# The top braiding through the merge

The braiding of the last two strands commutes with the block
merge: whiskering the two-strand braid inside the last block and
merging equals merging and braiding on top.  Abstract braided
coherence first, instantiated to the powers.
-/

namespace RS

open CategoryTheory MonoidalCategory

section Abstract

variable {C : Type*}

/-- The two-strand top braid over a prefix. -/
private def topB [Category C] [MonoidalCategory C] [BraidedCategory C]
    (X V : C) : (X ⊗ V) ⊗ V ⟶ (X ⊗ V) ⊗ V :=
  (α_ X V V).hom ≫ (X ◁ (β_ V V).hom) ≫ (α_ X V V).inv

/-- Braiding the last two strands is natural in the prefix. -/
private theorem topB_natural
    [Category C] [MonoidalCategory C] [BraidedCategory C]
    {X Y : C} (V : C) (r : X ⟶ Y) :
    ((r ▷ V) ▷ V) ≫ topB Y V = topB X V ≫ ((r ▷ V) ▷ V) := by
  unfold topB
  simp only [Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left]

-- Raised budget: the exchange is a coherence computation in an
-- arbitrary monoidal category, so both associators are unfolded.
/-- **The abstract merge-braid exchange**: whiskering the braid
inside the last two-strand block and merging equals merging and
braiding on top. -/
private theorem whisker_topB_merge
    [Category C] [MonoidalCategory C] [BraidedCategory C]
    (A B V : C) {D : C}
    (r : A ⊗ B ⟶ D) :
    (A ◁ topB B V) ≫
      (α_ A (B ⊗ V) V).inv ≫
        (((α_ A B V).inv ≫ (r ▷ V)) ▷ V) =
    ((α_ A (B ⊗ V) V).inv ≫
        (((α_ A B V).inv ≫ (r ▷ V)) ▷ V)) ≫ topB D V := by
  have hβ : A ◁ (B ◁ (β_ V V).hom) =
      (α_ A B (V ⊗ V)).inv ≫ ((A ⊗ B) ◁ (β_ V V).hom) ≫
        (α_ A B (V ⊗ V)).hom := by
    have h := associator_inv_naturality_right A B (β_ V V).hom
    calc A ◁ (B ◁ (β_ V V).hom)
        = (A ◁ (B ◁ (β_ V V).hom) ≫
            (α_ A B (V ⊗ V)).inv) ≫ (α_ A B (V ⊗ V)).hom := by
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = ((α_ A B (V ⊗ V)).inv ≫
            ((A ⊗ B) ◁ (β_ V V).hom)) ≫
              (α_ A B (V ⊗ V)).hom := by rw [h]
      _ = (α_ A B (V ⊗ V)).inv ≫ ((A ⊗ B) ◁ (β_ V V).hom) ≫
            (α_ A B (V ⊗ V)).hom := Category.assoc _ _ _
  have hpre : (A ◁ (α_ B V V).hom) ≫ (α_ A B (V ⊗ V)).inv =
      (α_ A (B ⊗ V) V).inv ≫ ((α_ A B V).inv ▷ V) ≫
        (α_ (A ⊗ B) V V).hom := by
    monoidal
  have hpost : (α_ A B (V ⊗ V)).hom ≫ (A ◁ (α_ B V V).inv) ≫
      (α_ A (B ⊗ V) V).inv ≫ ((α_ A B V).inv ▷ V) =
      (α_ (A ⊗ B) V V).inv := by
    monoidal
  have hnat := topB_natural (X := A ⊗ B) (Y := D) V r
  unfold topB at hnat ⊢
  simp only [MonoidalCategory.whiskerLeft_comp,
    comp_whiskerRight, Category.assoc] at hnat ⊢
  rw [hβ]
  simp only [Category.assoc]
  rw [hnat]
  slice_lhs 1 2 => rw [hpre]
  slice_lhs 5 8 => rw [hpost]

end Abstract

/-- **The merge-braid exchange on powers**: braiding inside the
last two-strand block and merging equals merging and braiding on
top. -/
theorem powMerge_topBraid (V : SuperVect) (a : ℕ) :
    (superPow V a ◁ topBraid V 0) ≫ powMerge V a 2 =
      powMerge V a 2 ≫ topBraid V a := by
  change (superPow V a ◁ topB (superPow V 0) V) ≫
      (α_ (superPow V a) (superPow V 1) V).inv ≫
        (((α_ (superPow V a) (superPow V 0) V).inv ≫
          ((ρ_ (superPow V a)).hom ▷ V)) ▷ V) =
    ((α_ (superPow V a) (superPow V 1) V).inv ≫
        (((α_ (superPow V a) (superPow V 0) V).inv ≫
          ((ρ_ (superPow V a)).hom ▷ V)) ▷ V)) ≫
      topB (superPow V a) V
  exact whisker_topB_merge (superPow V a) (superPow V 0) V
    (ρ_ (superPow V a)).hom

/-- The block merge is an isomorphism. -/
theorem powMerge_isIso (V : SuperVect) (a : ℕ) :
    ∀ b : ℕ, IsIso (powMerge V a b)
  | 0 => inferInstanceAs (IsIso (ρ_ (superPow V a)).hom)
  | b + 1 => by
    have := powMerge_isIso V a b
    exact inferInstanceAs (IsIso
      ((α_ (superPow V a) (superPow V b) V).inv ≫
        ((powMerge V a b) ▷ V)))

/-- Every power element is a merge image. -/
theorem powMerge_evenMap_surjective (V : SuperVect)
    (a b : ℕ) :
    Function.Surjective
      (((powMerge V a b) : SuperVect.Hom _ _).evenMap) := by
  have := powMerge_isIso V a b
  intro v
  refine ⟨((CategoryTheory.inv (powMerge V a b)) :
    SuperVect.Hom _ _).evenMap v, ?_⟩
  have h := congrArg (fun z : (superPow V (a + b) ⟶
      superPow V (a + b)) =>
    (z : SuperVect.Hom _ _).evenMap v)
    (IsIso.inv_hom_id (powMerge V a b))
  exact h

/-- Every odd power element is a merge image. -/
theorem powMerge_oddMap_surjective (V : SuperVect)
    (a b : ℕ) :
    Function.Surjective
      (((powMerge V a b) : SuperVect.Hom _ _).oddMap) := by
  have := powMerge_isIso V a b
  intro v
  refine ⟨((CategoryTheory.inv (powMerge V a b)) :
    SuperVect.Hom _ _).oddMap v, ?_⟩
  have h := congrArg (fun z : (superPow V (a + b) ⟶
      superPow V (a + b)) =>
    (z : SuperVect.Hom _ _).oddMap v)
    (IsIso.inv_hom_id (powMerge V a b))
  exact h

end RS
