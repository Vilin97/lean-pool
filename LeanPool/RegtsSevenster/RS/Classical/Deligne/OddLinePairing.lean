/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29

/-!
# The odd line is self-dual

The square trivialisation of an odd line is an exact pairing of
the line with itself.  The two triangle identities are forced by
the sign of the self-braiding: rearranging a triple of lines
cyclically costs two transpositions, hence no sign at all, and
the hexagon turns that cyclic rearrangement into a braiding past
the trivialisation, which the unit coherences absorb.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- Whiskering a negated identity on the right negates it. -/
theorem neg_id_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    (X Y : D) :
    (-𝟙 X) ▷ Y = -𝟙 (X ⊗ Y) := by
  change (tensorRight Y).map (-𝟙 X) = _
  rw [Functor.map_neg]
  simp

/-- Whiskering a negated identity on the left negates it. -/
theorem whiskerLeft_neg_id [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    (X Y : D) :
    X ◁ (-𝟙 Y) = -𝟙 (X ⊗ Y) := by
  change (tensorLeft X).map (-𝟙 Y) = _
  rw [Functor.map_neg]
  simp

/-- **Cyclic rearrangement of a triple of lines is free**: the
two transpositions each contribute a sign, and the signs
cancel. -/
theorem OddLine.cycle_triple
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) :
    ((β_ L.obj L.obj).hom ▷ L.obj) ≫
        (α_ L.obj L.obj L.obj).hom ≫
        (L.obj ◁ (β_ L.obj L.obj).hom) =
      (α_ L.obj L.obj L.obj).hom := by
  rw [L.braid_neg, neg_id_whiskerRight, whiskerLeft_neg_id]
  simp

/-- **Cyclic rearrangement of a triple of lines is free**, in the
mirror grouping. -/
theorem OddLine.cycle_triple'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) :
    (L.obj ◁ (β_ L.obj L.obj).hom) ≫
        (α_ L.obj L.obj L.obj).inv ≫
        ((β_ L.obj L.obj).hom ▷ L.obj) =
      (α_ L.obj L.obj L.obj).inv := by
  rw [L.braid_neg, neg_id_whiskerRight, whiskerLeft_neg_id]
  simp

/-- **The first triangle identity of the odd line.** -/
theorem OddLine.evaluation_coevaluation
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) :
    (L.sq.inv ▷ L.obj) ≫ (α_ L.obj L.obj L.obj).hom ≫
        (L.obj ◁ L.sq.hom) =
      (λ_ L.obj).hom ≫ (ρ_ L.obj).inv := by
  have hcyc : (α_ L.obj L.obj L.obj).inv ≫
      ((β_ L.obj L.obj).hom ▷ L.obj) ≫
      (α_ L.obj L.obj L.obj).hom ≫
      (L.obj ◁ (β_ L.obj L.obj).hom) =
      (β_ L.obj (L.obj ⊗ L.obj)).hom ≫
        (α_ L.obj L.obj L.obj).hom := by
    rw [BraidedCategory.braiding_tensor_right_hom L.obj L.obj
      L.obj]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hkey : (L.obj ◁ L.sq.inv) ≫
      (α_ L.obj L.obj L.obj).inv ≫
      ((β_ L.obj L.obj).hom ▷ L.obj) ≫
      (α_ L.obj L.obj L.obj).hom ≫
      (L.obj ◁ (β_ L.obj L.obj).hom) ≫
      (L.obj ◁ L.sq.hom) = 𝟙 (L.obj ⊗ 𝟙_ D) := by
    rw [reassoc_of% L.cycle_triple, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id]
  rw [reassoc_of% hcyc, ← Category.assoc,
    BraidedCategory.braiding_naturality_right L.obj L.sq.inv,
    Category.assoc] at hkey
  have hbr : (β_ L.obj (𝟙_ D)).inv =
      (λ_ L.obj).hom ≫ (ρ_ L.obj).inv := by
    refine (cancel_epi (β_ L.obj (𝟙_ D)).hom).mp ?_
    rw [Iso.hom_inv_id, ← Category.assoc, braiding_leftUnitor,
      Iso.hom_inv_id]
  rw [← hbr]
  refine Eq.trans ?_ (Category.comp_id _)
  exact (Iso.eq_inv_comp _).mpr hkey

/-- **The second triangle identity of the odd line.** -/
theorem OddLine.coevaluation_evaluation
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) :
    (L.obj ◁ L.sq.inv) ≫ (α_ L.obj L.obj L.obj).inv ≫
        (L.sq.hom ▷ L.obj) =
      (ρ_ L.obj).hom ≫ (λ_ L.obj).inv := by
  have hcyc : (α_ L.obj L.obj L.obj).hom ≫
      (L.obj ◁ (β_ L.obj L.obj).hom) ≫
      (α_ L.obj L.obj L.obj).inv ≫
      ((β_ L.obj L.obj).hom ▷ L.obj) =
      (β_ (L.obj ⊗ L.obj) L.obj).hom ≫
        (α_ L.obj L.obj L.obj).inv := by
    rw [BraidedCategory.braiding_tensor_left_hom L.obj L.obj
      L.obj]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hkey : (L.sq.inv ▷ L.obj) ≫
      (α_ L.obj L.obj L.obj).hom ≫
      (L.obj ◁ (β_ L.obj L.obj).hom) ≫
      (α_ L.obj L.obj L.obj).inv ≫
      ((β_ L.obj L.obj).hom ▷ L.obj) ≫
      (L.sq.hom ▷ L.obj) = 𝟙 (𝟙_ D ⊗ L.obj) := by
    rw [reassoc_of% L.cycle_triple', Iso.hom_inv_id_assoc,
      ← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id,
      MonoidalCategory.id_whiskerRight]
  rw [reassoc_of% hcyc, ← Category.assoc,
    BraidedCategory.braiding_naturality_left L.sq.inv L.obj,
    Category.assoc] at hkey
  have hbr : (β_ (𝟙_ D) L.obj).inv =
      (ρ_ L.obj).hom ≫ (λ_ L.obj).inv := by
    refine (cancel_epi (β_ (𝟙_ D) L.obj).hom).mp ?_
    rw [Iso.hom_inv_id, ← Category.assoc, braiding_rightUnitor,
      Iso.hom_inv_id]
  rw [← hbr]
  refine Eq.trans ?_ (Category.comp_id _)
  exact (Iso.eq_inv_comp _).mpr hkey

/-- **The odd line is self-dual**: the square trivialisation is
an exact pairing of the line with itself. -/
@[implicit_reducible]
noncomputable def OddLine.exactPairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) :
    ExactPairing L.obj L.obj where
  coevaluation' := L.sq.inv
  evaluation' := L.sq.hom
  coevaluation_evaluation' := L.coevaluation_evaluation
  evaluation_coevaluation' := L.evaluation_coevaluation

end RS
